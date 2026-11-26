// membership.go — what the dimension says: the n-vectors are closed
// under the pointwise operations and contain the basis vectors below n;
// the dimensions are nested; and two n-vectors are equal exactly when
// their active entries agree. (Closure under the fold is VecIterate, in
// subspace.go: a subspace's closure, read at the n-vectors.)
//
// `vec⟨n⟩(u)` unfolds to "u is zero from index n on"; a body reads
// that off the definition entry as a fact, so the closure laws are the
// ring's laws at one arbitrary index past the range. The closures under
// the sum, the negation, the difference and the scaling are proved at a
// ring on a set c (VecAddOn, VecNegOn, VecSubOn, and VecSmulOn, which asks
// the scalar to lie in c), and the whole-type laws are their views at 𝕌.

package vec_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
)

// VecZero — the zero vector is an n-vector for every n.
var VecZero = vecZeroThm{family.Add(registry.ProofEntry{
	Name: "VecZero",
	Key:  "prop_6e4ec16ac8a1ae2c",
	Build: family.Theorem("∀zero:A. ∀n:num. vec⟨n⟩(zero, vec_zero(zero))",
		func(a *Argument, zero, n Term) {
			a.Do(Unfold(VecDef), Unfold(VecZeroDef))
		}),
})}

// VecAdd — the sum of two n-vectors is an n-vector: VecAddOn on the
// whole type.
var VecAdd = vecAddThm{family.Add(registry.ProofEntry{
	Name: "VecAdd",
	Key:  "prop_323ddabea50a743e",
	Build: comm_ring.CommRingAtUniverse.Law(Statement{
		Binders: "∀n:num. ∀u v:(num → A).",
		Hypotheses: []string{
			"vec⟨n⟩(u)",
			"vec⟨n⟩(v)",
		},
		Conclusion: "vec⟨n⟩(u + v)",
	}, VecAddOn),
})}

// VecNeg — the negation of an n-vector is an n-vector: VecNegOn on the
// whole type.
var VecNeg = vecNegThm{family.Add(registry.ProofEntry{
	Name: "VecNeg",
	Key:  "prop_c4fb8bdc847b2ef3",
	Build: comm_ring.CommRingAtUniverse.Law(Statement{
		Binders: "∀n:num. ∀u:(num → A).",
		Hypotheses: []string{
			"vec⟨n⟩(u)",
		},
		Conclusion: "vec⟨n⟩(-u)",
	}, VecNegOn),
})}

// VecSmul — a scalar multiple of an n-vector is an n-vector: VecSmulOn
// on the whole type.
var VecSmul = vecSmulThm{family.Add(registry.ProofEntry{
	Name: "VecSmul",
	Key:  "prop_11568fd3e05cfd0e",
	Build: comm_ring.CommRingAtUniverse.Law(Statement{
		Binders: "∀n:num. ∀c:A. ∀u:(num → A).",
		Hypotheses: []string{
			"vec⟨n⟩(u)",
		},
		Conclusion: "vec⟨n⟩(c • u)",
	}, VecSmulOn),
})}

// VecSub — the difference of two n-vectors is an n-vector: VecSubOn on
// the whole type.
var VecSub = vecSubThm{family.Add(registry.ProofEntry{
	Name: "VecSub",
	Key:  "prop_8446349768a2f84b",
	Build: comm_ring.CommRingAtUniverse.Law(Statement{
		Binders: "∀n:num. ∀u v:(num → A).",
		Hypotheses: []string{
			"vec⟨n⟩(u)",
			"vec⟨n⟩(v)",
		},
		Conclusion: "vec⟨n⟩(u - v)",
	}, VecSubOn),
})}

// VecBasisVector — a basis vector whose index lies inside the range is a
// vector of that dimension. The one place it is not zero is index k,
// and an index past the range has already passed k, so the guard in
// the basis vector's definition fails there and the entry is zero.
//
// No ring is asked for: its zero and its one enter only as the two
// values the basis vector takes, and the argument is the definitions
// plus one order step, so the law holds for ANY two values and is
// stated so.
var VecBasisVector = vecBasisVectorThm{family.Add(registry.ProofEntry{
	Name: "VecBasisVector",
	Key:  "prop_15b4c90e2ef37f0e",
	Build: family.Theorem(Statement{
		Binders: "∀zero one:A. ∀m k:num.",
		Hypotheses: []string{
			"k < m",
		},
		Conclusion: "vec⟨m⟩(zero, basis_vector(zero, one, k))",
	},
		func(a *Argument, zero, one, m, k Term, below Fact) {
			a.Do(Unfold(VecDef))
			a.Fix("i")
			past := a.Assume()
			offBasis := a.Have(
				"k lies inside the range and i past it, so the two indices differ",
				"i ≠ k",
				By(below, past, nat_order.LessThanLessEqTrans, nat_order.LessThanIrrefl))
			a.Show(
				"and away from k the basis vector's entry is the ring's zero",
				By(Normalized, offBasis, BasisVectorDef))
		}),
})}

// VecMono — the dimensions are nested: an m-vector is an n-vector for
// every n ≥ m, since a sequence zero from index m on is zero from any
// later index on.
var VecMono = vecMonoThm{family.Add(registry.ProofEntry{
	Name: "VecMono",
	Key:  "prop_7fd84b68aeb14328",
	Build: family.Theorem(Statement{
		Binders: "∀zero:A. ∀m n:num. ∀u:(num → A).",
		Hypotheses: []string{
			"m ≤ n",
			"vec⟨m⟩(zero, u)",
		},
		Conclusion: "vec⟨n⟩(zero, u)",
	},
		func(a *Argument, zero, m, n, u Term, below, member Fact) {
			past := a.Have(
				"u is zero from index m on",
				"∀i:num. m ≤ i ⇒ u(i) = zero",
				By(member, VecDef))
			a.Show(
				"and an index at or past n is at or past m",
				Unfold(VecDef),
				By(below, past, nat_order.LessEqTrans))
		}),
})}

// Extensionality — two n-vectors are equal exactly when they agree on
// the active range: past it neither has anything of its own to say.
var Extensionality = extensionalityThm{family.Add(registry.ProofEntry{
	Name: "Extensionality",
	Key:  "prop_772dfb37efa1bf35",
	Build: family.Theorem(Statement{
		Binders: "∀zero:A. ∀n:num. ∀u v:(num → A).",
		Hypotheses: []string{
			"vec⟨n⟩(zero, u)",
			"vec⟨n⟩(zero, v)",
		},
		Conclusion: "u = v ⇔ ∀i:num. i < n ⇒ u(i) = v(i)",
	},
		func(a *Argument, zero, n, u, v Term, both Fact) {
			uPast := a.Have(
				"u is zero past the range",
				"∀i:num. n ≤ i ⇒ u(i) = zero",
				By(both, VecDef))
			vPast := a.Have(
				"and so is v",
				"∀i:num. n ≤ i ⇒ v(i) = zero",
				By(both, VecDef))
			a.Iff()
			a.Forward(
				"equal sequences agree at every index",
				func(b *Argument, eq Fact) {
					b.Do(eq.Rw(), Basic())
				})
			a.Backward(
				"they agree on the range, and past it both are zero",
				func(b *Argument, agree Fact) {
					b.Show(
						"so they agree at every index",
						Funext(),
						By(Normalized, agree, uPast, vPast, nat_order.NotLessThan))
				})
		}),
})}

// VecAddOn — at a ring on a set c, the sum of two n-vectors is an
// n-vector: past the range both entries are zero, and zero plus zero is
// zero, the ring's zero lying in c. Nothing is asked of the other
// entries, since only the padding is read.
var VecAddOn = vecAddOnThm{family.Add(registry.ProofEntry{
	Name: "VecAddOn",
	Key:  "prop_83cbf49a4ca0b59b",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀n:num. ∀u v:(num → A).",
		Hypotheses: []string{
			"vec⟨n⟩(u)",
			"vec⟨n⟩(v)",
		},
		Conclusion: "vec⟨n⟩(u + v)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], n *Expr[Nat], u, v *Vec[A, DimN], both Fact) {
			uPast := a.Have(
				"u is zero past the range",
				"∀i:num. n ≤ i ⇒ u(i) = R.zero",
				By(both, VecDef))
			vPast := a.Have(
				"and so is v",
				"∀i:num. n ≤ i ⇒ v(i) = R.zero",
				By(both, VecDef))
			zeroSum := a.Have(
				"zero plus zero is zero, zero lying in c",
				"R.zero + R.zero = R.zero",
				By(comm_ring.ZeroIn.Read(ring), comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(ring))))
			a.Show(
				"past the range the sum's entry is zero plus zero, which is zero",
				Unfold(VecDef),
				Unfold(VecAddDef),
				a.ForEach(func(i *Expr[Nat]) Action {
					return By(Normalized, uPast.At(i), vPast.At(i), zeroSum)
				}))
		}),
})}

// VecNegOn — at a ring on c, the negation of an n-vector is an n-vector:
// past the range the entry is the negation of zero, which is zero.
var VecNegOn = vecNegOnThm{family.Add(registry.ProofEntry{
	Name: "VecNegOn",
	Key:  "prop_a3d4c9f7506f0324",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀n:num. ∀u:(num → A).",
		Hypotheses: []string{
			"vec⟨n⟩(u)",
		},
		Conclusion: "vec⟨n⟩(-u)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], n *Expr[Nat], u *Vec[A, DimN], member Fact) {
			additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
			past := a.Have(
				"u is zero past the range",
				"∀i:num. n ≤ i ⇒ u(i) = R.zero",
				By(member, VecDef))
			a.Show(
				"past the range the entry is the negation of zero, which is zero",
				Unfold(VecDef),
				Unfold(VecNegDef),
				a.ForEach(func(i *Expr[Nat]) Action {
					return By(Normalized, past.At(i), group.InvOneOn.Read(additive))
				}))
		}),
})}

// VecSmulOn — at a ring on c, a member of c times an n-vector is an
// n-vector: past the range the entry is a times zero, which is zero, a
// lying in c.
var VecSmulOn = vecSmulOnThm{family.Add(registry.ProofEntry{
	Name: "VecSmulOn",
	Key:  "prop_3674749259b8f2b3",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀n:num. ∀a:A. ∀u:(num → A).",
		Hypotheses: []string{
			"a ∈ R.carrier",
			"vec⟨n⟩(u)",
		},
		Conclusion: "vec⟨n⟩(a • u)",
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			n *Expr[Nat],
			a *Expr[A],
			u *Vec[A, DimN],
			both Fact,
		) {
			past := arg.Have(
				"u is zero past the range",
				"∀i:num. n ≤ i ⇒ u(i) = R.zero",
				By(both, VecDef))
			zeroProduct := arg.Have(
				"a times zero is zero, a lying in c",
				"a * R.zero = R.zero",
				By(both, comm_ring.MulRightZeroOn.Read(ring)))
			arg.Show(
				"past the range the scaled entry is a times zero, which is zero",
				Unfold(VecDef),
				Unfold(VecScalarMulDef),
				arg.ForEach(func(i *Expr[Nat]) Action {
					return By(Normalized, past.At(i), zeroProduct)
				}))
		}),
})}

// VecSubOn — at a ring on c, the difference of two n-vectors is an
// n-vector: past the range the entry is zero less zero, which is zero.
var VecSubOn = vecSubOnThm{family.Add(registry.ProofEntry{
	Name: "VecSubOn",
	Key:  "prop_894b584b3b0b3039",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀n:num. ∀u v:(num → A).",
		Hypotheses: []string{
			"vec⟨n⟩(u)",
			"vec⟨n⟩(v)",
		},
		Conclusion: "vec⟨n⟩(u - v)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], n *Expr[Nat], u, v *Vec[A, DimN], both Fact) {
			uPast := a.Have(
				"u is zero past the range",
				"∀i:num. n ≤ i ⇒ u(i) = R.zero",
				By(both, VecDef))
			vPast := a.Have(
				"and so is v",
				"∀i:num. n ≤ i ⇒ v(i) = R.zero",
				By(both, VecDef))
			zeroDifference := a.Have(
				"zero less zero is zero, zero lying in c",
				"R.zero - R.zero = R.zero",
				ByArith(ring, comm_ring.ZeroIn.Read(ring)))
			a.Show(
				"past the range the difference's entry is zero less zero, which is zero",
				Unfold(VecDef),
				Unfold(VecSubDef),
				a.ForEach(func(i *Expr[Nat]) Action {
					return By(Normalized, uPast.At(i), vPast.At(i), zeroDifference)
				}))
		}),
})}

// VecDimZero — a sequence that is a 0-vector is the zero sequence: every
// index is at least 0, so every entry lies past the range and is zero.
var VecDimZero = vecDimZeroThm{family.Add(registry.ProofEntry{
	Name: "VecDimZero",
	Key:  "prop_ba983bf81c34e288",
	Build: family.Theorem(Statement{
		Binders: "∀zero:A. ∀u:(num → A).",
		Hypotheses: []string{
			"vec⟨0⟩(zero, u)",
		},
		Conclusion: "u = vec_zero(zero)",
	},
		func(a *Argument, zero *Expr[A], u *Arrow[Nat, A], member Fact) {
			a.Show(
				"entry by entry, every index is at least 0, so the entry of u is zero",
				Funext(),
				Simp(Fwd(VecZeroDef)),
				By(member, VecDef, nat_order.ZeroLessEq))
		}),
})}
