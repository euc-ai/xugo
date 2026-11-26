// simplicial_chain.go — the alternating face map complex of a
// simplicial set over a commutative ring on a set: the chains in
// dimension n are the free module on the n-simplices, the boundary of
// a generator is the alternating sum of its faces, and two boundaries
// in a row are zero, so the chains form a chain complex, and a
// simplicial map induces a chain map.
//
// Every law is under the ring on c and, but for the module of n-chains
// and the chain map of a simplicial map, the simplicial set X, so the
// ring's components and the simplicial set's are implicit:
// `face_sum(n, x)`, `simplicial_chains(c, n)`, `simplicial_boundary(n)`. A module over
// the ring is two record values: the ring is the record `R`, and the n-chains are `mk_module(fun_add⟨D:D⟩,
// fun_zero⟨D:D⟩, fun_neg⟨D:D⟩, fun_smul⟨D:D⟩, simplicial_chains(c, n))`,
// the free module's pointwise operations with the index type tied, as
// the free module chapter spells them.

package simplicial_chain

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// underSimplicial opens a law under one simplicial set: the ring on c is the law's
// structure, and the simplicial set is the body's first hypothesis.
const underSimplicial = "∀X:simplicial_ops(D). simplicial_set(X) ⇒ "

// ---------------------------------------------------------------------------
// The face sum and the boundary
// ---------------------------------------------------------------------------

// FaceSumDef — `face_sum(add, zero, one, neg, mul, d, n, x)`: the
// alternating sum Σ_{i ≤ n} (−1)^i δ(d(n, i, x)) of the generators at
// the faces of the n-simplex x, in the free module. Under the ring and
// the simplicial set the text writes `face_sum(n, x)`.
var FaceSumDef = faceSumDefThm{family.Define(registry.DefEntry{
	Name:     "FaceSumDef",
	Key:      "prop_92fcd423a9f5b430",
	Const:    "face_sum",
	Type:     "(A → A → A) → A → A → (A → A) → (A → A → A) → (num → num → D → D) → num → D → D → A",
	Implicit: []string{"add", "zero", "one", "neg", "mul", "d"},
	Equations: []string{
		"∀add:(A → A → A). " +
			"∀zero one:A. " +
			"∀neg:(A → A). " +
			"∀mul:(A → A → A). " +
			"∀d:(num → num → D → D). " +
			"∀n:num. " +
			"∀x:D. " +
			"    face_sum(add, zero, one, neg, mul, d, n, x) = " +
			"    module_sum(fun_add⟨D:D⟩(add), " +
			"        fun_zero⟨D:D⟩(zero), " +
			"        0 .. n, " +
			"        λi:num. " +
			"            fun_smul⟨D:D⟩(mul, alternating_sign(one, neg, i), delta_at(zero, one, d(n, i, x))))",
	},
	Reading: "At n = 0 the sum has the one term δ(d(0, 0, x)), a face no " +
		"axiom reads; the complex never reads the boundary out of degree 0 either.",
})}

// SimplicialChainsDef — `simplicial_chains(zero, X, c, n)`: the
// n-chains, the free module on the n-simplices over the ring on c.
// Under the ring and the simplicial set the text writes
// `simplicial_chains(c, n)`, and `simplicial_chains(c)` is the sequence.
var SimplicialChainsDef = simplicialChainsDefThm{family.Define(registry.DefEntry{
	Name:     "SimplicialChainsDef",
	Key:      "prop_3fac77e1eff26505",
	Const:    "simplicial_chains",
	Type:     "A → simplicial_ops(D) → set(A) → num → set(D → A)",
	Implicit: []string{"zero", "X"},
	Equations: []string{
		"∀zero:A. ∀X:simplicial_ops(D). ∀c:set(A). ∀n:num. " +
			"    simplicial_chains(zero, X, c, n) = finite_supp(zero, c, X.simplices(n))",
	},
})}

// ChainsModule — the n-chains are by definition the free module on
// X(n), a module over the ring by FreeModuleOn read at the ring's parts
// packed into one value; X need not be a simplicial set.
var ChainsModule = chainsModuleThm{family.Add(registry.ProofEntry{
	Name: "ChainsModule",
	Key:  "prop_ce3214c79ab00541",
	Build: comm_ring.CommRingOn.Law("∀X:simplicial_ops(D). ∀n:num. "+
		"    module_on(R, "+
		"        mk_module(fun_add⟨D:D⟩(R.add), "+
		"            fun_zero⟨D:D⟩(R.zero), "+
		"            fun_neg⟨D:D⟩(R.neg), "+
		"            fun_smul⟨D:D⟩(R.mul), "+
		"            simplicial_chains(R.zero, X, R.carrier, n)))",
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			_ *Expr[simplicial_set.SimplicialOps[D]],
			_ *Expr[Nat],
		) {
			packed := a.TermAs[module_record.RingOps[A]]("R")
			free := a.Simplified(
				GroupPremises(ring, free_module.FreeModuleOn.At(packed, a.TermAs[Set[D]]("X.simplices(n)"))),
				Fwd(free_module.FreeModuleRecordDef))
			a.Show(
				"the n-chains, the free module on X(n), are a module over the ring",
				Simp(Fwd(SimplicialChainsDef)),
				By(free, ring))
		}),
})}

// SimplicialBoundaryDef — `simplicial_boundary(add, zero, one, neg, mul,
// d, n)`: the boundary out of dimension n, the face sum extended
// linearly from the generators to the chains. Under the ring and the
// simplicial set the text writes `simplicial_boundary(n)`, and the bare
// `simplicial_boundary` is the sequence of boundaries.
var SimplicialBoundaryDef = simplicialBoundaryDefThm{family.Define(registry.DefEntry{
	Name:  "SimplicialBoundaryDef",
	Key:   "prop_657c8e337fc08dfe",
	Const: "simplicial_boundary",
	Type: "(A → A → A) → " +
		"A → " +
		"A → " +
		"(A → A) → " +
		"(A → A → A) → " +
		"(num → num → D → D) → " +
		"num → " +
		"(D → A) → " +
		"D → " +
		"A",
	Implicit: []string{"add", "zero", "one", "neg", "mul", "d"},
	Equations: []string{
		"∀add:(A → A → A). " +
			"∀zero one:A. " +
			"∀neg:(A → A). " +
			"∀mul:(A → A → A). " +
			"∀d:(num → num → D → D). " +
			"∀n:num. " +
			"∀f:(D → A). " +
			"    simplicial_boundary(add, zero, one, neg, mul, d, n, f) = " +
			"    free_lift(zero, " +
			"        fun_add⟨D:D⟩(add), " +
			"        fun_zero⟨D:D⟩(zero), " +
			"        fun_smul⟨D:D⟩(mul), " +
			"        λx:D. face_sum(add, zero, one, neg, mul, d, n, x), " +
			"        f)",
	},
	Deps: []registry.EntryLike{FaceSumDef},
})}

// FaceSumIn — the face sum of an (n+1)-simplex is an n-chain: a sum over
// a finite segment of members of the free module on X(n), each the
// generator at a face of x scaled by a sign in c.
var FaceSumIn = faceSumInThm{family.Add(registry.ProofEntry{
	Name: "FaceSumIn",
	Key:  "prop_c2cc63741a0cef51",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀X:simplicial_ops(D). ∀n:num. ∀x:D.",
		Hypotheses: []string{
			"simplicial_set(X)",
			"x ∈ X.simplices(n + 1)",
		},
		Conclusion: "face_sum(n + 1, x) ∈ simplicial_chains(R.carrier, n)",
	},
		func(
			a *Argument,
			ring Fact,
			_ *Expr[simplicial_set.SimplicialOps[D]],
			n *Expr[Nat],
			x *Expr[D],
			simplicial, xIn Fact,
		) {
			chains := a.Have(
				"the n-chains, the free module on X(n), are a module over the ring",
				"module_on(R, "+
					"    mk_module(fun_add⟨D:D⟩(R.add), "+
					"        fun_zero⟨D:D⟩(R.zero), "+
					"        fun_neg⟨D:D⟩(R.neg), "+
					"        fun_smul⟨D:D⟩(R.mul), "+
					"        finite_supp(R.zero, R.carrier, X.simplices(n))))",
				Simp(Rev(SimplicialChainsDef)),
				By(ChainsModule.Read(ring)))
			termIn := a.Have(
				"each term scales the generator at a face of x by a sign, a member of the n-chains",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"i ≤ n + 1",
					},
					Conclusion: "fun_smul(alternating_sign(i), delta_at(X.d(n + 1, i, x))) ∈ " +
						"finite_supp(R.zero, R.carrier, X.simplices(n))",
				},
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					bound := b.Assume()
					face := b.Have(
						"the i-th face of x is an n-simplex",
						"X.d(n + 1, i, x) ∈ X.simplices(n)",
						By(simplicial_set.FaceIn.Read(simplicial).At(n, i, x), xIn, bound))
					b.Show(
						"a sign in c scales a generator of the n-chains",
						By(
							face,
							b.Simplified(module.SmulIn.Read(chains)),
							free_module.DeltaAtIn.Read(ring),
							comm_ring.AlternatingSignIn.Read(ring)))
				}))
			sumIn := a.Simplified(module.ModuleSumIn.Read(chains).At(a.TermAs[Set[Nat]]("0 .. n + 1"),
				a.TermAs[Fun[Nat, Fun[D, A]]]("λi:num. fun_smul(alternating_sign(i), delta_at(X.d(n + 1, i, x)))")))
			a.Show(
				"so the face sum, the sum of the terms over the finite segment 0 .. n + 1, is an n-chain",
				Simp(Fwd(FaceSumDef), Fwd(SimplicialChainsDef)),
				By(sumIn, termIn, num_segment.Finite))
		}),
})}

// BoundaryHom — the boundary out of dimension n + 1 is the face sum
// extended linearly from the generators of the free module on X(n + 1);
// the face sum carries X(n + 1) into the n-chains, themselves a module,
// so the extension is a homomorphism into them.
var BoundaryHom = boundaryHomThm{family.Add(registry.ProofEntry{
	Name: "BoundaryHom",
	Key:  "prop_84dca989e8251de6",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀X:simplicial_ops(D). ∀n:num.",
		Hypotheses: []string{
			"simplicial_set(X)",
		},
		Conclusion: "module_homomorphism(R, " +
			"    mk_module(fun_add⟨D:D⟩(R.add), " +
			"        fun_zero⟨D:D⟩(R.zero), " +
			"        fun_neg⟨D:D⟩(R.neg), " +
			"        fun_smul⟨D:D⟩(R.mul), " +
			"        simplicial_chains(R.carrier, n + 1)), " +
			"    mk_module(fun_add⟨D:D⟩(R.add), " +
			"        fun_zero⟨D:D⟩(R.zero), " +
			"        fun_neg⟨D:D⟩(R.neg), " +
			"        fun_smul⟨D:D⟩(R.mul), " +
			"        simplicial_chains(R.carrier, n)), " +
			"    simplicial_boundary(n + 1))",
	},
		func(
			a *Argument,
			ring Fact,
			_ *Expr[simplicial_set.SimplicialOps[D]],
			_ *Expr[Nat],
			simplicial Fact,
		) {
			chains := a.Have(
				"the n-chains, the free module on X(n), are a module over the ring",
				"module_on(R, "+
					"    mk_module(fun_add⟨D:D⟩(R.add), "+
					"        fun_zero⟨D:D⟩(R.zero), "+
					"        fun_neg⟨D:D⟩(R.neg), "+
					"        fun_smul⟨D:D⟩(R.mul), "+
					"        finite_supp(R.zero, R.carrier, X.simplices(n))))",
				Simp(Rev(SimplicialChainsDef)),
				By(ChainsModule.Read(ring)))
			faces := a.Have(
				"the face sum carries the (n + 1)-simplices into the n-chains",
				Statement{
					Binders: "∀x:D.",
					Hypotheses: []string{
						"x ∈ X.simplices(n + 1)",
					},
					Conclusion: "face_sum(n + 1, x) ∈ finite_supp(R.zero, R.carrier, X.simplices(n))",
				},
				Simp(Rev(SimplicialChainsDef)),
				By(FaceSumIn.Read(ring), simplicial))
			source := a.Have(
				"the source record has the pointwise operations on the free module of simplices",
				"free_module_record(R, X.simplices(n + 1)) = "+
					"mk_module(fun_add⟨D:D⟩(R.add), "+
					"    fun_zero⟨D:D⟩(R.zero), "+
					"    fun_neg⟨D:D⟩(R.neg), "+
					"    fun_smul⟨D:D⟩(R.mul), "+
					"    finite_supp(R.zero, R.carrier, X.simplices(n + 1)))",
				Simp(Fwd(free_module.FreeModuleRecordDef)),
				Basic())
			a.Show(
				"so the face sum extended linearly from the free module on "+
					"X(n + 1), the boundary, is a homomorphism into the n-chains",
				Simp(Fwd(SimplicialBoundaryDef), Fwd(SimplicialChainsDef)),
				source.RwRev(),
				By(
					a.Simplified(GroupPremises(
						faces,
						free_module.FreeLiftHom.Read(chains).At(
							a.TermAs[Set[D]]("X.simplices(n + 1)"), a.TermAs[Fun[D, Fun[D, A]]]("λx:D. face_sum(n + 1, x)")))),
					faces))
		}),
})}

// BoundaryDelta — the boundary extends the face sum linearly from the
// generators of the free module on X(n + 1); the face sum carries
// X(n + 1) into the n-chains, themselves a module, so at the generator
// at x the extension takes the face sum's value at x.
var BoundaryDelta = boundaryDeltaThm{family.Add(registry.ProofEntry{
	Name: "BoundaryDelta",
	Key:  "prop_d32945bfb05600ea",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀X:simplicial_ops(D). ∀n:num. ∀x:D.",
		Hypotheses: []string{
			"simplicial_set(X)",
			"x ∈ X.simplices(n + 1)",
		},
		Conclusion: "simplicial_boundary(n + 1, delta_at(x)) = face_sum(n + 1, x)",
	},
		func(
			a *Argument,
			ring Fact,
			_ *Expr[simplicial_set.SimplicialOps[D]],
			_ *Expr[Nat],
			x *Expr[D],
			simplicial, xIn Fact,
		) {
			chains := a.Have(
				"the n-chains, the free module on X(n), are a module over the ring",
				"module_on(R, "+
					"    mk_module(fun_add⟨D:D⟩(R.add), "+
					"        fun_zero⟨D:D⟩(R.zero), "+
					"        fun_neg⟨D:D⟩(R.neg), "+
					"        fun_smul⟨D:D⟩(R.mul), "+
					"        finite_supp(R.zero, R.carrier, X.simplices(n))))",
				Simp(Rev(SimplicialChainsDef)),
				By(ChainsModule.Read(ring)))
			faces := a.Have(
				"the face sum carries the (n + 1)-simplices into the n-chains",
				Statement{
					Binders: "∀y:D.",
					Hypotheses: []string{
						"y ∈ X.simplices(n + 1)",
					},
					Conclusion: "face_sum(n + 1, y) ∈ finite_supp(R.zero, R.carrier, X.simplices(n))",
				},
				Simp(Rev(SimplicialChainsDef)),
				By(FaceSumIn.Read(ring), simplicial))
			a.Show(
				"so the boundary, the face sum extended linearly, takes the face sum's value at the generator at x",
				Simp(Fwd(SimplicialBoundaryDef)),
				By(
					a.Simplified(GroupPremises(
						faces,
						xIn,
						free_module.FreeLiftDelta.Read(chains).At(
							a.TermAs[Set[D]]("X.simplices(n + 1)"),
							a.TermAs[Fun[D, Fun[D, A]]]("λy:D. face_sum(n + 1, y)"),
							x))),
					faces,
					xIn))
		}),
})}

// FaceSumCancel — the double alternating sum over the faces of the
// faces of an (n+2)-simplex is zero. Write T(j, i) for the term at the
// pair (j, i). The pairs split into the half U where i < j and the half
// V where j ≤ i, and ψ(j, i) = (i + 1, j) carries V one-to-one onto U;
// at ψ(j, i) the simplex is the same, by the face identity
// d_j d_{i+1} = d_i d_j, and the sign is the opposite. So the sum over
// U is the negative of the sum over V, and the two halves cancel.
var FaceSumCancel = faceSumCancelThm{family.Add(registry.ProofEntry{
	Name: "FaceSumCancel",
	Reading: "The pairs (j, i) split into those with i < j and those with j ≤ i; (j, i) ↦ " +
		"(i + 1, j) maps the second part one-to-one onto the first, with no subtraction in " +
		"the map, and j ≥ 1 on the first part keeps the preimage (i, j − 1) exact. The sign " +
		"step is one clause of the sign's definition at i + 1, closed by the ring arithmetic; " +
		"the two halves cancel as a sum and its negative in the n-chains' additive group.",
	Key: "prop_a530005777758dc5",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀X:simplicial_ops(D). ∀n:num. ∀x:D.",
		Hypotheses: []string{
			"simplicial_set(X)",
			"x ∈ X.simplices(n + 2)",
		},
		Conclusion: "module_sum(fun_add⟨D:D⟩(R.add), " +
			"    fun_zero⟨D:D⟩(R.zero), " +
			"    0 .. n + 2, " +
			"    λj:num. " +
			"        module_sum(fun_add⟨D:D⟩(R.add), " +
			"            fun_zero⟨D:D⟩(R.zero), " +
			"            0 .. n + 1, " +
			"            λi:num. " +
			"                fun_smul⟨D:D⟩(R.mul, " +
			"                    alternating_sign(j) * alternating_sign(i), " +
			"                    delta_at(X.d(n + 1, i, X.d(n + 2, j, x)))))) = " +
			"fun_zero⟨D:D⟩(R.zero)",
	},
		func(
			a *Argument,
			ring Fact,
			_ *Expr[simplicial_set.SimplicialOps[D]],
			n *Expr[Nat],
			x *Expr[D],
			simplicial, xIn Fact,
		) {
			chains := a.Have(
				"the n-chains, the free module on X(n), are a module over the ring",
				"module_on(R, "+
					"    mk_module(fun_add⟨D:D⟩(R.add), "+
					"        fun_zero⟨D:D⟩(R.zero), "+
					"        fun_neg⟨D:D⟩(R.neg), "+
					"        fun_smul⟨D:D⟩(R.mul), "+
					"        finite_supp(R.zero, R.carrier, X.simplices(n))))",
				Simp(Rev(SimplicialChainsDef)),
				By(ChainsModule.Read(ring)))
			termIn := a.Have(
				"each term scales the generator at a face of a face "+
					"by a product of signs, a member of the n-chains",
				Statement{
					Binders: "∀i j:num.",
					Hypotheses: []string{
						"i ≤ n + 1",
						"j ≤ n + 2",
					},
					Conclusion: "fun_smul(alternating_sign(j) * alternating_sign(i), " +
						"    delta_at(X.d(n + 1, i, X.d(n + 2, j, x)))) ∈ " +
						"finite_supp(R.zero, R.carrier, X.simplices(n))",
				},
				Derive(func(b *Argument) {
					i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
					bounds := b.Assume()
					twoSteps := b.Have(
						"n + 2 is two steps above n",
						"n + 1 + 1 = n + 2",
						ByArith())
					face := b.Have(
						"the j-th face of x is an (n + 1)-simplex",
						"X.d(n + 2, j, x) ∈ X.simplices(n + 1)",
						By(
							Normalized,
							simplicial_set.FaceIn.Read(simplicial).At(b.TermAs[Nat]("n + 1"), j, x),
							xIn,
							bounds,
							twoSteps))
					faceOfFace := b.Have(
						"and its i-th face an n-simplex",
						"X.d(n + 1, i, X.d(n + 2, j, x)) ∈ X.simplices(n)",
						By(simplicial_set.FaceIn.Read(simplicial).At(n, i, b.TermAs[D]("X.d(n + 2, j, x)")), face, bounds))
					b.Show(
						"a product of signs in c scales a generator of the n-chains",
						By(
							chains,
							faceOfFace,
							b.Simplified(module.SmulIn.Read(chains)),
							free_module.DeltaAtIn.Read(ring),
							comm_ring.MulIn.Read(ring),
							comm_ring.AlternatingSignIn.Read(ring)))
				}))

			// The terms indexed by the pairs p = (j, i), the two halves of the
			// pairs, and the map that carries the second half onto the first.
			T, tDef := a.LetAs[Fun[Prod[Nat, Nat], Fun[D, A]]](
				"T",
				"λp:prod(num, num). "+
					"    fun_smul(alternating_sign(fst(p)) * alternating_sign(snd(p)), "+
					"        delta_at(X.d(n + 1, snd(p), X.d(n + 2, fst(p), x))))")
			U, uDef := a.LetAs[Set[Prod[Nat, Nat]]](
				"U", "{p:prod(num, num) | p ∈ set_cross(0 .. n + 2, 0 .. n + 1) ∧ snd(p) < fst(p)}")
			V, vDef := a.LetAs[Set[Prod[Nat, Nat]]](
				"V", "{p:prod(num, num) | p ∈ set_cross(0 .. n + 2, 0 .. n + 1) ∧ fst(p) ≤ snd(p)}")
			psi, psiDef := a.LetAs[Fun[Prod[Nat, Nat], Prod[Nat, Nat]]](
				"ψ", "λp:prod(num, num).(snd(p) + 1, fst(p))")

			inCross := a.Have(
				"a pair (j, i) lies in the product when j ≤ n + 2 and i ≤ n + 1",
				"∀p:prod(num, num). p ∈ set_cross(0 .. n + 2, 0 .. n + 1) ⇔ fst(p) ≤ n + 2 ∧ snd(p) ≤ n + 1",
				By(set_product.InCrossProjections, num_segment.MembershipFromZero))
			inU := a.Have(
				"U holds the pairs of the product with i < j",
				"∀p:prod(num, num). p ∈ U ⇔ p ∈ set_cross(0 .. n + 2, 0 .. n + 1) ∧ snd(p) < fst(p)",
				BySets(uDef))
			inV := a.Have(
				"V holds the pairs of the product with j ≤ i",
				"∀p:prod(num, num). p ∈ V ⇔ p ∈ set_cross(0 .. n + 2, 0 .. n + 1) ∧ fst(p) ≤ snd(p)",
				BySets(vDef))
			termAt := a.Have(
				"T(p) lies in the n-chains at every pair p of the product",
				Statement{
					Binders: "∀p:prod(num, num).",
					Hypotheses: []string{
						"p ∈ set_cross(0 .. n + 2, 0 .. n + 1)",
					},
					Conclusion: "T(p) ∈ finite_supp(R.zero, R.carrier, X.simplices(n))",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[Nat, Nat]]("p")
					inProduct := b.Assume()
					b.Show(
						"T at p = (j, i) is the term of the double sum at j and i",
						By(termIn.At(b.TermAs[Nat]("snd(p)"), b.TermAs[Nat]("fst(p)")), tDef, inProduct, inCross.At(p)))
				}))
			split := a.Have(
				"every pair of the product lies in U or in V",
				"set_cross(0 .. n + 2, 0 .. n + 1) = U ∪ V",
				BySets(uDef, vDef, nat_order.NotLessThan))
			apart := a.Have(
				"and in only one of them",
				"disjoint(U, V)",
				BySets(uDef, vDef, nat_order.NotLessThan))
			finite := a.Have(
				"both halves are finite, their union being the finite product",
				"finite(U) ∧ finite(V)",
				Derive(func(b *Argument) {
					whole := b.Have(
						"U ∪ V, the product of two segments, is finite",
						"finite(U ∪ V)",
						split.RwRev(),
						By(finite_set.FiniteProduct, num_segment.Finite))
					b.Show(
						"a union is finite exactly when both parts are",
						By(whole, finite_set.FiniteUnion))
				}))

			psiParts := a.Have(
				"ψ(j, i) has first coordinate i + 1 and second coordinate j",
				"∀p:prod(num, num). fst(ψ(p)) = snd(p) + 1 ∧ snd(ψ(p)) = fst(p)",
				psiDef.Rw(),
				Simp(
					Fwd(pairs.Fst.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat]())),
					Fwd(pairs.Snd.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat]()))),
				Basic())
			into := a.Have(
				"ψ carries V into U",
				"∀p:prod(num, num). p ∈ V ⇒ ψ(p) ∈ U",
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[Nat, Nat]]("p")
					inVp := b.Assume()
					image := b.TermAs[Prod[Nat, Nat]]("ψ(p)")
					below := b.Have(
						"p = (j, i) with j ≤ i ≤ n + 1",
						"fst(p) ≤ snd(p) ∧ snd(p) ≤ n + 1",
						By(inVp, inV.At(p), inCross.At(p)))
					above := b.Have(
						"so ψ(p) = (i + 1, j) has j < i + 1 ≤ n + 2",
						"snd(ψ(p)) < fst(ψ(p)) ∧ fst(ψ(p)) ≤ n + 2 ∧ snd(ψ(p)) ≤ n + 1",
						ByArith(below, psiParts.At(p)))
					b.Show(
						"a pair of the product with its second coordinate below its first",
						By(above, inU.At(image), inCross.At(image)))
				}))
			onto := a.Have(
				"every pair of U is ψ of a pair of V",
				"∀q:prod(num, num). q ∈ U ⇒ ∃p:prod(num, num). p ∈ V ∧ ψ(p) = q",
				Derive(func(b *Argument) {
					q := b.FixAs[Prod[Nat, Nat]]("q")
					inUq := b.Assume()
					above := b.Have(
						"q = (j, i) with i < j ≤ n + 2",
						"snd(q) < fst(q) ∧ fst(q) ≤ n + 2 ∧ snd(q) ≤ n + 1",
						By(inUq, inU.At(q), inCross.At(q)))
					w, wDef := b.LetAs[Prod[Nat, Nat]]("w", "(snd(q), fst(q) - 1)")
					coords := b.Have(
						"w = (i, j − 1)",
						"fst(w) = snd(q) ∧ snd(w) = fst(q) - 1",
						wDef.Rw(),
						Simp(
							Fwd(pairs.Fst.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat]())),
							Fwd(pairs.Snd.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat]()))),
						Basic())
					below := b.Have(
						"so i ≤ j − 1 ≤ n + 1",
						"fst(w) ≤ snd(w) ∧ fst(w) ≤ n + 2 ∧ snd(w) ≤ n + 1",
						ByArith(above, coords))
					back := b.Have(
						"and ψ(w) = (j − 1 + 1, i) = (j, i)",
						"fst(ψ(w)) = fst(q) ∧ snd(ψ(w)) = snd(q)",
						ByArith(above, coords, psiParts.At(w)))
					inVw := b.Have(
						"w lies in V",
						"w ∈ V",
						By(below, inV.At(w), inCross.At(w)))
					hits := b.Have(
						"and ψ sends it to q",
						"ψ(w) = q",
						By(Normalized, back, pairs.PairEta.At(b.TermAs[Prod[Nat, Nat]]("ψ(w)")), pairs.PairEta.At(q)))
					b.Take(w)
					b.Show(
						"w is the pair of V that ψ sends to q",
						By(inVw, hits))
				}))
			onU := a.Have(
				"so U is the image of V under ψ",
				"image(ψ, V) = U",
				BySets(into, onto))
			injective := a.Have(
				"ψ is one-to-one on V",
				"injective_on(V, ψ)",
				Derive(func(b *Argument) {
					oneToOne := b.Have(
						"ψ(j, i) determines i + 1 and j, hence the pair",
						"∀u v:prod(num, num). ψ(u) = ψ(v) ⇒ u = v",
						Derive(func(c *Argument) {
							u, v := c.FixAs[Prod[Nat, Nat]]("u"), c.FixAs[Prod[Nat, Nat]]("v")
							same := c.Assume()
							images := c.Have(
								"ψ(u) and ψ(v) have the same coordinates",
								"fst(ψ(u)) = fst(ψ(v)) ∧ snd(ψ(u)) = snd(ψ(v))",
								same.Rw(),
								Basic())
							coords := c.Have(
								"hence so do u and v",
								"fst(u) = fst(v) ∧ snd(u) = snd(v)",
								ByArith(images, psiParts.At(u), psiParts.At(v)))
							c.Show(
								"and a pair is its two coordinates",
								By(coords, pairs.PairEta.At(u), pairs.PairEta.At(v)))
						}))
					b.Show(
						"one-to-one everywhere, so on V",
						By(oneToOne, functions.InjectiveOnDef))
				}))
			termV := a.Have(
				"over V both T and T ∘ ψ lie in the n-chains",
				Statement{
					Binders: "∀p:prod(num, num).",
					Hypotheses: []string{
						"p ∈ V",
					},
					Conclusion: "T(p) ∈ finite_supp(R.zero, R.carrier, X.simplices(n)) ∧ " +
						"T(ψ(p)) ∈ finite_supp(R.zero, R.carrier, X.simplices(n))",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[Nat, Nat]]("p")
					inVp := b.Assume()
					image := b.TermAs[Prod[Nat, Nat]]("ψ(p)")
					b.Show(
						"p and ψ(p) are both pairs of the product",
						By(inVp, inV.At(p), into.At(p), inU.At(image), termAt.At(p), termAt.At(image)))
				}))

			generators := a.Have(
				"a generator takes the values one and zero, both in c",
				"∀z y:D. delta_at(z, y) ∈ R.carrier",
				By(comm_ring.OneIn.Read(ring), comm_ring.ZeroIn.Read(ring), free_module.DeltaAtDef))
			negated := a.Have(
				"at ψ(p) the term is the negative of the term at p",
				"∀p:prod(num, num). p ∈ V ⇒ T(ψ(p)) = fun_neg⟨D:D⟩(R.neg, T(p))",
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[Nat, Nat]]("p")
					inVp := b.Assume()
					j, i := b.TermAs[Nat]("fst(p)"), b.TermAs[Nat]("snd(p)")
					below := b.Have(
						"p = (j, i) with j ≤ i ≤ n + 1",
						"fst(p) ≤ snd(p) ∧ snd(p) ≤ n + 1",
						By(inVp, inV.At(p), inCross.At(p)))
					shifted := b.Have(
						"so j < i + 1 ≤ n + 2, and (i + 1) − 1 = i",
						"fst(p) < snd(p) + 1 ∧ snd(p) + 1 ≤ n + 2 ∧ snd(p) + 1 - 1 = snd(p)",
						ByArith(below))
					face := b.Have(
						"the face identity d_j d_{i+1} x = d_i d_j x",
						"X.d(n + 1, fst(p), X.d(n + 2, snd(p) + 1, x)) = X.d(n + 1, snd(p), X.d(n + 2, fst(p), x))",
						By(simplicial_set.FaceFace.Read(simplicial).At(n, j, b.TermAs[Nat]("snd(p) + 1"), x), xIn, shifted))
					sign := b.Have(
						"one more step negates the sign: the definition's clause at suc(i), with i + 1 read as suc(i)",
						"alternating_sign(snd(p) + 1) * alternating_sign(fst(p)) = "+
							"-(alternating_sign(fst(p)) * alternating_sign(snd(p)))",
						Simp(Rev(nat_arith.Add1), Fwd(comm_ring.AlternatingSignDef)),
						ByArith(
							ring,
							comm_ring.AlternatingSignIn.Read(ring).At(j),
							comm_ring.AlternatingSignIn.Read(ring).At(i)))
					negScale := b.Have(
						"a negated scalar negates the scaled generator",
						"fun_smul(-(alternating_sign(fst(p)) * alternating_sign(snd(p))), "+
							"    delta_at(X.d(n + 1, snd(p), X.d(n + 2, fst(p), x)))) = "+
							"fun_neg⟨D:D⟩(R.neg, "+
							"    fun_smul(alternating_sign(fst(p)) * alternating_sign(snd(p)), "+
							"        delta_at(X.d(n + 1, snd(p), X.d(n + 2, fst(p), x)))))",
						Funext(),
						Derive(func(c *Argument) {
							y := c.FixAs[D]("y")
							c.Do(Simp(
								Fwd(function_module.FunSmulDef.Inst(
									TypeBinder.BindA[A](), TypeBinder.BindC[A](), TypeBinder.BindD[D]())),
								Fwd(function_module.FunNegDef)))
							c.Show(
								"pointwise it is −r · δ(y) = −(r · δ(y)) in the ring",
								ByArith(
									ring,
									generators.At(c.TermAs[D]("X.d(n + 1, snd(p), X.d(n + 2, fst(p), x))"), y),
									comm_ring.AlternatingSignIn.Read(ring).At(j),
									comm_ring.AlternatingSignIn.Read(ring).At(i)))
						}))
					b.Show(
						"so T(ψ(p)) scales the generator of T(p) by the negated sign",
						By(tDef, psiParts.At(p), sign, face, negScale))
				}))
			reindexed := a.Have(
				"the sum over U is the negative of the sum over V",
				"module_sum(fun_add⟨D:D⟩(R.add), fun_zero⟨D:D⟩(R.zero), U, T) = "+
					"fun_neg⟨D:D⟩(R.neg, module_sum(fun_add⟨D:D⟩(R.add), fun_zero⟨D:D⟩(R.zero), V, T))",
				CalcEq(
					Leg(
						a.TermAs[Fun[D, A]](
							"module_sum(fun_add⟨D:D⟩(R.add), fun_zero⟨D:D⟩(R.zero), V, λp:prod(num, num). T(ψ(p)))"),
						"U is the image of V under the one-to-one ψ",
						By(a.Simplified(module.ModuleSumImage.Read(chains).At(V, psi, T)), finite, injective, termV, onU)),
					Leg(
						a.TermAs[Fun[D, A]](
							"module_sum(fun_add⟨D:D⟩(R.add), "+
								"    fun_zero⟨D:D⟩(R.zero), "+
								"    V, "+
								"    λp:prod(num, num). fun_neg⟨D:D⟩(R.neg, T(p)))"),
						"where each term is the negative of the term at p",
						By(module.ModuleSumCongruence, negated)),
					FinalLeg(
						"and the sum of the negatives is the negative of the sum",
						By(a.Simplified(module.ModuleSumNeg.Read(chains).At(V, T)), finite, termV)),
				))
			chainsGroup := a.Simplified(module.AddGroupOn.Read(chains))
			sumIn := a.Have(
				"the sum over V lies in the n-chains",
				"module_sum(fun_add⟨D:D⟩(R.add), fun_zero⟨D:D⟩(R.zero), V, T) ∈ "+
					"finite_supp(R.zero, R.carrier, X.simplices(n))",
				By(a.Simplified(module.ModuleSumIn.Read(chains).At(V, T)), finite, termV))
			a.Show(
				"the double sum is the sum of T over the pairs, whose two halves cancel",
				CalcEq(
					Leg(
						a.TermAs[Fun[D, A]](
							"module_sum(fun_add⟨D:D⟩(R.add), fun_zero⟨D:D⟩(R.zero), set_cross(0 .. n + 2, 0 .. n + 1), T)"),
						"the double sum is the sum of T over the pairs (j, i)",
						tDef.Rw(),
						By(
							a.Simplified(module.ModuleSumCross.Read(chains).At(
								a.TermAs[Set[Nat]]("0 .. n + 2"),
								a.TermAs[Set[Nat]]("0 .. n + 1"),
								a.TermAs[Fun2[Nat, Nat, Fun[D, A]]](
									"λj:num. λi:num. "+
										"    fun_smul(alternating_sign(j) * alternating_sign(i), "+
										"        delta_at(X.d(n + 1, i, X.d(n + 2, j, x))))"))),
							termIn,
							num_segment.Finite,
							num_segment.MembershipFromZero)),
					Leg(
						a.TermAs[Fun[D, A]](
							"fun_add⟨D:D⟩(R.add, "+
								"    module_sum(fun_add⟨D:D⟩(R.add), fun_zero⟨D:D⟩(R.zero), U, T), "+
								"    module_sum(fun_add⟨D:D⟩(R.add), fun_zero⟨D:D⟩(R.zero), V, T))"),
						"which splits over the disjoint halves U and V",
						By(
							split,
							a.Simplified(module.ModuleSumDisjointUnion.Read(chains).At(U, V, T)),
							finite,
							apart,
							termAt,
							set_basic.InUnion)),
					Leg(
						a.TermAs[Fun[D, A]](
							"fun_add⟨D:D⟩(R.add, "+
								"    fun_neg⟨D:D⟩(R.neg, module_sum(fun_add⟨D:D⟩(R.add), fun_zero⟨D:D⟩(R.zero), V, T)), "+
								"    module_sum(fun_add⟨D:D⟩(R.add), fun_zero⟨D:D⟩(R.zero), V, T))"),
						"the sum over U is the negative of the sum over V",
						reindexed.Rw(),
						Basic()),
					FinalLeg(
						"and a member of the n-chains plus its negative is zero",
						By(group.LeftInverseOn.Read(chainsGroup), sumIn)),
				))
		}),
})}

// BoundaryFaceSum — the boundary of the face sum of an (n+2)-simplex is
// zero. The face sum is a sum of signed generators at the faces of x,
// and the boundary is linear, so it passes through the sum and through
// each sign; on the generator at a face it is that face's own face sum.
// Carrying the outer sign into each of those sums leaves the double sum
// over the faces of the faces, signed by the products of the two signs,
// and that double sum cancels (FaceSumCancel).
var BoundaryFaceSum = boundaryFaceSumThm{family.Add(registry.ProofEntry{
	Name: "BoundaryFaceSum",
	Key:  "prop_72e355f188572cfd",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀X:simplicial_ops(D). ∀n:num. ∀x:D.",
		Hypotheses: []string{
			"simplicial_set(X)",
			"x ∈ X.simplices(n + 2)",
		},
		Conclusion: "simplicial_boundary(n + 1, face_sum(n + 2, x)) = fun_zero⟨D:D⟩(R.zero)",
	},
		func(
			a *Argument,
			ring Fact,
			X *Expr[simplicial_set.SimplicialOps[D]],
			n *Expr[Nat],
			x *Expr[D],
			simplicial, xIn Fact,
		) {
			upper := a.Have(
				"the (n + 1)-chains, the free module on X(n + 1), are a module over the ring",
				"module_on(R, "+
					"    mk_module(fun_add⟨D:D⟩(R.add), "+
					"        fun_zero⟨D:D⟩(R.zero), "+
					"        fun_neg⟨D:D⟩(R.neg), "+
					"        fun_smul⟨D:D⟩(R.mul), "+
					"        finite_supp(R.zero, R.carrier, X.simplices(n + 1))))",
				Simp(Rev(SimplicialChainsDef)),
				By(ChainsModule.Read(ring)))
			lower := a.Have(
				"and so are the n-chains, the free module on X(n)",
				"module_on(R, "+
					"    mk_module(fun_add⟨D:D⟩(R.add), "+
					"        fun_zero⟨D:D⟩(R.zero), "+
					"        fun_neg⟨D:D⟩(R.neg), "+
					"        fun_smul⟨D:D⟩(R.mul), "+
					"        finite_supp(R.zero, R.carrier, X.simplices(n))))",
				Simp(Rev(SimplicialChainsDef)),
				By(ChainsModule.Read(ring)))
			linear := a.Have(
				"the boundary out of dimension n + 1 is a homomorphism from the (n + 1)-chains to the n-chains",
				"module_homomorphism(R, "+
					"    mk_module(fun_add⟨D:D⟩(R.add), "+
					"        fun_zero⟨D:D⟩(R.zero), "+
					"        fun_neg⟨D:D⟩(R.neg), "+
					"        fun_smul⟨D:D⟩(R.mul), "+
					"        finite_supp(R.zero, R.carrier, X.simplices(n + 1))), "+
					"    mk_module(fun_add⟨D:D⟩(R.add), "+
					"        fun_zero⟨D:D⟩(R.zero), "+
					"        fun_neg⟨D:D⟩(R.neg), "+
					"        fun_smul⟨D:D⟩(R.mul), "+
					"        finite_supp(R.zero, R.carrier, X.simplices(n))), "+
					"    simplicial_boundary(n + 1))",
				Simp(Rev(SimplicialChainsDef)),
				By(BoundaryHom.Read(ring), simplicial))
			scales := a.Simplified(module_homomorphism.HomSmul.Read(linear))
			twoSteps := a.Have(
				"n + 2 is two steps above n",
				"n + 1 + 1 = n + 2",
				ByArith())
			n1 := a.TermAs[Nat]("n + 1")
			faces := a.Have(
				"each face of x is an (n + 1)-simplex",
				"∀j:num. j ∈ 0 .. n + 2 ⇒ X.d(n + 2, j, x) ∈ X.simplices(n + 1)",
				a.ForEach(func(j *Expr[Nat]) Action {
					return By(simplicial_set.FaceIn.Read(simplicial).At(n1, j, x), xIn, twoSteps)
				}))
			upperScales := a.Simplified(module.SmulIn.Read(upper))
			terms := a.Have(
				"so each term of the face sum, the generator at a face scaled by its sign, is an (n + 1)-chain",
				Statement{
					Binders: "∀j:num.",
					Hypotheses: []string{
						"j ∈ 0 .. n + 2",
					},
					Conclusion: "fun_smul(alternating_sign(j), delta_at(X.d(n + 2, j, x))) ∈ " +
						"finite_supp(R.zero, R.carrier, X.simplices(n + 1))",
				},
				a.ForEach(func(j *Expr[Nat]) Action {
					return By(
						faces.At(j),
						upperScales,
						free_module.DeltaAtIn.Read(ring),
						comm_ring.AlternatingSignIn.Read(ring))
				}))
			termwise := a.Have(
				"the boundary of each term is the sum over the faces "+
					"of its face, signed by the product of the two signs",
				Statement{
					Binders: "∀j:num.",
					Hypotheses: []string{
						"j ∈ 0 .. n + 2",
					},
					Conclusion: "simplicial_boundary(n + 1, " +
						"    fun_smul(alternating_sign(j), delta_at(X.d(n + 2, j, x)))) = " +
						"module_sum(fun_add⟨D:D⟩(R.add), " +
						"    fun_zero⟨D:D⟩(R.zero), " +
						"    0 .. n + 1, " +
						"    λi:num. " +
						"        fun_smul(alternating_sign(j) * alternating_sign(i), " +
						"            delta_at(X.d(n + 1, i, X.d(n + 2, j, x)))))",
				},
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					bound := b.Assume()
					face := b.TermAs[D]("X.d(n + 2, j, x)")
					faceIn := b.Have(
						"the j-th face of x is an (n + 1)-simplex",
						"X.d(n + 2, j, x) ∈ X.simplices(n + 1)",
						By(faces.At(j), bound))
					generators := b.Have(
						"the generators at the faces of that face are n-chains",
						Statement{
							Binders: "∀i:num.",
							Hypotheses: []string{
								"i ∈ 0 .. n + 1",
							},
							Conclusion: "delta_at(X.d(n + 1, i, X.d(n + 2, j, x))) ∈ " +
								"finite_supp(R.zero, R.carrier, X.simplices(n))",
						},
						b.ForEach(func(i *Expr[Nat]) Action {
							return By(
								free_module.DeltaAtIn.Read(ring),
								simplicial_set.FaceIn.Read(simplicial).At(n, i, face),
								faceIn)
						}))
					b.Show(
						"so the boundary of the j-th term unfolds to the double sum's j-th row",
						CalcEq(
							Leg(
								b.TermAs[Fun[D, A]](
									"fun_smul(alternating_sign(j), simplicial_boundary(n + 1, delta_at(X.d(n + 2, j, x))))"),
								"the boundary is linear, so the sign comes out",
								By(scales, comm_ring.AlternatingSignIn.Read(ring), free_module.DeltaAtIn.Read(ring), faceIn)),
							Leg(
								b.TermAs[Fun[D, A]]("fun_smul(alternating_sign(j), face_sum(n + 1, X.d(n + 2, j, x)))"),
								"on the generator at an (n + 1)-simplex the boundary is that simplex's face sum",
								Congr(),
								By(At(BoundaryDelta.Read(ring), X, n, face), simplicial, faceIn)),
							Leg(
								b.TermAs[Fun[D, A]](
									"fun_smul(alternating_sign(j), "+
										"    module_sum(fun_add⟨D:D⟩(R.add), "+
										"        fun_zero⟨D:D⟩(R.zero), "+
										"        0 .. n + 1, "+
										"        λi:num. fun_smul(alternating_sign(i), delta_at(X.d(n + 1, i, X.d(n + 2, j, x))))))"),
								"the alternating sum of the generators at the faces of the face",
								Simp(Fwd(FaceSumDef)),
								Refl()),
							Leg(
								b.TermAs[Fun[D, A]](
									"module_sum(fun_add⟨D:D⟩(R.add), "+
										"    fun_zero⟨D:D⟩(R.zero), "+
										"    0 .. n + 1, "+
										"    λi:num. "+
										"        fun_smul(alternating_sign(j), "+
										"            fun_smul(alternating_sign(i), delta_at(X.d(n + 1, i, X.d(n + 2, j, x))))))"),
								"the sign passes into the finite sum of n-chains",
								By(
									b.Simplified(module.ModuleSumSmul.Read(lower).AsFact().At(
										b.TermAs[Set[Nat]]("0 .. n + 1"),
										b.TermAs[A]("alternating_sign(j)"),
										b.TermAs[Fun[Nat, Fun[D, A]]](
											"λi:num. fun_smul(alternating_sign(i), delta_at(X.d(n + 1, i, X.d(n + 2, j, x))))"))),
									num_segment.Finite,
									generators,
									b.Simplified(module.SmulIn.Read(lower)),
									comm_ring.AlternatingSignIn.Read(ring))),
							FinalLeg(
								"and the two scalings of each generator compose into one by the product of the signs",
								By(
									module.ModuleSumCongruence,
									b.Simplified(module.SmulMul.Read(lower)),
									comm_ring.AlternatingSignIn.Read(ring),
									generators)),
						))
				}))
			sums := a.Have(
				"the boundary carries a finite sum to the sum of its values in the target record",
				Statement{
					Binders: "∀S:set(num). ∀F:(num → D → A).",
					Hypotheses: []string{
						"finite(S)",
						"∀j:num. j ∈ S ⇒ F(j) ∈ finite_supp(R.zero, R.carrier, X.simplices(n + 1))",
					},
					Conclusion: "simplicial_boundary(n + 1, " +
						"    module_sum(fun_add⟨D:D⟩(R.add), fun_zero⟨D:D⟩(R.zero), S, F)) = " +
						"module_sum(fun_add⟨D:D⟩(R.add), " +
						"    fun_zero⟨D:D⟩(R.zero), " +
						"    S, " +
						"    λj:num. simplicial_boundary(n + 1, F(j)))",
				},
				By(
					linear,
					Where(
						module_homomorphism.HomSum.Inst(
							TypeBinder.BindA[A](),
							TypeBinder.BindB[Fun[D, A]](),
							TypeBinder.BindC[Fun[D, A]](),
							TypeBinder.BindD[Nat]()),
						"R",
						a.TermAs[module_record.RingOps[A]]("R")).
						Where(
							"M",
							a.TermAs[module_record.ModuleOps[A, Fun[D, A]]](
								"mk_module(fun_add⟨D:D⟩, "+
									"    fun_zero⟨D:D⟩, "+
									"    fun_neg⟨D:D⟩, "+
									"    fun_smul⟨D:D⟩, "+
									"    finite_supp(R.zero, R.carrier, X.simplices(n + 1)))")).
						Where(
							"N",
							a.TermAs[module_record.ModuleOps[A, Fun[D, A]]](
								"mk_module(fun_add⟨D:D⟩, "+
									"    fun_zero⟨D:D⟩, "+
									"    fun_neg⟨D:D⟩, "+
									"    fun_smul⟨D:D⟩, "+
									"    finite_supp(R.zero, R.carrier, X.simplices(n)))")).
						Where("f", a.Term("simplicial_boundary(n + 1)"))))
			a.Show(
				"the boundary of the face sum is the double sum over the faces of the faces, which cancels",
				CalcEq(
					Leg(
						a.TermAs[Fun[D, A]](
							"simplicial_boundary(n + 1, "+
								"    module_sum(fun_add⟨D:D⟩(R.add), "+
								"        fun_zero⟨D:D⟩(R.zero), "+
								"        0 .. n + 2, "+
								"        λj:num. fun_smul(alternating_sign(j), delta_at(X.d(n + 2, j, x)))))"),
						"the face sum of x is the alternating sum of the generators at its faces",
						Simp(Fwd(FaceSumDef)),
						Refl()),
					Leg(
						a.TermAs[Fun[D, A]](
							"module_sum(fun_add⟨D:D⟩(R.add), "+
								"    fun_zero⟨D:D⟩(R.zero), "+
								"    0 .. n + 2, "+
								"    λj:num. "+
								"        simplicial_boundary(n + 1, fun_smul(alternating_sign(j), delta_at(X.d(n + 2, j, x)))))"),
						"the boundary is a homomorphism, so it passes through the finite sum of (n + 1)-chains",
						By(terms, num_segment.Finite, sums)),
					Leg(
						a.TermAs[Fun[D, A]](
							"module_sum(fun_add⟨D:D⟩(R.add), "+
								"    fun_zero⟨D:D⟩(R.zero), "+
								"    0 .. n + 2, "+
								"    λj:num. "+
								"        module_sum(fun_add⟨D:D⟩(R.add), "+
								"            fun_zero⟨D:D⟩(R.zero), "+
								"            0 .. n + 1, "+
								"            λi:num. "+
								"                fun_smul(alternating_sign(j) * alternating_sign(i), "+
								"                    delta_at(X.d(n + 1, i, X.d(n + 2, j, x))))))"),
						"term by term, each boundary unfolds to its row of the double sum",
						By(module.ModuleSumCongruence, termwise)),
					FinalLeg(
						"and the double sum over the faces of the faces cancels",
						By(FaceSumCancel.Read(ring), simplicial, xIn)),
				))
		}),
})}

// BoundaryTwice — the composite of two boundaries and the zero map are
// linear maps out of the free module on X(n + 2). They agree on every
// generator: BoundaryDelta gives its face sum, and BoundaryFaceSum
// takes that face sum to zero. FreeLiftUnique extends the equality to
// every chain.
var BoundaryTwice = boundaryTwiceThm{family.Add(registry.ProofEntry{
	Name: "BoundaryTwice",
	Reading: "The simplicial-set hypothesis supplies the boundary " +
		"homomorphisms and the vanishing boundary of each face sum.",
	Key: "prop_d776b3b8e935c546",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀X:simplicial_ops(D). ∀n:num. ∀u:(D → A).",
		Hypotheses: []string{
			"simplicial_set(X)",
			"u ∈ simplicial_chains(R.carrier, n + 2)",
		},
		Conclusion: "simplicial_boundary(n + 1, simplicial_boundary(n + 2, u)) = fun_zero⟨D:D⟩(R.zero)",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			X *Expr[simplicial_set.SimplicialOps[D]],
			n *Expr[Nat],
			u *Arrow[D, A],
			simplicial, chain Fact,
		) {
			bottom := a.Have(
				"the n-chains, the free module on X(n), are a module over the ring",
				"module_on(R, "+
					"    mk_module(fun_add⟨D:D⟩(R.add), "+
					"        fun_zero⟨D:D⟩(R.zero), "+
					"        fun_neg⟨D:D⟩(R.neg), "+
					"        fun_smul⟨D:D⟩(R.mul), "+
					"        finite_supp(R.zero, R.carrier, X.simplices(n))))",
				Simp(Rev(SimplicialChainsDef)),
				By(ChainsModule.Read(ring)))
			twoSteps := a.Have(
				"n + 2 is two steps above n",
				"n + 1 + 1 = n + 2",
				ByArith())
			inner := a.Have(
				"the boundary out of dimension n + 2 is linear into the (n + 1)-chains",
				"module_homomorphism(R, "+
					"    mk_module(fun_add⟨D:D⟩(R.add), "+
					"        fun_zero⟨D:D⟩(R.zero), "+
					"        fun_neg⟨D:D⟩(R.neg), "+
					"        fun_smul⟨D:D⟩(R.mul), "+
					"        finite_supp(R.zero, R.carrier, X.simplices(n + 2))), "+
					"    mk_module(fun_add⟨D:D⟩(R.add), "+
					"        fun_zero⟨D:D⟩(R.zero), "+
					"        fun_neg⟨D:D⟩(R.neg), "+
					"        fun_smul⟨D:D⟩(R.mul), "+
					"        finite_supp(R.zero, R.carrier, X.simplices(n + 1))), "+
					"    simplicial_boundary(n + 2))",
				twoSteps.RwRev(),
				Cite(BoundaryHom.Read(ring).AsFact(), X, a.TermAs[Nat]("n + 1")),
				Unfold(SimplicialChainsDef))
			outer := a.Have(
				"the next boundary is linear into the n-chains",
				"module_homomorphism(R, "+
					"    mk_module(fun_add⟨D:D⟩(R.add), "+
					"        fun_zero⟨D:D⟩(R.zero), "+
					"        fun_neg⟨D:D⟩(R.neg), "+
					"        fun_smul⟨D:D⟩(R.mul), "+
					"        finite_supp(R.zero, R.carrier, X.simplices(n + 1))), "+
					"    mk_module(fun_add⟨D:D⟩(R.add), "+
					"        fun_zero⟨D:D⟩(R.zero), "+
					"        fun_neg⟨D:D⟩(R.neg), "+
					"        fun_smul⟨D:D⟩(R.mul), "+
					"        finite_supp(R.zero, R.carrier, X.simplices(n))), "+
					"    simplicial_boundary(n + 1))",
				Cite(BoundaryHom.Read(ring).AsFact(), X, n),
				Unfold(SimplicialChainsDef))
			composite := a.Have(
				"their composite is linear from the free module on X(n + 2) to the n-chains",
				"module_homomorphism(R, "+
					"    free_module_record(R, X.simplices(n + 2)), "+
					"    mk_module(fun_add⟨D:D⟩(R.add), "+
					"        fun_zero⟨D:D⟩(R.zero), "+
					"        fun_neg⟨D:D⟩(R.neg), "+
					"        fun_smul⟨D:D⟩(R.mul), "+
					"        finite_supp(R.zero, R.carrier, X.simplices(n))), "+
					"    simplicial_boundary(n + 1) ∘ simplicial_boundary(n + 2))",
				Unfold(free_module.FreeModuleRecordDef),
				By(
					module_homomorphism.HomCompose.At(
						a.TermAs[module_record.RingOps[A]]("R"),
						a.TermAs[module_record.ModuleOps[A, Fun[D, A]]](
							"mk_module(fun_add⟨D:D⟩, "+
								"    fun_zero⟨D:D⟩, "+
								"    fun_neg⟨D:D⟩, "+
								"    fun_smul⟨D:D⟩, "+
								"    finite_supp(R.zero, R.carrier, X.simplices(n + 2)))"),
						a.TermAs[module_record.ModuleOps[A, Fun[D, A]]](
							"mk_module(fun_add⟨D:D⟩, "+
								"    fun_zero⟨D:D⟩, "+
								"    fun_neg⟨D:D⟩, "+
								"    fun_smul⟨D:D⟩, "+
								"    finite_supp(R.zero, R.carrier, X.simplices(n + 1)))"),
						a.TermAs[module_record.ModuleOps[A, Fun[D, A]]](
							"mk_module(fun_add⟨D:D⟩, "+
								"    fun_zero⟨D:D⟩, "+
								"    fun_neg⟨D:D⟩, "+
								"    fun_smul⟨D:D⟩, "+
								"    finite_supp(R.zero, R.carrier, X.simplices(n)))"),
						a.TermAs[Fun[Fun[D, A], Fun[D, A]]]("simplicial_boundary(n + 2)"),
						a.TermAs[Fun[Fun[D, A], Fun[D, A]]]("simplicial_boundary(n + 1)")),
					inner,
					outer))
			zeroMap := a.Have(
				"the constant-zero map is linear between the same modules",
				"module_homomorphism(R, "+
					"    free_module_record(R, X.simplices(n + 2)), "+
					"    mk_module(fun_add⟨D:D⟩(R.add), "+
					"        fun_zero⟨D:D⟩(R.zero), "+
					"        fun_neg⟨D:D⟩(R.neg), "+
					"        fun_smul⟨D:D⟩(R.mul), "+
					"        finite_supp(R.zero, R.carrier, X.simplices(n))), "+
					"    λv:(D → A). fun_zero⟨D:D⟩(R.zero))",
				Simp(Fwd(free_module.FreeModuleRecordDef), Fwd(module_homomorphism.ModuleHomomorphismDef)),
				SplitConjAll(
					Case(
						"its source is a module",
						By(module_homomorphism.HomSource.Read(inner))),
					Case(
						"its target is a module",
						By(bottom)),
					Case(
						"zero lies in the target",
						By(group.OneIn.Read(module.AddGroupOn.Read(bottom)))),
					Case(
						"zero plus zero is zero",
						By(
							group.OneIn.Read(module.AddGroupOn.Read(bottom)),
							group.LeftIdentityOn.Read(module.AddGroupOn.Read(bottom)))),
					Case(
						"every scalar times zero is zero",
						By(module.SmulZero.Read(bottom))),
				))
			agree := a.Have(
				"the composite agrees with zero on every generator",
				Statement{
					Binders: "∀x:D.",
					Hypotheses: []string{
						"x ∈ X.simplices(n + 2)",
					},
					Conclusion: "(simplicial_boundary(n + 1) ∘ simplicial_boundary(n + 2))(delta_at(x)) = " +
						"fun_zero⟨D:D⟩(R.zero)",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[D]("x")
					simplex := b.Assume()
					b.Do(Unfold(functions.ComposeApply))
					generator := b.Have(
						"the inner boundary takes the generator to its face sum",
						"simplicial_boundary(n + 2, delta_at(x)) = face_sum(n + 2, x)",
						By(At(BoundaryDelta.Read(ring), X, b.TermAs[Nat]("n + 1"), x), simplicial, simplex, twoSteps))
					b.Show(
						"the boundary of that face sum is zero",
						generator.Rw(),
						By(BoundaryFaceSum.Read(ring), simplicial, simplex))
				}))
			free := a.Unfolded(chain, SimplicialChainsDef)
			twice := a.TermAs[Fun[Fun[D, A], Fun[D, A]]](
				"simplicial_boundary(n + 1) ∘ simplicial_boundary(n + 2)")
			zero := a.TermAs[Fun[Fun[D, A], Fun[D, A]]]("λv:(D → A). fun_zero⟨D:D⟩(R.zero)")
			a.Show(
				"the composite vanishes on every chain",
				CalcEq(
					Leg(
						a.TermAs[Fun[D, A]]("(simplicial_boundary(n + 1) ∘ simplicial_boundary(n + 2))(u)"),
						"the composite applies the two boundaries in order",
						Unfold(functions.ComposeApply)),
					FinalLeg(
						"linear maps out of a free module that agree on its generators agree on u",
						By(
							a.Simplified(GroupPremises(
								composite,
								zeroMap,
								agree,
								free,
								free_module.FreeLiftUnique.Read(bottom).At(
									a.TermAs[Set[D]]("X.simplices(n + 2)"), twice, zero, u))),
							composite,
							zeroMap,
							agree,
							free)),
				))
		}),
})}

// ChainComplex — the alternating face map complex is a chain complex:
// its three clauses are ChainsModule, BoundaryHom and BoundaryTwice.
var ChainComplex = chainComplexThm{family.Add(registry.ProofEntry{
	Name: "ChainComplex",
	Key:  "prop_febf21e6fa3ccdca",
	Build: comm_ring.CommRingOn.Law(underSimplicial+"chain_complex(R, pack_complex(fun_add⟨D:D⟩(R.add), fun_zero⟨D:D⟩(R.zero), fun_neg⟨D:D⟩(R.neg), fun_smul⟨D:D⟩(R.mul), simplicial_chains(R.carrier), simplicial_boundary))",
		func(a *Argument, ring Fact, _ *Expr[simplicial_set.SimplicialOps[D]], simplicial Fact) {
			a.Do(Unfold(chain_complex.ChainComplex), SplitConjAll(
				Case(
					"the n-chains are a module over the ring",
					Simp(Fwd(chain_complex.ComplexModuleDef)),
					By(ChainsModule.Read(ring))),
				Case(
					"the boundary out of dimension n + 1 is a homomorphism from the (n + 1)-chains to the n-chains",
					Simp(Fwd(chain_complex.ComplexModuleDef)),
					By(BoundaryHom.Read(ring), simplicial)),
				Case(
					"the boundary of the boundary of an (n + 2)-chain is zero",
					By(BoundaryTwice.Read(ring), simplicial)),
			))
		}),
})}

// ---------------------------------------------------------------------------
// The chain map of a simplicial map, and homology
// ---------------------------------------------------------------------------

// SimplicialChainMapDef — `simplicial_chain_map(zero, one, add, mul, F, n)`:
// the map of n-chains a simplicial map induces, the generator at x sent
// to the generator at F(n, x) and extended linearly. Under the ring the
// text writes `simplicial_chain_map(F, n)`.
var SimplicialChainMapDef = simplicialChainMapDefThm{family.Define(registry.DefEntry{
	Name:     "SimplicialChainMapDef",
	Key:      "prop_844049f40308abf9",
	Const:    "simplicial_chain_map",
	Type:     "A → A → (A → A → A) → (A → A → A) → (num → D → E) → num → (D → A) → E → A",
	Implicit: []string{"zero", "one", "add", "mul"},
	Equations: []string{
		"∀zero one:A. ∀add mul:(A → A → A). ∀F:(num → D → E). ∀n:num. ∀f:(D → A). " +
			"    simplicial_chain_map(zero, one, add, mul, F, n, f) = " +
			"    free_lift(zero, " +
			"        fun_add⟨D:E⟩(add), " +
			"        fun_zero⟨D:E⟩(zero), " +
			"        fun_smul⟨D:E⟩(mul), " +
			"        λx:D. delta_at⟨D:E⟩(zero, one, F(n, x)), " +
			"        f)",
	},
})}

// ChainMapOfSimplicialMap — a simplicial map induces a chain map of the
// alternating face map complexes. Each induced map extends linearly the
// generators' images, generators of the target, so it is a homomorphism.
// For the square, the two ways round from the (n + 1)-chains of X to the
// n-chains of Y are homomorphisms out of a free module, so they agree
// once they agree on its generators: on the generator at x, the boundary
// then the induced map gives the alternating sum of the generators at the
// images of the faces of x, the induced map then the boundary the
// alternating sum of the generators at the faces of F(n + 1, x), and F
// commutes with the faces term by term.
var ChainMapOfSimplicialMap = chainMapOfSimplicialMapThm{family.Add(registry.ProofEntry{
	Name: "ChainMapOfSimplicialMap",
	Key:  "prop_dd7da5a90972d16b",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀X:simplicial_ops(D). ∀Y:simplicial_ops(E). ∀F:(num → D → E).",
		Hypotheses: []string{
			"simplicial_map(X, Y, F)",
		},
		Conclusion: "chain_map(R, " +
			"    pack_complex(fun_add⟨D:D⟩(R.add), " +
			"        fun_zero⟨D:D⟩(R.zero), " +
			"        fun_neg⟨D:D⟩(R.neg), " +
			"        fun_smul⟨D:D⟩(R.mul), " +
			"        simplicial_chains(R.zero, X, R.carrier), " +
			"        simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, X.d)), " +
			"    pack_complex(fun_add⟨D:E⟩(R.add), " +
			"        fun_zero⟨D:E⟩(R.zero), " +
			"        fun_neg⟨D:E⟩(R.neg), " +
			"        fun_smul⟨D:E⟩(R.mul), " +
			"        simplicial_chains(R.zero, Y, R.carrier), " +
			"        simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, Y.d)), " +
			"    simplicial_chain_map(F))",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			X *Expr[simplicial_set.SimplicialOps[D]],
			Y *Expr[simplicial_set.SimplicialOps[E]],
			F *Arrow2[Nat, D, E],
			mapping Fact,
		) {
			source := a.Have(
				"the source of F is a simplicial set",
				"simplicial_set(X)",
				By(simplicial_set.MapSource.Read(mapping)))
			target := a.Have(
				"and so is its target",
				"simplicial_set(Y)",
				By(simplicial_set.MapTarget.Read(mapping)))
			targets := a.Have(
				"in every dimension the chains of Y, the free module on Y(m), are a module over the ring",
				"∀m:num. "+
					"    module_on(R, "+
					"        mk_module(fun_add⟨D:E⟩(R.add), "+
					"            fun_zero⟨D:E⟩(R.zero), "+
					"            fun_neg⟨D:E⟩(R.neg), "+
					"            fun_smul⟨D:E⟩(R.mul), "+
					"            finite_supp(R.zero, R.carrier, Y.simplices(m))))",
				Simp(Rev(SimplicialChainsDef)),
				By(ChainsModule.Read(ring)))
			generators := a.Have(
				"F carries an m-simplex of X to an m-simplex of Y, whose generator is an m-chain of Y",
				Statement{
					Binders: "∀m:num. ∀y:D.",
					Hypotheses: []string{
						"y ∈ X.simplices(m)",
					},
					Conclusion: "delta_at(F(m, y)) ∈ finite_supp(R.zero, R.carrier, Y.simplices(m))",
				},
				By(simplicial_set.MapIn.Read(mapping), free_module.DeltaAtIn.Read(ring)))
			maps := a.Have(
				"so each induced map, the generators' images extended linearly, is a homomorphism of the m-chains",
				"∀m:num. "+
					"    module_homomorphism(R, "+
					"        free_module_record(R, X.simplices(m)), "+
					"        mk_module(fun_add⟨D:E⟩(R.add), "+
					"            fun_zero⟨D:E⟩(R.zero), "+
					"            fun_neg⟨D:E⟩(R.neg), "+
					"            fun_smul⟨D:E⟩(R.mul), "+
					"            finite_supp(R.zero, R.carrier, Y.simplices(m))), "+
					"        simplicial_chain_map(F, m))",
				Derive(func(b *Argument) {
					m := b.FixAs[Nat]("m")
					chainsOfY := b.Have(
						"the m-chains of Y are a module over the ring",
						"module_on(R, "+
							"    mk_module(fun_add⟨D:E⟩(R.add), "+
							"        fun_zero⟨D:E⟩(R.zero), "+
							"        fun_neg⟨D:E⟩(R.neg), "+
							"        fun_smul⟨D:E⟩(R.mul), "+
							"        finite_supp(R.zero, R.carrier, Y.simplices(m))))",
						By(targets.At(m)))
					b.Show(
						"the linear extension of the generators' images is a homomorphism",
						Simp(Fwd(SimplicialChainMapDef)),
						By(
							b.Simplified(free_module.FreeLiftHom.Read(chainsOfY).At(
								b.TermAs[Set[D]]("X.simplices(m)"), b.TermAs[Fun[D, Fun[E, A]]]("λz:D. delta_at(F(m, z))"))),
							generators.At(m)))
				}))
			a.Do(maps.Simp(Fwd(free_module.FreeModuleRecordDef)))
			images := a.Have(
				"and takes the generator at an m-simplex y to the generator at F(m, y)",
				"∀m:num. ∀y:D. y ∈ X.simplices(m) ⇒ simplicial_chain_map(F, m, delta_at(y)) = delta_at(F(m, y))",
				Derive(func(b *Argument) {
					m := b.FixAs[Nat]("m")
					y := b.FixAs[D]("y")
					simplex := b.Assume()
					chainsOfY := b.Have(
						"the m-chains of Y are a module, stated at m as a fact a law is read at",
						"module_on(R, "+
							"    mk_module(fun_add⟨D:E⟩(R.add), "+
							"        fun_zero⟨D:E⟩(R.zero), "+
							"        fun_neg⟨D:E⟩(R.neg), "+
							"        fun_smul⟨D:E⟩(R.mul), "+
							"        finite_supp(R.zero, R.carrier, Y.simplices(m))))",
						By(targets.At(m)))
					onGenerators := b.TermAs[Fun[D, Fun[E, A]]]("λz:D. delta_at(F(m, z))")
					b.Show(
						"the linear extension returns, at a generator, the image it extends",
						Simp(Fwd(SimplicialChainMapDef)),
						By(
							b.Simplified(
								free_module.FreeLiftDelta.Read(chainsOfY).At(b.TermAs[Set[D]]("X.simplices(m)"), onGenerators, y)),
							generators.At(m),
							simplex))
				}))
			a.Do(Unfold(chain_complex.ChainMapDef), SplitConjAll(
				Case(
					"each induced map is a homomorphism from the n-chains of X to the n-chains of Y",
					Simp(Fwd(chain_complex.ComplexModuleDef)),
					Simp(Fwd(SimplicialChainsDef)),
					By(maps)),
				Case(
					"the square commutes: the two ways round agree on every (n + 1)-chain of X",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						u := b.FixAs[Fun[D, A]]("u")
						chain := b.Assume()
						n1 := b.TermAs[Nat]("n + 1")
						free := b.Unfolded(chain, SimplicialChainsDef)
						sourceLower := b.Have(
							"the n-chains of X, the free module on X(n), are a module over the ring",
							"module_on(R, "+
								"    mk_module(fun_add⟨D:D⟩(R.add), "+
								"        fun_zero⟨D:D⟩(R.zero), "+
								"        fun_neg⟨D:D⟩(R.neg), "+
								"        fun_smul⟨D:D⟩(R.mul), "+
								"        finite_supp(R.zero, R.carrier, X.simplices(n))))",
							Simp(Rev(SimplicialChainsDef)),
							By(ChainsModule.Read(ring)))
						targetLower := b.Have(
							"and so are the n-chains of Y, stated at n as a fact a law is read at",
							"module_on(R, "+
								"    mk_module(fun_add⟨D:E⟩(R.add), "+
								"        fun_zero⟨D:E⟩(R.zero), "+
								"        fun_neg⟨D:E⟩(R.neg), "+
								"        fun_smul⟨D:E⟩(R.mul), "+
								"        finite_supp(R.zero, R.carrier, Y.simplices(n))))",
							Simp(Rev(SimplicialChainsDef)),
							By(ChainsModule.Read(ring)))
						lower := b.Have(
							"the induced map in dimension n is a homomorphism of the n-chains",
							"module_homomorphism(R, "+
								"    mk_module(fun_add⟨D:D⟩(R.add), "+
								"        fun_zero⟨D:D⟩(R.zero), "+
								"        fun_neg⟨D:D⟩(R.neg), "+
								"        fun_smul⟨D:D⟩(R.mul), "+
								"        finite_supp(R.zero, R.carrier, X.simplices(n))), "+
								"    mk_module(fun_add⟨D:E⟩(R.add), "+
								"        fun_zero⟨D:E⟩(R.zero), "+
								"        fun_neg⟨D:E⟩(R.neg), "+
								"        fun_smul⟨D:E⟩(R.mul), "+
								"        finite_supp(R.zero, R.carrier, Y.simplices(n))), "+
								"    simplicial_chain_map(F, n))",
							By(maps))
						lowerScales := b.Simplified(module_homomorphism.HomSmul.Read(lower))
						boundaryX := b.Have(
							"the boundary of X out of dimension n + 1 is a "+
								"homomorphism from its (n + 1)-chains to its n-chains",
							"module_homomorphism(R, "+
								"    mk_module(fun_add⟨D:D⟩(R.add), "+
								"        fun_zero⟨D:D⟩(R.zero), "+
								"        fun_neg⟨D:D⟩(R.neg), "+
								"        fun_smul⟨D:D⟩(R.mul), "+
								"        finite_supp(R.zero, R.carrier, X.simplices(n + 1))), "+
								"    mk_module(fun_add⟨D:D⟩(R.add), "+
								"        fun_zero⟨D:D⟩(R.zero), "+
								"        fun_neg⟨D:D⟩(R.neg), "+
								"        fun_smul⟨D:D⟩(R.mul), "+
								"        finite_supp(R.zero, R.carrier, X.simplices(n))), "+
								"    simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, X.d, n + 1))",
							Simp(Rev(SimplicialChainsDef)),
							By(BoundaryHom.Read(ring), source))
						boundaryY := b.Have(
							"and so is the boundary of Y",
							"module_homomorphism(R, "+
								"    mk_module(fun_add⟨D:E⟩(R.add), "+
								"        fun_zero⟨D:E⟩(R.zero), "+
								"        fun_neg⟨D:E⟩(R.neg), "+
								"        fun_smul⟨D:E⟩(R.mul), "+
								"        finite_supp(R.zero, R.carrier, Y.simplices(n + 1))), "+
								"    mk_module(fun_add⟨D:E⟩(R.add), "+
								"        fun_zero⟨D:E⟩(R.zero), "+
								"        fun_neg⟨D:E⟩(R.neg), "+
								"        fun_smul⟨D:E⟩(R.mul), "+
								"        finite_supp(R.zero, R.carrier, Y.simplices(n))), "+
								"    simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, Y.d, n + 1))",
							Simp(Rev(SimplicialChainsDef)),
							By(BoundaryHom.Read(ring), target))
						acrossHom := b.Unfolded(b.Have(
							"the boundary of X followed by the induced map, the composite "+
								"∘ being the constant o, is a homomorphism of the chains",
							"module_homomorphism(R, "+
								"    free_module_record(R, X.simplices(n + 1)), "+
								"    mk_module(fun_add⟨D:E⟩(R.add), "+
								"        fun_zero⟨D:E⟩(R.zero), "+
								"        fun_neg⟨D:E⟩(R.neg), "+
								"        fun_smul⟨D:E⟩(R.mul), "+
								"        finite_supp(R.zero, R.carrier, Y.simplices(n))), "+
								"    simplicial_chain_map(F, n) ∘ "+
								"    simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, X.d, n + 1))",
							Simp(Fwd(free_module.FreeModuleRecordDef)),
							By(module_homomorphism.HomCompose, lower, boundaryX)), functions.ComposeApply)
						aroundHom := b.Unfolded(b.Have(
							"and so is the induced map followed by the boundary of Y",
							"module_homomorphism(R, "+
								"    free_module_record(R, X.simplices(n + 1)), "+
								"    mk_module(fun_add⟨D:E⟩(R.add), "+
								"        fun_zero⟨D:E⟩(R.zero), "+
								"        fun_neg⟨D:E⟩(R.neg), "+
								"        fun_smul⟨D:E⟩(R.mul), "+
								"        finite_supp(R.zero, R.carrier, Y.simplices(n))), "+
								"    simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, Y.d, n + 1) ∘ "+
								"    simplicial_chain_map(F, n + 1))",
							Simp(Fwd(free_module.FreeModuleRecordDef)),
							By(module_homomorphism.HomCompose, maps.At(n1), boundaryY)), functions.ComposeApply)
						agree := b.Have(
							"the two ways round agree on the generator at every (n + 1)-simplex x of X",
							Statement{
								Binders: "∀x:D.",
								Hypotheses: []string{
									"x ∈ X.simplices(n + 1)",
								},
								Conclusion: "simplicial_chain_map(F, " +
									"    n, " +
									"    simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, X.d, n + 1, delta_at(x))) = " +
									"simplicial_boundary(R.add, " +
									"    R.zero, " +
									"    R.one, " +
									"    R.neg, " +
									"    R.mul, " +
									"    Y.d, " +
									"    n + 1, " +
									"    simplicial_chain_map(F, n + 1, delta_at(x)))",
							},
							Derive(func(c *Argument) {
								x := c.FixAs[D]("x")
								simplex := c.Assume()
								faces := c.Have(
									"each face of x is an n-simplex",
									"∀i:num. i ∈ 0 .. n + 1 ⇒ X.d(n + 1, i, x) ∈ X.simplices(n)",
									c.ForEach(func(i *Expr[Nat]) Action {
										return By(simplicial_set.FaceIn.Read(source).At(n, i, x), simplex)
									}))
								sourceScales := c.Simplified(module.SmulIn.Read(sourceLower))
								terms := c.Have(
									"so each term of the face sum of x, a signed generator at a face, is an n-chain of X",
									Statement{
										Binders: "∀i:num.",
										Hypotheses: []string{
											"i ∈ 0 .. n + 1",
										},
										Conclusion: "fun_smul(alternating_sign(i), delta_at(X.d(n + 1, i, x))) ∈ " +
											"finite_supp(R.zero, R.carrier, X.simplices(n))",
									},
									c.ForEach(func(i *Expr[Nat]) Action {
										return By(
											faces.At(i),
											sourceScales,
											free_module.DeltaAtIn.Read(ring),
											comm_ring.AlternatingSignIn.Read(ring))
									}))
								termwise := c.Have(
									"the induced map takes each term to the generator "+
										"at the same face of F(n + 1, x), with the same sign",
									Statement{
										Binders: "∀i:num.",
										Hypotheses: []string{
											"i ∈ 0 .. n + 1",
										},
										Conclusion: "simplicial_chain_map(F, " +
											"    n, " +
											"    fun_smul(alternating_sign(i), delta_at(X.d(n + 1, i, x)))) = " +
											"fun_smul(alternating_sign(i), delta_at(Y.d(n + 1, i, F(n + 1, x))))",
									},
									Derive(func(e *Argument) {
										i := e.FixAs[Nat]("i")
										bound := e.Assume()
										face := e.Have(
											"the i-th face of x is an n-simplex",
											"X.d(n + 1, i, x) ∈ X.simplices(n)",
											By(faces.At(i), bound))
										image := e.Have(
											"the induced map takes the generator at that face to the generator at its image",
											"simplicial_chain_map(F, n, delta_at(X.d(n + 1, i, x))) = delta_at(F(n, X.d(n + 1, i, x)))",
											By(images.At(n, e.TermAs[D]("X.d(n + 1, i, x)")), face))
										commutes := e.Have(
											"F commutes with the i-th face",
											"F(n, X.d(n + 1, i, x)) = Y.d(n + 1, i, F(n + 1, x))",
											By(simplicial_set.MapFace.Read(mapping).At(n, i, x), simplex, bound))
										e.Show(
											"the sign comes out, then the generator goes to the generator at the commuted face",
											CalcEq(
												Leg(
													e.TermAs[Fun[E, A]](
														"fun_smul(alternating_sign(i), simplicial_chain_map(F, n, delta_at(X.d(n + 1, i, x))))"),
													"the induced map is linear, so the sign comes out",
													By(lowerScales, comm_ring.AlternatingSignIn.Read(ring), free_module.DeltaAtIn.Read(ring), face)),
												Leg(
													e.TermAs[Fun[E, A]]("fun_smul(alternating_sign(i), delta_at(F(n, X.d(n + 1, i, x))))"),
													"the generator at the face goes to the generator at its image",
													image.Rw(),
													Basic()),
												FinalLeg(
													"which is the i-th face of F(n + 1, x)",
													commutes.Rw(),
													Basic()),
											))
									}))
								image := c.Have(
									"F(n + 1, x) is an (n + 1)-simplex of Y",
									"F(n + 1, x) ∈ Y.simplices(n + 1)",
									By(simplicial_set.MapIn.Read(mapping).At(n1, x), simplex))
								generator := c.Have(
									"the induced map takes the generator at x to the generator at F(n + 1, x)",
									"simplicial_chain_map(F, n + 1, delta_at(x)) = delta_at(F(n + 1, x))",
									By(images.At(n1, x), simplex))
								lowerSums := c.Have(
									"the induced map carries a finite sum to the sum of its values in the target record",
									Statement{
										Binders: "∀S:set(num). ∀G:(num → D → A).",
										Hypotheses: []string{
											"finite(S)",
											"∀j:num. j ∈ S ⇒ G(j) ∈ finite_supp(R.zero, R.carrier, X.simplices(n))",
										},
										Conclusion: "simplicial_chain_map(F, " +
											"    n, " +
											"    module_sum(fun_add⟨D:D⟩(R.add), fun_zero⟨D:D⟩(R.zero), S, G)) = " +
											"module_sum(fun_add⟨D:E⟩(R.add), " +
											"    fun_zero⟨D:E⟩(R.zero), " +
											"    S, " +
											"    λj:num. simplicial_chain_map(F, n, G(j)))",
									},
									By(
										lower,
										Where(
											module_homomorphism.HomSum.Inst(
												TypeBinder.BindA[A](),
												TypeBinder.BindB[Fun[D, A]](),
												TypeBinder.BindC[Fun[E, A]](),
												TypeBinder.BindD[Nat]()),
											"R",
											c.TermAs[module_record.RingOps[A]]("R")).
											Where(
												"M",
												c.TermAs[module_record.ModuleOps[A, Fun[D, A]]](
													"mk_module(fun_add⟨D:D⟩, "+
														"    fun_zero⟨D:D⟩, "+
														"    fun_neg⟨D:D⟩, "+
														"    fun_smul⟨D:D⟩, "+
														"    finite_supp(R.zero, R.carrier, X.simplices(n)))")).
											Where(
												"N",
												c.TermAs[module_record.ModuleOps[A, Fun[E, A]]](
													"mk_module(fun_add⟨D:E⟩, "+
														"    fun_zero⟨D:E⟩, "+
														"    fun_neg⟨D:E⟩, "+
														"    fun_smul⟨D:E⟩, "+
														"    finite_supp(R.zero, R.carrier, Y.simplices(n)))")).
											Where("f", c.Term("simplicial_chain_map(F, n)"))))
								c.Show(
									"both ways round give the alternating sum of the generators at the faces of F(n + 1, x)",
									CalcEq(
										Leg(
											c.TermAs[Fun[E, A]]("simplicial_chain_map(F, n, face_sum(n + 1, x))"),
											"the boundary of the generator at x is its face sum",
											Congr(),
											By(At(BoundaryDelta.Read(ring), X, n, x), source, simplex)),
										Leg(
											c.TermAs[Fun[E, A]](
												"simplicial_chain_map(F, "+
													"    n, "+
													"    module_sum(fun_add⟨D:D⟩(R.add), "+
													"        fun_zero⟨D:D⟩(R.zero), "+
													"        0 .. n + 1, "+
													"        λi:num. fun_smul(alternating_sign(i), delta_at(X.d(n + 1, i, x)))))"),
											"the alternating sum of the generators at its faces",
											Simp(Fwd(FaceSumDef)),
											Refl()),
										Leg(
											c.TermAs[Fun[E, A]](
												"module_sum(fun_add⟨D:E⟩(R.add), "+
													"    fun_zero⟨D:E⟩(R.zero), "+
													"    0 .. n + 1, "+
													"    λi:num. "+
													"        simplicial_chain_map(F, n, fun_smul(alternating_sign(i), delta_at(X.d(n + 1, i, x)))))"),
											"the induced map is a homomorphism, so it passes through the finite sum of n-chains",
											By(lowerSums, terms, num_segment.Finite)),
										Leg(
											c.TermAs[Fun[E, A]](
												"module_sum(fun_add⟨D:E⟩(R.add), "+
													"    fun_zero⟨D:E⟩(R.zero), "+
													"    0 .. n + 1, "+
													"    λi:num. fun_smul(alternating_sign(i), delta_at(Y.d(n + 1, i, F(n + 1, x)))))"),
											"term by term, F commutes with the faces",
											By(module.ModuleSumCongruence, termwise)),
										Leg(
											c.TermAs[Fun[E, A]]("face_sum(n + 1, F(n + 1, x))"),
											"which is the face sum of F(n + 1, x)",
											Simp(Fwd(FaceSumDef)),
											Refl()),
										Leg(
											c.TermAs[Fun[E, A]](
												"simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, Y.d, n + 1, delta_at(F(n + 1, x)))"),
											"the boundary of the generator at F(n + 1, x)",
											By(At(BoundaryDelta.Read(ring), Y, n, F.Apply(n1, x)), target, image)),
										FinalLeg(
											"and the generator at F(n + 1, x) is the image of the generator at x",
											generator.Rw(),
											Basic()),
									))
							}))
						across := b.TermAs[Fun[Fun[D, A], Fun[E, A]]](
							"λv:(D → A). " +
								"    simplicial_chain_map(F, " +
								"        n, " +
								"        simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, X.d, n + 1, v))")
						around := b.TermAs[Fun[Fun[D, A], Fun[E, A]]](
							"λv:(D → A). " +
								"    simplicial_boundary(R.add, " +
								"        R.zero, " +
								"        R.one, " +
								"        R.neg, " +
								"        R.mul, " +
								"        Y.d, " +
								"        n + 1, " +
								"        simplicial_chain_map(F, n + 1, v))")
						b.Show(
							"two homomorphisms out of the free module on X(n + 1) that agree on its generators agree on u",
							By(
								b.Simplified(GroupPremises(
									acrossHom,
									aroundHom,
									agree,
									free,
									free_module.FreeLiftUnique.Read(targetLower).At(
										b.TermAs[Set[D]]("X.simplices(n + 1)"), across, around, u))),
								acrossHom,
								aroundHom,
								agree,
								free))
					})),
			))
		}),
})}

// SimplicialHomologyDef — `simplicial_homology(…, X, d, c, n)`: the
// homology of the alternating face map complex, the cycles modulo the
// boundaries as cosets. Under the ring and the simplicial set the text
// writes `simplicial_homology(c, n)`.
var SimplicialHomologyDef = simplicialHomologyDefThm{family.Define(registry.DefEntry{
	Name:  "SimplicialHomologyDef",
	Key:   "prop_b9a342c8c483ea88",
	Const: "simplicial_homology",
	Type: "(A → A → A) → " +
		"A → " +
		"A → " +
		"(A → A) → " +
		"(A → A → A) → " +
		"simplicial_ops(D) → " +
		"set(A) → " +
		"num → " +
		"set(set(D → A))",
	Implicit: []string{"add", "zero", "one", "neg", "mul", "X"},
	Equations: []string{
		"∀add:(A → A → A). " +
			"∀zero one:A. " +
			"∀neg:(A → A). " +
			"∀mul:(A → A → A). " +
			"∀X:simplicial_ops(D). " +
			"∀c:set(A). " +
			"∀n:num. " +
			"    simplicial_homology(add, zero, one, neg, mul, X, c, n) = " +
			"    homology(pack_complex(fun_add⟨D:D⟩(add), " +
			"            fun_zero⟨D:D⟩(zero), " +
			"            fun_neg⟨D:D⟩(neg), " +
			"            fun_smul⟨D:D⟩(mul), " +
			"            simplicial_chains(zero, X, c), " +
			"            simplicial_boundary(add, zero, one, neg, mul, X.d)), " +
			"        n)",
	},
	Deps: []registry.EntryLike{SimplicialChainsDef, SimplicialBoundaryDef},
})}
