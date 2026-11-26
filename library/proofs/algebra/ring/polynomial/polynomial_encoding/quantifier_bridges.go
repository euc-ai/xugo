// quantifier_bridges.go — a block of names quantified one after another
// read, under any evaluator, as one quantifier over what the block decodes
// to: a ring tuple, a degree-bounded polynomial, or a family of them.

package polynomial_encoding

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// substitutedTuple is the step both tuple bridges take: the environment that substitutes a ring
// tuple y into the block of n names at s is carrier-valued, agrees with σ below s and reads y
// back at s, so the body hypothesis says the block's body holds there exactly when Q holds of y.
func substitutedTuple(
	a *Argument,
	R *Expr[RingOps[A]],
	s, n *Expr[Nat],
	σ *Arrow[Nat, A],
	env, body Fact,
) Fact {
	carrier := a.TermAs[Set[A]]("R.carrier")
	return a.Have(
		"at a ring tuple substituted into the block, the block's body says what Q says of it",
		Statement{
			Binders: "∀y:(num → A).",
			Hypotheses: []string{
				"ring_tuple(R, n, y)",
			},
			Conclusion: "Q(y) ⇔ fo_eval(R.carrier, e, fo_update_range(σ, s, n, y), φ)",
		},
		Derive(func(b *Argument) {
			y := b.FixAs[Fun[Nat, A]]("y")
			tuple := b.Assume()
			τ := b.TermAs[Fun[Nat, A]]("fo_update_range(σ, s, n, y)")
			legal := b.Have(
				"the substituted environment is carrier-valued",
				"fo_env_ok(R.carrier, 𝕌, fo_update_range(σ, s, n, y))",
				By(
					env,
					tuple,
					RingTupleDef.At(R, b.VecAs[A, DimN]("y")),
					first_order.UpdateRangeEnvironment.At(carrier, σ, s, n, y)))
			below := b.Have(
				"it agrees with σ below s",
				"∀v:num. v < s ⇒ fo_update_range(σ, s, n, y, v) = σ(v)",
				By(first_order.UpdateRangeOutside))
			b.Show(
				"and reads y back at s",
				By(legal, below, tuple, DecodeUpdatedTuple.At(R, n, s, σ, y), body.At(τ, y)))
		}))
}

// paddedTuple is the other step both tuple bridges take: carrier values z at the names of the
// block, padded by zero past n, form a ring tuple w, and substituting w puts z's values in the
// block.
func paddedTuple(b *Argument, values Fact) (w *Expr[Fun[Nat, A]], padded, same Fact) {
	padded = b.Have(
		"z padded by zero past n is a ring tuple",
		"ring_tuple(R, n, λi:num. COND(i < n, z(i), R.zero))",
		Unfold(RingTupleDef),
		Unfold(vec_space.VecDef),
		By(values, nat_order.NotLessThan))
	offset := b.Have(
		"a name of the block lies fewer than n past s",
		"∀v:num. s ≤ v ∧ v < s + n ⇒ v - s < n",
		ByArith())
	same = b.Have(
		"the padded tuple puts the same values in the block",
		"fo_update_range(σ, s, n, λi:num. COND(i < n, z(i), R.zero)) = fo_update_range(σ, s, n, z)",
		Unfold(first_order.UpdateRangeDef),
		Funext(),
		By(offset))
	return b.TermAs[Fun[Nat, A]]("λi:num. COND(i < n, z(i), R.zero)"), padded, same
}

// AllRangeTupleBridge — a universal block of n names at s reads as a universal quantifier over the
// ring tuples of length n, whatever the evaluator: the block ranges over the carrier values at its
// names, which the ring tuples substituted there give, each of them padded by zero past n; and
// the environment that substitutes a ring tuple y agrees with σ below s, is carrier-valued and
// reads y back at s, so the hypothesis matches the block's body with what it says of y.
var AllRangeTupleBridge = allRangeTupleBridgeThm{family.Add(registry.ProofEntry{
	Name: "AllRangeTupleBridge",
	Key:  "prop_f0904b0c99c8c0c6",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀e:(B → (num → A) → bool). " +
			"∀s n:num. " +
			"∀σ:(num → A). " +
			"∀φ:fo_formula(B). " +
			"∀Q:((num → A) → bool).",
		Hypotheses: []string{
			"fo_env_ok(R.carrier, 𝕌, σ)",
			"∀τ y:(num → A). " +
				"    fo_env_ok(R.carrier, 𝕌, τ) ∧ " +
				"    (∀v:num. v < s ⇒ τ(v) = σ(v)) ∧ " +
				"    ring_tuple(R, n, y) ∧ " +
				"    decode_tuple(R, n, s, τ) = y ⇒ " +
				"    (Q(y) ⇔ fo_eval(R.carrier, e, τ, φ))",
		},
		Conclusion: "(∀y:(num → A). ring_tuple(R, n, y) ⇒ Q(y)) ⇔ " +
			"fo_eval(R.carrier, e, σ, fo_all_range(s, n, φ))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		e *Arrow2[B, Fun[Nat, A], Bool],
		s, n *Expr[Nat],
		σ *Arrow[Nat, A],
		φ *Expr[Formula[B]],
		Q *Arrow[Fun[Nat, A], Bool],
		env, body Fact,
	) {
		updated := substitutedTuple(a, R, s, n, σ, env, body)
		a.Do(Simp(Fwd(first_order.AllRangeSemantics)))
		a.Iff()
		a.Forward(
			"carrier values at the names of the block, padded by zero past n, form a ring tuple",
			func(b *Argument, holds Fact) {
				b.FixAs[Fun[Nat, A]]("z")
				w, padded, same := paddedTuple(b, b.Assume())
				b.Show(
					"Q holds of the padded tuple, whose block is z's",
					By(same, padded, holds.At(w), updated.At(w)))
			})
		a.Backward(
			"a ring tuple is carrier-valued below n",
			func(b *Argument, block Fact) {
				y := b.FixAs[Fun[Nat, A]]("y")
				tuple := b.Assume()
				b.Show(
					"so the block's body holds with y substituted, which is what Q says of y",
					By(tuple, RingTupleDef.At(R, b.VecAs[A, DimN]("y")), block.At(y), updated.At(y)))
			})
	}),
})}

// ExistsRangeTupleBridge — an existential block of n names at s reads as an existential
// quantifier over the ring tuples of length n, whatever the evaluator: a witness of the block is
// a carrier value at each of its names, which padded by zero past n is a ring tuple putting the
// same values there, and a ring tuple is carrier-valued below n; the environment that substitutes
// a ring tuple y agrees with σ below s, is carrier-valued and reads y back at s, so the hypothesis
// matches the block's body with what Q says of y.
var ExistsRangeTupleBridge = existsRangeTupleBridgeThm{family.Add(registry.ProofEntry{
	Name: "ExistsRangeTupleBridge",
	Key:  "prop_b303b3c59203d192",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀e:(B → (num → A) → bool). " +
			"∀s n:num. " +
			"∀σ:(num → A). " +
			"∀φ:fo_formula(B). " +
			"∀Q:((num → A) → bool).",
		Hypotheses: []string{
			"fo_env_ok(R.carrier, 𝕌, σ)",
			"∀τ y:(num → A). " +
				"    fo_env_ok(R.carrier, 𝕌, τ) ∧ " +
				"    (∀v:num. v < s ⇒ τ(v) = σ(v)) ∧ " +
				"    ring_tuple(R, n, y) ∧ " +
				"    decode_tuple(R, n, s, τ) = y ⇒ " +
				"    (Q(y) ⇔ fo_eval(R.carrier, e, τ, φ))",
		},
		Conclusion: "(∃y:(num → A). ring_tuple(R, n, y) ∧ Q(y)) ⇔ " +
			"fo_eval(R.carrier, e, σ, fo_exists_range(s, n, φ))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		e *Arrow2[B, Fun[Nat, A], Bool],
		s, n *Expr[Nat],
		σ *Arrow[Nat, A],
		φ *Expr[Formula[B]],
		Q *Arrow[Fun[Nat, A], Bool],
		env, body Fact,
	) {
		updated := substitutedTuple(a, R, s, n, σ, env, body)
		a.Do(Simp(Fwd(first_order.ExistsRangeSemantics)))
		a.Iff()
		a.Forward(
			"a ring tuple Q holds of is carrier-valued below n, and the block's body holds with it substituted",
			func(b *Argument, holds Fact) {
				y, witness := b.UnpackAs[Fun[Nat, A]](holds, "y")
				parts := b.Conjuncts(
					witness,
					"y is a ring tuple",
					"Q holds of y")
				b.Take(y)
				b.Show(
					"y is carrier-valued below n, and the body holds with y substituted",
					By(parts[0], parts[1], RingTupleDef.At(R, b.VecAs[A, DimN]("y")), updated.At(y)))
			})
		a.Backward(
			"carrier values at the names of the block, padded by zero past n, form a ring tuple Q holds of",
			func(b *Argument, block Fact) {
				_, zFact := b.UnpackAs[Fun[Nat, A]](block, "z")
				parts := b.Conjuncts(
					zFact,
					"z is carrier-valued below n",
					"the block's body holds with z substituted")
				w, padded, same := paddedTuple(b, parts[0])
				b.Take(w)
				b.Show(
					"the padded tuple is a ring tuple, and Q holds of it since the body does at its block",
					By(same, padded, parts[1], updated.At(w)))
			})
	}),
})}

// substitutedPolynomial is the step both polynomial bridges take: the environment that
// substitutes carrier values c into the coefficient block at s is carrier-valued and agrees with
// σ below s, so when that block decodes to a polynomial p of degree at most d, the body
// hypothesis says the block's body holds there exactly when Q holds of p.
func substitutedPolynomial(
	a *Argument,
	R *Expr[RingOps[A]],
	s, n, d *Expr[Nat],
	σ *Arrow[Nat, A],
	env, body Fact,
) Fact {
	carrier := a.TermAs[Set[A]]("R.carrier")
	count := a.TermAs[Nat]("coefficient_count(n, d)")
	return a.Have(
		"with carrier values substituted into the block, the "+
			"block's body says what Q says of a polynomial they decode to",
		Statement{
			Binders: "∀c:(num → A). ∀p:((num → num) → A).",
			Hypotheses: []string{
				"∀i:num. i < coefficient_count(n, d) ⇒ c(i) ∈ R.carrier",
				"polynomial_bound(R, n, d, p)",
				"decode_polynomial(R, n, d, s, fo_update_range(σ, s, coefficient_count(n, d), c)) = p",
			},
			Conclusion: "fo_env_ok(R.carrier, 𝕌, fo_update_range(σ, s, coefficient_count(n, d), c)) ∧ " +
				"(Q(p) ⇔ fo_eval(R.carrier, e, fo_update_range(σ, s, coefficient_count(n, d), c), φ))",
		},
		Derive(func(b *Argument) {
			c := b.FixAs[Fun[Nat, A]]("c")
			p := b.FixAs[Fun[_Monomial, A]]("p")
			given := b.Conjuncts(
				b.Assume(),
				"c is carrier-valued below the block's length",
				"p has degree at most d",
				"the substituted block decodes to p")
			values, bounded, decoded := given[0], given[1], given[2]
			τ := b.TermAs[Fun[Nat, A]]("fo_update_range(σ, s, coefficient_count(n, d), c)")
			legal := b.Have(
				"the substituted environment is carrier-valued",
				"fo_env_ok(R.carrier, 𝕌, fo_update_range(σ, s, coefficient_count(n, d), c))",
				By(env, values, first_order.UpdateRangeEnvironment.At(carrier, σ, s, count, c)))
			below := b.Have(
				"it agrees with σ below s",
				"∀v:num. v < s ⇒ fo_update_range(σ, s, coefficient_count(n, d), c, v) = σ(v)",
				By(first_order.UpdateRangeOutside))
			b.Show(
				"and decodes to p at s",
				By(legal, below, bounded, decoded, body.At(τ, p)))
		}))
}

// decodedPolynomial is the step from a block of coefficients to the polynomial it decodes to:
// substituting carrier values c into the block gives a carrier-valued environment, whose block
// at s decodes to a polynomial of degree at most d.
func decodedPolynomial(
	b *Argument,
	R *Expr[RingOps[A]],
	s, n, d *Expr[Nat],
	σ *Arrow[Nat, A],
	c *Expr[Fun[Nat, A]],
	ring comm_ring.CommRingFact[on.R],
	env, values Fact,
) (decodedAt *Expr[Fun[_Monomial, A]], bounded Fact) {
	carrier := b.TermAs[Set[A]]("R.carrier")
	universe := b.TermAs[Set[Nat]]("𝕌")
	count := b.TermAs[Nat]("coefficient_count(n, d)")
	τ := b.TermAs[Fun[Nat, A]]("fo_update_range(σ, s, coefficient_count(n, d), c)")
	legal := b.Have(
		"the substituted environment is carrier-valued",
		"fo_env_ok(R.carrier, 𝕌, fo_update_range(σ, s, coefficient_count(n, d), c))",
		By(env, values, first_order.UpdateRangeEnvironment.At(carrier, σ, s, count, c)))
	bounded = b.Have(
		"the polynomial decoded at s has degree at most d",
		"polynomial_bound(R, "+
			"    n, "+
			"    d, "+
			"    decode_polynomial(R, n, d, s, fo_update_range(σ, s, coefficient_count(n, d), c)))",
		By(
			ring,
			legal,
			first_order.EnvOKSubset.At(
				carrier, b.TermAs[Set[Nat]]("{j:num | s ≤ j ∧ j < s + coefficient_count(n, d)}"), universe, τ),
			set_order.SubsetUniv,
			DecodePolynomialBound.At(R, n, d, s, τ)))
	return b.TermAs[Fun[_Monomial, A]](
			"decode_polynomial(R, n, d, s, fo_update_range(σ, s, coefficient_count(n, d), c))"),
		bounded
}

// representedPolynomial is the step from a polynomial p of degree at most d back to a block of
// coefficients: p is decoded from some carrier-valued environment ρ at s, and substituting ρ's
// values from s on into the block decodes to p again.
func representedPolynomial(
	b *Argument,
	R *Expr[RingOps[A]],
	s, n, d *Expr[Nat],
	σ *Arrow[Nat, A],
	p *Expr[Fun[_Monomial, A]],
	ring comm_ring.CommRingFact[on.R],
	bounded Fact,
) (c *Expr[Fun[Nat, A]], values, decoded Fact) {
	ρ, encoding := b.UnpackAs[Fun[Nat, A]](
		GroupPremises(ring, bounded, CoefficientRepresentation.At(R, n, d, s, p)),
		"ρ")
	parts := b.Conjuncts(
		encoding,
		"ρ is carrier-valued",
		"its block at s decodes to p")
	c = b.TermAs[Fun[Nat, A]]("λi:num. ρ(s + i)")
	τ := b.TermAs[Fun[Nat, A]]("fo_update_range(σ, s, coefficient_count(n, d), λi:num. ρ(s + i))")
	values = b.Have(
		"ρ's values from s on are carrier values",
		"∀i:num. i < coefficient_count(n, d) ⇒ ρ(s + i) ∈ R.carrier",
		By(parts[0], first_order.EnvOKDef, set_basic.InUniv))
	shifted := b.Have(
		"substituting ρ's values from s into the block agrees with ρ on the block",
		Statement{
			Binders: "∀v:num.",
			Hypotheses: []string{
				"s ≤ v",
				"v < s + coefficient_count(n, d)",
			},
			Conclusion: "fo_update_range(σ, s, coefficient_count(n, d), λi:num. ρ(s + i), v) = ρ(v)",
		},
		Cite(first_order.UpdateRangeCopy))
	decoded = b.Have(
		"so the substituted block decodes to p",
		"decode_polynomial(R, "+
			"    n, "+
			"    d, "+
			"    s, "+
			"    fo_update_range(σ, s, coefficient_count(n, d), λi:num. ρ(s + i))) = "+
			"p",
		By(shifted, parts[1], DecodeCongruence.At(R, n, d, s, τ, ρ)))
	return c, values, decoded
}

// AllRangePolynomialBridge — a universal block of coefficient_count(n, d) names at s reads as a
// universal quantifier over the polynomials in n variables of degree at most d, whatever the
// evaluator: the coefficients substituted into the block decode to such a polynomial, and every
// such polynomial is decoded from some carrier-valued environment at s, whose block substituted
// into σ decodes to it again; the environment substituting a block agrees with σ below s and is
// carrier-valued, so the hypothesis matches the block's body with what Q says of the decoded
// polynomial.
var AllRangePolynomialBridge = allRangePolynomialBridgeThm{family.Add(registry.ProofEntry{
	Name: "AllRangePolynomialBridge",
	Key:  "prop_ca3ae9e09cefe99f",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀e:(B → (num → A) → bool). " +
			"∀s n d:num. " +
			"∀σ:(num → A). " +
			"∀φ:fo_formula(B). " +
			"∀Q:(((num → num) → A) → bool).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"fo_env_ok(R.carrier, 𝕌, σ)",
			"∀τ:(num → A). ∀p:((num → num) → A). " +
				"    fo_env_ok(R.carrier, 𝕌, τ) ∧ " +
				"    (∀v:num. v < s ⇒ τ(v) = σ(v)) ∧ " +
				"    polynomial_bound(R, n, d, p) ∧ " +
				"    decode_polynomial(R, n, d, s, τ) = p ⇒ " +
				"    (Q(p) ⇔ fo_eval(R.carrier, e, τ, φ))",
		},
		Conclusion: "(∀p:((num → num) → A). polynomial_bound(R, n, d, p) ⇒ Q(p)) ⇔ " +
			"fo_eval(R.carrier, e, σ, fo_all_range(s, coefficient_count(n, d), φ))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		e *Arrow2[B, Fun[Nat, A], Bool],
		s, n, d *Expr[Nat],
		σ *Arrow[Nat, A],
		φ *Expr[Formula[B]],
		Q *Arrow[Fun[_Monomial, A], Bool],
		ring comm_ring.CommRingFact[on.R],
		env, body Fact,
	) {
		updated := substitutedPolynomial(a, R, s, n, d, σ, env, body)
		a.Do(Simp(Fwd(first_order.AllRangeSemantics)))
		a.Iff()
		a.Forward(
			"the coefficients substituted into the block decode "+
				"to a polynomial of degree at most d, which Q holds of",
			func(b *Argument, holds Fact) {
				c := b.FixAs[Fun[Nat, A]]("c")
				values := b.Assume()
				decodedAt, bounded := decodedPolynomial(b, R, s, n, d, σ, c, ring, env, values)
				b.Show(
					"Q holds of it, so the block's body holds",
					By(values, bounded, holds.At(decodedAt), updated.At(c, decodedAt)))
			})
		a.Backward(
			"a polynomial of degree at most d is decoded from carrier values substituted into the block",
			func(b *Argument, block Fact) {
				p := b.FixAs[Fun[_Monomial, A]]("p")
				bounded := b.Assume()
				c, values, decoded := representedPolynomial(b, R, s, n, d, σ, p, ring, bounded)
				b.Show(
					"the block's body holds there, so Q holds of p",
					By(values, bounded, decoded, block.At(c), updated.At(c, p)))
			})
	}),
})}

// ExistsRangePolynomialBridge — an existential block of coefficient_count(n, d) names at s reads
// as an existential quantifier over the polynomials in n variables of degree at most d, whatever
// the evaluator: a witness of the block decodes to such a polynomial, and such a polynomial is
// decoded from some carrier-valued environment at s, whose block substituted into σ decodes to it
// again; the environment substituting a block agrees with σ below s and is carrier-valued, so the
// hypothesis matches the block's body with what Q says of the decoded polynomial.
var ExistsRangePolynomialBridge = existsRangePolynomialBridgeThm{family.Add(registry.ProofEntry{
	Name: "ExistsRangePolynomialBridge",
	Key:  "prop_ce1a3d90f2277b72",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀e:(B → (num → A) → bool). " +
			"∀s n d:num. " +
			"∀σ:(num → A). " +
			"∀φ:fo_formula(B). " +
			"∀Q:(((num → num) → A) → bool).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"fo_env_ok(R.carrier, 𝕌, σ)",
			"∀τ:(num → A). ∀p:((num → num) → A). " +
				"    fo_env_ok(R.carrier, 𝕌, τ) ∧ " +
				"    (∀v:num. v < s ⇒ τ(v) = σ(v)) ∧ " +
				"    polynomial_bound(R, n, d, p) ∧ " +
				"    decode_polynomial(R, n, d, s, τ) = p ⇒ " +
				"    (Q(p) ⇔ fo_eval(R.carrier, e, τ, φ))",
		},
		Conclusion: "(∃p:((num → num) → A). polynomial_bound(R, n, d, p) ∧ Q(p)) ⇔ " +
			"fo_eval(R.carrier, e, σ, fo_exists_range(s, coefficient_count(n, d), φ))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		e *Arrow2[B, Fun[Nat, A], Bool],
		s, n, d *Expr[Nat],
		σ *Arrow[Nat, A],
		φ *Expr[Formula[B]],
		Q *Arrow[Fun[_Monomial, A], Bool],
		ring comm_ring.CommRingFact[on.R],
		env, body Fact,
	) {
		updated := substitutedPolynomial(a, R, s, n, d, σ, env, body)
		a.Do(Simp(Fwd(first_order.ExistsRangeSemantics)))
		a.Iff()
		a.Forward(
			"a polynomial of degree at most d that Q holds of is "+
				"decoded from carrier values substituted into the block",
			func(b *Argument, holds Fact) {
				p, witness := b.UnpackAs[Fun[_Monomial, A]](holds, "p")
				given := b.Conjuncts(
					witness,
					"p has degree at most d",
					"Q holds of p")
				c, values, decoded := representedPolynomial(b, R, s, n, d, σ, p, ring, given[0])
				b.Take(c)
				b.Show(
					"the values are carrier values, and the block's body holds with them substituted",
					By(values, given[0], given[1], decoded, updated.At(c, p)))
			})
		a.Backward(
			"the coefficients substituted into the block decode "+
				"to a polynomial of degree at most d, which Q holds of",
			func(b *Argument, block Fact) {
				c, witness := b.UnpackAs[Fun[Nat, A]](block, "c")
				parts := b.Conjuncts(
					witness,
					"c is carrier-valued below the coefficient count",
					"the block's body holds with c substituted")
				decodedAt, bounded := decodedPolynomial(b, R, s, n, d, σ, c, ring, env, parts[0])
				b.Take(decodedAt)
				b.Show(
					"it has degree at most d, and Q holds of it since the body does at the block",
					By(parts[0], parts[1], bounded, updated.At(c, decodedAt)))
			})
	}),
})}

// substitutedFamily is the step both family bridges take: the environment that substitutes
// carrier values c into the run of k coefficient blocks at s is carrier-valued and agrees with σ
// below s, so when its blocks decode below k to a family P of degree at most d, the body
// hypothesis says the block's body holds there exactly when Q holds of P.
func substitutedFamily(
	a *Argument,
	R *Expr[RingOps[A]],
	s, n, d, k *Expr[Nat],
	σ *Arrow[Nat, A],
	env, body Fact,
) Fact {
	carrier := a.TermAs[Set[A]]("R.carrier")
	length := a.TermAs[Nat]("k * coefficient_count(n, d)")
	return a.Have(
		"with carrier values substituted into the block, the "+
			"block's body says what Q says of a family they decode to",
		Statement{
			Binders: "∀c:(num → A). ∀P:(num → (num → num) → A).",
			Hypotheses: []string{
				"∀i:num. i < k * coefficient_count(n, d) ⇒ c(i) ∈ R.carrier",
				"∀j:num. j < k ⇒ polynomial_bound(R, n, d, P(j))",
				"∀j:num. " +
					"    j < k ⇒ " +
					"    decode_polynomials(R, n, d, s, fo_update_range(σ, s, k * coefficient_count(n, d), c), j) = " +
					"    P(j)",
			},
			Conclusion: "fo_env_ok(R.carrier, 𝕌, fo_update_range(σ, s, k * coefficient_count(n, d), c)) ∧ " +
				"(Q(P) ⇔ fo_eval(R.carrier, e, fo_update_range(σ, s, k * coefficient_count(n, d), c), φ))",
		},
		Derive(func(b *Argument) {
			c := b.FixAs[Fun[Nat, A]]("c")
			P := b.FixAs[Fun2[Nat, _Monomial, A]]("P")
			given := b.Conjuncts(
				b.Assume(),
				"c is carrier-valued below the block's length",
				"P has degree at most d below k",
				"the substituted blocks decode to P below k")
			values, bounded, decoded := given[0], given[1], given[2]
			τ := b.TermAs[Fun[Nat, A]]("fo_update_range(σ, s, k * coefficient_count(n, d), c)")
			legal := b.Have(
				"the substituted environment is carrier-valued",
				"fo_env_ok(R.carrier, 𝕌, fo_update_range(σ, s, k * coefficient_count(n, d), c))",
				By(env, values, first_order.UpdateRangeEnvironment.At(carrier, σ, s, length, c)))
			below := b.Have(
				"it agrees with σ below s",
				"∀v:num. v < s ⇒ fo_update_range(σ, s, k * coefficient_count(n, d), c, v) = σ(v)",
				By(first_order.UpdateRangeOutside))
			b.Show(
				"and decodes to P below k",
				By(legal, below, bounded, decoded, body.At(τ, P)))
		}))
}

// decodedFamily is the step from a run of coefficient blocks to the family it decodes to:
// substituting carrier values c into the run gives a carrier-valued environment, each of whose
// blocks from s on decodes to a polynomial of degree at most d.
func decodedFamily(
	b *Argument,
	R *Expr[RingOps[A]],
	s, n, d, k *Expr[Nat],
	σ *Arrow[Nat, A],
	c *Expr[Fun[Nat, A]],
	ring comm_ring.CommRingFact[on.R],
	env, values Fact,
) (decodedAt *Expr[Fun2[Nat, _Monomial, A]], bounded Fact) {
	carrier := b.TermAs[Set[A]]("R.carrier")
	universe := b.TermAs[Set[Nat]]("𝕌")
	length := b.TermAs[Nat]("k * coefficient_count(n, d)")
	τ := b.TermAs[Fun[Nat, A]]("fo_update_range(σ, s, k * coefficient_count(n, d), c)")
	legal := b.Have(
		"the substituted environment is carrier-valued",
		"fo_env_ok(R.carrier, 𝕌, fo_update_range(σ, s, k * coefficient_count(n, d), c))",
		By(env, values, first_order.UpdateRangeEnvironment.At(carrier, σ, s, length, c)))
	bounded = b.Have(
		"each polynomial decoded from the blocks has degree at most d",
		"∀j:num. "+
			"    polynomial_bound(R, "+
			"        n, "+
			"        d, "+
			"        decode_polynomials(R, n, d, s, fo_update_range(σ, s, k * coefficient_count(n, d), c), j))",
		Derive(func(f *Argument) {
			f.FixAs[Nat]("j")
			start := f.TermAs[Nat]("s + j * coefficient_count(n, d)")
			f.Show(
				"the j-th block of a carrier-valued environment decodes to a polynomial of degree at most d",
				Simp(Fwd(DecodePolynomialsDef)),
				By(
					ring,
					legal,
					first_order.EnvOKSubset.At(
						carrier,
						f.TermAs[Set[Nat]](
							"{v:num | "+
								"    s + j * coefficient_count(n, d) ≤ v ∧ "+
								"    v < s + j * coefficient_count(n, d) + coefficient_count(n, d)}"),
						universe,
						τ),
					set_order.SubsetUniv,
					DecodePolynomialBound.At(R, n, d, start, τ)))
		}))
	return b.TermAs[Fun2[Nat, _Monomial, A]](
			"decode_polynomials(R, n, d, s, fo_update_range(σ, s, k * coefficient_count(n, d), c))"),
		bounded
}

// representedFamily is the step from a family P of degree at most d back to a run of coefficient
// blocks: P is decoded below k from some carrier-valued environment ρ from s on, and
// substituting ρ's values from s on into the run decodes to P again below k.
func representedFamily(
	b *Argument,
	R *Expr[RingOps[A]],
	s, n, d, k *Expr[Nat],
	σ *Arrow[Nat, A],
	P *Expr[Fun2[Nat, _Monomial, A]],
	ring comm_ring.CommRingFact[on.R],
	bounded Fact,
) (c *Expr[Fun[Nat, A]], values, decoded Fact) {
	ρ, encoding := b.UnpackAs[Fun[Nat, A]](
		GroupPremises(ring, bounded, CoefficientBlockRepresentation.At(R, n, d, s, k, P)),
		"ρ")
	parts := b.Conjuncts(
		encoding,
		"ρ is carrier-valued",
		"its blocks from s decode to P below k")
	c = b.TermAs[Fun[Nat, A]]("λi:num. ρ(s + i)")
	τ := b.TermAs[Fun[Nat, A]]("fo_update_range(σ, s, k * coefficient_count(n, d), λi:num. ρ(s + i))")
	values = b.Have(
		"ρ's values from s on are carrier values",
		"∀i:num. i < k * coefficient_count(n, d) ⇒ ρ(s + i) ∈ R.carrier",
		By(parts[0], first_order.EnvOKDef, set_basic.InUniv))
	shifted := b.Have(
		"substituting ρ's values from s into the block agrees with ρ on the block",
		Statement{
			Binders: "∀v:num.",
			Hypotheses: []string{
				"s ≤ v",
				"v < s + k * coefficient_count(n, d)",
			},
			Conclusion: "fo_update_range(σ, s, k * coefficient_count(n, d), λi:num. ρ(s + i), v) = ρ(v)",
		},
		Cite(first_order.UpdateRangeCopy))
	decoded = b.Have(
		"so the substituted blocks decode to P below k",
		Statement{
			Binders: "∀j:num.",
			Hypotheses: []string{
				"j < k",
			},
			Conclusion: "decode_polynomials(R, " +
				"    n, " +
				"    d, " +
				"    s, " +
				"    fo_update_range(σ, s, k * coefficient_count(n, d), λi:num. ρ(s + i)), " +
				"    j) = " +
				"P(j)",
		},
		Derive(func(f *Argument) {
			j := f.FixAs[Nat]("j")
			below := f.Assume()
			f.Show(
				"the j-th substituted block reads ρ's j-th block",
				By(below, shifted, parts[1], DecodePolynomialsCongruence.At(R, n, d, s, k, τ, ρ, j)))
		}))
	return c, values, decoded
}

// AllRangeFamilyBridge — a universal block of k · coefficient_count(n, d) names at s reads as a
// universal quantifier over the families of k polynomials in n variables of degree at most d,
// whatever the evaluator: the coefficients substituted into the block decode, block by block, to
// such a family, and every such family is decoded from some carrier-valued environment from s
// on, whose blocks substituted into σ decode to it again below k; the environment substituting
// the block agrees with σ below s and is carrier-valued, so the hypothesis matches the block's
// body with what Q says of a family its blocks decode to. The hypothesis pins the family below k
// only, so Q need not ignore the members from k on.
var AllRangeFamilyBridge = allRangeFamilyBridgeThm{family.Add(registry.ProofEntry{
	Name: "AllRangeFamilyBridge",
	Key:  "prop_af043f8fbb6c0a54",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀e:(B → (num → A) → bool). " +
			"∀s n d k:num. " +
			"∀σ:(num → A). " +
			"∀φ:fo_formula(B). " +
			"∀Q:((num → (num → num) → A) → bool).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"fo_env_ok(R.carrier, 𝕌, σ)",
			"∀τ:(num → A). ∀P:(num → (num → num) → A). " +
				"    fo_env_ok(R.carrier, 𝕌, τ) ∧ " +
				"    (∀v:num. v < s ⇒ τ(v) = σ(v)) ∧ " +
				"    (∀j:num. j < k ⇒ polynomial_bound(R, n, d, P(j))) ∧ " +
				"    (∀j:num. j < k ⇒ decode_polynomials(R, n, d, s, τ, j) = P(j)) ⇒ " +
				"    (Q(P) ⇔ fo_eval(R.carrier, e, τ, φ))",
		},
		Conclusion: "(∀P:(num → (num → num) → A). " +
			"    (∀j:num. j < k ⇒ polynomial_bound(R, n, d, P(j))) ⇒ Q(P)) ⇔ " +
			"fo_eval(R.carrier, e, σ, fo_all_range(s, k * coefficient_count(n, d), φ))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		e *Arrow2[B, Fun[Nat, A], Bool],
		s, n, d, k *Expr[Nat],
		σ *Arrow[Nat, A],
		φ *Expr[Formula[B]],
		Q *Arrow[Fun2[Nat, _Monomial, A], Bool],
		ring comm_ring.CommRingFact[on.R],
		env, body Fact,
	) {
		updated := substitutedFamily(a, R, s, n, d, k, σ, env, body)
		a.Do(Simp(Fwd(first_order.AllRangeSemantics)))
		a.Iff()
		a.Forward(
			"the coefficients substituted into the block decode "+
				"to a family of degree at most d, which Q holds of",
			func(b *Argument, holds Fact) {
				c := b.FixAs[Fun[Nat, A]]("c")
				values := b.Assume()
				decodedAt, bounded := decodedFamily(b, R, s, n, d, k, σ, c, ring, env, values)
				b.Show(
					"Q holds of the decoded family, so the block's body holds",
					By(values, bounded, holds.At(decodedAt), updated.At(c, decodedAt)))
			})
		a.Backward(
			"a family of degree at most d is decoded below k from carrier values substituted into the block",
			func(b *Argument, block Fact) {
				P := b.FixAs[Fun2[Nat, _Monomial, A]]("P")
				bounded := b.Assume()
				c, values, decoded := representedFamily(b, R, s, n, d, k, σ, P, ring, bounded)
				b.Show(
					"the block's body holds there, so Q holds of P",
					By(values, bounded, decoded, block.At(c), updated.At(c, P)))
			})
	}),
})}

// ExistsRangeFamilyBridge — an existential block of k · coefficient_count(n, d) names at s reads
// as an existential quantifier over the families of k polynomials in n variables of degree at most
// d, whatever the evaluator: a witness of the block decodes, block by block, to such a family, and
// such a family is decoded below k from some carrier-valued environment from s on, whose blocks
// substituted into σ decode to it again; the environment substituting the block agrees with σ
// below s and is carrier-valued, so the hypothesis matches the block's body with what Q says of a
// family its blocks decode to.
var ExistsRangeFamilyBridge = existsRangeFamilyBridgeThm{family.Add(registry.ProofEntry{
	Name: "ExistsRangeFamilyBridge",
	Key:  "prop_2927036e675af8b5",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀e:(B → (num → A) → bool). " +
			"∀s n d k:num. " +
			"∀σ:(num → A). " +
			"∀φ:fo_formula(B). " +
			"∀Q:((num → (num → num) → A) → bool).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"fo_env_ok(R.carrier, 𝕌, σ)",
			"∀τ:(num → A). ∀P:(num → (num → num) → A). " +
				"    fo_env_ok(R.carrier, 𝕌, τ) ∧ " +
				"    (∀v:num. v < s ⇒ τ(v) = σ(v)) ∧ " +
				"    (∀j:num. j < k ⇒ polynomial_bound(R, n, d, P(j))) ∧ " +
				"    (∀j:num. j < k ⇒ decode_polynomials(R, n, d, s, τ, j) = P(j)) ⇒ " +
				"    (Q(P) ⇔ fo_eval(R.carrier, e, τ, φ))",
		},
		Conclusion: "(∃P:(num → (num → num) → A). " +
			"    (∀j:num. j < k ⇒ polynomial_bound(R, n, d, P(j))) ∧ Q(P)) ⇔ " +
			"fo_eval(R.carrier, e, σ, fo_exists_range(s, k * coefficient_count(n, d), φ))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		e *Arrow2[B, Fun[Nat, A], Bool],
		s, n, d, k *Expr[Nat],
		σ *Arrow[Nat, A],
		φ *Expr[Formula[B]],
		Q *Arrow[Fun2[Nat, _Monomial, A], Bool],
		ring comm_ring.CommRingFact[on.R],
		env, body Fact,
	) {
		updated := substitutedFamily(a, R, s, n, d, k, σ, env, body)
		// The law is pinned at the chapter's carrier A and atoms B: unpinned, Simp adapts it to no
		// instance that rewrites this goal.
		a.Do(Simp(Fwd(first_order.ExistsRangeSemantics.Inst(TypeBinder.BindB[A](), TypeBinder.BindA[B]()))))
		a.Iff()
		a.Forward(
			"a family of degree at most d that Q holds of is decoded "+
				"below k from carrier values substituted into the block",
			func(b *Argument, holds Fact) {
				P, witness := b.UnpackAs[Fun2[Nat, _Monomial, A]](holds, "P")
				given := b.Conjuncts(
					witness,
					"P has degree at most d below k",
					"Q holds of P")
				c, values, decoded := representedFamily(b, R, s, n, d, k, σ, P, ring, given[0])
				b.Take(c)
				b.Show(
					"the values are carrier values, and the block's body holds with them substituted",
					By(values, given[0], given[1], decoded, updated.At(c, P)))
			})
		a.Backward(
			"the coefficients substituted into the block decode "+
				"to a family of degree at most d, which Q holds of",
			func(b *Argument, block Fact) {
				c, witness := b.UnpackAs[Fun[Nat, A]](block, "c")
				parts := b.Conjuncts(
					witness,
					"c is carrier-valued below the block's length",
					"the block's body holds with c substituted")
				decodedAt, bounded := decodedFamily(b, R, s, n, d, k, σ, c, ring, env, parts[0])
				b.Take(decodedAt)
				b.Show(
					"it has degree at most d below k, and Q holds of it since the body does at the block",
					By(parts[0], parts[1], bounded, updated.At(c, decodedAt)))
			})
	}),
})}
