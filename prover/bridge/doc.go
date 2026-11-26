// Package bridge proves the bridge the reifier plans, the equivalence of
// a proposition about a field record with its reified formula's
// evaluation. From a reification of a proposition Φ about a field
// record F it builds the theorem
//
//	O ⊢ Φ ⇔ fo_eval(F.carrier, e, ρ, φ)
//
// where φ is the reified formula, e the theory's atom (ring_formula_atom(F),
// or ordered_ring_formula_atom(F, lt) in the ordered theory), ρ the
// environment the formula is read at, and O the reification's
// obligations. The proof follows the plan node by node: each node's
// equivalence is an instance of the lemma the plan names for it, applied
// by modus ponens to the equivalences of its children. Nothing searches:
// the refuter is never called, and the only closer used is the
// arithmetic one, for the inequalities between block boundaries and an
// index's bound, a product a · t of a bounded index read through
// suc(a) · t ≤ m · t. The reifier's Arithmetic is the same closer
// (Arithmetic), so an index the reifier reads is one the builder places.
//
// A node is proved under a context: the environment σ it is read at,
// carrier-valued everywhere, and the HOL binders above it, each still a
// free variable, with its guard and a representation fact saying that σ
// holds it in its block (decode_tuple(R, n, s, σ) = x, the members of a
// family decoded from their blocks, σ(v) = a). The HOL side of a node is
// the proposition as written, the binders as variables; at a quantifier
// the child's environment agrees with the parent's below the new block,
// and each outer representation fact is carried across. A node the
// reifier accepted and the builder cannot prove is a defect of one of
// the two and panics, naming the node. A sentence is read at the zero
// environment (Build); a formula with parameters at a fresh ρ, each
// parameter a binder of the root (BuildWithParameters).
//
// Elementarity is the elementarity step's executor. The equivalence mode reads
// the goal as a closed sentence and carries its truth from a source: an
// entry stating the property at a concrete structure, whose closed-field
// fact is a fact of the call or the corpus entry stating it, or a family
// of models by prime. The fixed-parameter form .At transfers the source's
// property, an entry's or a family's, at a common degree bound of the
// parameters and instantiates it at them. The embedding mode reads an
// iff Φ(F, params) ⇔ Φ(G, i(params)), F and G both algebraically closed
// or both real closed, and proves it at an environment ρ representing
// the parameters, their images represented in λv. i(ρ(v))
// (EmbeddingBridge); ρ is then the parameters' encoding, block by block
// from λv. F.zero, for families and polynomials, each bounded by a fact
// or by the common degree bound of its membership in the polynomial
// algebra. A call outside what the executor reads is refused with the
// subterm or the obligation it stops at.
package bridge
