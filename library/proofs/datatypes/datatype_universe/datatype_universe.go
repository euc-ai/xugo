// datatype_universe.go — the universe is_recspace read into the type recspace(A):
// the three theorems the definition comes with, the bijection's two
// halves, and the constructors recspace_bottom / recspace_node that bring the universe's
// two constructors up into the type — with family_cons, the countable-family
// constructor, beside the recursion that consumes it. The README carries
// the chapter story.

package datatype_universe

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The universe, and the type it carves out
// ---------------------------------------------------------------------------

// UniverseRules — is_recspace contains the empty tree and is closed under
// the node constructor: the definition's rule set, registered verbatim
// as its Rules theorem. The node rule's premise is that EVERY child lies
// in is_recspace.
var UniverseRules = universeRulesThm{universe.Rules}

// UniverseInduct — a property holding at the empty tree and inherited
// by a node from its children holds throughout is_recspace: "smallest"
// read as an induction principle.
var UniverseInduct = universeInductThm{universe.Induct}

// UniverseCases — the two rules are exhaustive: a well-formed tree is
// the empty tree or a node whose every child is well-formed, and
// nothing else.
var UniverseCases = universeCasesThm{universe.Cases}

// UniverseInductStrong — the same induction with the step told that the
// children it climbs from are themselves well-formed. That is what
// reading the principle into the type recspace(A) needs: a child's
// round trip up and back is the identity only on a representative.
var UniverseInductStrong = universeInductStrongThm{universe.InductStrong}

// EncodedNodeNotBottom — a node is never the empty tree.
//
// Unfolded, both sides are inject_pair encodings, and inject_pair-equality is
// component-wise (InjectPairInjective): the first components are inject_num(suc(c))
// and inject_num(0), which inject_num's injectivity (InjectNumInjective) reads as
// suc(c) = 0 — false (peano.SucNotZero). The three laws are
// equivalences, so they run as a rewrite ladder on the equation rather
// than as a refutation, and the ladder ends at ⊥.
var EncodedNodeNotBottom = encodedNodeNotBottomThm{family.Add(registry.ProofEntry{
	Name: "EncodedNodeNotBottom",
	Key:  "prop_a2c877158f39a54e",
	Build: family.Theorem(
		"∀c:num. ∀i:A. ∀r:(num → num → A → bool). encoded_node(c, i, r) ≠ encoded_bottom",
		func(a *Argument, c, i, r Term) {
			a.Do(
				// ↦ inject_pair(inject_num(suc(c)), inject_pair(inject_atom(i), inject_family(r))) ≠ encoded_bottom
				Unfold(encodedNodeDef),
				// ↦ inject_pair(inject_num(suc(c)), inject_pair(inject_atom(i), inject_family(r))) ≠ inject_pair(inject_num(0), εz. ⊤)
				Unfold(encodedBottomDef),
				// The equation of encodings ↦ equal components ↦ suc(c) = 0 in
				// the first component ↦ ⊥; the second component's equation is
				// then moot.
				Simp(Fwd(InjectPairInjective), Fwd(InjectNumInjective), Fwd(peano.SucNotZero)),
				TrivialNormalized(), // ¬(⊥ ∧ …) is ⊤
			)
		}),
})}

// The type recspace(A) is the subset is_recspace carves out of the
// predicates on pairs, in bijection with it via mk_recspace / dest_recspace. A
// type definition may only be stamped against a NON-EMPTY subset; the
// empty tree is the inhabitant this one was stamped with (encodedBottomRep,
// below), and RecspaceDef (definitions.go) carries the two axioms of
// the definition — the retraction and the membership criterion — as
// its Retraction and Membership entries. The injectivity facts and the
// constructors' laws then read as transport rather than construction.

// encodedBottomRep — the empty tree is a representative.
//
// The first conjunct of UniverseRules, and the inhabitant the type
// definition of recspace(A) needs before it may be stamped at all.
var encodedBottomRep = encodedBottomRepThm{family.Add(registry.ProofEntry{
	Name:  "encodedBottomRep",
	Key:   "prop_62dac6081f5f5ba9",
	Build: family.Theorem("is_recspace⟨A:A⟩(encoded_bottom⟨A:A⟩)", Cite(UniverseRules)),
})}

// MkRecspaceInjective — distinct representatives never share an image under
// mk_recspace.
//
// The membership criterion is the whole argument: a representative
// survives the round trip dest_recspace ∘ mk_recspace, so equal images of two
// representatives force x = dest_recspace(mk_recspace x) = dest_recspace(mk_recspace y)
// = y.
var MkRecspaceInjective = mkRecspaceInjectiveThm{family.Add(registry.ProofEntry{
	Name: "MkRecspaceInjective",
	Key:  "prop_201b4dbd9a6a5335",
	Build: family.Theorem(
		Statement{
			Binders: "∀x y:(num → A → bool).",
			Hypotheses: []string{
				"is_recspace(x)",
				"is_recspace(y)",
				"mk_recspace(x) = mk_recspace(y)",
			},
			Conclusion: "x = y",
		},
		func(a *Argument, x, y Term, in Fact) {
			a.Show(
				"both survive the round trip, so equal images collapse x and y through dest_recspace",
				By(
					At(RecspaceDef.Membership, x), // is_recspace(x) ⇔ dest_recspace(mk_recspace(x)) = x
					At(RecspaceDef.Membership, y), // is_recspace(y) ⇔ dest_recspace(mk_recspace(y)) = y
					in))
		}),
})}

// DestRecspaceInjective — dest_recspace is injective: two trees are equal exactly
// when their representatives are.
//
// The retraction mk_recspace ∘ dest_recspace = id is the whole argument in the
// forward direction: applying mk_recspace to equal representatives recovers
// the trees. The backward direction is congruence.
var DestRecspaceInjective = destRecspaceInjectiveThm{family.Add(registry.ProofEntry{
	Name: "DestRecspaceInjective",
	Key:  "prop_ea23806f5f9ea9f7",
	Build: family.Theorem(
		"∀x y:recspace(A). dest_recspace(x) = dest_recspace(y) ⇔ x = y",
		func(a *Argument, x, y Term) {
			a.Iff()
			a.Forward(
				"equal representatives force equal trees: mk_recspace undoes dest_recspace on each",
				func(b *Argument, eq Fact) {
					b.Show(
						"apply mk_recspace to both sides; the retraction at x and y recovers x = y",
						By(
							At(RecspaceDef.Retraction, x), // mk_recspace(dest_recspace(x)) = x
							At(RecspaceDef.Retraction, y), // mk_recspace(dest_recspace(y)) = y
							eq))
				})
			a.Backward(
				"equal trees have equal representatives: congruence",
				func(b *Argument, eq Fact) {
					b.Show(
						"x = y forces dest_recspace(x) = dest_recspace(y)",
						By(Normalized, eq))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The constructors, read into the type
// ---------------------------------------------------------------------------

// nodeRep — the representative a recspace_node is brought up from lies in
// is_recspace: its children are the trees' representatives dest_recspace(r(n)),
// each of which is a representative (the membership criterion read
// through the retraction), and is_recspace is closed under nodes
// (UniverseRules). Both constructor laws below rest on this, so it is
// stated once.
var nodeRep = nodeRepThm{family.Add(registry.ProofEntry{
	Name: "nodeRep",
	Key:  "prop_31eb3092e7603fc3",
	Build: family.Theorem(
		"∀c:num. ∀i:A. ∀r:(num → recspace(A)). "+
			"    is_recspace(encoded_node(c, i, λn:num. dest_recspace(r(n))))",
		func(a *Argument, c, i, r Term) {
			childrenRep := a.Have(
				"each child's representative lies in is_recspace: membership at it is "+
					"the round-trip equation, which the retraction at the child collapses",
				"∀n:num. is_recspace(dest_recspace(r(n)))",
				Derive(func(b *Argument) {
					b.Fix() // n
					b.Show(
						"the two type-definition axioms at the child r(n)",
						By(
							Normalized,
							At(RecspaceDef.Membership, b.Term("dest_recspace(r(n))")),
							At(RecspaceDef.Retraction, b.Term("r(n)"))))
				}))
			// The rules' node clause is taken at the λ-family of representatives,
			// which the refuter β-reduces against childrenRep.
			a.Show(
				"the node lies in is_recspace, since its children's representatives do",
				By(childrenRep, UniverseRules))
		}),
})}

// NodeNotBottom — a node is never the empty tree.
//
// Both constructors are trees brought up from representatives: recspace_bottom is
// mk_recspace(encoded_bottom), and recspace_node(c, i, r) is mk_recspace of the node whose
// children are the trees' representatives dest_recspace(r(n)). encoded_bottom is a
// representative (encodedBottomRep); so is the node (nodeRep). mk_recspace is
// injective on representatives (MkRecspaceInjective), so equal trees would
// make the node encoded_bottom itself — which EncodedNodeNotBottom refuses.
var NodeNotBottom = nodeNotBottomThm{family.Add(registry.ProofEntry{
	Name: "NodeNotBottom",
	Key:  "prop_3a54808e7b20a37c",
	Build: family.Theorem(
		"∀c:num. ∀i:A. ∀r:(num → recspace(A)). recspace_node(c, i, r) ≠ recspace_bottom",
		func(a *Argument, c, i, r Term) {
			// ↦ mk_recspace(encoded_node(c, i, λn. dest_recspace(r(n)))) ≠ mk_recspace(encoded_bottom)
			a.Do(Unfold(recspaceNodeDef), Unfold(recspaceBottomDef))
			children := a.Term("λn:num. dest_recspace(r(n))") // the children's representatives
			// MkRecspaceInjective is cited bare: its conclusion is a function equality,
			// whose install form hoists the two extensionality points into the
			// ∀-prefix, so no stated-order tuple grounds it.
			a.Show(
				"equal trees would make the node encoded_bottom, both "+
					"being representatives — and a node is never the empty tree",
				By(
					At(nodeRep, c, i, r),
					encodedBottomRep,
					MkRecspaceInjective,
					At(EncodedNodeNotBottom, c, i, children)))
		}),
})}

// NodeInjective — recspace_node is injective in all three arguments: two nodes
// are equal exactly when their tags, labels and children are.
//
// Unfolded, the trees are mk_recspace of the nodes encoded_node(c, i, λn.
// dest_recspace(r(n))). Backwards is congruence. Forwards: both nodes are
// representatives (nodeRep), so MkRecspaceInjective makes them equal; a node
// is an inject_pair encoding of its tag, label and children (Unfold(encodedNodeDef)),
// and the four encodings are injective — InjectPairInjective twice,
// InjectNumInjective with peano.SucInjective for the tags, InjectAtomInjective for
// the labels, InjectFamilyInjective for the children — so the components agree,
// the children as the family of representatives λn. dest_recspace(r(n)).
// Pointwise, DestRecspaceInjective turns equal representatives back into
// equal children, and extensionality gives r1 = r2 (nodesDetermine).
var NodeInjective = nodeInjectiveThm{family.Add(registry.ProofEntry{
	Name:     "NodeInjective",
	Key:      "prop_ad376cb79a969d15",
	ServesAs: "recspace_node_injective",
	Build: family.Sections(
		"∀c₁ c₂:num. ∀i₁ i₂:A. ∀r₁ r₂:(num → recspace(A)). "+
			"    recspace_node(c₁, i₁, r₁) = recspace_node(c₂, i₂, r₂) ⇔ c₁ = c₂ ∧ i₁ = i₂ ∧ r₁ = r₂",
		func(ctx *Script, headline string) *GoalStackNode {
			// nodesDetermine — equal nodes have equal tags, labels and
			// children. The node is an inject_pair encoding, and the encodings'
			// injectivity laws run as a rewrite ladder on the equation
			// (they are equivalences over function-typed terms, which
			// refute badly as ground premises); what survives is the
			// components' equations, the children's as a λ-equation of
			// representatives.
			nodesDetermine := ctx.Lemma(
				Statement{
					Binders: "∀c₁ c₂:num. ∀i₁ i₂:A. ∀r₁ r₂:(num → recspace(A)).",
					Hypotheses: []string{
						"encoded_node(c₁, i₁, λn:num. dest_recspace(r₁(n))) = " +
							"encoded_node(c₂, i₂, λn:num. dest_recspace(r₂(n)))",
					},
					Conclusion: "c₁ = c₂ ∧ i₁ = i₂ ∧ r₁ = r₂",
				},
				Opening(Chain(
					// ↦ inject_pair(inject_num(suc(c1)), inject_pair(inject_atom(i1), inject_family(λn. dest_recspace(r1(n))))) = inject_pair(…c2…) ⇒ …
					Unfold(encodedNodeDef),
					// Every rule fires as its statement reads: an equation between
					// encodings, or between successors, becomes the equation of
					// what they encode.
					Simp(
						Fwd(InjectPairInjective),
						Fwd(InjectNumInjective),
						Fwd(peano.SucInjective),
						Fwd(InjectAtomInjective),
						Fwd(InjectFamilyInjective)),
					// ↦ c1 = c2 ∧ i1 = i2 ∧ (λn. dest_recspace(r1(n))) = (λn. dest_recspace(r2(n))) ⇒ c1 = c2 ∧ i1 = i2 ∧ r1 = r2
				),
					func(a *Argument, c1, c2, i1, i2, r1, r2 Term, components Fact) {
						a.Do(SplitConj(
							Case(
								"the tags and the labels agree: two of the three components",
								By(components)),
							Case(
								"the children agree: at each n the representatives agree, and dest_recspace is injective",
								Derive(func(b *Argument) {
									b.Do(Funext()) // r1 = r2 ↦ ∀n. r1(n) = r2(n)
									b.Fix("n")
									b.Show(
										"the children's λ-equation at n, read through the injectivity of dest_recspace at (r₁(n), r₂(n))",
										// Normalized: the λ-equation at n meets the injectivity instance by
										// simplification — no refute.
										By(Normalized, components, At(DestRecspaceInjective, b.Term("r₁(n)"), b.Term("r₂(n)"))))
								})),
						))
					}))

			return ctx.Theorem(headline, func(a *Argument, c1, c2, i1, i2, r1, r2 Term) {
				// ↦ mk_recspace(encoded_node(c1, i1, λn. dest_recspace(r1(n)))) = mk_recspace(encoded_node(c2, i2, λn. dest_recspace(r2(n)))) ⇔ …
				a.Do(Unfold(recspaceNodeDef))
				a.Iff()
				a.Forward(
					"equal trees have equal nodes, both being representatives, and equal nodes have equal components",
					func(b *Argument, treesEq Fact) {
						// MkRecspaceInjective is cited bare: its conclusion is a function
						// equality, whose install form hoists the two extensionality
						// points into the ∀-prefix, so no stated-order tuple grounds it.
						nodesEq := b.Have(
							"the nodes are equal: both are representatives, and mk_recspace is injective on representatives",
							"encoded_node(c₁, i₁, λn:num. dest_recspace(r₁(n))) = "+
								"encoded_node(c₂, i₂, λn:num. dest_recspace(r₂(n)))",
							By(treesEq, At(nodeRep, c1, i1, r1), At(nodeRep, c2, i2, r2), MkRecspaceInjective))
						// nodesDetermine is cited bare for the same reason (its
						// conclusion r1 = r2 hoists an extensionality point), and last:
						// its install discharges the antecedent against the resident
						// nodesEq and closes the goal there, with no refute.
						b.Show(
							"read the components off the equal nodes",
							By(nodesEq, nodesDetermine))
					})
				a.Backward(
					"equal components give equal trees: congruence",
					func(b *Argument, same Fact) {
						b.Show(
							"substitute c₁ = c₂, i₁ = i₂ and r₁ = r₂",
							By(Normalized, same))
					})
			})
		}),
})}

// Induction — a property holding at recspace_bottom and inherited by a node from
// its children holds of every tree.
//
// The universe's induction principle read into the type. Run
// UniverseInduct on
//
//	Q(z) :⇔ is_recspace(z) ∧ P(mk_recspace(z))
//
// — "z is a representative, and its tree satisfies P". The
// representative-ness carried inside Q is load-bearing, not bookkeeping
// (datatypes/list's Induction makes the same move one type down): the
// step must produce a TREE whose node is recspace_node over the children's
// trees, and only children that are representatives come back from
// their trees as themselves. At encoded_bottom, Q is encodedBottomRep together with
// P(recspace_bottom), recspace_bottom being mk_recspace(encoded_bottom). At a node whose children r(n)
// are representatives with P at their trees: the node is in is_recspace
// (UniverseRules), and recspace_node(c, i, λn. mk_recspace(r(n))) unfolds to
// mk_recspace(encoded_node(c, i, r)) because each child survives the round trip
// (the membership criterion), so the step hypothesis gives P there.
// Finally dest_recspace(x) is a representative (membership read with the
// retraction), so Q at it gives P(mk_recspace(dest_recspace(x))), which the
// retraction reads as
// P(x).
var Induction = inductionThm{family.Add(registry.ProofEntry{
	Name: "Induction",
	Key:  "prop_d6fe4b197ab724d5",
	Build: family.Theorem(
		Statement{
			Binders: "∀P:(recspace(A) → bool). ∀x:recspace(A).",
			Hypotheses: []string{
				"P(recspace_bottom)",
				"∀c:num. ∀i:A. ∀r:(num → recspace(A)). (∀n:num. P(r(n))) ⇒ P(recspace_node(c, i, r))",
			},
			Conclusion: "P(x)",
		},
		func(a *Argument, P, x Term, closure Fact) {
			// The property carried down to the representatives: P read at
			// the representative's tree. Spelled as its λ-literal because
			// it is an argument, not a statement.
			atTree := a.Term("λz:(num → A → bool). P(mk_recspace(z))")
			rep := a.Term("dest_recspace(x)") // x's representative

			step := a.Have(
				"the step hypothesis on its own, so it can be taken at a node",
				"∀c:num. ∀i:A. ∀r:(num → recspace(A)). (∀n:num. P(r(n))) ⇒ P(recspace_node(c, i, r))",
				By(closure))
			repX := a.Have(
				"x's representative lies in is_recspace: membership at it is "+
					"the round-trip equation, which the retraction at x collapses",
				"is_recspace(dest_recspace(x))",
				By(Normalized, At(RecspaceDef.Membership, rep), At(RecspaceDef.Retraction, x)))

			qAtRep := a.Have(
				"P holds at the tree of x's representative, by the "+
					"universe's strengthened induction read through mk_recspace",
				"P(mk_recspace(dest_recspace(x)))",
				ByInduction(At(UniverseInductStrong, atTree, rep), repX,
					Case(
						"at encoded_bottom: P(recspace_bottom) is P at mk_recspace(encoded_bottom)",
						Derive(func(b *Argument) {
							bottomEq := b.Have(
								"recspace_bottom is the empty tree brought up",
								"recspace_bottom⟨A:A⟩ = mk_recspace(encoded_bottom⟨A:A⟩)",
								Unfold(recspaceBottomDef))
							// encodedBottomRep is listed last: its install simplifies the goal against
							// the two resident facts and closes it there, with no refute.
							b.Show(
								"the base hypothesis read through bottomEq is P(mk_recspace(encoded_bottom))",
								By(Normalized, closure, bottomEq))
						})),
					Case(
						"at a node whose children are representatives with P at their "+
							"trees: its tree is recspace_node over the children's trees",
						Derive(func(b *Argument) {
							c := b.Fix()
							i := b.Fix()
							b.Fix()                                      // r — the children, spelled in the claims below
							ih := b.Assume()                             // ∀n. is_recspace(r(n)) ∧ P(mk_recspace(r(n)))
							trees := b.Term("λn:num. mk_recspace(r(n))") // the children as trees
							node := b.Have(
								"recspace_node over the children's trees is the node brought up",
								"recspace_node(c, i, λn:num. mk_recspace(r(n))) = mk_recspace(encoded_node(c, i, r))",
								Derive(func(d *Argument) {
									// ↦ mk_recspace(encoded_node(c, i, λn. dest_recspace(mk_recspace(r(n))))) = mk_recspace(encoded_node(c, i, r))
									d.Do(Unfold(recspaceNodeDef))
									childrenBack := d.Have(
										"each child, brought up to a tree and taken down again, is itself",
										"(λn:num. dest_recspace(mk_recspace(r(n)))) = r",
										By(RecspaceDef.Membership, ih))
									d.Show(
										"with the children's round trip rewritten away, the two sides are identical",
										By(Normalized, childrenBack))
								}))
							b.Show(
								"the step hypothesis at the node's tag, label and children's "+
									"trees, with P at each child's tree from the induction hypothesis",
								// Normalized: node rewrites the goal to P(recspace_node(c, i, trees)), which
								// the ground step instance discharges against ih by simplification.
								By(Normalized, step.At(c, i, trees), ih, node))
						}))))

			a.Show(
				"the retraction at x reads P(mk_recspace(dest_recspace(x))) as P(x)",
				By(Normalized, qAtRep, At(RecspaceDef.Retraction, x)))
		}),
})}

// FamilyCons — the countable-family constructor, defined by its two
// recursion clauses: family_cons(a, f) is the family whose first element is
// a and whose tail is f, so it reads a at 0 and f(n) at suc(n). The
// definition is compiled against peano.Recursion at the family's type;
// the datatype kit reads it under the library name family_cons.
var FamilyCons = familyConsThm{family.Define(registry.DefEntry{
	Name:     "FamilyCons",
	Key:      "prop_9caaa975a2d09dd9",
	Const:    "family_cons",
	ServesAs: "family_cons_definition",
	Type:     "A → (num → A) → num → A",
	Equations: []string{
		"∀a:A. ∀f:(num → A). family_cons(a, f, 0) = a",
		"∀a:A. ∀f:(num → A). ∀n:num. family_cons(a, f, suc(n)) = f(n)",
	},
})}
