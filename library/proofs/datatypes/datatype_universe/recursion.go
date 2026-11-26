// recursion.go — the universe's recursion theorem recspace_recursion. The
// README carries the chapter story.
//
// For any Fn there is a function f on trees with
//
//	f(recspace_node(c, i, r)) = Fn(c, i, r, λn. f(r(n)))
//
// — a function on trees is determined by how it combines a node's tag,
// label, children and the values it already has at those children. This
// is the theorem every datatype's recursion schema is an
// instance of.
//
// The construction is the classical graph argument. Z is the least
// relation closed under the two rules "(recspace_bottom, εy.⊤) is in Z" and "if
// a node's children all have values in Z then the node has Fn's value
// in Z" — built as the intersection of every such relation (`graph`).
// Being least, Z inverts: a Z-pair is either the empty tree at εy.⊤ or
// a node at Fn of some children's values (`inversion`), and since a
// node is never the empty tree and recspace_node is injective, a node's value
// is Fn of the children's (`invConstr`). Induction then makes Z a
// function — every tree has exactly one Z-value (`uniqueValue`) — and
// f := λx. εv. Z(x, v) reads the recursion equation off inversion.

package datatype_universe

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var Recursion = recursionThm{family.Add(registry.ProofEntry{
	Name:     "Recursion",
	Key:      "prop_28212322cc043a94",
	ServesAs: "recspace_recursion",
	Build: family.Sections(
		Statement{
			Binders: "∀Fn:(num → A → (num → recspace(A)) → (num → B) → B).",
			Conclusion: "∃f:(recspace(A) → B). ∀c:num. ∀i:A. ∀r:(num → recspace(A)). " +
				"    f(recspace_node(c, i, r)) = Fn(c, i, r, λn:num. f(r(n)))",
			Abbrev: Abbrev{
				{Name: "bottomRule", Text: "Z(recspace_bottom, (εy:B. ⊤))"},
				// "Zp is closed", for the relation Zp that strengthens Z with
				// the inversion alternatives: β-reduced, so that it matches
				// what leastness's closed(Zp) reduces to. The alternatives'
				// existentials are named d, j, s, z (not c, i, r, y), so that
				// a term built from the closure's own c, i, r, y is not
				// captured.
				{Name: "closedZp", Text: "(Z(recspace_bottom, (εy:B. ⊤)) ∧ " +
					"    ((recspace_bottom = recspace_bottom ∧ (εy:B. ⊤) = (εy:B. ⊤)) ∨ " +
					"        (∃d:num. ∃j:A. ∃s:(num → recspace(A)). ∃z:(num → B). " +
					"            recspace_bottom = recspace_node(d, j, s) ∧ " +
					"            (∀n:num. Z(s(n), z(n))) ∧ " +
					"            (εy:B. ⊤) = Fn(d, j, s, z)))) ∧ " +
					"∀c:num. ∀i:A. ∀r:(num → recspace(A)). ∀y:(num → B). " +
					"    (∀n:num. " +
					"        (Z(r(n), y(n)) ∧ " +
					"            ((r(n) = recspace_bottom ∧ y(n) = (εy:B. ⊤)) ∨ " +
					"                (∃d:num. ∃j:A. ∃s:(num → recspace(A)). ∃z:(num → B). " +
					"                    r(n) = recspace_node(d, j, s) ∧ " +
					"                    (∀n:num. Z(s(n), z(n))) ∧ " +
					"                    y(n) = Fn(d, j, s, z))))) ⇒ " +
					"    (Z(recspace_node(c, i, r), Fn(c, i, r, y)) ∧ " +
					"        ((recspace_node(c, i, r) = recspace_bottom ∧ Fn(c, i, r, y) = (εy:B. ⊤)) ∨ " +
					"            (∃d:num. ∃j:A. ∃s:(num → recspace(A)). ∃z:(num → B). " +
					"                recspace_node(c, i, r) = recspace_node(d, j, s) ∧ " +
					"                (∀n:num. Z(s(n), z(n))) ∧ " +
					"                Fn(c, i, r, y) = Fn(d, j, s, z))))"},
			},
		},
		func(ctx *Script, headline string) *GoalStackNode {

			// -----------------------------------------------------------
			// graph — the least relation closed under the two rules
			// -----------------------------------------------------------
			//
			// Built impredicatively as the intersection of every closed
			// relation: (x, v) is in Z exactly when every closed R holds
			// there. That relation is closed (a node's children in every
			// closed R put the node in every closed R) and, being an
			// intersection of closed relations, sits inside each — which
			// is minimality.
			graph := ctx.Lemma(
				"∀Fn:(num → A → (num → recspace(A)) → (num → B) → B). ∃Z:(recspace(A) → B → bool). "+
					"    Z(recspace_bottom, εy:B. ⊤) ∧ "+
					"    (∀c:num. ∀i:A. ∀r:(num → recspace(A)). ∀y:(num → B). "+
					"        (∀n:num. Z(r(n), y(n))) ⇒ Z(recspace_node(c, i, r), Fn(c, i, r, y))) ∧ "+
					"    (∀R:(recspace(A) → B → bool). "+
					"        R(recspace_bottom, εy:B. ⊤) ∧ "+
					"        (∀c:num. ∀i:A. ∀r:(num → recspace(A)). ∀y:(num → B). "+
					"            (∀n:num. R(r(n), y(n))) ⇒ R(recspace_node(c, i, r), Fn(c, i, r, y))) ⇒ "+
					"        ∀x:recspace(A). ∀v:B. Z(x, v) ⇒ R(x, v))",
				func(a *Argument, Fn Term) {
					a.Take(a.Term(
						"λx:recspace(A). λv:B. ∀R:(recspace(A) → B → bool). " +
							"    R(recspace_bottom, εy:B. ⊤) ∧ " +
							"    (∀c:num. ∀i:A. ∀r:(num → recspace(A)). ∀y:(num → B). " +
							"        (∀n:num. R(r(n), y(n))) ⇒ R(recspace_node(c, i, r), Fn(c, i, r, y))) ⇒ " +
							"    R(x, v)"))
					a.Do(SplitConjAll(
						Case(
							"the empty tree's value lies in every closed relation, so in the intersection",
							Derive(func(b *Argument) {
								b.Fix("R")
								closed := b.Assume() // R closed
								b.Show(
									"closure's base clause places it in R",
									By(closed))
							})),
						Case(
							"a node lies in every closed relation once its children's values do",
							Derive(func(b *Argument) {
								b.Fix()                       // c
								b.Fix()                       // i
								b.Fix()                       // r
								b.Fix()                       // y — the node's tag, label, children and their values
								childrenInEvery := b.Assume() // ∀n. ∀R. R closed ⇒ R(r(n), y(n))
								R := b.Fix("R")
								closed := b.Assume() // R closed
								children := b.Have(
									"each child's value lies in R",
									"∀n:num. R(r(n), y(n))",
									Derive(func(d *Argument) {
										n := d.Fix()
										d.Show(
											"child n lies in every closed relation, taken at R",
											By(childrenInEvery.At(n, R), closed))
									}))
								b.Show(
									"closure's node clause then places the node in R",
									By(children, closed))
							})),
						Case(
							"the intersection sits inside each closed relation — that is what membership in it says",
							Derive(func(b *Argument) {
								R := b.Fix("R")
								closed := b.Assume()  // R closed
								b.Fix()               // x
								b.Fix()               // v
								inEvery := b.Assume() // (x, v) in every closed relation
								b.Show(
									"the intersection at (x, v) is exactly R's obligation, read at R",
									By(inEvery.At(R), closed))
							})),
					))
				})

			// -----------------------------------------------------------
			// inversion — a Z-pair is one of the two rule shapes
			// -----------------------------------------------------------
			//
			// Minimality read at the relation Zp strengthening Z with the
			// alternatives it is meant to have: Zp is closed (the empty
			// tree takes the first alternative, a node the second, each
			// witnessed by its own components), so Z ⊆ Zp, and a Z-pair
			// then satisfies the alternatives.
			inversion := ctx.Lemma(
				"∀Fn:(num → A → (num → recspace(A)) → (num → B) → B). ∀Z:(recspace(A) → B → bool). "+
					"    «bottomRule» ⇒ "+
					"    ((∀c:num. ∀i:A. ∀r:(num → recspace(A)). ∀y:(num → B). "+
					"            (∀n:num. Z(r(n), y(n))) ⇒ Z(recspace_node(c, i, r), Fn(c, i, r, y))) ⇒ "+
					"        ((∀R:(recspace(A) → B → bool). "+
					"                R(recspace_bottom, εy:B. ⊤) ∧ "+
					"                (∀c:num. ∀i:A. ∀r:(num → recspace(A)). ∀y:(num → B). "+
					"                    (∀n:num. R(r(n), y(n))) ⇒ R(recspace_node(c, i, r), Fn(c, i, r, y))) ⇒ "+
					"                ∀x:recspace(A). ∀v:B. Z(x, v) ⇒ R(x, v)) ⇒ "+
					"            ∀x:recspace(A). ∀v:B. "+
					"                Z(x, v) ⇒ "+
					"                Z(x, v) ∧ "+
					"                (x = recspace_bottom ∧ v = (εy:B. ⊤) ∨ "+
					"                    (∃d:num. ∃j:A. ∃s:(num → recspace(A)). ∃z:(num → B). "+
					"                        x = recspace_node(d, j, s) ∧ "+
					"                        (∀n:num. Z(s(n), z(n))) ∧ "+
					"                        v = Fn(d, j, s, z)))))",
				func(a *Argument, Fn, Z Term, bottomrule, steprule, leastness Fact) {
					// Zp strengthens Z with the alternatives it is meant to have.
					zp := a.Term(
						"λx:recspace(A). λv:B. " +
							"    Z(x, v) ∧ " +
							"    (x = recspace_bottom ∧ v = (εy:B. ⊤) ∨ " +
							"        (∃d:num. ∃j:A. ∃s:(num → recspace(A)). ∃z:(num → B). " +
							"            x = recspace_node(d, j, s) ∧ (∀n:num. Z(s(n), z(n))) ∧ v = Fn(d, j, s, z)))")
					closedZp := a.Have(
						"the strengthened relation is closed: the empty tree takes the first "+
							"alternative and a node the second, witnessed by its own components",
						"«closedZp»",
						Derive(func(b *Argument) {
							b.Do(SplitConj(
								Case(
									"the empty tree's value is in Z (base rule) and takes the first alternative",
									By(bottomrule)),
								Case(
									"a node's value is in Z (step rule) and takes the second alternative, "+
										"witnessed by its own tag, label, children and their values",
									By(steprule)),
							))
						}))
					// Minimality read at Zp: leastness grounded at the
					// strengthened relation on the spine, its obligation
					// discharged by the closedness just shown, β-reduces to
					// the strengthened membership, which is the goal, so the
					// grounding is a step and the close an assumption.
					a.Show(
						"minimality carries every Z-pair into the strengthened relation",
						GroupPremises(closedZp, leastness.At(zp)),
						Assumption())
				})

			// -----------------------------------------------------------
			// invConstr — a node's value is Fn of its children's
			// -----------------------------------------------------------
			//
			// The node alternative of `inversion`: the first alternative
			// would make the node the empty tree (NodeNotBottom refuses
			// it) and the second's node equation forces the components to
			// agree (NodeInjective), leaving Fn of the children's
			// values.
			invConstr := ctx.Lemma(
				"∀Fn:(num → A → (num → recspace(A)) → (num → B) → B). ∀Z:(recspace(A) → B → bool). "+
					"    «bottomRule» ⇒ "+
					"    ((∀c:num. ∀i:A. ∀r:(num → recspace(A)). ∀y:(num → B). "+
					"            (∀n:num. Z(r(n), y(n))) ⇒ Z(recspace_node(c, i, r), Fn(c, i, r, y))) ⇒ "+
					"        ((∀R:(recspace(A) → B → bool). "+
					"                R(recspace_bottom, εy:B. ⊤) ∧ "+
					"                (∀c:num. ∀i:A. ∀r:(num → recspace(A)). ∀y:(num → B). "+
					"                    (∀n:num. R(r(n), y(n))) ⇒ R(recspace_node(c, i, r), Fn(c, i, r, y))) ⇒ "+
					"                ∀x:recspace(A). ∀v:B. Z(x, v) ⇒ R(x, v)) ⇒ "+
					"            ∀c:num. ∀i:A. ∀r:(num → recspace(A)). ∀v:B. "+
					"                Z(recspace_node(c, i, r), v) ⇒ "+
					"                ∃y:(num → B). (∀n:num. Z(r(n), y(n))) ∧ v = Fn(c, i, r, y)))",
				func(a *Argument, Fn, Z Term, bottomrule, steprule, leastness Fact) {
					inv := a.Have(
						"the disjunctive inversion at this graph",
						Statement{
							Binders: "∀x:recspace(A). ∀v:B.",
							Hypotheses: []string{
								"Z(x, v)",
							},
							Conclusion: "Z(x, v) ∧ " +
								"(x = recspace_bottom ∧ v = (εy:B. ⊤) ∨ " +
								"    (∃d:num. ∃j:A. ∃s:(num → recspace(A)). ∃z:(num → B). " +
								"        x = recspace_node(d, j, s) ∧ (∀n:num. Z(s(n), z(n))) ∧ v = Fn(d, j, s, z)))",
						},
						By(At(inversion, Fn, Z), bottomrule, steprule, leastness))
					a.Fix()           // c
					a.Fix()           // i
					a.Fix()           // r
					a.Fix()           // v
					zcv := a.Assume() // Z(recspace_node(c, i, r), v)
					// The empty-tree alternative would make the node the empty
					// tree (NodeNotBottom refuses it), so inversion leaves the
					// node alternative — a family (d, j, s, z) with the node
					// equal to recspace_node(d, j, s).
					nodeAlt := a.Have(
						"the node takes inversion's node alternative",
						"∃d:num. ∃j:A. ∃s:(num → recspace(A)). ∃z:(num → B). "+
							"    recspace_node(c, i, r) = recspace_node(d, j, s) ∧ "+
							"    (∀n:num. Z(s(n), z(n))) ∧ "+
							"    v = Fn(d, j, s, z)",
						By(inv, zcv, NodeNotBottom))
					// Any such family collapses to one for c, i, r: the node
					// equation forces d = c, j = i, s = r (NodeInjective), so
					// z is the witnessing family. Stated ∀-first so the closing
					// refute runs on the ground instance.
					collapse := a.Have(
						"any node-witnessing family is a witness for this node",
						Statement{
							Binders: "∀d:num. ∀j:A. ∀s:(num → recspace(A)). ∀z:(num → B).",
							Hypotheses: []string{
								"recspace_node(c, i, r) = recspace_node(d, j, s)",
								"∀n:num. Z(s(n), z(n))",
								"v = Fn(d, j, s, z)",
							},
							Conclusion: "∃y:(num → B). (∀n:num. Z(r(n), y(n))) ∧ v = Fn(c, i, r, y)",
						},
						Derive(func(b *Argument) {
							b.Fix() // d
							b.Fix() // j
							b.Fix() // s
							z := b.Fix()
							family := b.Assume() // the node equation with its family
							nodeEq := b.Have(
								"the node equation on its own",
								"recspace_node(c, i, r) = recspace_node(d, j, s)",
								By(family))
							// NodeInjective gives the tags and labels outright and
							// the children pointwise; funext raises the last to a
							// function equality so Fn's argument can be rewritten.
							tagLabel := b.Have(
								"the tag and label agree",
								"c = d ∧ i = j",
								By(nodeEq, NodeInjective))
							sameChildren := b.Have(
								"the children agree as functions",
								"s = r",
								Derive(func(d2 *Argument) {
									d2.Do(Funext())
									d2.Fix("n")
									d2.Show(
										"pointwise, by the node equation (NodeInjective)",
										By(nodeEq, NodeInjective))
								}))
							b.Take(z)
							b.Do(SplitConj(
								Case(
									"z's values are the children's, the children being equal as functions",
									By(family, sameChildren)),
								Case(
									"and the node's value is Fn of them",
									Derive(func(e *Argument) {
										// The value equation is r-free (Fn of s), so it
										// survives rewriting r ↦ s in the goal — a function
										// equality the refuter keeps opaque, unlike the scalar
										// tags and labels it closes with.
										vEq := e.Have(
											"the value is Fn of the family (d, j, s, z)",
											"v = Fn(d, j, s, z)",
											By(family))
										e.Do(sameChildren.RwRev())
										e.Show(
											"the equal tag and label close it",
											By(vEq, tagLabel))
									})),
							))
						}))
					a.Show(
						"so the node's value is Fn of that family",
						By(nodeAlt, collapse))
				})

			// -----------------------------------------------------------
			// uniqueValue — every tree has exactly one Z-value
			// -----------------------------------------------------------
			//
			// Induction on the tree. At the empty tree εy.⊤ is a value
			// (base rule) and the only one (inversion: the node
			// alternative is impossible there). At a node whose children
			// each have a unique value, choose them into a family g; then
			// Fn(c, i, r, g) is a value (step rule) and the only one —
			// invConstr decomposes any value as Fn of a family that, being
			// Z-values at the children, must be g pointwise.
			uniqueValue := ctx.Lemma(
				"∀Fn:(num → A → (num → recspace(A)) → (num → B) → B). ∀Z:(recspace(A) → B → bool). "+
					"    «bottomRule» ⇒ "+
					"    ((∀c:num. ∀i:A. ∀r:(num → recspace(A)). ∀y:(num → B). "+
					"            (∀n:num. Z(r(n), y(n))) ⇒ Z(recspace_node(c, i, r), Fn(c, i, r, y))) ⇒ "+
					"        ((∀R:(recspace(A) → B → bool). "+
					"                R(recspace_bottom, εy:B. ⊤) ∧ "+
					"                (∀c:num. ∀i:A. ∀r:(num → recspace(A)). ∀y:(num → B). "+
					"                    (∀n:num. R(r(n), y(n))) ⇒ R(recspace_node(c, i, r), Fn(c, i, r, y))) ⇒ "+
					"                ∀x:recspace(A). ∀v:B. Z(x, v) ⇒ R(x, v)) ⇒ "+
					"            ∀x:recspace(A). ∃v:B. Z(x, v) ∧ (∀w:B. Z(x, w) ⇒ w = v)))",
				func(a *Argument, Fn, Z Term, bottomrule, steprule, leastness Fact) {
					inv := a.Have(
						"the disjunctive inversion at this graph",
						Statement{
							Binders: "∀x:recspace(A). ∀v:B.",
							Hypotheses: []string{
								"Z(x, v)",
							},
							Conclusion: "Z(x, v) ∧ " +
								"(x = recspace_bottom ∧ v = (εy:B. ⊤) ∨ " +
								"    (∃d:num. ∃j:A. ∃s:(num → recspace(A)). ∃z:(num → B). " +
								"        x = recspace_node(d, j, s) ∧ (∀n:num. Z(s(n), z(n))) ∧ v = Fn(d, j, s, z)))",
						},
						By(At(inversion, Fn, Z), bottomrule, steprule, leastness))
					invBottom := a.Have(
						"the empty tree's only value is εy.⊤",
						"∀v:B. Z(recspace_bottom, v) ⇒ v = εy:B. ⊤",
						Derive(func(b *Argument) {
							b.Fix()           // v
							zbv := b.Assume() // Z(recspace_bottom, v)
							// inv is cited bare: zbv anchors the instance at recspace_bottom,
							// where spelling recspace_bottom as a witness would freeze its own
							// type variable and build the wrong instance.
							b.Show(
								"inversion's node alternative is impossible at the empty tree (NodeNotBottom)",
								By(inv, zbv, NodeNotBottom))
						}))
					invC := a.Have(
						"a node's value is Fn of some family of children's values",
						Statement{
							Binders: "∀c:num. ∀i:A. ∀r:(num → recspace(A)). ∀v:B.",
							Hypotheses: []string{
								"Z(recspace_node(c, i, r), v)",
							},
							Conclusion: "∃y:(num → B). (∀n:num. Z(r(n), y(n))) ∧ v = Fn(c, i, r, y)",
						},
						By(At(invConstr, Fn, Z), bottomrule, steprule, leastness))

					x := a.Fix()
					pred := a.Term("λx:recspace(A). ∃v:B. Z(x, v) ∧ (∀w:B. Z(x, w) ⇒ w = v)")
					a.Show(
						"induction on the tree carries the property everywhere",
						ByInduction(At(Induction, x, pred),
							Case(
								"at the empty tree: εy.⊤ is a value and, by inversion, the only one",
								Derive(func(b *Argument) {
									b.Take(a.Term("εy:B. ⊤"))
									b.Show(
										"εy.⊤ is a value (base rule) and unique (invBottom)",
										By(bottomrule, invBottom))
								})),
							Case(
								"at a node: the children's values, chosen by ε, make Fn's value the node's",
								Derive(func(b *Argument) {
									c := b.Fix()
									i := b.Fix()
									r := b.Fix()
									ih := b.Assume() // ∀n. the child r(n) has a unique value
									// g(n) := εw. Z(r(n), w) — the child chooser. It is a
									// value at every child (ε realizes the inhabited set)
									// and the only one there (child uniqueness).
									childValue := b.Have(
										"each child's ε-chosen value is a value there",
										"∀n:num. Z(r(n), εw:B. Z(r(n), w))",
										Derive(func(d *Argument) {
											d.Fix() // n
											d.Show(
												"ε realizes the child's inhabited value set",
												By(Normalized, At(ih, d.Term("n"))))
										}))
									childUnique := b.Have(
										"the ε is the child's only value",
										"∀n:num. ∀u:B. Z(r(n), u) ⇒ u = εw:B. Z(r(n), w)",
										Derive(func(d *Argument) {
											d.Fix()          // n
											d.Fix()          // u
											zu := d.Assume() // Z(r(n), u)
											d.Show(
												"both u and the ε are values at r(n), which has one",
												By(At(ih, d.Term("n")), zu, At(childValue, d.Term("n"))))
										}))
									g := b.Term("λn:num. εw:B. Z(r(n), w)")
									b.Take(b.Term("Fn(c, i, r, λn:num. εw:B. Z(r(n), w))"))
									b.Do(SplitConj(
										Case(
											"Fn of the chosen children's values is a value: the step rule",
											By(At(steprule, c, i, r, g), childValue)),
										Case(
											"and the only one: invConstr decomposes any value, whose family is the chooser pointwise",
											Derive(func(d *Argument) {
												w := d.Fix()
												zcw := d.Assume() // Z(recspace_node(c, i, r), w)
												// Any family that decomposes w is the chooser
												// pointwise, so w is Fn of the chooser. Stated
												// ∀-first so invConstr's ∃y meets it as a
												// modus ponens, not a Skolemization.
												collapse := d.Have(
													"any decomposing family is the chooser, so w is the chosen value",
													Statement{
														Binders: "∀y:(num → B).",
														Hypotheses: []string{
															"(∀n:num. Z(r(n), y(n))) ∧ w = Fn(c, i, r, y)",
														},
														Conclusion: "w = Fn(c, i, r, λn:num. εw:B. Z(r(n), w))",
													},
													Derive(func(e *Argument) {
														e.Fix()              // y
														decomp := e.Assume() // (∀n. Z(r(n), y(n))) ∧ w = Fn(c, i, r, y)
														wEq := e.Have(
															"w is Fn of that family",
															"w = Fn(c, i, r, y)",
															By(decomp))
														sameChooser := e.Have(
															"the family is the chooser pointwise, both being the child's value",
															"y = (λn:num. εw:B. Z(r(n), w))",
															Derive(func(f *Argument) {
																f.Do(Funext())
																f.Fix() // n
																f.Show(
																	"at n both are the child's ε value",
																	By(At(childUnique, f.Term("n")), decomp))
															}))
														e.Do(sameChooser.RwRev()) // chooser ↦ y in the goal
														e.Show(
															"so w is Fn of the chooser",
															By(wEq))
													}))
												d.Show(
													"so w is the chosen value",
													By(At(invC, c, i, r, w), zcw, collapse))
											})),
									))
								})),
						))
				})

			// -----------------------------------------------------------
			// the recursion function
			// -----------------------------------------------------------
			//
			// f := λx. εv. Z(x, v). Since Z is total and single-valued
			// (uniqueValue), f(x) is Z's value at x. invConstr decomposes
			// f(recspace_node(c, i, r)) as Fn of a family that, being Z-values at
			// the children, is λn. f(r(n)) — the recursion equation.
			return ctx.Theorem(headline, func(a *Argument, Fn Term) {
				Z, spec := a.Unpack(At(graph, Fn))
				rules := a.Conjuncts(
					spec,
					"Z contains the empty tree's value",
					"Z carries a node's value from its children's",
					"Z is the least closed relation")

				uv := a.Have(
					"every tree has a unique Z-value",
					"∀x:recspace(A). ∃v:B. Z(x, v) ∧ (∀w:B. Z(x, w) ⇒ w = v)",
					By(At(uniqueValue, Fn, Z), rules[0], rules[1], rules[2]))
				invC := a.Have(
					"a node's value is Fn of some family of children's values",
					Statement{
						Binders: "∀c:num. ∀i:A. ∀r:(num → recspace(A)). ∀v:B.",
						Hypotheses: []string{
							"Z(recspace_node(c, i, r), v)",
						},
						Conclusion: "∃y:(num → B). (∀n:num. Z(r(n), y(n))) ∧ v = Fn(c, i, r, y)",
					},
					By(At(invConstr, Fn, Z), rules[0], rules[1], rules[2]))

				// f(x) = εv. Z(x, v) is a Z-value everywhere (totality),
				// and Z is single-valued.
				total := a.Have(
					"f(x) := εv. Z(x, v) is a Z-value at every tree",
					"∀x:recspace(A). Z(x, εv:B. Z(x, v))",
					Derive(func(b *Argument) {
						b.Fix()
						b.Show(
							"the value uniqueValue provides realizes the choice",
							By(uv))
					}))
				functional := a.Have(
					"Z has at most one value at each tree",
					"∀x:recspace(A). ∀u:B. ∀w:B. Z(x, u) ⇒ Z(x, w) ⇒ u = w",
					Derive(func(b *Argument) {
						b.Fix()
						b.Show(
							"two Z-values at a tree both equal the unique one",
							By(uv))
					}))

				a.Take(a.Term("λx:recspace(A). εv:B. Z(x, v)"))
				c := a.Fix()
				i := a.Fix()
				r := a.Fix()
				node := a.Term("recspace_node(c, i, r)")
				_, ySpec := a.Obtain(
					"decompose f(recspace_node(c, i, r)) as Fn of a family of children's values",
					"∃y:(num → B). (∀n:num. Z(r(n), y(n))) ∧ (εv:B. Z(recspace_node(c, i, r), v)) = Fn(c, i, r, y)",
					By(At(invC, c, i, r, a.Term("εv:B. Z(recspace_node(c, i, r), v)")), total.At(node)),
					Named("y"))
				yEq := a.Have(
					"that family is λn. f(r(n)): both are Z-values at each child",
					"y = (λn:num. εv:B. Z(r(n), v))",
					Derive(func(b *Argument) {
						b.Do(Funext())
						b.Fix() // n
						b.Show(
							"at n the decomposed value and f(r(n)) are Z-values at r(n), so equal",
							By(
								At(functional, b.Term("r(n)"), b.Term("y(n)"), b.Term("εv:B. Z(r(n), v)")),
								ySpec,
								total.At(b.Term("r(n)"))))
					}))
				a.Show(
					"so f(recspace_node(c, i, r)) = Fn(c, i, r, λn. f(r(n)))",
					By(ySpec, yEq))
			})
		}),
})}
