// cone_horns.go — horn filling over a fixed prefix: the partial cone
// horn fill, and the two left fibrations of the cones on a fixed
// simplex k — the restriction of its cone to its boundary cone, and the
// boundary cone's projection to X.

package quasi_category

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_fibration"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// PartialConeHornFill — fill a tail horn over a specified tail simplex
// while retaining the first t prefix faces. The face set names precisely
// the prescribed codimension-one faces of the ambient (p+q+1)-simplex.
// By induction on p. With one prefix vertex the supplied tail becomes
// face 0 and one inner horn fills. The step to p + 1 builds the missing
// prefix facets r = t, …, p + 1 one at a time: facet r is the case p for
// its first r faces and its tail faces, which the face identities read
// off the facets already present. One inner horn fill then completes
// the simplex.
var PartialConeHornFill = partialConeHornFillThm{family.Add(registry.ProofEntry{
	Name: "PartialConeHornFill",
	Key:  "prop_47ebd448d0697e6c",
	Build: QuasiCategory.Law(Statement{
		Binders: "∀p q i t:num. ∀y:(num → A). ∀b:A.",
		Hypotheses: []string{
			"i < q",
			"t ≤ p + 1",
			"b ∈ X.simplices(q)",
			"face_family(p + q, {j:num | j < t ∨ (p + 1 ≤ j ∧ j ≤ p + q + 1 ∧ j ≠ p + 1 + i)}, y)",
			"∀j:num. j < t ⇒ face_iterate_bottom(p + q, p, y(j)) = b",
			"∀a:num. a ≤ q ∧ a ≠ i ⇒ face_iterate_bottom(p + q, p + 1, y(p + 1 + a)) = X.d(q, a, b)",
		},
		Conclusion: "∃x:A. " +
			"    x ∈ X.simplices(p + q + 1) ∧ " +
			"    face_iterate_bottom(p + q + 1, p + 1, x) = b ∧ " +
			"    faces_filler(p + q, {j:num | j < t ∨ (p + 1 ≤ j ∧ j ≤ p + q + 1 ∧ j ≠ p + 1 + i)}, y, x)",
	},
		func(a *Argument, quasi Fact) {
			a.Induct("p")
			a.Base(
				"with one prefix vertex, insert the supplied tail as face zero",
				func(base *Argument) {
					base.Do(Simp(Fwd(nat_arith.Add), Fwd(simplicial_set.FaceIterateBottomDef)))
					q := base.FixAs[Nat]()
					base.FixAs[Nat]()
					base.FixAs[Nat]()
					base.FixAs[Fun[Nat, A]]()
					base.FixAs[A]()
					domain := base.Let("S", base.TermAs[Set[Nat]]("{j:num | j < t ∨ (1 ≤ j ∧ j ≤ q + 1 ∧ j ≠ 1 + i)}"))
					given := base.Conjuncts(
						base.Assume(),
						"the missing tail face is not last",
						"at most the one prefix face is prescribed",
						"the supplied tail is a simplex",
						"the prescribed faces form a face family",
						"a prescribed prefix face equals the supplied tail",
						"the tail faces have the prescribed faces of b")
					missing, width, tail, prefix := given[0], given[1], given[2], given[4]
					prescribed := base.Conjuncts(
						base.Unfolded(given[3], simplicial_set.FaceFamilyDef),
						"the prescribed faces are simplices",
						"the prescribed faces are compatible")
					members, compatible :=
						prescribed[0], base.Unfolded(prescribed[1], simplicial_set.FacesCompatibleDef)
					z, inserted := base.LetAs[Fun[Nat, A]]("z", "λj:num. COND(j = 0, b, y(j))")
					bottomOnce := base.Have(
						"one bottom iteration is face zero",
						"∀n:num. ∀v:A. face_iterate_bottom(n, 1, v) = X.d(n, 0, v)",
						Derive(func(e *Argument) {
							n, v := e.FixAs[Nat](), e.FixAs[A]()
							successor := e.Simplified(
								simplicial_set.FaceIterateBottomSucc.At(
									e.TermAs[Fun3[Nat, Nat, A, A]]("X.d"), n, e.TermAs[Nat]("0"), v),
								Fwd(nat_arith.Add),
								Fwd(nat_monus.Sub),
								Fwd(simplicial_set.FaceIterateBottomDef))
							e.Show(
								"the successor law at k = 0, over no iteration",
								By(successor))
						}))
					tailFaces := base.Simplified(given[5], Fwd(bottomOnce))
					base.Do(Simp(Fwd(bottomOnce)))
					k := base.TermAs[Nat]("1 + i")
					inner := base.Have(
						"the inserted horn misses an inner face",
						"0 < 1 + i ∧ 1 + i ≤ q",
						ByArith(missing))
					domainAt := base.Have(
						"membership in the prescribed domain",
						"∀j:num. j ∈ S ⇔ j < t ∨ (1 ≤ j ∧ j ≤ q + 1 ∧ j ≠ 1 + i)",
						BySets(domain))
					zeroFace := base.Have(
						"the inserted face zero is b",
						"z(0) = b",
						Simp(Fwd(inserted)),
						Basic())
					oldFace := base.Have(
						"every other face keeps its value",
						"∀j:num. j ≠ 0 ⇒ z(j) = y(j)",
						Derive(func(e *Argument) {
							e.FixAs[Nat]()
							e.Assume()
							e.Show(
								"the insertion leaves every positive index in place",
								Simp(Fwd(inserted)),
								Basic())
						}))
					fullMembers := base.Have(
						"all specified faces of the inserted horn lie in X",
						"∀j:num. j ∈ horn_faces(q, 1 + i) ⇒ z(j) ∈ X.simplices(q)",
						Derive(func(e *Argument) {
							j := e.FixAs[Nat]()
							face := e.Assume()
							index := e.Have(
								"a face of the inner horn is at most q + 1 and other than 1 + i",
								"j ≤ q + 1 ∧ j ≠ 1 + i",
								By(kan_complex.HornFacesMember.At(q, k, j), face))
							e.Cases(e.Term("j = 0"))
							e.When(
								"the inserted face is the supplied simplex",
								func(f *Argument, atZero Fact) {
									f.Show(
										"face zero lies in X",
										By(atZero, zeroFace, tail))
								})
							e.Otherwise(
								"a positive face is already prescribed",
								func(f *Argument, nonzero Fact) {
									lower := f.Have(
										"the face index is positive",
										"1 ≤ j",
										ByArith(nonzero))
									known := f.Have(
										"the face belongs to S",
										"j ∈ S",
										BySets(domainAt, index, lower))
									f.Show(
										"the original simplex supplies this face",
										By(Normalized, oldFace.At(j), nonzero, members.At(j), known))
								})
						}))
					fullCompatible := base.Have(
						"the inserted horn is compatible",
						"faces_compatible(q, horn_faces(q, 1 + i), z)",
						Simp(Fwd(simplicial_set.FacesCompatibleDef)),
						Derive(func(e *Argument) {
							first, last := e.FixAs[Nat]("a"), e.FixAs[Nat]("c")
							faces := e.Assume()
							pair := e.Have(
								"both faces are faces of the inner horn, in order",
								"a < c ∧ c ≤ q + 1 ∧ a ≠ 1 + i ∧ c ≠ 1 + i",
								ByArith(
									faces,
									kan_complex.HornFacesMember.At(q, k, first),
									kan_complex.HornFacesMember.At(q, k, last)))
							e.Cases(e.Term("a = 0"))
							e.When(
								"a pair with face zero uses the prescribed tail face",
								func(f *Argument, atZero Fact) {
									indices := f.Have(
										"the other face determines an admissible tail index",
										"c ≠ 0 ∧ c - 1 ≤ q ∧ c - 1 ≠ i ∧ 1 + (c - 1) = c",
										ByArith(pair, atZero))
									f.Show(
										"the tail face equation is exactly compatibility with b",
										Simp(Fwd(atZero), Fwd(zeroFace), Fwd(oldFace)),
										By(tailFaces.At(f.TermAs[Nat]("c - 1")), indices))
								})
							e.Otherwise(
								"two positive faces retain their original compatibility",
								func(f *Argument, nonzero Fact) {
									indices := f.Have(
										"both indices are positive and in range",
										"1 ≤ a ∧ 1 ≤ c ∧ a ≤ q + 1 ∧ c ≠ 0",
										ByArith(pair, nonzero))
									known := f.Have(
										"both faces belong to S",
										"a ∈ S ∧ c ∈ S",
										BySets(domainAt, indices, pair))
									f.Show(
										"the original compatibility equation applies",
										Simp(Fwd(oldFace)),
										By(compatible.At(first, last), known, pair))
								})
						}))
					retained := base.Have(
						"the inserted family agrees with every originally prescribed face",
						"∀j:num. j ∈ S ⇒ z(j) = y(j)",
						Derive(func(e *Argument) {
							j := e.FixAs[Nat]()
							known := e.Assume()
							e.Cases(e.Term("j = 0"))
							e.When(
								"a prescribed face zero already equals b",
								func(f *Argument, atZero Fact) {
									before := f.Have(
										"face zero was in the prefix",
										"j < t",
										ByArith(domainAt.At(j), known, atZero))
									f.Show(
										"the insertion retains the original value",
										Simp(Fwd(atZero), Fwd(zeroFace)),
										By(Normalized, prefix.At(j), before, atZero))
								})
							e.Otherwise(
								"every positive face is left in place",
								func(f *Argument, nonzero Fact) {
									f.Show(
										"the value is retained",
										By(oldFace.At(j), nonzero))
								})
						}))
					horn := base.Have(
						"the inserted family is a face family on the inner horn",
						"face_family(q, horn_faces(q, 1 + i), z)",
						Unfold(simplicial_set.FaceFamilyDef),
						By(fullMembers, fullCompatible))
					x, filled := base.ObtainAs[A](
						"fill the inner horn with b inserted",
						"∃x:A. x ∈ X.simplices(q + 1) ∧ faces_filler(q, horn_faces(q, 1 + i), z, x)",
						By(InnerFill.Read(quasi).At(q, k, z), inner, horn),
						Named("x"))
					filler := base.Conjuncts(
						filled,
						"the filler is a simplex",
						"the horn faces are prescribed")
					faces := base.Unfolded(filler[1], simplicial_set.FacesFillerDef)
					base.Take(x)
					base.Show(
						"the filler has the supplied tail and retains S",
						SplitConjAll(
							Case(
								"the filler has the required dimension",
								By(filler[0])),
							Case(
								"face zero is the supplied tail",
								Derive(func(e *Argument) {
									index := e.Have(
										"face zero is specified in the horn",
										"0 ≤ q + 1 ∧ 0 ≠ 1 + i",
										ByArith())
									zero := e.TermAs[Nat]("0")
									e.Show(
										"the filler has face zero b",
										By(faces.At(zero), kan_complex.HornFacesMember.At(q, k, zero), index, zeroFace))
								})),
							Case(
								"each originally specified face is retained",
								Unfold(simplicial_set.FacesFillerDef),
								Derive(func(e *Argument) {
									j := e.FixAs[Nat]("j")
									known := e.Assume()
									index := e.Have(
										"the original index is an index of the filled horn",
										"j ≤ q + 1 ∧ j ≠ 1 + i",
										Derive(func(f *Argument) {
											shape := f.Have(
												"the original index lies in the prescribed range",
												"j < t ∨ (1 ≤ j ∧ j ≤ q + 1 ∧ j ≠ 1 + i)",
												By(domainAt.At(j), known))
											f.Show(
												"both ranges avoid the missing face",
												ByArith(shape, width, missing))
										}))
									e.Show(
										"the horn face is the retained original value",
										By(faces.At(j), kan_complex.HornFacesMember.At(q, k, j), index, retained.At(j), known))
								}))))
				})
			a.Step(
				"extend the prefix facets one at a time using the smaller prefix dimension",
				func(step *Argument, smaller Fact) {
					simplicial := step.Have(
						"a quasi-category is a simplicial set",
						"simplicial_set(X)",
						By(QuasiSimplicialSet.Read(quasi)))
					q, i, t := step.FixAs[Nat](), step.FixAs[Nat](), step.FixAs[Nat]()
					y := step.FixAs[Fun[Nat, A]]()
					b := step.FixAs[A]()
					dimensions := step.Have(
						"successor dimensions in additive form",
						"suc(p) = p + 1 ∧ p + 1 + q = p + q + 1 ∧ p + 1 + 1 = p + 2",
						ByArith())
					step.Do(Simp(Fwd(dimensions)))
					ranges := step.Let(
						"R",
						step.TermAs[Fun[Nat, Set[Nat]]](
							"λm:num. {j:num | j < m ∨ (p + 2 ≤ j ∧ j ≤ p + q + 1 + 1 ∧ j ≠ p + 2 + i)}"))
					given := step.Conjuncts(
						step.Assume(),
						"the missing tail face is not last",
						"the prescribed prefix faces are among the p + 2 prefix faces",
						"the supplied tail is a simplex",
						"the prescribed faces form a face family",
						"the prefix faces have common bottom b",
						"the tail faces have the prescribed faces of b")
					missing, width, tail, prefix, tails := given[0], given[1], given[2], given[4], given[5]
					prescribed := step.Conjuncts(
						step.Unfolded(given[3], simplicial_set.FaceFamilyDef),
						"the prescribed faces are simplices",
						"the prescribed faces are compatible")
					members, compatible :=
						prescribed[0], step.Unfolded(prescribed[1], simplicial_set.FacesCompatibleDef)
					positive := step.Have(
						"the tail degree is positive because i < q",
						"1 ≤ q",
						ByArith(missing))
					rangeAt := step.Have(
						"membership in a progressive prefix domain",
						"∀m j:num. j ∈ R(m) ⇔ j < m ∨ (p + 2 ≤ j ∧ j ≤ p + q + 1 + 1 ∧ j ≠ p + 2 + i)",
						Simp(Fwd(ranges)),
						BySets())
					progress := step.Have(
						"extend the prescribed prefix while retaining all face and bottom data",
						Statement{
							Binders: "∀h:num.",
							Hypotheses: []string{
								"t + h ≤ p + 2",
							},
							Conclusion: "∃z:(num → A). " +
								"    (∀j:num. j ∈ R(t + h) ⇒ z(j) ∈ X.simplices(p + q + 1)) ∧ " +
								"    (∀a c:num. " +
								"        a ∈ R(t + h) ∧ c ∈ R(t + h) ∧ a < c ⇒ " +
								"        X.d(p + q + 1, a, z(c)) = X.d(p + q + 1, c - 1, z(a))) ∧ " +
								"    (∀j:num. j < t + h ⇒ face_iterate_bottom(p + q + 1, p + 1, z(j)) = b) ∧ " +
								"    (∀j:num. j ∈ R(t) ⇒ z(j) = y(j))",
						},
						Derive(func(extend *Argument) {
							extend.Induct("h")
							extend.Base(
								"the original family supplies the initial prefix",
								func(e *Argument) {
									zero := e.Have(
										"the initial prefix size is t",
										"t + 0 = t",
										ByArith())
									e.Do(Simp(Fwd(zero)), StripImp())
									e.Take(y)
									e.Show(
										"all four initial invariants are the given data",
										SplitConjAll(
											Case(
												"the original faces are simplices",
												By(members)),
											Case(
												"the original faces are compatible",
												By(compatible)),
											Case(
												"the original prefix has bottom b",
												By(prefix)),
											Case(
												"the original face values are retained",
												Basic())))
								})
							extend.Step(
								"construct the next prefix facet from its smaller-dimensional horn",
								func(e *Argument, earlier Fact) {
									next := e.Have(
										"the next prefix size is one larger",
										"t + suc(h) = t + h + 1",
										ByArith())
									e.Do(Simp(Fwd(next)))
									room := e.Assume()
									r, position := e.LetAs[Nat]("r", "t + h")
									bounds := e.Have(
										"the next prefix facet lies before the tail",
										"r ≤ p + 1 ∧ r ≤ p + 2 ∧ t ≤ r",
										ByArith(room, position))
									_, current := e.ObtainAs[Fun[Nat, A]](
										"take the family with r prefix facets",
										"∃z:(num → A). "+
											"    (∀j:num. j ∈ R(r) ⇒ z(j) ∈ X.simplices(p + q + 1)) ∧ "+
											"    (∀a c:num. "+
											"        a ∈ R(r) ∧ c ∈ R(r) ∧ a < c ⇒ X.d(p + q + 1, a, z(c)) = X.d(p + q + 1, c - 1, z(a))) ∧ "+
											"    (∀j:num. j < r ⇒ face_iterate_bottom(p + q + 1, p + 1, z(j)) = b) ∧ "+
											"    (∀j:num. j ∈ R(t) ⇒ z(j) = y(j))",
										By(earlier, bounds),
										Named("z"))
									old := e.Conjuncts(
										current,
										"the current faces are simplices",
										"the current faces are compatible",
										"the current prefix has bottom b",
										"the current family retains the original faces")
									oldMembers, oldCompatible, oldPrefix, oldRetained := old[0], old[1], old[2], old[3]
									childDomain := e.Let(
										"T", e.TermAs[Set[Nat]]("{a:num | a < r ∨ (p + 1 ≤ a ∧ a ≤ p + q + 1 ∧ a ≠ p + 1 + i)}"))
									w, childFamily := e.LetAs[Fun[Nat, A]](
										"w", "λa:num. COND(a < r, X.d(p + q + 1, r - 1, z(a)), X.d(p + q + 1, r, z(a + 1)))")
									childAt := e.Have(
										"membership in the child face domain",
										"∀a:num. a ∈ T ⇔ a < r ∨ (p + 1 ≤ a ∧ a ≤ p + q + 1 ∧ a ≠ p + 1 + i)",
										BySets(childDomain))
									deleting := e.Have(
										"the deleting faces are in range",
										"r - 1 ≤ p + q + 1 ∧ r ≤ p + q + 1",
										ByArith(bounds, positive))
									childBefore := e.Have(
										"face a < r of the new facet deletes vertex r from z(a), where it has index r - 1",
										"∀a:num. a < r ⇒ w(a) = X.d(p + q + 1, r - 1, z(a))",
										Derive(func(f *Argument) {
											f.FixAs[Nat]("a")
											f.Assume()
											f.Show(
												"the branch for a < r applies",
												Simp(Fwd(childFamily)),
												Basic())
										}))
									childAfter := e.Have(
										"face a ≥ r of the new facet deletes the same vertex r from z(a + 1), where it has index r",
										"∀a:num. ¬(a < r) ⇒ w(a) = X.d(p + q + 1, r, z(a + 1))",
										Derive(func(f *Argument) {
											f.FixAs[Nat]("a")
											f.Assume()
											f.Show(
												"the branch for a ≥ r applies",
												Simp(Fwd(childFamily)),
												Basic())
										}))
									childMembers := e.Have(
										"every child face is a simplex",
										"∀a:num. a ∈ T ⇒ w(a) ∈ X.simplices(p + q)",
										Derive(func(f *Argument) {
											index := f.FixAs[Nat]("a")
											known := f.Assume()
											f.Cases(f.Term("a < r"))
											f.When(
												"a prefix face is a face of the current face at a",
												func(g *Argument, before Fact) {
													simplex := g.Have(
														"the original face is a simplex",
														"z(a) ∈ X.simplices(p + q + 1)",
														By(oldMembers.At(index), rangeAt.At(r, index), before))
													g.Show(
														"the preceding deleting face lies in X",
														Simp(Fwd(childBefore)),
														By(
															simplicial_set.FaceIn.Read(simplicial).At(
																g.TermAs[Nat]("p + q"), g.TermAs[Nat]("r - 1"), g.TermAs[A]("z(a)")),
															deleting,
															simplex))
												})
											f.Otherwise(
												"a tail face comes from the shifted current face",
												func(g *Argument, after Fact) {
													shape := g.Have(
														"the child index lies in its numeric domain",
														"a < r ∨ (p + 1 ≤ a ∧ a ≤ p + q + 1 ∧ a ≠ p + 1 + i)",
														By(childAt.At(index), known))
													shift := g.Have(
														"the shifted index lies in the current tail",
														"p + 2 ≤ a + 1 ∧ a + 1 ≤ p + q + 1 + 1 ∧ a + 1 ≠ p + 2 + i",
														ByArith(shape, after))
													simplex := g.Have(
														"the shifted current face is a simplex",
														"z(a + 1) ∈ X.simplices(p + q + 1)",
														By(oldMembers.At(g.TermAs[Nat]("a + 1")), rangeAt.At(r, g.TermAs[Nat]("a + 1")), shift))
													g.Show(
														"the deleting face lies in X",
														Simp(Fwd(childAfter)),
														By(
															simplicial_set.FaceIn.Read(simplicial).At(g.TermAs[Nat]("p + q"), r, g.TermAs[A]("z(a + 1)")),
															deleting,
															simplex))
												})
										}))
									deletingBelow := e.Have(
										"the deleting indices are below the bottom iterations",
										"r - 1 ≤ p ∧ p + 1 ≤ p + q ∧ p ≤ p + q",
										ByArith(bounds, positive))
									childPrefix := e.Have(
										"the child prefix still has common bottom b",
										"∀j:num. j < r ⇒ face_iterate_bottom(p + q, p, w(j)) = b",
										Derive(func(f *Argument) {
											j := f.FixAs[Nat]()
											before := f.Assume()
											simplex := f.Have(
												"the current prefix face is a simplex",
												"z(j) ∈ X.simplices(p + q + 1)",
												By(oldMembers.At(j), rangeAt.At(r, j), before))
											f.Show(
												"the deleting face is absorbed by the bottom iteration",
												Simp(
													Fwd(childBefore),
													Fwd(simplicial_set.FaceIterateBottomBelow.Read(simplicial)),
													Fwd(simplex),
													Fwd(deletingBelow)),
												By(oldPrefix.At(j), before))
										}))
									childTails := e.Have(
										"the child tail faces have the prescribed bottom faces of b",
										"∀a:num. a ≤ q ∧ a ≠ i ⇒ face_iterate_bottom(p + q, p + 1, w(p + 1 + a)) = X.d(q, a, b)",
										Derive(func(f *Argument) {
											index := f.FixAs[Nat]("a")
											admissible := f.Assume()
											tailRange := f.Have(
												"the child tail position shifts to the current tail",
												"¬(p + 1 + a < r) ∧ p + 2 ≤ p + 2 + a ∧ p + 2 + a ≤ p + q + 1 + 1 ∧ p + 2 + a ≠ p + 2 + i",
												ByArith(bounds, admissible))
											simplex := f.Have(
												"the current tail face is a simplex",
												"z(p + 2 + a) ∈ X.simplices(p + q + 1)",
												By(oldMembers.At(f.TermAs[Nat]("p + 2 + a")), rangeAt.At(r, f.TermAs[Nat]("p + 2 + a")), tailRange))
											original := f.Have(
												"the current tail face is the original one",
												"z(p + 2 + a) = y(p + 2 + a)",
												By(
													oldRetained.At(f.TermAs[Nat]("p + 2 + a")),
													rangeAt.At(t, f.TermAs[Nat]("p + 2 + a")),
													tailRange))
											shift := f.Have(
												"the shifted child tail index is the current tail index",
												"p + 1 + a + 1 = p + 2 + a",
												ByArith())
											f.Show(
												"the deleting face is absorbed by the bottom iteration of the original tail face",
												Simp(
													Fwd(childAfter),
													Fwd(shift),
													Fwd(simplicial_set.FaceIterateBottomBelow.Read(simplicial)),
													Fwd(simplex),
													Fwd(deletingBelow),
													Fwd(dimensions)),
												Simp(Fwd(original)),
												By(tails.At(index), admissible))
										}))
									adjacent := e.Have(
										"the two relevant degrees differ by one",
										"p + q - 1 + 1 = p + q ∧ p + q - 1 + 2 = p + q + 1",
										ByArith(positive))
									faceFace := e.Have(
										"commute two faces of a current simplex",
										Statement{
											Binders: "∀a c:num. ∀v:A.",
											Hypotheses: []string{
												"v ∈ X.simplices(p + q + 1)",
												"a < c",
												"c ≤ p + q + 1",
											},
											Conclusion: "X.d(p + q, a, X.d(p + q + 1, c, v)) = X.d(p + q, c - 1, X.d(p + q + 1, a, v))",
										},
										Derive(func(f *Argument) {
											first, last := f.FixAs[Nat]("a"), f.FixAs[Nat]("c")
											simplex := f.FixAs[A]("v")
											pair := f.Assume()
											f.Show(
												"the ambient face identity at the two adjacent degrees",
												By(
													simplicial_set.FaceFace.Read(simplicial).At(f.TermAs[Nat]("p + q - 1"), first, last, simplex),
													adjacent,
													pair))
										}))
									childCompatible := e.Have(
										"the child faces are compatible across the deleted facet",
										"∀a c:num. a ∈ T ∧ c ∈ T ∧ a < c ⇒ X.d(p + q, a, w(c)) = X.d(p + q, c - 1, w(a))",
										Derive(func(f *Argument) {
											first, last := f.FixAs[Nat]("a"), f.FixAs[Nat]("c")
											pair := f.Assume()
											firstRange := f.Have(
												"the first child index lies in its numeric domain",
												"a < r ∨ (p + 1 ≤ a ∧ a ≤ p + q + 1 ∧ a ≠ p + 1 + i)",
												By(childAt.At(first), pair))
											lastRange := f.Have(
												"the second child index lies in its numeric domain",
												"c < r ∨ (p + 1 ≤ c ∧ c ≤ p + q + 1 ∧ c ≠ p + 1 + i)",
												By(childAt.At(last), pair))
											lastAfter := f.Unless(
												f.Term("c < r"),
												"two prefix indices commute with the preceding deleting face",
												Given(func(g *Argument, bothBefore Fact) {
													indices := g.Have(
														"both face indices precede the deleting face",
														"a < r ∧ a < r - 1 ∧ c - 1 < r - 1",
														ByArith(pair, bothBefore))
													firstKnown := g.Have(
														"the first current face is prescribed",
														"a ∈ R(r)",
														By(rangeAt.At(r, first), bothBefore, indices))
													firstSimplex := g.Have(
														"the first current face is a simplex",
														"z(a) ∈ X.simplices(p + q + 1)",
														By(oldMembers.At(first), firstKnown))
													lastKnown := g.Have(
														"the second current face is prescribed",
														"c ∈ R(r)",
														By(rangeAt.At(r, last), bothBefore, indices))
													lastSimplex := g.Have(
														"the second current face is a simplex",
														"z(c) ∈ X.simplices(p + q + 1)",
														By(oldMembers.At(last), lastKnown))
													g.Show(
														"commute, use current compatibility, and commute back",
														Simp(Fwd(childBefore), Fwd(faceFace), Fwd(firstSimplex), Fwd(lastSimplex), Fwd(oldCompatible)),
														Basic())
												}))
											f.Cases(f.Term("a < r"))
											f.When(
												"a prefix and a tail commute on opposite sides of the deleted facet",
												func(across *Argument, firstBefore Fact) {
													indices := across.Have(
														"the shifted tail index is above the preceding deleting face",
														"r - 1 < c ∧ c ≤ p + q + 1 ∧ a < c + 1 ∧ p + 2 ≤ c + 1 ∧ c + 1 ≤ p + q + 1 + 1 ∧ c + 1 ≠ p + 2 + i",
														ByArith(pair, lastRange, lastAfter, firstBefore, bounds))
													firstKnown := across.Have(
														"the prefix current face is prescribed",
														"a ∈ R(r)",
														By(rangeAt.At(r, first), firstBefore))
													lastKnown := across.Have(
														"the shifted tail current face is prescribed",
														"c + 1 ∈ R(r)",
														By(rangeAt.At(r, across.TermAs[Nat]("c + 1")), indices))
													firstSimplex := across.Have(
														"the prefix current face is a simplex",
														"z(a) ∈ X.simplices(p + q + 1)",
														By(oldMembers.At(first), firstKnown))
													lastSimplex := across.Have(
														"the tail current face is a simplex",
														"z(c + 1) ∈ X.simplices(p + q + 1)",
														By(oldMembers.At(across.TermAs[Nat]("c + 1")), lastKnown))
													cancel := across.Have(
														"the shifted upper index returns to c",
														"c + 1 - 1 = c",
														ByArith())
													across.Show(
														"commute through the current prefix-tail equation",
														Simp(
															Fwd(childBefore),
															Fwd(childAfter),
															Fwd(faceFace),
															Fwd(firstSimplex),
															Fwd(lastSimplex),
															Fwd(oldCompatible),
															Fwd(cancel)),
														Basic())
												})
											f.Otherwise(
												"two tail indices both shift past the deleted facet",
												func(beyond *Argument, firstAfter Fact) {
													indices := beyond.Have(
														"both shifted indices lie in the current tail above r",
														"r < a + 1 ∧ "+
															"a + 1 ≤ p + q + 1 ∧ "+
															"r < c ∧ "+
															"c ≤ p + q + 1 ∧ "+
															"a + 1 < c + 1 ∧ "+
															"p + 2 ≤ a + 1 ∧ "+
															"a + 1 ≤ p + q + 1 + 1 ∧ "+
															"a + 1 ≠ p + 2 + i ∧ "+
															"p + 2 ≤ c + 1 ∧ "+
															"c + 1 ≤ p + q + 1 + 1 ∧ "+
															"c + 1 ≠ p + 2 + i",
														ByArith(pair, firstRange, lastRange, firstAfter, lastAfter, bounds))
													firstKnown := beyond.Have(
														"the first shifted current face is prescribed",
														"a + 1 ∈ R(r)",
														By(rangeAt.At(r, beyond.TermAs[Nat]("a + 1")), indices))
													lastKnown := beyond.Have(
														"the second shifted current face is prescribed",
														"c + 1 ∈ R(r)",
														By(rangeAt.At(r, beyond.TermAs[Nat]("c + 1")), indices))
													firstSimplex := beyond.Have(
														"the first shifted current face is a simplex",
														"z(a + 1) ∈ X.simplices(p + q + 1)",
														By(oldMembers.At(beyond.TermAs[Nat]("a + 1")), firstKnown))
													lastSimplex := beyond.Have(
														"the second shifted current face is a simplex",
														"z(c + 1) ∈ X.simplices(p + q + 1)",
														By(oldMembers.At(beyond.TermAs[Nat]("c + 1")), lastKnown))
													cancel := beyond.Have(
														"the shifted indices return to a and c",
														"a + 1 - 1 = a ∧ c + 1 - 1 = c",
														ByArith())
													commute := beyond.Have(
														"the lower face passes the deletion at r",
														"X.d(p + q, a, X.d(p + q + 1, r, z(c + 1))) = X.d(p + q, r, X.d(p + q + 1, a + 1, z(c + 1)))",
														By(
															faceFace.At(r, beyond.TermAs[Nat]("a + 1"), beyond.TermAs[A]("z(c + 1)")),
															indices,
															cancel,
															lastSimplex))
													beyond.Show(
														"the shifted current tail equation supplies compatibility",
														Simp(
															Fwd(childAfter),
															Fwd(commute),
															Fwd(oldCompatible),
															Fwd(cancel),
															Fwd(faceFace),
															Fwd(firstSimplex)),
														Basic())
												})
										}))
									childFaceFamily := e.Have(
										"the child faces form a face family",
										"face_family(p + q, T, w)",
										Simp(Fwd(simplicial_set.FaceFamilyDef), Fwd(simplicial_set.FacesCompatibleDef)),
										By(childMembers, childCompatible))
									child := e.Simplified(smaller.At(q, i, r, w, b), Rev(childDomain))
									_, newFacet := e.ObtainAs[A](
										"fill the child horn by the outer dimension hypothesis",
										"∃u:A. "+
											"    u ∈ X.simplices(p + q + 1) ∧ "+
											"    face_iterate_bottom(p + q + 1, p + 1, u) = b ∧ "+
											"    faces_filler(p + q, T, w, u)",
										By(child, missing, bounds, tail, childFaceFamily, childPrefix, childTails),
										Named("u"))
									facet := e.Conjuncts(
										newFacet,
										"the new facet is a simplex",
										"the new facet has bottom b",
										"the new facet has the child face data")
									childFaces := e.Unfolded(facet[2], simplicial_set.FacesFillerDef)
									zNext, updated := e.LetAs[Fun[Nat, A]]("z'", "λj:num. COND(j = r, u, z(j))")
									atNew := e.Have(
										"the next family uses u at the new position",
										"z'(r) = u",
										Simp(Fwd(updated)),
										Basic())
									away := e.Have(
										"every other face keeps its current value",
										"∀j:num. j ≠ r ⇒ z'(j) = z(j)",
										Derive(func(f *Argument) {
											f.FixAs[Nat]()
											f.Assume()
											f.Show(
												"the update leaves every other index in place",
												Simp(Fwd(updated)),
												Basic())
										}))
									prefixGrowth := e.Have(
										"the prefix grows by exactly one index",
										"∀j:num. j < r + 1 ⇔ j < r ∨ j = r",
										ByArith())
									growth := e.Have(
										"the next prescribed domain adds just r",
										"∀j:num. j ∈ R(r + 1) ⇔ j ∈ R(r) ∨ j = r",
										Simp(Fwd(ranges), Fwd(prefixGrowth)),
										BySets())
									outside := e.Have(
										"r is outside both the original domain and the current prefix domain",
										"r ∉ R(t) ∧ r ∉ R(r)",
										Derive(func(f *Argument) {
											numeric := f.Have(
												"r is in neither numeric range",
												"¬(r < t ∨ (p + 2 ≤ r ∧ r ≤ p + q + 1 + 1 ∧ r ≠ p + 2 + i)) ∧ "+
													"¬(r < r ∨ (p + 2 ≤ r ∧ r ≤ p + q + 1 + 1 ∧ r ≠ p + 2 + i))",
												ByArith(bounds))
											f.Show(
												"neither domain previously prescribed this facet",
												Simp(Fwd(ranges)),
												BySets(numeric))
										}))
									e.Take(zNext)
									e.Show(
										"replacing the one new facet preserves all four invariants",
										SplitConjAll(
											Case(
												"every prescribed next face is a simplex",
												Derive(func(f *Argument) {
													j := f.FixAs[Nat]()
													known := f.Assume()
													f.Cases(f.Term("j = r"))
													f.When(
														"the new position uses the child filler",
														func(g *Argument, equal Fact) {
															g.Show(
																"the new facet is a simplex",
																Simp(Fwd(equal), Fwd(atNew)),
																By(facet[0]))
														})
													f.Otherwise(
														"every other position was already prescribed",
														func(g *Argument, different Fact) {
															oldKnown := g.Have(
																"the index lies in the current domain",
																"j ∈ R(r)",
																By(growth.At(j), known, different))
															g.Show(
																"the current face supplies its membership",
																Simp(Fwd(away)),
																By(oldMembers.At(j), oldKnown))
														})
												})),
											Case(
												"all pairs of next faces are compatible",
												Derive(func(f *Argument) {
													first, last := f.FixAs[Nat]("a"), f.FixAs[Nat]("c")
													pair := f.Assume()
													lowerOld := f.Unless(
														f.Term("a = r"),
														"the new lower face matches a tail face through the child filler",
														Given(func(g *Argument, lowerNew Fact) {
															indices := g.Have(
																"the other index is strictly above r",
																"r < c ∧ c ≠ r",
																ByArith(pair, lowerNew))
															known := g.Have(
																"the upper face was already prescribed",
																"c ∈ R(r)",
																By(growth.At(last), pair, indices))
															shape := g.Have(
																"the upper index lies in the current numeric domain",
																"c < r ∨ (p + 2 ≤ c ∧ c ≤ p + q + 1 + 1 ∧ c ≠ p + 2 + i)",
																By(rangeAt.At(r, last), known))
															shift := g.Have(
																"the child index is c minus one and lies after its prefix",
																"¬(c - 1 < r) ∧ p + 1 ≤ c - 1 ∧ c - 1 ≤ p + q + 1 ∧ c - 1 ≠ p + 1 + i ∧ c - 1 + 1 = c",
																ByArith(shape, indices, bounds))
															face := g.Have(
																"the child filler supplies the upper matching face",
																"X.d(p + q + 1, c - 1, u) = X.d(p + q + 1, r, z(c))",
																By(
																	childFaces.At(g.TermAs[Nat]("c - 1")),
																	childAt.At(g.TermAs[Nat]("c - 1")),
																	childAfter.At(g.TermAs[Nat]("c - 1")),
																	shift))
															g.Show(
																"the new lower face matches the old upper face",
																Simp(Fwd(lowerNew), Fwd(atNew), Fwd(away)),
																By(face))
														}))
													f.Cases(f.Term("c = r"))
													f.When(
														"the new upper face matches an earlier prefix face",
														func(upper *Argument, upperNew Fact) {
															before := upper.Have(
																"the lower index precedes the new facet",
																"a < r",
																ByArith(pair, upperNew))
															face := upper.Have(
																"the child filler supplies the lower matching face",
																"X.d(p + q + 1, a, u) = X.d(p + q + 1, r - 1, z(a))",
																By(childFaces.At(first), childAt.At(first), childBefore.At(first), before))
															upper.Show(
																"the old lower face matches the new upper face",
																Simp(Fwd(upperNew), Fwd(atNew), Fwd(away)),
																By(face))
														})
													f.Otherwise(
														"a pair disjoint from r keeps its current compatibility",
														func(disjoint *Argument, upperOld Fact) {
															known := disjoint.Have(
																"both indices belong to the current domain",
																"a ∈ R(r) ∧ c ∈ R(r)",
																By(growth.At(first), growth.At(last), pair, lowerOld, upperOld))
															disjoint.Show(
																"the current compatibility equation is retained",
																Simp(Fwd(away)),
																By(oldCompatible.At(first, last), known, pair))
														})
												})),
											Case(
												"every next prefix face has bottom b",
												Derive(func(f *Argument) {
													j := f.FixAs[Nat]()
													before := f.Assume()
													f.Cases(f.Term("j = r"))
													f.When(
														"the new prefix face has the child filler's bottom",
														func(g *Argument, equal Fact) {
															g.Show(
																"the new face has bottom b",
																Simp(Fwd(equal), Fwd(atNew)),
																By(facet[1]))
														})
													f.Otherwise(
														"an earlier prefix face keeps its bottom",
														func(g *Argument, different Fact) {
															oldBefore := g.Have(
																"the index is in the current prefix",
																"j < r",
																ByArith(before, different))
															g.Show(
																"the current bottom equation remains valid",
																Simp(Fwd(away)),
																By(oldPrefix.At(j), oldBefore))
														})
												})),
											Case(
												"every originally prescribed face is retained",
												Derive(func(f *Argument) {
													j := f.FixAs[Nat]()
													known := f.Assume()
													fresh := f.Have(
														"the original face is not the newly inserted facet",
														"j ≠ r",
														BySets(known, outside))
													f.Show(
														"the current retained value remains valid",
														Simp(Fwd(away), Fwd(fresh)),
														By(oldRetained.At(j), known))
												}))))
								})
						}))
					completeSize := step.Have(
						"the remaining number of prefix facets reaches the full prefix",
						"t + (p + 2 - t) = p + 2",
						ByArith(width))
					admissibleSize := step.Have(
						"the full prefix is allowed by the induction bound",
						"t + (p + 2 - t) ≤ p + 2",
						ByArith(width))
					z, full := step.ObtainAs[Fun[Nat, A]](
						"take the family with every prefix facet present",
						"∃z:(num → A). "+
							"    (∀j:num. j ∈ R(p + 2) ⇒ z(j) ∈ X.simplices(p + q + 1)) ∧ "+
							"    (∀a c:num. "+
							"        a ∈ R(p + 2) ∧ c ∈ R(p + 2) ∧ a < c ⇒ "+
							"        X.d(p + q + 1, a, z(c)) = X.d(p + q + 1, c - 1, z(a))) ∧ "+
							"    (∀j:num. j < p + 2 ⇒ face_iterate_bottom(p + q + 1, p + 1, z(j)) = b) ∧ "+
							"    (∀j:num. j ∈ R(t) ⇒ z(j) = y(j))",
						By(progress.At(step.TermAs[Nat]("p + 2 - t")), completeSize, admissibleSize),
						Named("z"))
					fullParts := step.Conjuncts(
						full,
						"all full-domain faces are simplices",
						"all full-domain faces are compatible",
						"all full-prefix faces have bottom b",
						"the full family retains the prescribed faces")
					fullDomain := step.Have(
						"the complete prefix domain is exactly one horn",
						"∀j:num. j ∈ R(p + 2) ⇔ j ≤ p + q + 1 + 1 ∧ j ≠ p + 2 + i",
						Simp(Fwd(rangeAt)),
						ByArith(positive))
					inner := step.Have(
						"the complete horn misses an inner face",
						"0 < p + 2 + i ∧ p + 2 + i ≤ p + q + 1",
						ByArith(missing))
					hornDomain := step.Have(
						"the complete prefix domain is the set of faces of the inner horn",
						"R(p + 2) = horn_faces(p + q + 1, p + 2 + i)",
						Unfold(kan_complex.HornFacesDef),
						BySets(fullDomain))
					horn := step.Have(
						"the complete family is a face family on the inner horn",
						"face_family(p + q + 1, horn_faces(p + q + 1, p + 2 + i), z)",
						Simp(Rev(hornDomain), Fwd(simplicial_set.FaceFamilyDef), Fwd(simplicial_set.FacesCompatibleDef)),
						By(fullParts[0], fullParts[1]))
					top, missingFace := step.TermAs[Nat]("p + q + 1"), step.TermAs[Nat]("p + 2 + i")
					x, filled := step.ObtainAs[A](
						"fill the complete inner horn",
						"∃x:A. "+
							"    x ∈ X.simplices(p + q + 1 + 1) ∧ "+
							"    faces_filler(p + q + 1, horn_faces(p + q + 1, p + 2 + i), z, x)",
						By(InnerFill.Read(quasi).At(top, missingFace, z), inner, horn),
						Named("x"))
					filler := step.Conjuncts(
						filled,
						"the final filler is a simplex",
						"the final filler has the specified horn faces")
					faces := step.Unfolded(filler[1], simplicial_set.FacesFillerDef)
					step.Take(x)
					step.Show(
						"the filler has bottom b and all the originally prescribed faces",
						SplitConjAll(
							Case(
								"the filler has the required dimension",
								By(filler[0])),
							Case(
								"the bottom of face zero recovers the supplied tail",
								Derive(func(e *Argument) {
									indices := e.Have(
										"face zero is specified and is absorbed by the bottom iteration",
										"0 ≤ p + 1 ∧ p + 1 ≤ p + q + 1 ∧ 0 ≤ p + q + 1 + 1 ∧ 0 ≠ p + 2 + i ∧ 0 < p + 2 ∧ p + 1 + 1 = p + 2",
										ByArith())
									zero := e.TermAs[Nat]("0")
									zeroFace := e.Have(
										"the final face zero is the specified face",
										"X.d(p + q + 1 + 1, 0, x) = z(0)",
										By(faces.At(zero), kan_complex.HornFacesMember.At(top, missingFace, zero), indices))
									bottom := e.Have(
										"the bottom of face zero is b",
										"face_iterate_bottom(p + q + 1, p + 1, X.d(p + q + 1 + 1, 0, x)) = b",
										By(fullParts[2].At(e.TermAs[Nat]("0")), indices, zeroFace))
									e.Show(
										"absorbing face zero is the required bottom iteration",
										By(
											simplicial_set.FaceIterateBottomBelow.Read(simplicial).At(
												e.TermAs[Nat]("p + q + 1"), e.TermAs[Nat]("p + 1"), e.TermAs[Nat]("0"), x),
											filler[0],
											indices,
											bottom))
								})),
							Case(
								"all the originally prescribed faces survive the construction",
								Unfold(simplicial_set.FacesFillerDef),
								Derive(func(e *Argument) {
									j := e.FixAs[Nat]("j")
									known := e.Assume()
									shape := e.Have(
										"the original index lies in its numeric domain",
										"j < t ∨ (p + 2 ≤ j ∧ j ≤ p + q + 1 + 1 ∧ j ≠ p + 2 + i)",
										By(rangeAt.At(t, j), known))
									index := e.Have(
										"the original face belongs to the complete horn",
										"j ≤ p + q + 1 + 1 ∧ j ≠ p + 2 + i",
										ByArith(shape, width, positive))
									e.Show(
										"the final horn value is the retained original value",
										By(
											faces.At(j),
											kan_complex.HornFacesMember.At(top, missingFace, j),
											fullParts[3].At(j),
											known,
											index))
								}))))
				})
		}),
	Reading: "The domain is (A_t^p ⋆ Δ^q) ∪ (Δ^p ⋆ Λ_i^q) ∪ Δ^q, where A_t^p is " +
		"the union of the first t prefix facets. The supplied tail b is required " +
		"even when t = 0. All iterations are within dimension because i < q.",
})}

// ConeRestrictionLeftFibration — restriction to the boundary of the
// fixed prefix lifts every non-last tail horn by one inner horn in X.
var ConeRestrictionLeftFibration = coneRestrictionLeftFibrationThm{family.Add(registry.ProofEntry{
	Name: "ConeRestrictionLeftFibration",
	Key:  "prop_f0c0be4aaaae87c5",
	Build: QuasiCategory.Law("∀r:num. ∀k:A. "+
		"    left_fibration(simplex_cone(r, k), simplex_boundary_cone(r, k), simplex_cone_restriction(r))",
		func(a *Argument, quasi Fact, r *Expr[Nat], k *Expr[A]) {
			simplicial := a.Have(
				"a quasi-category is a simplicial set",
				"simplicial_set(X)",
				By(QuasiSimplicialSet.Read(quasi)))
			a.Show(
				"restriction to the boundary cone is a left fibration",
				Simp(Fwd(kan_fibration.LeftFibration)),
				SplitConj(
					Case(
						"restriction is a simplicial map",
						By(simplicial_set.ConeRestrictionMap.Read(simplicial).At(r, k))),
					Case(
						"a non-last cone horn lifts by one ambient inner horn",
						Derive(func(lift *Argument) {
							n, i := lift.FixAs[Nat]("n"), lift.FixAs[Nat]("i")
							lift.FixAs[Fun[Nat, A]]("y")
							lift.FixAs[Fun[Nat, A]]("z")
							given := lift.Conjuncts(
								lift.Assume(),
								"the missing cone face is not last",
								"the cone horn is a face family of the cone",
								"the boundary-cone base is a simplex",
								"the horn maps to the faces of the base")
							boundarySet := lift.Simplified(given[2], Fwd(simplicial_set.SimplexBoundaryConeSimplicesDef))
							boundaryData := lift.Have(
								"the boundary simplex supplies its normalized face family",
								"z = normalize_on(0 .. r, junk, z) ∧ "+
									"face_family(X, r + (n + 1), 0 .. r, z) ∧ "+
									"(∀j:num. 0 < r ∧ j ≤ r ⇒ face_iterate_top(r + (n + 1), n + 1 + 1, z(j)) = X.d(r, j, k))",
								BySets(boundarySet))
							dimension := lift.Have(
								"the boundary faces and cone horn faces have the same ambient dimension",
								"r + (n + 1) = r + n + 1",
								ByArith())
							boundary := lift.Conjuncts(
								lift.Simplified(boundaryData, Fwd(dimension)),
								"the boundary family is normalized",
								"the prefix faces form a face family",
								"the prefix faces retain the boundary of k")
							prefixFamily := lift.Conjuncts(
								lift.Simplified(
									boundary[1],
									Fwd(simplicial_set.FaceFamilyDef),
									Fwd(simplicial_set.FacesCompatibleDef)),
								"the prefix faces are simplices",
								"the prefix faces are compatible")
							hornFamily := lift.Conjuncts(
								lift.Unfolded(given[1], simplicial_set.FaceFamilyDef),
								"the cone horn faces are simplices",
								"the cone horn is compatible")
							coneFaces := lift.Simplified(
								hornFamily[0],
								Fwd(simplicial_set.SimplexConeSimplicesDef),
								Fwd(kan_complex.HornFacesMember))
							hornData := lift.Have(
								"each cone horn face is an ambient simplex with prefix k",
								Statement{
									Binders: "∀j:num.",
									Hypotheses: []string{
										"j ≤ n + 1",
										"j ≠ i",
									},
									Conclusion: "y(j) ∈ X.simplices(r + n + 1) ∧ face_iterate_top(r + n + 1, n + 1, y(j)) = k",
								},
								BySets(coneFaces))
							tailCompatible := lift.Simplified(
								hornFamily[1],
								Fwd(simplicial_set.FacesCompatibleDef),
								Fwd(kan_complex.HornFacesMember),
								Fwd(simplicial_set.SimplexConeFaceDef))
							image := lift.Simplified(
								given[3],
								Fwd(simplicial_set.FacesFillerDef),
								Fwd(kan_complex.HornFacesMember),
								Fwd(simplicial_set.SimplexBoundaryConeFaceDef),
								Fwd(simplicial_set.SimplexConeRestrictionDef),
								Fwd(dimension))
							M, ambientDimension := lift.LetAs[Nat]("M", "r + n + 1")
							K, missingIndex := lift.LetAs[Nat]("K", "r + 1 + i")
							H, assembled := lift.LetAs[Fun[Nat, A]]("H", "λj:num. COND(j ≤ r, z(j), y(j - r - 1))")
							inner := lift.Have(
								"the assembled horn misses an inner face",
								"0 < K ∧ K ≤ M",
								ByArith(missingIndex, ambientDimension, given[0]))
							prefixValue := lift.Have(
								"prefix coordinates of the assembled horn are the boundary faces",
								"∀j:num. j ≤ r ⇒ H(j) = z(j)",
								Derive(func(e *Argument) {
									e.FixAs[Nat]()
									e.Assume()
									e.Show(
										"the prefix branch of the assembled family applies",
										Simp(Fwd(assembled)),
										Basic())
								}))
							tailValue := lift.Have(
								"tail coordinates of the assembled horn are the shifted cone horn",
								"∀j:num. ¬(j ≤ r) ⇒ H(j) = y(j - r - 1)",
								Derive(func(e *Argument) {
									e.FixAs[Nat]()
									e.Assume()
									e.Show(
										"the tail branch of the assembled family applies",
										Simp(Fwd(assembled)),
										Basic())
								}))
							mixed := lift.Have(
								"the lifting image equation matches every prefix face with every specified tail face",
								"∀a b:num. a ≤ r ∧ b ≤ n + 1 ∧ b ≠ i ⇒ X.d(M, a, y(b)) = X.d(M, r + b, z(a))",
								Derive(func(e *Argument) {
									prefix, tail := e.FixAs[Nat]("a"), e.FixAs[Nat]("b")
									pair := e.Conjuncts(
										e.Assume(),
										"the prefix coordinate is at most r",
										"the tail face is at most n + 1",
										"the tail face is not the missing one")
									normal := e.Have(
										"the lifting image equation holds at this prefix coordinate",
										"normalize_on(0 .. r, junk, λj:num. X.d(M, r + b, z(j)), a) = "+
											"normalize_on(0 .. r, junk, λj:num. X.d(M, j, y(b)), a)",
										By(image.At(tail, prefix), pair[1], pair[2]))
									pointwise := e.Simplified(normal, Fwd(num_segment.NormalizeOnSegmentIn))
									e.Show(
										"evaluation inside the interval gives the matching face equation",
										Simp(Fwd(pointwise)),
										Basic())
								}))
							members := lift.Have(
								"all specified ambient horn faces lie in X",
								"∀j:num. j ∈ horn_faces(M, K) ⇒ H(j) ∈ X.simplices(M)",
								Derive(func(e *Argument) {
									j := e.FixAs[Nat]()
									face := e.Assume()
									index := e.Have(
										"a face of the ambient horn is at most M + 1 and other than K",
										"j ≤ M + 1 ∧ j ≠ K",
										By(kan_complex.HornFacesMember.At(M, K, j), face))
									e.Cases(e.Term("j ≤ r"))
									e.When(
										"a prefix face comes from the boundary simplex",
										func(f *Argument, prefix Fact) {
											f.Show(
												"the boundary face is a simplex",
												Simp(Fwd(prefixValue)),
												By(prefixFamily[0].At(j), num_segment.MembershipFromZero.At(j, r), prefix))
										})
									e.Otherwise(
										"a tail face comes from the specified cone horn",
										func(f *Argument, tail Fact) {
											reversed := f.Have(
												"the shifted tail index is specified in the cone horn",
												"j - r - 1 ≤ n + 1 ∧ j - r - 1 ≠ i",
												ByArith(index, tail, ambientDimension, missingIndex))
											f.Show(
												"the cone horn supplies the ambient simplex",
												Simp(Fwd(tailValue)),
												By(hornData.At(f.TermAs[Nat]("j - r - 1")), reversed))
										})
								}))
							compatible := lift.Have(
								"the assembled faces are compatible on the faces of the ambient horn",
								"faces_compatible(M, horn_faces(M, K), H)",
								Simp(Fwd(simplicial_set.FacesCompatibleDef)),
								Derive(func(e *Argument) {
									first, last := e.FixAs[Nat]("a"), e.FixAs[Nat]("c")
									faces := e.Assume()
									pair := e.Have(
										"both faces are faces of the ambient horn, in order",
										"a < c ∧ c ≤ M + 1 ∧ a ≠ K ∧ c ≠ K",
										ByArith(
											faces,
											kan_complex.HornFacesMember.At(M, K, first),
											kan_complex.HornFacesMember.At(M, K, last)))
									e.Cases(e.Term("c ≤ r"))
									e.When(
										"two prefix faces use the boundary simplex compatibility",
										func(f *Argument, prefix Fact) {
											lower := f.Have(
												"the lower index is a prefix index too",
												"a ≤ r",
												ByArith(pair, prefix))
											f.Show(
												"the boundary compatibility equation applies",
												Simp(Fwd(prefixValue)),
												By(
													prefixFamily[1].At(first, last),
													num_segment.MembershipFromZero.At(first, r),
													num_segment.MembershipFromZero.At(last, r),
													lower,
													pair,
													prefix))
										})
									e.Otherwise(
										"the upper face is a tail face",
										func(f *Argument, upperTail Fact) {
											f.Cases(f.Term("a ≤ r"))
											f.When(
												"a prefix and a tail match by the lifting image equation",
												func(g *Argument, lowerPrefix Fact) {
													shift := g.Have(
														"the upper index shifts to an admissible cone-horn index",
														"c - r - 1 ≤ n + 1 ∧ c - r - 1 ≠ i ∧ r + (c - r - 1) = c - 1",
														ByArith(pair, upperTail, ambientDimension, missingIndex))
													g.Show(
														"the mixed matching equation gives ambient compatibility",
														Simp(Fwd(prefixValue), Fwd(tailValue)),
														By(mixed.At(first, g.TermAs[Nat]("c - r - 1")), lowerPrefix, shift))
												})
											f.Otherwise(
												"two tail faces use the shifted cone horn compatibility",
												func(g *Argument, lowerTail Fact) {
													shift := g.Have(
														"both shifted indices are ordered, specified, and return to the ambient indices",
														"a - r - 1 < c - r - 1 ∧ "+
															"a - r - 1 ≤ n + 1 ∧ "+
															"c - r - 1 ≤ n + 1 ∧ "+
															"a - r - 1 ≠ i ∧ "+
															"c - r - 1 ≠ i ∧ "+
															"r + 1 + (a - r - 1) = a ∧ "+
															"r + 1 + (c - r - 1 - 1) = c - 1",
														ByArith(pair, lowerTail, upperTail, ambientDimension, missingIndex))
													g.Show(
														"the cone-horn compatibility equation becomes the ambient equation",
														Simp(Fwd(tailValue)),
														By(tailCompatible.At(g.TermAs[Nat]("a - r - 1"), g.TermAs[Nat]("c - r - 1")), shift))
												})
										})
								}))
							horn := lift.Have(
								"the assembled faces form an ambient inner horn",
								"face_family(M, horn_faces(M, K), H)",
								Unfold(simplicial_set.FaceFamilyDef),
								By(members, compatible))
							x, filled := lift.ObtainAs[A](
								"fill the assembled inner horn in X",
								"∃x:A. x ∈ X.simplices(M + 1) ∧ faces_filler(M, horn_faces(M, K), H, x)",
								By(InnerFill.Read(quasi).At(M, K, H), inner, horn),
								Named("x"))
							filler := lift.Conjuncts(
								filled,
								"the ambient filler is a simplex",
								"the ambient filler has the assembled horn faces")
							faces := lift.Unfolded(filler[1], simplicial_set.FacesFillerDef)
							lift.Take(x)
							lift.Show(
								"the ambient filler is the required cone lift",
								SplitConjAll(
									Case(
										"the filler retains the fixed prefix k",
										Derive(func(e *Argument) {
											last := e.Have(
												"the final tail face is present and its iteration lies in range",
												"n + 1 ≤ n + 1 ∧ "+
													"n + 1 ≠ i ∧ "+
													"¬(M + 1 ≤ r) ∧ "+
													"M + 1 ≤ M + 1 ∧ "+
													"M + 1 ≠ K ∧ "+
													"M + 1 - r - 1 = n + 1 ∧ "+
													"n + 1 ≤ M ∧ "+
													"M < M + 1 + (n + 1)",
												ByArith(ambientDimension, missingIndex, given[0]))
											top := e.TermAs[Nat]("M + 1")
											lastFace := e.Have(
												"the ambient last face is the cone horn's last face",
												"X.d(M + 1, M + 1, x) = y(n + 1)",
												By(faces.At(top), kan_complex.HornFacesMember.At(M, K, top), tailValue.At(top), last))
											lastPrefix := e.Have(
												"the last face has prefix k",
												"face_iterate_top(M, n + 1, X.d(M + 1, M + 1, x)) = k",
												By(hornData.At(e.TermAs[Nat]("n + 1")), last, lastFace))
											prefix := e.Have(
												"the whole filler has prefix k",
												"face_iterate_top(M + 1, n + 1 + 1, x) = k",
												By(
													Normalized,
													simplicial_set.FaceIterateTopAbove.Read(simplicial).At(
														M, e.TermAs[Nat]("n + 1"), e.TermAs[Nat]("M + 1"), x),
													filler[0],
													last,
													lastPrefix))
											e.Show(
												"the filler lies in the next cone degree",
												Simp(Fwd(simplicial_set.SimplexConeSimplicesDef), Fwd(dimension)),
												BySets(filler[0], prefix))
										})),
									Case(
										"all specified cone horn faces are the supplied faces",
										Unfold(simplicial_set.FacesFillerDef),
										Derive(func(e *Argument) {
											j := e.FixAs[Nat]("j")
											hornFace := e.Assume()
											admissible := e.Have(
												"a face of the cone horn is at most n + 1 and other than i",
												"j ≤ n + 1 ∧ j ≠ i",
												By(kan_complex.HornFacesMember.At(n, i, j), hornFace))
											shift := e.Have(
												"the cone index shifts to a specified ambient tail index",
												"r + 1 + j ≤ M + 1 ∧ r + 1 + j ≠ K ∧ ¬(r + 1 + j ≤ r) ∧ r + 1 + j - r - 1 = j",
												ByArith(admissible, ambientDimension, missingIndex))
											face := e.TermAs[Nat]("r + 1 + j")
											e.Show(
												"the ambient filler supplies this cone face",
												Simp(Fwd(simplicial_set.SimplexConeFaceDef), Fwd(dimension)),
												By(faces.At(face), kan_complex.HornFacesMember.At(M, K, face), tailValue.At(face), shift))
										})),
									Case(
										"the filler restricts to the specified boundary-cone simplex",
										Derive(func(e *Argument) {
											prefixFaces := e.Have(
												"the ambient prefix faces are the prescribed boundary faces",
												"∀j:num. j ≤ r ⇒ X.d(M + 1, j, x) = z(j)",
												Derive(func(f *Argument) {
													j := f.FixAs[Nat]()
													prefix := f.Assume()
													index := f.Have(
														"each prefix index is specified in the ambient horn",
														"j ≤ M + 1 ∧ j ≠ K",
														ByArith(prefix, ambientDimension, missingIndex))
													f.Show(
														"the ambient filler supplies this boundary face",
														By(faces.At(j), kan_complex.HornFacesMember.At(M, K, j), prefixValue.At(j), index, prefix))
												}))
											normalized := e.Have(
												"the normalized prefix-face families agree",
												"normalize_on(0 .. r, junk, λj:num. X.d(M + 1, j, x)) = normalize_on(0 .. r, junk, z)",
												Simp(Fwd(functions.NormalizeOnEqIff), Fwd(num_segment.MembershipFromZero)),
												By(prefixFaces))
											e.Show(
												"restriction is the prescribed normalized family",
												Simp(Fwd(simplicial_set.SimplexConeRestrictionDef), Fwd(dimension)),
												Simp(Fwd(normalized), Rev(boundary[0])),
												Basic())
										}))))
						}))))
		}),
	Reading: "A q-simplex of the cone is an (r + q + 1)-simplex of X with prefix k, and " +
		"its restriction is the family of its first r + 1 faces, normalized on 0 .. r. The " +
		"smallest lift n = 0 has tail degree n + 1 = 1 and is an inner 2-horn when r = 0. At r " +
		"= 0 the boundary cone does not mention k, which enters through the faces of the horn.",
})}

// ConeProjectionLeftFibration — the boundary-cone projection is a left
// fibration: a horn over a base simplex b lifts to the normalized family
// of r + 1 facets with tail b, which is b itself when the fixed prefix k
// is a vertex and is built one facet at a time otherwise.
var ConeProjectionLeftFibration = coneProjectionLeftFibrationThm{family.Add(registry.ProofEntry{
	Name: "ConeProjectionLeftFibration",
	Key:  "prop_e0a04ed891bfefd",
	Build: family.Sections(QuasiCategory.Statement(
		"∀r:num. ∀k:A. "+
			"    left_fibration(simplex_boundary_cone(r, k), X, simplex_boundary_cone_projection(r))"),
		func(ctx *Script, headline string) *GoalStackNode {
			// firstFacets — for every t ≤ r + 1 the first t facets exist:
			// simplices with tail b that carry the faces of k on top, have the
			// supplied faces as their tail faces and agree on their common
			// faces. The hypotheses are the horn of the boundary cone over b,
			// opened into its clauses: the facets of each supplied face are
			// simplices and agree on their common faces, those of the last
			// supplied face carry the faces of k on top, the supplied faces
			// agree on their common tail faces, and facet 0 of the supplied
			// face a has the face a of b as its tail. By induction on t: facet
			// t is a partial cone-horn fill over the earlier facets and the
			// supplied faces.
			firstFacets := ctx.Lemma(QuasiCategory.Statement(Statement{
				Binders: "∀r:num. ∀k:A. ∀n i:num. ∀y:(num → num → A). ∀b:A. ∀t:num.",
				Hypotheses: []string{
					"0 < r",
					"i ≤ n",
					"b ∈ X.simplices(n + 1)",
					"∀a j:num. a ≤ n + 1 ∧ a ≠ i ∧ j ≤ r ⇒ y(a, j) ∈ X.simplices(r + n)",
					"∀a l j:num. " +
						"    a ≤ n + 1 ∧ a ≠ i ∧ l < j ∧ j ≤ r ⇒ X.d(r + n, l, y(a, j)) = X.d(r + n, j - 1, y(a, l))",
					"∀j:num. j ≤ r ⇒ face_iterate_top(r + n, n + 1, y(n + 1, j)) = X.d(r, j, k)",
					"∀a c j:num. " +
						"    a < c ∧ c ≤ n + 1 ∧ a ≠ i ∧ c ≠ i ∧ j ≤ r ⇒ " +
						"    X.d(r + n, r + a, y(c, j)) = X.d(r + n, r + c - 1, y(a, j))",
					"∀a:num. a ≤ n + 1 ∧ a ≠ i ⇒ face_iterate_bottom(r + n, r, y(a, 0)) = X.d(n + 1, a, b)",
					"t ≤ r + 1",
				},
				Conclusion: "∃z:(num → A). " +
					"    (∀j:num. j < t ⇒ z(j) ∈ X.simplices(r + n + 1)) ∧ " +
					"    (∀j:num. j < t ⇒ face_iterate_bottom(r + n + 1, r, z(j)) = b) ∧ " +
					"    (∀j:num. j < t ⇒ face_iterate_top(r + n + 1, n + 2, z(j)) = X.d(r, j, k)) ∧ " +
					"    (∀j a:num. j < t ∧ a ≤ n + 1 ∧ a ≠ i ⇒ X.d(r + n + 1, r + a, z(j)) = y(a, j)) ∧ " +
					"    (∀l j:num. l < j ∧ j < t ⇒ X.d(r + n + 1, l, z(j)) = X.d(r + n + 1, j - 1, z(l)))",
			}),
				func(
					a *Argument,
					X *Expr[simplicial_set.SimplicialOps[A]],
					quasi Fact,
					r *Expr[Nat],
					k *Expr[A],
					n, i *Expr[Nat],
					y *Expr[Fun[Nat, Fun[Nat, A]]],
					b *Expr[A],
					positive, notLast, baseSimplex, hornMembers, hornPrefix, hornTop, tailCompatibility, zeroBottom Fact,
				) {
					simplicial := QuasiSimplicialSet.Read(quasi)
					dimensions := a.Have(
						"r and r + n are successors",
						"r + n - 1 + 1 = r + n ∧ r - 1 + 1 = r",
						ByArith(positive))
					commonBottom := a.Have(
						"every facet of each supplied face y(a) has the face a of b as its tail",
						"∀a j:num. a ≤ n + 1 ∧ a ≠ i ∧ j ≤ r ⇒ face_iterate_bottom(r + n, r, y(a, j)) = X.d(n + 1, a, b)",
						Derive(func(m *Argument) {
							face, j := m.FixAs[Nat]("a"), m.FixAs[Nat]("j")
							indices := m.Assume()
							supplied := m.Have(
								"a indexes a supplied face",
								"a ≤ n + 1 ∧ a ≠ i",
								By(indices))
							m.Cases(m.TermAs[Bool]("j = 0"))
							m.When(
								"at j = 0 the tail is the projection of y(a), the face a of b",
								func(p *Argument, atZero Fact) {
									p.Show(
										"facet 0 of y(a) has the face a of b as its tail",
										Simp(Fwd(atZero)),
										By(zeroBottom.At(face), supplied))
								})
							m.Otherwise(
								"a positive facet shares its tail with facet 0 through their common face",
								func(p *Argument, notZero Fact) {
									zero := p.TermAs[Nat]("0")
									bounds := p.Have(
										"j is a positive facet index, and the faces 0 and j - 1 delete prefix vertices",
										"0 < j ∧ j ≤ r ∧ 0 ≤ r - 1 ∧ r - 1 ≤ r + n - 1 ∧ j - 1 ≤ r - 1",
										ByArith(notZero, indices, positive))
									simplices := p.Have(
										"facets j and 0 of y(a) are (r + n)-simplices",
										"y(a, j) ∈ X.simplices(r + n) ∧ y(a, 0) ∈ X.simplices(r + n)",
										ByArith(hornMembers.At(face, j), hornMembers.At(face, zero), indices))
									successors := p.Have(
										"facets j and 0 of y(a) are (r + n - 1 + 1)-simplices",
										"y(a, j) ∈ X.simplices(r + n - 1 + 1) ∧ y(a, 0) ∈ X.simplices(r + n - 1 + 1)",
										By(simplices, dimensions))
									common := p.Have(
										"facets 0 and j of y(a) agree on their common face",
										"X.d(r + n, 0, y(a, j)) = X.d(r + n, j - 1, y(a, 0))",
										ByArith(hornPrefix.At(face, zero, j), indices, bounds))
									throughZero := p.Have(
										"the tail of facet j is the tail of its face 0",
										"face_iterate_bottom(r + n - 1, r - 1, X.d(r + n, 0, y(a, j))) = "+
											"face_iterate_bottom(r + n, r, y(a, j))",
										By(
											successors,
											bounds,
											dimensions,
											simplicial_set.FaceIterateBottomBelow.Read(simplicial).At(
												p.TermAs[Nat]("r + n - 1"), p.TermAs[Nat]("r - 1"), zero, p.TermAs[A]("y(a, j)"))))
									throughPredecessor := p.Have(
										"the tail of facet 0 is the tail of its face j - 1",
										"face_iterate_bottom(r + n - 1, r - 1, X.d(r + n, j - 1, y(a, 0))) = "+
											"face_iterate_bottom(r + n, r, y(a, 0))",
										By(
											successors,
											bounds,
											dimensions,
											simplicial_set.FaceIterateBottomBelow.Read(simplicial).At(
												p.TermAs[Nat]("r + n - 1"),
												p.TermAs[Nat]("r - 1"),
												p.TermAs[Nat]("j - 1"),
												p.TermAs[A]("y(a, 0)"))))
									tailOfZero := p.Have(
										"facet 0 of y(a) has the face a of b as its tail",
										"face_iterate_bottom(r + n, r, y(a, 0)) = X.d(n + 1, a, b)",
										By(zeroBottom.At(face), supplied))
									p.Show(
										"facet j of y(a) has the face a of b as its tail",
										Simp(Rev(throughZero), Fwd(common), Fwd(throughPredecessor), Fwd(tailOfZero)),
										Basic())
								})
						}))
					a.Induct("t")
					a.Base(
						"with no facets every condition is vacuous",
						func(p *Argument) {
							p.Assume()
							p.Take(p.TermAs[Fun[Nat, A]]("λj:num. junk"))
							p.Show(
								"the junk family meets the vacuous conditions",
								ByArith())
						})
					a.Step(
						"facet t is a partial cone-horn fill over the earlier facets and the supplied faces",
						func(p *Argument, earlier Fact) {
							t := p.TermAs[Nat]("t")
							room := p.Assume()
							prefixBound := p.Have(
								"the next facet index is at most r",
								"t ≤ r",
								ByArith(room))
							inductionBound := p.Have(
								"the first t facets lie in the induction range",
								"t ≤ r + 1",
								ByArith(room))
							_, previousData := p.ObtainAs[Fun[Nat, A]](
								"take the first t facets",
								"∃z:(num → A). "+
									"    (∀j:num. j < t ⇒ z(j) ∈ X.simplices(r + n + 1)) ∧ "+
									"    (∀j:num. j < t ⇒ face_iterate_bottom(r + n + 1, r, z(j)) = b) ∧ "+
									"    (∀j:num. j < t ⇒ face_iterate_top(r + n + 1, n + 2, z(j)) = X.d(r, j, k)) ∧ "+
									"    (∀j a:num. j < t ∧ a ≤ n + 1 ∧ a ≠ i ⇒ X.d(r + n + 1, r + a, z(j)) = y(a, j)) ∧ "+
									"    (∀l j:num. l < j ∧ j < t ⇒ X.d(r + n + 1, l, z(j)) = X.d(r + n + 1, j - 1, z(l)))",
								By(earlier, inductionBound))
							previousFacets := p.Conjuncts(
								previousData,
								"the first t facets are (r + n + 1)-simplices",
								"each has tail b",
								"facet j carries the face j of k on top",
								"the tail face a of facet j is facet j of y(a)",
								"the first t facets agree on their common faces")
							faceDomainDef := p.Let(
								"S", p.TermAs[Set[Nat]]("{l:num | l < t ∨ (r ≤ l ∧ l ≤ r + n + 1 ∧ l ≠ r + i)}"))
							faceFamilyDef := p.Let(
								"F", p.TermAs[Fun[Nat, A]]("λl:num. COND(l < t, X.d(r + n + 1, t - 1, z(l)), y(l - r, t))"))
							prefixValues := p.Have(
								"below t, F(l) is the face t - 1 of facet l",
								"∀l:num. l < t ⇒ F(l) = X.d(r + n + 1, t - 1, z(l))",
								Derive(func(q *Argument) {
									q.FixAs[Nat]("l")
									before := q.Assume()
									q.Show(
										"F(l) is the face t - 1 of facet l",
										Simp(Fwd(faceFamilyDef), Fwd(before)),
										Basic())
								}))
							tailValues := p.Have(
								"from t on, F(l) is facet t of the supplied face l - r",
								"∀l:num. ¬(l < t) ⇒ F(l) = y(l - r, t)",
								Derive(func(q *Argument) {
									q.FixAs[Nat]("l")
									after := q.Assume()
									q.Show(
										"F(l) is facet t of y(l - r)",
										Simp(Fwd(faceFamilyDef), Fwd(after)),
										Basic())
								}))
							fillerDimensions := p.Have(
								"the partial cone-horn fill at r - 1 and n + 1 has the dimensions of facet t",
								"r - 1 + 1 = r ∧ "+
									"r - 1 + (n + 1) = r + n ∧ "+
									"r - 1 + (n + 1) + 1 = r + n + 1 ∧ "+
									"r + n - 1 + 2 = r + n + 1",
								ByArith(positive))
							fillerBounds := p.Have(
								"the missing tail face lies before the last tail face",
								"i < n + 1",
								ByArith(notLast))
							faceDomain := p.Have(
								"S holds the faces below t and the tail faces other than r + i",
								"∀l:num. l ∈ S ⇔ l < t ∨ (r ≤ l ∧ l ≤ r + n + 1 ∧ l ≠ r + i)",
								Simp(Fwd(faceDomainDef)),
								BySets())
							faceMembers := p.Have(
								"every prescribed face F(l) is an (r + n)-simplex",
								"∀l:num. l ∈ S ⇒ F(l) ∈ X.simplices(r + n)",
								Derive(func(q *Argument) {
									l := q.FixAs[Nat]("l")
									prescribed := q.Assume()
									q.Cases(q.TermAs[Bool]("l < t"))
									q.When(
										"below t, F(l) is a face of facet l",
										func(u *Argument, before Fact) {
											simplex := u.Have(
												"the face t - 1 of facet l is an (r + n)-simplex",
												"X.d(r + n + 1, t - 1, z(l)) ∈ X.simplices(r + n)",
												ByArith(
													previousFacets[0].At(l),
													before,
													prefixBound,
													simplicial_set.FaceIn.Read(simplicial).At(
														u.TermAs[Nat]("r + n"), u.TermAs[Nat]("t - 1"), u.TermAs[A]("z(l)"))))
											value := u.Have(
												"F(l) is the face t - 1 of facet l",
												"F(l) = X.d(r + n + 1, t - 1, z(l))",
												By(prefixValues.At(l), before))
											u.Show(
												"F(l) is an (r + n)-simplex",
												Simp(Fwd(value)),
												By(simplex))
										})
									q.Otherwise(
										"from t on, F(l) is a facet of a supplied face",
										func(u *Argument, after Fact) {
											tailFace := u.Have(
												"l is a tail face other than r + i",
												"r ≤ l ∧ l ≤ r + n + 1 ∧ l ≠ r + i",
												By(faceDomain.At(l), prescribed, after))
											supplied := u.Have(
												"l - r indexes a supplied face",
												"l - r ≤ n + 1 ∧ l - r ≠ i",
												ByArith(tailFace))
											simplex := u.Have(
												"facet t of y(l - r) is an (r + n)-simplex",
												"y(l - r, t) ∈ X.simplices(r + n)",
												ByArith(hornMembers.At(u.TermAs[Nat]("l - r"), t), supplied, prefixBound))
											value := u.Have(
												"F(l) is facet t of y(l - r)",
												"F(l) = y(l - r, t)",
												By(tailValues.At(l), after))
											u.Show(
												"F(l) is an (r + n)-simplex",
												Simp(Fwd(value)),
												By(simplex))
										})
								}))
							doublePredecessor := p.Have(
								"t - 1 - 1 is t - 2",
								"t - 1 - 1 = t - 2",
								ByArith())
							faceCompatibility := p.Have(
								"the prescribed faces F(l) are compatible",
								"∀a c:num. a ∈ S ∧ c ∈ S ∧ a < c ⇒ X.d(r + n, a, F(c)) = X.d(r + n, c - 1, F(a))",
								Derive(func(q *Argument) {
									first, last := q.FixAs[Nat]("a"), q.FixAs[Nat]("c")
									pair := q.Assume()
									q.Cases(q.TermAs[Bool]("c < t"))
									q.When(
										"faces a < c below t are faces of facets a and c",
										func(u *Argument, lastBefore Fact) {
											bounds := u.Have(
												"a and c - 1 lie below t - 1",
												"a < t ∧ a < t - 1 ∧ c - 1 < t - 1 ∧ t - 1 ≤ r + n + 1",
												ByArith(pair, lastBefore, prefixBound))
											values := u.Have(
												"F(a) and F(c) are the faces t - 1 of facets a and c",
												"F(a) = X.d(r + n + 1, t - 1, z(a)) ∧ F(c) = X.d(r + n + 1, t - 1, z(c))",
												By(prefixValues.At(first), prefixValues.At(last), bounds, lastBefore))
											compatible := u.Have(
												"facets a and c agree on their common face",
												"X.d(r + n + 1, a, z(c)) = X.d(r + n + 1, c - 1, z(a))",
												By(previousFacets[4].At(first, last), pair, lastBefore))
											simplices := u.Have(
												"facets a and c are (r + n - 1 + 2)-simplices",
												"z(a) ∈ X.simplices(r + n - 1 + 2) ∧ z(c) ∈ X.simplices(r + n - 1 + 2)",
												By(previousFacets[0].At(first), previousFacets[0].At(last), bounds, lastBefore, fillerDimensions))
											facesOfC := u.Have(
												"the faces a and t - 1 of facet c commute",
												"X.d(r + n, a, X.d(r + n + 1, t - 1, z(c))) = X.d(r + n, t - 2, X.d(r + n + 1, a, z(c)))",
												By(
													simplices,
													bounds,
													dimensions,
													fillerDimensions,
													doublePredecessor,
													simplicial_set.FaceFace.Read(simplicial).At(
														u.TermAs[Nat]("r + n - 1"), first, u.TermAs[Nat]("t - 1"), u.TermAs[A]("z(c)"))))
											facesOfA := u.Have(
												"the faces c - 1 and t - 1 of facet a commute",
												"X.d(r + n, c - 1, X.d(r + n + 1, t - 1, z(a))) = X.d(r + n, t - 2, X.d(r + n + 1, c - 1, z(a)))",
												By(
													simplices,
													bounds,
													dimensions,
													fillerDimensions,
													doublePredecessor,
													simplicial_set.FaceFace.Read(simplicial).At(
														u.TermAs[Nat]("r + n - 1"), u.TermAs[Nat]("c - 1"), u.TermAs[Nat]("t - 1"), u.TermAs[A]("z(a)"))))
											u.Show(
												"F(a) and F(c) agree on their common face",
												Simp(Fwd(values), Fwd(facesOfC), Fwd(compatible), Fwd(facesOfA)),
												Basic())
										})
									q.Otherwise(
										"the later face c is a tail face",
										func(u *Argument, lastAfter Fact) {
											lastTail := u.Have(
												"c is a tail face other than r + i",
												"r ≤ c ∧ c ≤ r + n + 1 ∧ c ≠ r + i",
												By(faceDomain.At(last), pair, lastAfter))
											lastSupplied := u.Have(
												"c - r indexes a supplied face",
												"c - r ≤ n + 1 ∧ c - r ≠ i ∧ r + (c - r) = c",
												ByArith(lastTail))
											u.Cases(u.TermAs[Bool]("a < t"))
											u.When(
												"a face a below t meets the tail face c",
												func(v *Argument, firstBefore Fact) {
													values := v.Have(
														"F(a) is the face t - 1 of facet a and F(c) is facet t of y(c - r)",
														"F(a) = X.d(r + n + 1, t - 1, z(a)) ∧ F(c) = y(c - r, t)",
														By(prefixValues.At(first), tailValues.At(last), firstBefore, lastAfter))
													supplied := v.Have(
														"facets a and t of y(c - r) agree on their common face",
														"X.d(r + n, a, y(c - r, t)) = X.d(r + n, t - 1, y(c - r, a))",
														ByArith(hornPrefix.At(v.TermAs[Nat]("c - r"), first, t), lastSupplied, firstBefore, prefixBound))
													tailFace := v.Have(
														"the tail face c - r of facet a is facet a of y(c - r)",
														"X.d(r + n + 1, r + (c - r), z(a)) = y(c - r, a)",
														ByArith(previousFacets[3].At(first, v.TermAs[Nat]("c - r")), firstBefore, lastSupplied))
													tailFaceAtC := v.Simplified(tailFace, Fwd(lastSupplied))
													simplex := v.Have(
														"facet a is an (r + n - 1 + 2)-simplex",
														"z(a) ∈ X.simplices(r + n - 1 + 2)",
														By(previousFacets[0].At(first), firstBefore, fillerDimensions))
													bounds := v.Have(
														"the face c lies after t - 1",
														"t - 1 < c ∧ c ≤ r + n + 1",
														ByArith(firstBefore, prefixBound, lastTail))
													commute := v.Have(
														"the faces t - 1 and c of facet a commute",
														"X.d(r + n, t - 1, X.d(r + n + 1, c, z(a))) = X.d(r + n, c - 1, X.d(r + n + 1, t - 1, z(a)))",
														By(
															simplex,
															bounds,
															dimensions,
															fillerDimensions,
															simplicial_set.FaceFace.Read(simplicial).At(
																v.TermAs[Nat]("r + n - 1"), v.TermAs[Nat]("t - 1"), last, v.TermAs[A]("z(a)"))))
													v.Show(
														"F(a) and F(c) agree on their common face",
														Simp(Fwd(values), Fwd(supplied), Rev(tailFaceAtC), Fwd(commute)),
														Basic())
												})
											u.Otherwise(
												"two tail faces a < c",
												func(v *Argument, firstAfter Fact) {
													firstTail := v.Have(
														"a is a tail face other than r + i",
														"r ≤ a ∧ a ≤ r + n + 1 ∧ a ≠ r + i",
														By(faceDomain.At(first), pair, firstAfter))
													supplied := v.Have(
														"a - r < c - r index supplied faces",
														"a - r < c - r ∧ c - r ≤ n + 1 ∧ a - r ≠ i ∧ c - r ≠ i ∧ t ≤ r",
														ByArith(firstTail, lastTail, pair, prefixBound))
													values := v.Have(
														"F(a) and F(c) are facets t of y(a - r) and y(c - r)",
														"F(a) = y(a - r, t) ∧ F(c) = y(c - r, t)",
														By(tailValues.At(first), tailValues.At(last), firstAfter, lastAfter))
													shifts := v.Have(
														"shifting back by r returns a and c - 1",
														"r + (a - r) = a ∧ r + (c - r) - 1 = c - 1",
														ByArith(firstTail, lastTail))
													compatible := v.Have(
														"facets t of y(a - r) and y(c - r) agree on their common tail face",
														"X.d(r + n, r + (a - r), y(c - r, t)) = X.d(r + n, r + (c - r) - 1, y(a - r, t))",
														By(tailCompatibility.At(v.TermAs[Nat]("a - r"), v.TermAs[Nat]("c - r"), t), supplied))
													shifted := v.Simplified(compatible, Fwd(shifts))
													v.Show(
														"F(a) and F(c) agree on their common face",
														Simp(Fwd(values), Fwd(shifted)),
														Basic())
												})
										})
								}))
							prefixBottom := p.Have(
								"below t, each F(l) has tail b",
								"∀l:num. l < t ⇒ face_iterate_bottom(r + n, r - 1, F(l)) = b",
								Derive(func(q *Argument) {
									l := q.FixAs[Nat]("l")
									before := q.Assume()
									tail := q.Have(
										"facet l has tail b",
										"face_iterate_bottom(r + n + 1, r, z(l)) = b",
										By(previousFacets[1].At(l), before))
									value := q.Have(
										"F(l) is the face t - 1 of facet l",
										"F(l) = X.d(r + n + 1, t - 1, z(l))",
										By(prefixValues.At(l), before))
									bounds := q.Have(
										"the face t - 1 deletes one of the first r vertices",
										"t - 1 ≤ r - 1 ∧ r - 1 ≤ r + n",
										ByArith(prefixBound, positive))
									through := q.Have(
										"the face t - 1 of facet l has the tail of facet l",
										"face_iterate_bottom(r + n, r - 1, X.d(r + n + 1, t - 1, z(l))) = "+
											"face_iterate_bottom(r + n + 1, r, z(l))",
										By(
											previousFacets[0].At(l),
											before,
											bounds,
											fillerDimensions,
											simplicial_set.FaceIterateBottomBelow.Read(simplicial).At(
												q.TermAs[Nat]("r + n"), q.TermAs[Nat]("r - 1"), q.TermAs[Nat]("t - 1"), q.TermAs[A]("z(l)"))))
									q.Show(
										"F(l) has tail b",
										Simp(Fwd(value), Fwd(through), Fwd(tail)),
										Basic())
								}))
							shiftedTail := p.Have(
								"F(r + a) is facet t of the supplied face a",
								"∀a:num. a ≤ n + 1 ∧ a ≠ i ⇒ F(r + a) = y(a, t)",
								Derive(func(q *Argument) {
									q.FixAs[Nat]("a")
									q.Assume()
									after := q.Have(
										"r + a is not below t",
										"¬(r + a < t)",
										ByArith(prefixBound))
									cancel := q.Have(
										"r + a - r is a",
										"r + a - r = a",
										ByArith())
									value := q.Have(
										"F(r + a) is facet t of y(r + a - r)",
										"F(r + a) = y(r + a - r, t)",
										By(tailValues.At(q.TermAs[Nat]("r + a")), after))
									q.Show(
										"F(r + a) is facet t of y(a)",
										Simp(Fwd(value), Fwd(cancel)),
										Basic())
								}))
							tailBottom := p.Have(
								"each tail face F(r + a) has the face a of b as its tail",
								"∀a:num. a ≤ n + 1 ∧ a ≠ i ⇒ face_iterate_bottom(r + n, r, F(r + a)) = X.d(n + 1, a, b)",
								Derive(func(q *Argument) {
									face := q.FixAs[Nat]("a")
									supplied := q.Assume()
									value := q.Have(
										"F(r + a) is facet t of y(a)",
										"F(r + a) = y(a, t)",
										By(shiftedTail.At(face), supplied))
									tail := q.Have(
										"facet t of y(a) has the face a of b as its tail",
										"face_iterate_bottom(r + n, r, y(a, t)) = X.d(n + 1, a, b)",
										ByArith(commonBottom.At(face, t), supplied, prefixBound))
									q.Show(
										"F(r + a) has the face a of b as its tail",
										Simp(Fwd(value), Fwd(tail)),
										Basic())
								}))
							faceFamily := p.Have(
								"the prescribed faces form a face family on S",
								"face_family(r + n, S, F)",
								Simp(Fwd(simplicial_set.FaceFamilyDef), Fwd(simplicial_set.FacesCompatibleDef)),
								By(faceMembers, faceCompatibility))
							partial := p.Simplified(
								PartialConeHornFill.Read(quasi).At(
									p.TermAs[Nat]("r - 1"), p.TermAs[Nat]("n + 1"), i, t, p.TermAs[Fun[Nat, A]]("F"), b),
								Fwd(fillerDimensions),
								Rev(faceDomainDef))
							x, filled := p.ObtainAs[A](
								"fill the partial cone horn F over b",
								"∃x:A. "+
									"    x ∈ X.simplices(r + n + 1) ∧ "+
									"    face_iterate_bottom(r + n + 1, r, x) = b ∧ "+
									"    faces_filler(r + n, S, F, x)",
								By(partial, fillerBounds, prefixBound, baseSimplex, faceFamily, prefixBottom, tailBottom))
							newFacet := p.Conjuncts(
								filled,
								"the new facet x is an (r + n + 1)-simplex",
								"x has tail b",
								"x has the faces F(l) for l in S")
							assigned := p.Unfolded(newFacet[2], simplicial_set.FacesFillerDef)
							newPrefixFaces := p.Have(
								"x agrees with every earlier facet l on their common face",
								"∀l:num. l < t ⇒ X.d(r + n + 1, l, x) = X.d(r + n + 1, t - 1, z(l))",
								Derive(func(q *Argument) {
									l := q.FixAs[Nat]("l")
									before := q.Assume()
									assignedFace := q.Have(
										"the face l of x is F(l)",
										"X.d(r + n + 1, l, x) = F(l)",
										By(assigned.At(l), faceDomain.At(l), before))
									value := q.Have(
										"F(l) is the face t - 1 of facet l",
										"F(l) = X.d(r + n + 1, t - 1, z(l))",
										By(prefixValues.At(l), before))
									q.Show(
										"x and facet l agree on their common face",
										Simp(Fwd(assignedFace), Fwd(value)),
										Basic())
								}))
							newTailFaces := p.Have(
								"the tail face a of x is facet t of y(a)",
								"∀a:num. a ≤ n + 1 ∧ a ≠ i ⇒ X.d(r + n + 1, r + a, x) = y(a, t)",
								Derive(func(q *Argument) {
									face := q.FixAs[Nat]("a")
									supplied := q.Assume()
									position := q.TermAs[Nat]("r + a")
									prescribed := q.Have(
										"r + a is a prescribed face",
										"r + a ∈ S",
										ByArith(faceDomain.At(position), supplied))
									assignedFace := q.Have(
										"the face r + a of x is F(r + a)",
										"X.d(r + n + 1, r + a, x) = F(r + a)",
										By(assigned.At(position), prescribed))
									value := q.Have(
										"F(r + a) is facet t of y(a)",
										"F(r + a) = y(a, t)",
										By(shiftedTail.At(face), supplied))
									q.Show(
										"the face r + a of x is facet t of y(a)",
										Simp(Fwd(assignedFace), Fwd(value)),
										Basic())
								}))
							finalSupplied := p.Have(
								"the final tail face is supplied because i ≤ n",
								"n + 1 ≤ n + 1 ∧ n + 1 ≠ i",
								ByArith(notLast))
							lastFace := p.Have(
								"the last face of x is facet t of y(n + 1)",
								"X.d(r + n + 1, r + (n + 1), x) = y(n + 1, t)",
								By(newTailFaces.At(p.TermAs[Nat]("n + 1")), finalSupplied))
							lastIndex := p.Have(
								"the last face of x has index r + n + 1",
								"r + (n + 1) = r + n + 1",
								ByArith())
							lastFaceAtTop := p.Simplified(lastFace, Fwd(lastIndex))
							prescribedTop := p.Have(
								"facet t of y(n + 1) carries the face t of k on top",
								"face_iterate_top(r + n, n + 1, y(n + 1, t)) = X.d(r, t, k)",
								ByArith(hornTop.At(t), prefixBound))
							topBounds := p.Have(
								"the last face deletes a tail vertex, and n + 1 ≤ r + n",
								"r + n < r + n + 1 + (n + 1) ∧ r + n + 1 ≤ r + n + 1 ∧ n + 1 ≤ r + n ∧ n + 1 + 1 = n + 2",
								ByArith(positive))
							topThroughLast := p.Have(
								"the top of x is the top of its last face",
								"face_iterate_top(r + n, n + 1, X.d(r + n + 1, r + n + 1, x)) = "+
									"face_iterate_top(r + n + 1, n + 2, x)",
								By(
									newFacet[0],
									topBounds,
									simplicial_set.FaceIterateTopAbove.Read(simplicial).At(
										p.TermAs[Nat]("r + n"), p.TermAs[Nat]("n + 1"), p.TermAs[Nat]("r + n + 1"), x)))
							newTop := p.Have(
								"x carries the face t of k on top",
								"face_iterate_top(r + n + 1, n + 2, x) = X.d(r, t, k)",
								Simp(Rev(topThroughLast), Fwd(lastFaceAtTop), Fwd(prescribedTop)),
								Basic())
							updatedFamilyDef := p.Let("U", p.TermAs[Fun[Nat, A]]("λj:num. COND(j = t, x, z(j))"))
							atNew := p.Have(
								"the updated family U has x at t",
								"U(t) = x",
								Simp(Fwd(updatedFamilyDef)),
								Basic())
							earlierValues := p.Have(
								"U keeps every earlier facet",
								"∀j:num. j < t ⇒ U(j) = z(j)",
								Derive(func(q *Argument) {
									q.FixAs[Nat]("j")
									before := q.Assume()
									differs := q.Have(
										"an earlier index differs from t",
										"j ≠ t",
										ByArith(before))
									q.Show(
										"U(j) is facet j",
										Simp(Fwd(updatedFamilyDef), Fwd(differs)),
										Basic())
								}))
							p.Take(p.TermAs[Fun[Nat, A]]("U"))
							p.Show(
								"U gives the first t + 1 facets",
								SplitConjAll(
									Case(
										"the first t + 1 facets are (r + n + 1)-simplices",
										Derive(func(q *Argument) {
											j := q.FixAs[Nat]("j")
											below := q.Assume()
											q.Cases(q.TermAs[Bool]("j < t"))
											q.When(
												"j is an earlier facet",
												func(u *Argument, before Fact) {
													u.Show(
														"facet j is an (r + n + 1)-simplex",
														Simp(Fwd(earlierValues)),
														By(previousFacets[0].At(j), before))
												})
											q.Otherwise(
												"j is the new facet t",
												func(u *Argument, notBefore Fact) {
													isNew := u.Have(
														"j is t",
														"j = t",
														ByArith(below, notBefore))
													u.Show(
														"x is an (r + n + 1)-simplex",
														Simp(Fwd(isNew), Fwd(atNew)),
														By(newFacet[0]))
												})
										})),
									Case(
										"the first t + 1 facets have tail b",
										Derive(func(q *Argument) {
											j := q.FixAs[Nat]("j")
											below := q.Assume()
											q.Cases(q.TermAs[Bool]("j < t"))
											q.When(
												"j is an earlier facet",
												func(u *Argument, before Fact) {
													u.Show(
														"facet j has tail b",
														Simp(Fwd(earlierValues)),
														By(previousFacets[1].At(j), before))
												})
											q.Otherwise(
												"j is the new facet t",
												func(u *Argument, notBefore Fact) {
													isNew := u.Have(
														"j is t",
														"j = t",
														ByArith(below, notBefore))
													u.Show(
														"x has tail b",
														Simp(Fwd(isNew), Fwd(atNew)),
														By(newFacet[1]))
												})
										})),
									Case(
										"the first t + 1 facets carry the faces of k on top",
										Derive(func(q *Argument) {
											j := q.FixAs[Nat]("j")
											below := q.Assume()
											q.Cases(q.TermAs[Bool]("j < t"))
											q.When(
												"j is an earlier facet",
												func(u *Argument, before Fact) {
													u.Show(
														"facet j carries the face j of k on top",
														Simp(Fwd(earlierValues)),
														By(previousFacets[2].At(j), before))
												})
											q.Otherwise(
												"j is the new facet t",
												func(u *Argument, notBefore Fact) {
													isNew := u.Have(
														"j is t",
														"j = t",
														ByArith(below, notBefore))
													u.Show(
														"x carries the face t of k on top",
														Simp(Fwd(isNew), Fwd(atNew)),
														By(newTop))
												})
										})),
									Case(
										"the tail face a of each of the first t + 1 facets j is facet j of y(a)",
										Derive(func(q *Argument) {
											j, face := q.FixAs[Nat]("j"), q.FixAs[Nat]("a")
											indices := q.Assume()
											q.Cases(q.TermAs[Bool]("j < t"))
											q.When(
												"j is an earlier facet",
												func(u *Argument, before Fact) {
													u.Show(
														"the tail face a of facet j is facet j of y(a)",
														Simp(Fwd(earlierValues)),
														By(previousFacets[3].At(j, face), before, indices))
												})
											q.Otherwise(
												"j is the new facet t",
												func(u *Argument, notBefore Fact) {
													isNew := u.Have(
														"j is t",
														"j = t",
														ByArith(indices, notBefore))
													supplied := u.Have(
														"a indexes a supplied face",
														"a ≤ n + 1 ∧ a ≠ i",
														By(indices))
													u.Show(
														"the tail face a of x is facet t of y(a)",
														Simp(Fwd(isNew), Fwd(atNew)),
														By(newTailFaces.At(face), supplied))
												})
										})),
									Case(
										"the first t + 1 facets agree on their common faces",
										Derive(func(q *Argument) {
											l, j := q.FixAs[Nat]("l"), q.FixAs[Nat]("j")
											pair := q.Assume()
											q.Cases(q.TermAs[Bool]("j < t"))
											q.When(
												"j is an earlier facet",
												func(u *Argument, before Fact) {
													lowerBefore := u.Have(
														"the lower facet l precedes t",
														"l < t",
														ByArith(pair, before))
													u.Show(
														"facets l and j agree on their common face",
														Simp(Fwd(earlierValues), Fwd(lowerBefore), Fwd(before)),
														By(previousFacets[4].At(l, j), pair, before))
												})
											q.Otherwise(
												"the later facet j is the new facet t",
												func(u *Argument, notBefore Fact) {
													isNew := u.Have(
														"j is t and l precedes it",
														"j = t ∧ l < t",
														ByArith(pair, notBefore))
													u.Show(
														"x and facet l agree on their common face",
														Simp(Fwd(isNew), Fwd(earlierValues), Fwd(atNew)),
														By(newPrefixFaces.At(l), isNew))
												})
										}))))
						})
				})

			return ctx.Theorem(headline,
				func(a *Argument, X *Expr[simplicial_set.SimplicialOps[A]], quasi Fact, r *Expr[Nat], k *Expr[A]) {
					simplicial := QuasiSimplicialSet.Read(quasi)
					a.Show(
						"the boundary-cone projection is a simplicial map that lifts every non-last horn",
						Simp(Fwd(kan_fibration.LeftFibration)),
						SplitConj(
							Case(
								"the boundary-cone projection is a simplicial map",
								By(simplicial_set.ConeProjectionMap.Read(simplicial).At(r, k))),
							Case(
								"every non-last horn of the boundary cone lifts over its base simplex",
								Derive(func(e *Argument) {
									n, i := e.FixAs[Nat]("n"), e.FixAs[Nat]("i")
									y := e.FixAs[Fun[Nat, Fun[Nat, A]]]("y")
									b := e.FixAs[A]("b")
									horn := e.Conjuncts(
										e.Assume(),
										"the missing face i is not the last",
										"the supplied faces form a face family of the boundary cone",
										"the base simplex b is an (n + 1)-simplex",
										"the faces of b are the projections of the supplied faces")
									hornFamily := e.Conjuncts(
										e.Unfolded(horn[1], simplicial_set.FaceFamilyDef),
										"the supplied faces are simplices of the boundary cone",
										"the supplied faces are compatible")
									hornData := e.Have(
										"each supplied face y(a) is a normalized compatible "+
											"family of (r + n)-simplices with the faces of k on top",
										Statement{
											Binders: "∀a:num.",
											Hypotheses: []string{
												"a ≤ n + 1",
												"a ≠ i",
											},
											Conclusion: "y(a) = normalize_on(0 .. r, junk, y(a)) ∧ " +
												"(∀j:num. j ≤ r ⇒ y(a, j) ∈ X.simplices(r + n)) ∧ " +
												"(∀l j:num. l ≤ r ∧ j ≤ r ∧ l < j ⇒ X.d(r + n, l, y(a, j)) = X.d(r + n, j - 1, y(a, l))) ∧ " +
												"(∀j:num. 0 < r ∧ j ≤ r ⇒ face_iterate_top(r + n, n + 1, y(a, j)) = X.d(r, j, k))",
										},
										BySets(e.Simplified(
											hornFamily[0],
											Fwd(simplicial_set.SimplexBoundaryConeSimplicesDef),
											Fwd(simplicial_set.FaceFamilyDef),
											Fwd(simplicial_set.FacesCompatibleDef),
											Fwd(num_segment.MembershipFromZero),
											Fwd(kan_complex.HornFacesMember))))
									zeroBottom := e.Have(
										"facet 0 of each supplied face y(a) has the face a of b as its tail",
										"∀a:num. a ≤ n + 1 ∧ a ≠ i ⇒ face_iterate_bottom(r + n, r, y(a, 0)) = X.d(n + 1, a, b)",
										By(e.Simplified(
											horn[3],
											Fwd(simplicial_set.FacesFillerDef),
											Fwd(kan_complex.HornFacesMember),
											Fwd(simplicial_set.SimplexBoundaryConeProjectionDef))))
									hornPadding := e.Have(
										"the supplied faces are normalized on 0 .. r",
										"∀a:num. a ≤ n + 1 ∧ a ≠ i ⇒ y(a) = normalize_on(0 .. r, junk, y(a))",
										By(hornData))
									hornMembers := e.Have(
										"every facet of each supplied face is an (r + n)-simplex",
										"∀a j:num. a ≤ n + 1 ∧ a ≠ i ∧ j ≤ r ⇒ y(a, j) ∈ X.simplices(r + n)",
										Derive(func(f *Argument) {
											face, j := f.FixAs[Nat]("a"), f.FixAs[Nat]("j")
											indices := f.Assume()
											cone := f.Conjuncts(
												GroupPremises(indices, hornData.At(face)),
												"y(a) is normalized on 0 .. r",
												"every facet of y(a) is an (r + n)-simplex",
												"the facets of y(a) agree on their common faces",
												"every facet of y(a) carries the corresponding face of k on top")
											f.Show(
												"facet j of y(a) is an (r + n)-simplex",
												By(cone[1].At(j), indices))
										}))
									hornPrefix := e.Have(
										"the facets of each supplied face agree on their common faces",
										Statement{
											Binders: "∀a l j:num.",
											Hypotheses: []string{
												"a ≤ n + 1",
												"a ≠ i",
												"l < j",
												"j ≤ r",
											},
											Conclusion: "X.d(r + n, l, y(a, j)) = X.d(r + n, j - 1, y(a, l))",
										},
										Derive(func(f *Argument) {
											face, l, j := f.FixAs[Nat]("a"), f.FixAs[Nat]("l"), f.FixAs[Nat]("j")
											indices := f.Assume()
											cone := f.Conjuncts(
												GroupPremises(indices, hornData.At(face)),
												"y(a) is normalized on 0 .. r",
												"every facet of y(a) is an (r + n)-simplex",
												"the facets of y(a) agree on their common faces",
												"every facet of y(a) carries the corresponding face of k on top")
											lower := f.Have(
												"the lower facet index l is at most r",
												"l ≤ r",
												ByArith(indices))
											f.Show(
												"facets l and j of y(a) agree on their common face",
												By(cone[2].At(l, j), indices, lower))
										}))
									hornTop := e.Have(
										"facet j of each supplied face carries the face j of k on top",
										Statement{
											Binders: "∀a j:num.",
											Hypotheses: []string{
												"a ≤ n + 1",
												"a ≠ i",
												"0 < r",
												"j ≤ r",
											},
											Conclusion: "face_iterate_top(r + n, n + 1, y(a, j)) = X.d(r, j, k)",
										},
										Derive(func(f *Argument) {
											face, j := f.FixAs[Nat]("a"), f.FixAs[Nat]("j")
											indices := f.Assume()
											cone := f.Conjuncts(
												GroupPremises(indices, hornData.At(face)),
												"y(a) is normalized on 0 .. r",
												"every facet of y(a) is an (r + n)-simplex",
												"the facets of y(a) agree on their common faces",
												"every facet of y(a) carries the corresponding face of k on top")
											f.Show(
												"facet j of y(a) carries the face j of k on top",
												By(cone[3].At(j), indices))
										}))
									suppliedCompatible := e.Simplified(
										hornFamily[1],
										Fwd(simplicial_set.FacesCompatibleDef),
										Fwd(simplicial_set.SimplexBoundaryConeFaceDef))
									tailCompatibility := e.Have(
										"for supplied faces a < c, facets j of y(a) and y(c) agree on their common tail face",
										Statement{
											Binders: "∀a c j:num.",
											Hypotheses: []string{
												"a < c",
												"c ≤ n + 1",
												"a ≠ i",
												"c ≠ i",
												"j ≤ r",
											},
											Conclusion: "X.d(r + n, r + a, y(c, j)) = X.d(r + n, r + c - 1, y(a, j))",
										},
										Derive(func(f *Argument) {
											first, last := f.FixAs[Nat]("a"), f.FixAs[Nat]("c")
											f.FixAs[Nat]("j")
											indices := f.Assume()
											pair := f.Have(
												"a < c are faces of the horn",
												"a ∈ horn_faces(n, i) ∧ c ∈ horn_faces(n, i) ∧ a < c",
												ByArith(
													indices,
													kan_complex.HornFacesMember.At(n, i, first),
													kan_complex.HornFacesMember.At(n, i, last)))
											live := f.Have(
												"the facet index j lies in 0 .. r",
												"j ≤ r",
												ByArith(indices))
											normalized := f.Have(
												"the compatibility of y(a) and y(c), read at facet j",
												"normalize_on(0 .. r, junk, λl:num. X.d(r + n, r + a, y(c, l)), j) = "+
													"normalize_on(0 .. r, junk, λl:num. X.d(r + n, r + (c - 1), y(a, l)), j)",
												By(suppliedCompatible.At(first, last), pair))
											pointwise := f.Simplified(normalized, Fwd(num_segment.NormalizeOnSegmentIn), Fwd(live))
											shift := f.Have(
												"shifting the predecessor index commutes with adding r",
												"r + (c - 1) = r + c - 1",
												ByArith(indices))
											f.Show(
												"facets j of y(a) and y(c) agree on their common tail face",
												Simp(Rev(shift), Fwd(pointwise)),
												Basic())
										}))
									z, allFacets := e.ObtainAs[Fun[Nat, A]](
										"take r + 1 facets with tail b, the faces of k on top and the supplied faces as tail faces",
										"∃z:(num → A). "+
											"    (∀j:num. j < r + 1 ⇒ z(j) ∈ X.simplices(r + n + 1)) ∧ "+
											"    (∀j:num. j < r + 1 ⇒ face_iterate_bottom(r + n + 1, r, z(j)) = b) ∧ "+
											"    (∀j:num. 0 < r ∧ j < r + 1 ⇒ face_iterate_top(r + n + 1, n + 2, z(j)) = X.d(r, j, k)) ∧ "+
											"    (∀j a:num. j < r + 1 ∧ a ≤ n + 1 ∧ a ≠ i ⇒ X.d(r + n + 1, r + a, z(j)) = y(a, j)) ∧ "+
											"    (∀l j:num. l < j ∧ j < r + 1 ⇒ X.d(r + n + 1, l, z(j)) = X.d(r + n + 1, j - 1, z(l)))",
										Derive(func(f *Argument) {
											f.Cases(f.TermAs[Bool]("r = 0"))
											f.When(
												"the fixed prefix k is a vertex, and b itself is the one facet",
												func(g *Argument, vertex Fact) {
													degree := g.Have(
														"with r = 0 a facet is an (n + 1)-simplex",
														"r + n + 1 = n + 1",
														ByArith(vertex))
													g.Take(g.TermAs[Fun[Nat, A]]("λj:num. b"))
													g.Show(
														"the constant family at b meets every facet condition",
														SplitConjAll(
															Case(
																"b is an (n + 1)-simplex",
																Simp(Fwd(degree)),
																By(horn[2])),
															Case(
																"with r = 0 the tail of b is b itself",
																Simp(Fwd(vertex), Fwd(simplicial_set.FaceIterateBottomDef)),
																Basic()),
															Case(
																"with r = 0 the condition on top is vacuous",
																ByArith(vertex)),
															Case(
																"the tail faces of b are the facets 0 of the supplied faces",
																Derive(func(m *Argument) {
																	m.FixAs[Nat]("j")
																	face := m.FixAs[Nat]("a")
																	indices := m.Assume()
																	atZero := m.Have(
																		"the one facet index is 0",
																		"j = 0",
																		ByArith(indices, vertex))
																	unshifted := m.Have(
																		"r = 0 leaves the degree and the tail index unshifted",
																		"r + n + 1 = n + 1 ∧ r + a = a",
																		ByArith(vertex))
																	zeroFace := m.Simplified(
																		GroupPremises(indices, zeroBottom.At(face)),
																		Fwd(vertex),
																		Fwd(simplicial_set.FaceIterateBottomDef))
																	m.Show(
																		"the face a of b is facet 0 of y(a)",
																		Simp(Fwd(atZero), Fwd(unshifted)),
																		By(zeroFace))
																})),
															Case(
																"one facet has no pair of faces to compare",
																ByArith(vertex))))
												})
											f.Otherwise(
												"the fixed prefix k has positive dimension, and the facets are built one at a time",
												func(g *Argument, nonzero Fact) {
													positive := g.Have(
														"the fixed prefix k has positive dimension",
														"0 < r",
														ByArith(nonzero))
													g.Show(
														"the construction reaches all r + 1 facets",
														ByArith(
															At(firstFacets, X, r, k, n, i, y, b, g.TermAs[Nat]("r + 1")),
															quasi,
															positive,
															horn[0],
															horn[2],
															hornMembers,
															hornPrefix,
															hornTop,
															tailCompatibility,
															zeroBottom))
												})
										}),
										Named("z"))
									facets := e.Conjuncts(
										allFacets,
										"the r + 1 facets are (r + n + 1)-simplices",
										"each facet has tail b",
										"facet j carries the face j of k on top",
										"the tail face a of facet j is facet j of y(a)",
										"the facets agree on their common faces")
									normalizedFamilyDef := e.Let("V", e.TermAs[Fun[Nat, A]]("normalize_on(0 .. r, junk, z)"))
									degrees := e.Have(
										"in degree n + 1 a facet is an (r + n + 1)-simplex with n + 2 tail vertices",
										"r + (n + 1) = r + n + 1 ∧ n + 1 + 1 = n + 2",
										ByArith())
									values := e.Have(
										"V(j) is facet j for every j ≤ r",
										"∀j:num. j ≤ r ⇒ V(j) = z(j)",
										Derive(func(f *Argument) {
											f.FixAs[Nat]("j")
											live := f.Assume()
											f.Show(
												"normalization on 0 .. r keeps facet j",
												Simp(Fwd(normalizedFamilyDef), Fwd(num_segment.NormalizeOnSegmentIn), Fwd(live)),
												Basic())
										}))
									members := e.Have(
										"every facet is an (r + n + 1)-simplex",
										"∀j:num. j ∈ 0 .. r ⇒ z(j) ∈ X.simplices(r + (n + 1))",
										Derive(func(f *Argument) {
											j := f.FixAs[Nat]("j")
											live := f.Assume()
											atMost := f.Have(
												"j is at most r",
												"j ≤ r",
												By(live))
											among := f.Have(
												"j is among the r + 1 facets",
												"j < r + 1",
												ByArith(atMost))
											f.Show(
												"facet j is an (r + n + 1)-simplex",
												Simp(Fwd(degrees)),
												By(facets[0].At(j), among))
										}))
									compatible := e.Have(
										"the facets agree on their common faces",
										Statement{
											Binders: "∀l j:num.",
											Hypotheses: []string{
												"l ∈ 0 .. r",
												"j ∈ 0 .. r",
												"l < j",
											},
											Conclusion: "X.d(r + (n + 1), l, z(j)) = X.d(r + (n + 1), j - 1, z(l))",
										},
										Derive(func(f *Argument) {
											l, j := f.FixAs[Nat]("l"), f.FixAs[Nat]("j")
											live := f.Assume()
											atMost := f.Have(
												"l < j and j is at most r",
												"l < j ∧ j ≤ r",
												By(live))
											among := f.Have(
												"l < j are among the r + 1 facets",
												"l < j ∧ j < r + 1",
												ByArith(atMost))
											f.Show(
												"facets l and j agree on their common face",
												Simp(Fwd(degrees)),
												By(facets[4].At(l, j), among))
										}))
									family := e.Have(
										"the facets form a face family on 0 .. r",
										"face_family(r + (n + 1), 0 .. r, z)",
										Simp(Fwd(simplicial_set.FaceFamilyDef), Fwd(simplicial_set.FacesCompatibleDef)),
										By(members, compatible))
									fixedTop := e.Have(
										"every facet j carries the face j of k on top",
										"∀j:num. 0 < r ∧ j ≤ r ⇒ face_iterate_top(r + (n + 1), n + 1 + 1, z(j)) = X.d(r, j, k)",
										Derive(func(f *Argument) {
											j := f.FixAs[Nat]("j")
											indices := f.Assume()
											among := f.Have(
												"j is among the r + 1 facets",
												"0 < r ∧ j < r + 1",
												ByArith(indices))
											f.Show(
												"facet j carries the face j of k on top",
												Simp(Fwd(degrees)),
												By(facets[2].At(j), among))
										}))
									coneMember := e.Have(
										"V is a simplex of the boundary cone",
										"V ∈ simplex_boundary_cone_simplices(X, r, k, n + 1)",
										Simp(Fwd(normalizedFamilyDef)),
										By(
											At(
												simplicial_set.BoundaryConeMembership,
												e.TermAs[simplicial_set.SimplicialOps[A]]("X"),
												r,
												e.TermAs[Nat]("n + 1"),
												k,
												z),
											family,
											fixedTop))
									coneFaces := e.Have(
										"the face a of V is the supplied face y(a)",
										"∀a:num. a ≤ n + 1 ∧ a ≠ i ⇒ simplex_boundary_cone_face(r, n + 1, a, V) = y(a)",
										Derive(func(f *Argument) {
											face := f.FixAs[Nat]("a")
											supplied := f.Assume()
											normalized := f.Have(
												"on 0 .. r the tail faces a of the facets of V are the facets of y(a)",
												"normalize_on(0 .. r, junk, λj:num. X.d(r + (n + 1), r + a, V(j))) = "+
													"normalize_on(0 .. r, junk, y(a))",
												Simp(Fwd(functions.NormalizeOnEqIff)),
												Derive(func(g *Argument) {
													x := g.FixAs[Nat]("x")
													live := g.Assume()
													atMost := g.Have(
														"x is at most r",
														"x ≤ r",
														By(live))
													among := g.Have(
														"x is among the r + 1 facets",
														"x < r + 1",
														ByArith(atMost))
													tailFace := g.Have(
														"the tail face a of facet x is facet x of y(a)",
														"X.d(r + n + 1, r + a, z(x)) = y(a, x)",
														By(facets[3].At(x, face), among, supplied))
													g.Show(
														"the tail face a of V(x) is facet x of y(a)",
														Simp(Fwd(values), Fwd(degrees), Fwd(tailFace)),
														Basic())
												}))
											f.Show(
												"the face a of V is y(a), which is normalized on 0 .. r",
												Simp(Fwd(simplicial_set.SimplexBoundaryConeFaceDef)),
												By(normalized, hornPadding.At(face), supplied))
										}))
									fills := e.Have(
										"V has the supplied faces as its horn faces",
										"faces_filler(simplex_boundary_cone_face(r), n, horn_faces(n, i), y, V)",
										Simp(Fwd(simplicial_set.FacesFillerDef), Fwd(kan_complex.HornFacesMember)),
										By(coneFaces))
									zeroValue := e.Have(
										"V(0) is facet 0",
										"V(0) = z(0)",
										ByArith(values.At(e.TermAs[Nat]("0"))))
									zeroTail := e.Have(
										"facet 0 has tail b",
										"face_iterate_bottom(r + n + 1, r, z(0)) = b",
										ByArith(facets[1].At(e.TermAs[Nat]("0"))))
									projects := e.Have(
										"V projects to the base simplex b",
										"simplex_boundary_cone_projection(r, n + 1, V) = b",
										Simp(
											Fwd(simplicial_set.SimplexBoundaryConeProjectionDef),
											Fwd(zeroValue),
											Fwd(degrees),
											Fwd(zeroTail)),
										Basic())
									e.Take(e.TermAs[Fun[Nat, A]]("V"))
									e.Show(
										"V lifts the horn over b",
										By(coneMember, fills, projects))
								}))))
				})
		}),
	Reading: "Compatibility implies that every prefix facet has the same tail as " +
		"facet 0, so the supplied base simplex controls them all. Each facet may " +
		"require several inner fills through PartialConeHornFill; the outer " +
		"construction is an induction on its numeric index, not on a lattice of subsets.",
})}
