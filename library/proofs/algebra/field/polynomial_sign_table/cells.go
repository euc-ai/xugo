// cells.go — the cells of increasing cuts, read at an index: an even cell is
// an open interval and an odd one a cut, every cell holds a point, an open
// cell is infinite and convex, a member of a sign table whose sign on an open
// cell is zero is the zero polynomial, and a polynomial over a real closed
// field without a root in an open cell keeps one sign there.

package polynomial_sign_table

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// SignCellInCarrier — every point of a cell of cuts lies in the carrier: the
// cells are cut out of the carrier, whatever the cuts and the index.
var SignCellInCarrier = signCellInCarrierThm{family.Add(registry.ProofEntry{
	Name: "SignCellInCarrier",
	Key:  "prop_26f1c808cef7d7b1",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀k:num. ∀r:(num → A). ∀j:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ polynomial_sign_cell(F, lt, k, r, j)",
		},
		Conclusion: "x ∈ F.carrier",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		k *Expr[Nat],
		r *Arrow[Nat, A],
		j *Expr[Nat],
		x *Expr[A],
		member Fact,
	) {
		a.Show(
			"a cell is a set of points of the carrier",
			By(a.Unfolded(member, SignCellDef)))
	}),
})}

// OpenCellMember — the even cell 2i of k cuts, for i ≤ k, is the open
// interval of index i: the points of the carrier above the cut r(i − 1),
// unless i = 0, and below the cut r(i), unless i = k. Its index is even, so
// it is no cut cell, and 2i = 2i′ names the interval of index i′ = i.
var OpenCellMember = openCellMemberThm{family.Add(registry.ProofEntry{
	Name: "OpenCellMember",
	Key:  "prop_7ed20be492afc8e4",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀k:num. ∀r:(num → A). ∀i:num. ∀x:A.",
		Hypotheses: []string{
			"i ≤ k",
		},
		Conclusion: "x ∈ polynomial_sign_cell(F, lt, k, r, 2 * i) ⇔ " +
			"x ∈ F.carrier ∧ (i = 0 ∨ lt(r(i - 1), x)) ∧ (i = k ∨ lt(x, r(i)))",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		k *Expr[Nat],
		r *Arrow[Nat, A],
		i *Expr[Nat],
		x *Expr[A],
		iLe Fact,
	) {
		a.Iff()
		a.Forward(
			"a point of cell 2i lies in the open interval of index i",
			func(b *Argument, member Fact) {
				parts := b.Conjuncts(
					b.Unfolded(member, SignCellDef),
					"x lies in the carrier",
					"x is a cut of odd cell index 2i, or lies in an open interval of cell index 2i")
				b.Show(
					"an even index names no cut, and the interval of cell index 2i is the one of index i",
					parts[1].SplitDisj(
						LeftHolds(
							"a cut has an odd cell index",
							Given(func(c *Argument, cut Fact) {
								_, at := c.UnpackAs[Nat](cut, "j")
								c.Show(
									"2i is not 2j + 1",
									ByArith(at))
							})),
						RightHolds(
							"the open interval of index j, with 2i = 2j",
							Given(func(c *Argument, open Fact) {
								_, at := c.UnpackAs[Nat](open, "j")
								same := c.Have(
									"2i = 2j gives j = i",
									"j = i",
									ByArith(at))
								c.Show(
									"so x lies in the open interval of index i",
									By(parts[0], same, at))
							}))))
			})
		a.Backward(
			"a point of the open interval of index i lies in cell 2i",
			func(b *Argument, open Fact) {
				b.Show(
					"the interval of index i is cell 2i",
					Simp(Fwd(SignCellDef)),
					By(iLe, open))
			})
	}),
})}

// CutCellMember — the odd cell 2i + 1 of k cuts, for i < k, is the single
// cut r(i): its index is odd, so it is no open interval, and 2i + 1 =
// 2i′ + 1 names the cut of index i′ = i.
var CutCellMember = cutCellMemberThm{family.Add(registry.ProofEntry{
	Name: "CutCellMember",
	Key:  "prop_ee9506d475614e76",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀k:num. ∀r:(num → A). ∀i:num. ∀x:A.",
		Hypotheses: []string{
			"i < k",
		},
		Conclusion: "x ∈ polynomial_sign_cell(F, lt, k, r, 2 * i + 1) ⇔ x ∈ F.carrier ∧ x = r(i)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		k *Expr[Nat],
		r *Arrow[Nat, A],
		i *Expr[Nat],
		x *Expr[A],
		iLt Fact,
	) {
		a.Iff()
		a.Forward(
			"a point of cell 2i + 1 is the cut r(i)",
			func(b *Argument, member Fact) {
				parts := b.Conjuncts(
					b.Unfolded(member, SignCellDef),
					"x lies in the carrier",
					"x is a cut of cell index 2i + 1, or lies in an open interval of cell index 2i + 1")
				b.Show(
					"the cut of cell index 2i + 1 is r(i), and an odd index names no open interval",
					parts[1].SplitDisj(
						LeftHolds(
							"the cut r(j), with 2i + 1 = 2j + 1",
							Given(func(c *Argument, cut Fact) {
								_, at := c.UnpackAs[Nat](cut, "j")
								same := c.Have(
									"2i + 1 = 2j + 1 gives j = i",
									"j = i",
									ByArith(at))
								c.Show(
									"so x is the cut r(i)",
									By(Normalized, parts[0], same, at))
							})),
						RightHolds(
							"an open interval has an even cell index",
							Given(func(c *Argument, open Fact) {
								_, at := c.UnpackAs[Nat](open, "j")
								c.Show(
									"2i + 1 is not 2j",
									ByArith(at))
							}))))
			})
		a.Backward(
			"the cut r(i) lies in cell 2i + 1",
			func(b *Argument, cut Fact) {
				b.Show(
					"r(i) is the cut of cell index 2i + 1",
					Simp(Fwd(SignCellDef)),
					By(iLt, cut))
			})
	}),
})}

// SignCellsNonempty — every cell of increasing cuts in an ordered field
// holds a point: a cut cell holds its cut; an open interval holds zero when
// there are no cuts, a point beyond its cut when it is a ray, as an ordered
// field has no endpoints, and a point between its two cuts by density.
var SignCellsNonempty = signCellsNonemptyThm{family.Add(registry.ProofEntry{
	Name: "SignCellsNonempty",
	Key:  "prop_257ee2c977151059",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀k:num. ∀r:(num → A). ∀l:num.",
		Hypotheses: []string{
			"ordered_field_on(F, lt)",
			"increasing_cuts(F, lt, k, r)",
			"l ≤ 2 * k",
		},
		Conclusion: "polynomial_sign_cell(F, lt, k, r, l) ≠ ∅",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		k *Expr[Nat],
		r *Arrow[Nat, A],
		l *Expr[Nat],
		ordered, cuts, bound Fact,
	) {
		bounds := a.Conjuncts(
			a.Unfolded(cuts, ordered_field.IncreasingCutsDef),
			"the cuts lie in the carrier",
			"the cuts increase")
		cutsIn, increasing := bounds[0], bounds[1]
		ring := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
		a.Do(GroupPremises(bound, nat_parity.DoubleOrSucDoubleBelow.At(k, l)).SplitDisj(
			LeftHolds(
				"an even index names an open interval",
				Given(func(b *Argument, even Fact) {
					i, shape := b.UnpackAs[Nat](even, "i")
					half := b.Conjuncts(
						shape,
						"i is at most k",
						"l is twice i")
					iLe, lEq := half[0], half[1]
					x, xIs := b.ObtainAs[A](
						"a point x of that open interval",
						"∃x:A. x ∈ F.carrier ∧ (i = 0 ∨ lt(r(i - 1), x)) ∧ (i = k ∨ lt(x, r(i)))",
						Derive(func(c *Argument) {
							c.Cases(c.TermAs[Bool]("i = 0"))
							c.When(
								"the first interval",
								func(d *Argument, first Fact) {
									d.Cases(d.TermAs[Bool]("i = k"))
									d.When(
										"with no cuts the one interval is the carrier, which holds zero",
										func(e *Argument, last Fact) {
											e.Take(e.TermAs[A]("F.zero"))
											e.Show(
												"zero lies in the carrier",
												By(last, first, comm_ring.ZeroIn.Read(ring)))
										})
									d.Otherwise(
										"the left ray holds a point below the first cut",
										func(e *Argument, notLast Fact) {
											early := e.Have(
												"i is a cut index",
												"i < k",
												ByArith(notLast, iLe))
											y, below := e.ObtainAs[A](
												"a point below the cut r(i)",
												"∃y:A. y ∈ F.carrier ∧ lt(y, r(i))",
												By(cutsIn.At(i), early, ordered_field.NoEndpoints.Read(ordered)))
											e.Take(y)
											e.Show(
												"it lies in the left ray",
												By(first, below))
										})
								})
							c.Otherwise(
								"a later interval",
								func(d *Argument, notFirst Fact) {
									d.Cases(d.TermAs[Bool]("i = k"))
									d.When(
										"the right ray holds a point above the last cut",
										func(e *Argument, last Fact) {
											previous := e.Have(
												"i − 1 is a cut index",
												"i - 1 < k",
												ByArith(notFirst, iLe))
											z, above := e.ObtainAs[A](
												"a point above the cut r(i − 1)",
												"∃z:A. z ∈ F.carrier ∧ lt(r(i - 1), z)",
												By(cutsIn.At(e.TermAs[Nat]("i - 1")), previous, ordered_field.NoEndpoints.Read(ordered)))
											e.Take(z)
											e.Show(
												"it lies in the right ray",
												By(last, above))
										})
									d.Otherwise(
										"an interval between two cuts holds a point between them",
										func(e *Argument, notLast Fact) {
											consecutive := e.Have(
												"the two cuts are in order",
												"lt(r(i - 1), r(i))",
												ByArith(notLast, notFirst, increasing, iLe))
											both := e.Have(
												"both cuts lie in the carrier",
												"r(i - 1) ∈ F.carrier ∧ r(i) ∈ F.carrier",
												ByArith(notLast, notFirst, cutsIn, iLe))
											e.Show(
												"the order is dense",
												By(consecutive, both, ordered_field.DenseOrder.Read(ordered)))
										})
								})
						}))
					inCell := b.Have(
						"x lies in the cell 2i",
						"x ∈ polynomial_sign_cell(F, lt, k, r, l)",
						By(xIs, lEq, OpenCellMember.At(F, lt, k, r, i, x), iLe))
					b.Show(
						"so the cell is not empty",
						BySets(inCell))
				})),
			RightHolds(
				"an odd index names a cut",
				Given(func(b *Argument, odd Fact) {
					i, index := b.UnpackAs[Nat](odd, "i")
					inCell := b.Have(
						"the cut r(i) lies in the cell 2i + 1",
						"r(i) ∈ polynomial_sign_cell(F, lt, k, r, l)",
						By(Normalized, index, cutsIn.At(i), CutCellMember.At(F, lt, k, r, i, r.Apply(i))))
					b.Show(
						"so the cell is not empty",
						BySets(inCell))
				}))))
	}),
})}

// OpenCellConvex — an open cell of cuts in an ordered field holds every
// point of the carrier between two of its points: the lower cut lies below
// the lower point, hence below the point between, and the upper cut above
// the upper point, hence above the point between.
var OpenCellConvex = openCellConvexThm{family.Add(registry.ProofEntry{
	Name: "OpenCellConvex",
	Key:  "prop_3ec3ae72024928a7",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀k:num. ∀r:(num → A). ∀i:num. ∀x y z:A.",
		Hypotheses: []string{
			"ordered_field_on(F, lt)",
			"∀j:num. j < k ⇒ r(j) ∈ F.carrier",
			"i ≤ k",
			"x ∈ polynomial_sign_cell(F, lt, k, r, 2 * i)",
			"y ∈ polynomial_sign_cell(F, lt, k, r, 2 * i)",
			"z ∈ F.carrier",
			"ordered_le(lt, x, z)",
			"ordered_le(lt, z, y)",
		},
		Conclusion: "z ∈ polynomial_sign_cell(F, lt, k, r, 2 * i)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		k *Expr[Nat],
		r *Arrow[Nat, A],
		i *Expr[Nat],
		x, y, z *Expr[A],
		ordered, cutsIn, iLe, xIn, yIn, zIn, xz, zy Fact,
	) {
		transitive := ordered_field.Transitive.Read(ordered).AsFact()
		xOpen := a.Have(
			"x lies in the carrier, in the open interval of index i",
			"x ∈ F.carrier ∧ (i = 0 ∨ lt(r(i - 1), x)) ∧ (i = k ∨ lt(x, r(i)))",
			By(xIn, iLe, OpenCellMember.At(F, lt, k, r, i, x)))
		yOpen := a.Have(
			"y lies in the carrier, in the open interval of index i",
			"y ∈ F.carrier ∧ (i = 0 ∨ lt(r(i - 1), y)) ∧ (i = k ∨ lt(y, r(i)))",
			By(yIn, iLe, OpenCellMember.At(F, lt, k, r, i, y)))
		lower := a.Have(
			"z lies above the lower cut, as x does",
			"i = 0 ∨ lt(r(i - 1), z)",
			Derive(func(b *Argument) {
				b.Cases(b.TermAs[Bool]("i = 0"))
				b.When(
					"the first interval has no lower cut",
					func(c *Argument, first Fact) {
						c.Show(
							"nothing to clear",
							By(first))
					})
				b.Otherwise(
					"a later interval",
					func(c *Argument, notFirst Fact) {
						previous := c.Have(
							"its lower cut lies in the carrier",
							"r(i - 1) ∈ F.carrier",
							ByArith(cutsIn, notFirst, iLe))
						c.Show(
							"by transitivity through x",
							By(
								notFirst,
								xOpen,
								xz,
								ordered_field.OrderedLeDef.At(lt, x, z),
								transitive.At(c.TermAs[A]("r(i - 1)"), x, z),
								previous,
								zIn))
					})
			}))
		upper := a.Have(
			"z lies below the upper cut, as y does",
			"i = k ∨ lt(z, r(i))",
			Derive(func(b *Argument) {
				b.Cases(b.TermAs[Bool]("i = k"))
				b.When(
					"the last interval has no upper cut",
					func(c *Argument, last Fact) {
						c.Show(
							"nothing to stay below",
							By(last))
					})
				b.Otherwise(
					"an earlier interval",
					func(c *Argument, notLast Fact) {
						current := c.Have(
							"its upper cut lies in the carrier",
							"r(i) ∈ F.carrier",
							ByArith(cutsIn, notLast, iLe))
						c.Show(
							"by transitivity through y",
							By(
								Normalized,
								notLast,
								yOpen,
								zy,
								ordered_field.OrderedLeDef.At(lt, z, y),
								transitive.At(z, y, c.TermAs[A]("r(i)")),
								current,
								zIn))
					})
			}))
		a.Show(
			"so z lies in the open interval of index i",
			By(zIn, lower, upper, iLe, OpenCellMember.At(F, lt, k, r, i, z)))
	}),
})}

// OpenCellInfinite — an open cell of increasing cuts in an ordered field is
// infinite: it holds a point, so a finite one would have a greatest point m,
// and the cell holds a point above m — beyond m when the cell is the right
// ray, between m and the upper cut otherwise.
var OpenCellInfinite = openCellInfiniteThm{family.Add(registry.ProofEntry{
	Name: "OpenCellInfinite",
	Key:  "prop_941c3fc4be61782c",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀k:num. ∀r:(num → A). ∀i:num.",
		Hypotheses: []string{
			"ordered_field_on(F, lt)",
			"increasing_cuts(F, lt, k, r)",
			"i ≤ k",
		},
		Conclusion: "¬finite(polynomial_sign_cell(F, lt, k, r, 2 * i))",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		k *Expr[Nat],
		r *Arrow[Nat, A],
		i *Expr[Nat],
		ordered, cuts, iLe Fact,
	) {
		cutsIn := a.Conjuncts(
			a.Unfolded(cuts, ordered_field.IncreasingCutsDef),
			"the cuts lie in the carrier",
			"the cuts increase")[0]
		transitive := ordered_field.Transitive.Read(ordered).AsFact()
		irreflexive := ordered_field.Irreflexive.Read(ordered).AsFact()
		cell := a.TermAs[Set[A]]("polynomial_sign_cell(F, lt, k, r, 2 * i)")
		finiteCell := a.Have(
			"suppose the cell were finite",
			"finite(polynomial_sign_cell(F, lt, k, r, 2 * i))",
			By(a.SupposeNot()))
		index := a.Have(
			"2i is a cell index",
			"2 * i ≤ 2 * k",
			ByArith(iLe))
		inhabited := a.Have(
			"the cell holds a point",
			"polynomial_sign_cell(F, lt, k, r, 2 * i) ≠ ∅",
			By(ordered, cuts, index, SignCellsNonempty.At(F, lt, k, r, a.TermAs[Nat]("2 * i"))))
		within := a.Have(
			"the cell lies in the carrier",
			"polynomial_sign_cell(F, lt, k, r, 2 * i) ⊆ F.carrier",
			Simp(Fwd(SignCellDef)),
			BySets())
		m, greatest := a.UnpackAs[A](
			GroupPremises(ordered, finiteCell, inhabited, within, ordered_field.FiniteGreatest.At(F, lt, cell)),
			"m")
		top := a.Conjuncts(
			greatest,
			"m lies in the cell",
			"every point of the cell is at most m")
		mOpen := a.Have(
			"m lies in the open interval of index i",
			"m ∈ F.carrier ∧ (i = 0 ∨ lt(r(i - 1), m)) ∧ (i = k ∨ lt(m, r(i)))",
			By(top[0], iLe, OpenCellMember.At(F, lt, k, r, i, m)))
		lowerIn := a.Have(
			"the lower cut, if any, lies below every point of the carrier above m, as it lies below m",
			"∀z:A. z ∈ F.carrier ∧ lt(m, z) ⇒ i = 0 ∨ lt(r(i - 1), z)",
			Derive(func(b *Argument) {
				z := b.FixAs[A]("z")
				pastM := b.Assume()
				b.Cases(b.TermAs[Bool]("i = 0"))
				b.When(
					"no lower cut",
					func(c *Argument, first Fact) {
						c.Show(
							"nothing to clear",
							By(first))
					})
				b.Otherwise(
					"the lower cut lies in the carrier",
					func(c *Argument, notFirst Fact) {
						previous := c.Have(
							"r(i − 1) lies in the carrier",
							"r(i - 1) ∈ F.carrier",
							ByArith(cutsIn, notFirst, iLe))
						c.Show(
							"by transitivity through m",
							By(notFirst, mOpen, pastM, previous, transitive.At(c.TermAs[A]("r(i - 1)"), m, z)))
					})
			}))
		z, above := a.ObtainAs[A](
			"a point z of the cell above m",
			"∃z:A. z ∈ polynomial_sign_cell(F, lt, k, r, 2 * i) ∧ lt(m, z)",
			Derive(func(b *Argument) {
				b.Cases(b.TermAs[Bool]("i = k"))
				b.When(
					"the right ray holds a point beyond m",
					func(c *Argument, last Fact) {
						z, beyond := c.ObtainAs[A](
							"a point z above m",
							"∃z:A. z ∈ F.carrier ∧ lt(m, z)",
							By(mOpen, ordered_field.NoEndpoints.Read(ordered)))
						c.Take(z)
						c.Show(
							"z lies in the right ray",
							By(beyond, lowerIn.At(z), last, iLe, OpenCellMember.At(F, lt, k, r, i, z)))
					})
				b.Otherwise(
					"between m and the upper cut lies another point of the cell",
					func(c *Argument, notLast Fact) {
						current := c.Have(
							"the upper cut lies in the carrier",
							"r(i) ∈ F.carrier",
							ByArith(cutsIn, notLast, iLe))
						z, between := c.ObtainAs[A](
							"a point z between m and r(i)",
							"∃z:A. z ∈ F.carrier ∧ lt(m, z) ∧ lt(z, r(i))",
							By(mOpen, notLast, current, ordered_field.DenseOrder.Read(ordered)))
						c.Take(z)
						c.Show(
							"z lies in the open interval",
							By(between, lowerIn.At(z), iLe, OpenCellMember.At(F, lt, k, r, i, z)))
					})
			}))
		zParts := a.Conjuncts(
			above,
			"z lies in the cell",
			"m lies below z")
		zIn := a.Have(
			"z lies in the carrier",
			"z ∈ F.carrier",
			BySets(zParts[0], within))
		a.Show(
			"z would be at most m and above it",
			By(
				zParts[1],
				top[1].At(z),
				zParts[0],
				ordered_field.OrderedLeDef.At(lt, z, m),
				irreflexive.At(m),
				transitive.At(m, z, m),
				mOpen,
				zIn))
	}),
})}

// VanishingOnOpenCell — a member of a sign table that is a polynomial over
// the carrier and has sign zero on an open cell is the zero polynomial: it
// vanishes at every point of the cell, which is infinite, while a nonzero
// polynomial over a field has finitely many roots.
var VanishingOnOpenCell = vanishingOnOpenCellThm{family.Add(registry.ProofEntry{
	Name: "VanishingOnOpenCell",
	Key:  "prop_f235433fe382ffae",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀m:num. " +
			"∀f:(num → num → A). " +
			"∀k:num. " +
			"∀r:(num → A). " +
			"∀t:(num → num → int). " +
			"∀i l:num.",
		Hypotheses: []string{
			"ordered_field_on(F, lt)",
			"polynomial_family_sign_table(F, lt, m, f, k, r, t)",
			"i < m",
			"polynomial_over(F.carrier, f(i))",
			"l ≤ k",
			"t(2 * l, i) = &0",
		},
		Conclusion: "f(i) = vec_zero",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		m *Expr[Nat],
		f *Arrow[Nat, Fun[Nat, A]],
		k *Expr[Nat],
		r *Arrow[Nat, A],
		t *Arrow2[Nat, Nat, Int],
		i, l *Expr[Nat],
		ordered, table, iLt, over, lLe, zeroSign Fact,
	) {
		parts := a.Conjuncts(
			a.Unfolded(table, PolynomialFamilySignTableDef),
			"the cuts increase in the carrier",
			"every cell is nonempty",
			"each member keeps the sign t(j, i) on cell j")
		cuts, signs := parts[0], parts[2]
		nonzero := a.SupposeNot()
		domain := integral_domain.FieldIntegralDomain.Read(ordered_field.FieldOn.Read(ordered))
		fewRoots := a.Have(
			"a nonzero polynomial over a field has finitely many roots",
			"finite(polynomial_roots(F.carrier, f(i)))",
			By(over, nonzero, polynomial_roots.RootBound.Read(domain).At(f.Apply(i))))
		index := a.Have(
			"2l is a cell index",
			"2 * l ≤ 2 * k",
			ByArith(lLe))
		vanishes := a.Have(
			"f(i) vanishes at every point of the cell",
			Statement{
				Binders: "∀x:A.",
				Hypotheses: []string{
					"x ∈ polynomial_sign_cell(F, lt, k, r, 2 * l)",
				},
				Conclusion: "x ∈ F.carrier ∧ polynomial_eval(f(i), x) = F.zero",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				member := b.Assume()
				xIn := b.Have(
					"x lies in the carrier",
					"x ∈ F.carrier",
					By(member, SignCellInCarrier.At(F, lt, k, r, b.TermAs[Nat]("2 * l"), x)))
				b.Show(
					"its sign there is t(2l, i) = 0",
					By(
						xIn,
						zeroSign,
						signs.At(b.TermAs[Nat]("2 * l"), i, x),
						index,
						iLt,
						member,
						ordered_field.SignValues.Read(ordered).AsFact().At(b.TermAs[A]("polynomial_eval(f(i), x)")),
						over,
						polynomial_evaluation.EvalIn.Read(field.RingOn.Read(ordered_field.FieldOn.Read(ordered))).At(
							f.Apply(i), b.MemberOf[on.Any](x, xIn))))
			}))
		inRoots := a.Have(
			"so the cell lies among the roots of f(i)",
			"polynomial_sign_cell(F, lt, k, r, 2 * l) ⊆ polynomial_roots(F.carrier, f(i))",
			BySets(vanishes, polynomial_roots.PolynomialRootsDef))
		a.Show(
			"so the infinite cell would be finite",
			By(
				fewRoots,
				inRoots,
				finite_set.FiniteSubset.At(
					a.TermAs[Set[A]]("polynomial_sign_cell(F, lt, k, r, 2 * l)"),
					a.TermAs[Set[A]]("polynomial_roots(F.carrier, f(i))")),
				OpenCellInfinite.At(F, lt, k, r, l),
				ordered,
				cuts,
				lLe))
	}),
})}

// RootFreeCellSign — a polynomial over a real closed field without a root in
// an open cell of cuts has one sign on the cell: the closed interval between
// two points of the cell lies in the cell, which is convex, and so carries
// no root.
var RootFreeCellSign = rootFreeCellSignThm{family.Add(registry.ProofEntry{
	Name: "RootFreeCellSign",
	Key:  "prop_a7768b6f5dec0688",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀k:num. " +
			"∀r:(num → A). " +
			"∀i:num. " +
			"∀p:(num → A). " +
			"∀x y:A.",
		Hypotheses: []string{
			"real_closed_field(F, lt)",
			"∀j:num. j < k ⇒ r(j) ∈ F.carrier",
			"i ≤ k",
			"polynomial_over(F.carrier, p)",
			"∀z:A. z ∈ polynomial_sign_cell(F, lt, k, r, 2 * i) ⇒ polynomial_eval(p, z) ≠ F.zero",
			"x ∈ polynomial_sign_cell(F, lt, k, r, 2 * i)",
			"y ∈ polynomial_sign_cell(F, lt, k, r, 2 * i)",
		},
		Conclusion: "ordered_sign(F, lt, polynomial_eval(p, x)) = " +
			"ordered_sign(F, lt, polynomial_eval(p, y))",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		k *Expr[Nat],
		r *Arrow[Nat, A],
		i *Expr[Nat],
		p *Arrow[Nat, A],
		x, y *Expr[A],
		closed, cutsIn, iLe, poly, rootFree, xIn, yIn Fact,
	) {
		ordered := real_closed_field.OrderedFieldOn.Read(closed)
		cellIndex := a.TermAs[Nat]("2 * i")
		between := a.Have(
			"p has one sign between two points of the cell",
			Statement{
				Binders: "∀u v:A.",
				Hypotheses: []string{
					"u ∈ polynomial_sign_cell(F, lt, k, r, 2 * i)",
					"v ∈ polynomial_sign_cell(F, lt, k, r, 2 * i)",
					"lt(u, v)",
				},
				Conclusion: "ordered_sign(F, lt, polynomial_eval(p, u)) = " +
					"ordered_sign(F, lt, polynomial_eval(p, v))",
			},
			Derive(func(b *Argument) {
				u := b.FixAs[A]("u")
				v := b.FixAs[A]("v")
				given := b.Conjuncts(
					b.Assume(),
					"u lies in the cell",
					"v lies in the cell",
					"u lies below v")
				uIn := b.Have(
					"u lies in F",
					"u ∈ F.carrier",
					By(given[0], SignCellInCarrier.At(F, lt, k, r, cellIndex, u)))
				vIn := b.Have(
					"v lies in F",
					"v ∈ F.carrier",
					By(given[1], SignCellInCarrier.At(F, lt, k, r, cellIndex, v)))
				interval := b.Have(
					"no point from u to v is a root, as all lie in the cell",
					Statement{
						Binders: "∀z:A.",
						Hypotheses: []string{
							"z ∈ F.carrier",
							"ordered_le(lt, u, z)",
							"ordered_le(lt, z, v)",
						},
						Conclusion: "polynomial_eval(p, z) ≠ F.zero",
					},
					Derive(func(c *Argument) {
						z := c.FixAs[A]("z")
						point := c.Conjuncts(
							c.Assume(),
							"z lies in F",
							"u is at or below z",
							"z is at or below v")
						c.Show(
							"z lies in the cell, which is convex",
							By(
								rootFree.At(z),
								OpenCellConvex.At(F, lt, k, r, i, u, v, z),
								ordered,
								cutsIn,
								iLe,
								given[0],
								given[1],
								point[0],
								point[1],
								point[2]))
					}))
				b.Show(
					"p keeps its sign on the closed interval",
					By(
						real_closed_field.RootFreeIntervalSign.Read(closed).AsFact().At(p, u, v),
						poly,
						uIn,
						vIn,
						given[2],
						interval))
			}))
		xC := a.Have(
			"x lies in F",
			"x ∈ F.carrier",
			By(xIn, SignCellInCarrier.At(F, lt, k, r, cellIndex, x)))
		yC := a.Have(
			"y lies in F",
			"y ∈ F.carrier",
			By(yIn, SignCellInCarrier.At(F, lt, k, r, cellIndex, y)))
		a.Show(
			"x and y are equal or ordered",
			By(
				ordered_field.Trichotomy.Read(ordered).AsFact().At(x, y),
				xC,
				yC,
				between.At(x, y),
				between.At(y, x),
				xIn,
				yIn))
	}),
})}
