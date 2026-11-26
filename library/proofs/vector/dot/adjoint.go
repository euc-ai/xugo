// adjoint.go — the adjoint of a map, and the two readings of the form
// it is built from.
//
// An adjoint is a map carried to the other side of the form: what `f`
// does to the first argument, its adjoint is to do to the second. The
// chapter BUILDS it rather than demanding it, coordinate by coordinate
// off the standard basis — the j-th coordinate of `adjoint(m, n, f, y)`
// is ⟪f(basis_vector(j)), y⟫_n. A demand would reach only the coordinates
// below the dimension in play and leave every one past it open, which
// is why the involution below is a theorem here and a wish elsewhere;
// the README argues that at length.
//
// Two readings of the form come first, because the construction is made
// of them and nothing else.
//
// COORDINATES. The basis vector at an index is the ring's one there and
// its zero elsewhere, so the products the form folds are a Kronecker
// summand and the fold mechanism's delta law collapses it: the form
// reads the entry at that index (`BasisVectorLeft`). One probe decides one
// coordinate, and from there an n-vector is determined by how it pairs
// with the n-vectors (`Nondegenerate`) — the form is non-degenerate on
// a dimension, which is what turns an equation between vectors into a
// statement about pairings.
//
// THE FORM ACROSS A FOLD. `IterateLeft` carries the form over a sum of
// arbitrarily many vectors. Its two sums are folds at DIFFERENT
// operations — vectors on the left, ring elements on the right, the
// text writing both the same way and the type deciding which — and what
// bridges them is pairing against `y`, a homomorphism of the two
// additions whose two obligations are `ZeroLeft` where the fold starts
// and `AddLeft` where it turns.
//
// Both dimensions of the adjoint earn their place. `m` is the dimension
// of the vector being built, so it counts the basis vectors there are
// to read; `n` is the dimension the form is read at, where the images
// of `f` and the vector `y` are paired. Past m there is no basis vector
// left to read, and what the definition writes there is the ring's
// zero — which is not bookkeeping, for the reason `AdjointVec` states.

package dot

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------
// Coordinates: what the form says about a vector's entries
// ---------------------------------------------------------------

// BasisVectorLeft — the form reads a coordinate off the standard basis: the
// summands are the Kronecker delta of the entries, and the delta sum
// keeps the one term whose index the range holds.
var BasisVectorLeft = basisVectorLeftThm{family.Add(registry.ProofEntry{
	Name: "BasisVectorLeft",
	Key:  "prop_7c82f1682f0fb7c5",
	Build: comm_ring.CommRing.Law(Statement{
		Binders: "∀n j:num. ∀u:(num → A).",
		Hypotheses: []string{
			"j < n",
		},
		Conclusion: "⟪basis_vector(j), u⟫_n = u(j)",
	},
		func(a *Argument, ring Fact, n, j *Expr[Nat], u *Vec[A, DimN], below Fact) {
			inRange := a.Have(
				"the index lies in the active range",
				"j ∈ {i:num | i < n}",
				BySets(below))

			kronecker := a.Have(
				"each summand is the entry of u at its own index when that "+
					"index is j, and the element the fold starts from elsewhere",
				"∀i:num. basis_vector(j)(i) * u(i) = COND(i = j, u(i), neutral_elem(R.add))",
				Derive(func(b *Argument) {
					b.Fix("i")
					b.Do(Unfold(vec_space.BasisVectorDef))
					b.Cases(b.Term("i = j"))
					b.When(
						"i = j: the basis entry is the ring's one",
						func(c *Argument, eq Fact) {
							c.Show(
								"and one times the entry is the entry",
								By(Normalized, eq, comm_ring.MulMonoid, ring, comm_monoid.LeftIdentity))
						})
					b.Otherwise(
						"¬(i = j): the basis entry is the ring's zero",
						func(c *Argument, neq Fact) {
							c.Show(
								"and zero times the entry is that zero, which is the additive neutral",
								By(Normalized, neq, ring, comm_ring.MulLeftZero, comm_ring.NeutralAdd))
						})
				}))

			a.Show(
				"so the fold of that summand keeps the single term the range admits",
				Unfold(DotDef),
				CalcEq(
					Leg(
						a.Term("Σ_{i<n} COND(i = j, u(i), neutral_elem(R.add))"),
						"the summands are that Kronecker delta",
						Congr(),
						Funext(),
						By(kronecker)),
					Leg(
						a.Term("COND(j ∈ {i:num | i < n}, u(j), neutral_elem(R.add))"),
						"the delta sum keeps only the term at j, guarded by the range",
						// Delta speaks of a summand silent off one point; the
						// value it keeps there is u's entry, which is the binder
						// the goal's β-reduct does not spell.
						By(comm_ring.MonoidalAdd, ring, Where(monoidal.Delta, "f", u))),
					FinalLeg(
						"and j lies in the range, so that term is u(j)",
						By(inRange)),
				))
		}),
})}

// Nondegenerate — the form is NON-DEGENERATE on a dimension: an
// n-vector is determined by how it pairs with the n-vectors. The probe
// is confined to the dimension along with the two vectors, so the
// direction that carries content is drawn from fewer probes — and
// those are the ones a consumer can produce anyway, the basis vectors
// below n.
//
// One probe decides one coordinate. At an index below n the basis
// vector there is an n-vector, so the hypothesis speaks about it, and
// the reading above turns each side of the resulting pairing into that
// coordinate: the hypothesis at that single probe IS the agreement at
// the index. Agreement on the active range is equality, and that step
// is the only place the membership hypothesis is spent.
var Nondegenerate = nondegenerateThm{family.Add(registry.ProofEntry{
	Name: "Nondegenerate",
	Key:  "prop_3f63bcaf8b5209d2",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀n:num. ∀u v:(num → A).",
			Hypotheses: []string{
				"vec⟨n⟩(u)",
				"vec⟨n⟩(v)",
			},
			Conclusion: "u = v ⇔ ∀w:(num → A). vec⟨n⟩(w) ⇒ ⟪w, u⟫_n = ⟪w, v⟫_n",
		},
		func(a *Argument, ring Fact, n *Expr[Nat], u, v *Vec[A, DimN], both Fact) {
			a.Iff()
			a.Forward(
				"equal vectors pair alike against every n-vector",
				func(b *Argument, eq Fact) {
					b.Do(eq.Rw(), Basic())
				})
			a.Backward(
				"pairing alike against every n-vector settles every coordinate below n",
				func(b *Argument, paired Fact) {
					agree := b.Have(
						"u and v agree on the active range",
						"∀j:num. j < n ⇒ u(j) = v(j)",
						Derive(func(c *Argument) {
							c.Fix("j")
							below := c.Assume()
							basis := c.Term("basis_vector(j)")
							inDim := c.Have(
								"the basis vector at j is an n-vector, so it is one of the probes",
								"vec⟨n⟩(basis_vector(j))",
								By(below, vec_space.VecBasisVector))
							readU := c.Have(
								"the form at that probe reads u's j-th coordinate",
								"⟪basis_vector(j), u⟫_n = u(j)",
								By(below, ring, BasisVectorLeft))
							readV := c.Have(
								"and v's",
								"⟪basis_vector(j), v⟫_n = v(j)",
								By(below, ring, BasisVectorLeft))
							c.Show(
								"so the two pairings the hypothesis equates there are the two coordinates",
								By(paired.At(basis), inDim, readU, readV))
						}))
					// Extensionality is stated for ANY zero rather than under
					// the ring, so the ring's own zero is supplied at the cite;
					// VecBasisVector above is bare for the same reason in reverse —
					// the apply rung reads its two values off the goal.
					vectors := b.Conjuncts(
						both,
						"u is an n-vector",
						"so is v")
					b.Show(
						"and two n-vectors agreeing on the range are equal",
						By(
							agree,
							vec_space.Extensionality.At(
								b.TermAs[A]("R.zero"), proof.Inhabit(u, vectors[0]), proof.Inhabit(v, vectors[1]))))
				})
		}),
})}

// Definite — on a dimension the form is DEFINITE as soon as every
// vector null for it is orthogonal to every vector: the zero vector is
// then the only null n-vector.
//
// One hypothesis suffices because equality of n-vectors is decided by
// non-degeneracy, so what definiteness needs of the carrier is only
// that null vectors pair to zero with everything — at an ordered
// carrier a consequence of the form's positivity, and the one place an
// order enters. Left to right, a null vector is orthogonal to
// everything, so every vector pairs to zero against u — which is what
// every vector does against the zero vector. So u and the zero vector
// pair alike against every n-vector, and non-degeneracy reads that
// agreement back as equality; the zero vector is an n-vector for every
// n, which is what non-degeneracy asks of its second argument. Right to
// left the form is merely evaluated at the zero vector.
var Definite = definiteThm{family.Add(registry.ProofEntry{
	Name: "Definite",
	Key:  "prop_fa1afb34211945d7",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀n:num. ∀u:(num → A).",
			Hypotheses: []string{
				"∀w v:(num → A). ⟪w, w⟫_n = R.zero ⇒ ⟪w, v⟫_n = R.zero",
				"vec⟨n⟩(u)",
			},
			Conclusion: "⟪u, u⟫_n = R.zero ⇔ u = vec_zero",
		},
		func(a *Argument, ring Fact, n *Expr[Nat], u *Vec[A, DimN], nullOrthogonal, member Fact) {
			a.Iff()
			a.Forward(
				"u pairs against every n-vector exactly as the zero vector does",
				func(b *Argument, null Fact) {
					pairs := b.Have(
						"every vector pairs against u as it pairs against the zero vector: both pairings are zero",
						"∀w:(num → A). ⟪w, u⟫_n = ⟪w, vec_zero⟫_n",
						Derive(func(c *Argument) {
							c.Fix("w")
							c.Show(
								"the pairing turns around, vanishes, and is what the zero vector pairs to",
								CalcEq(
									Leg(
										c.Term("⟪u, w⟫_n"),
										"the form is symmetric",
										By(Sym, ring)),
									Leg(
										c.Term("R.zero"),
										"and u, being null, is orthogonal to every vector",
										By(null, nullOrthogonal)),
									FinalLeg(
										"which is what every vector pairs to against the zero vector",
										Symm(),
										By(ZeroRight, ring)),
								))
						}))
					reading := b.Have(
						"non-degeneracy, at u and the zero vector",
						"u = vec_zero ⇔ ∀w:(num → A). vec⟨n⟩(w) ⇒ ⟪w, u⟫_n = ⟪w, vec_zero⟫_n",
						By(member, vec_space.VecZero, Nondegenerate, ring))
					b.Show(
						"so the equality is agreement against every n-vector, and they do agree",
						reading.Rw(),
						By(pairs))
				})
			a.Backward(
				"u is the zero vector",
				func(b *Argument, isZero Fact) {
					b.Show(
						"and the form annihilates the zero vector",
						isZero.Rw(),
						By(ZeroRight, ring))
				})
		}),
})}

// ---------------------------------------------------------------
// The form across a fold
// ---------------------------------------------------------------

// IterateLeft — pairing against a fixed vector is a homomorphism from
// the vectors under addition to the ring under addition, so it carries
// a finite sum of vectors to the sum of the pairings.
//
// The induction is not here. `monoidal.Homomorphic` carries a fold
// across a map between two monoidal carriers, and what this chapter
// owes it is the map — "pair against y", the one binder the goal's
// β-reduct does not spell — with the two facts a homomorphism is asked
// for: that it sends the element the vector fold starts from to the one
// the ring's fold starts from, and that it crosses addition. Those are
// `ZeroLeft` and `AddLeft`, the chapter's own two readings of the form.
var IterateLeft = iterateLeftThm{family.Add(registry.ProofEntry{
	Name: "IterateLeft",
	Key:  "prop_f335aab962ae9e09",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀n:num. ∀s:set(num). ∀F:(num → num → A). ∀y:(num → A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "⟪Σ_{i∈s} F(i), y⟫_n = Σ_{i∈s} ⟪F(i), y⟫_n",
		},
		func(a *Argument, ring Fact, n *Expr[Nat], s *Expr[Set[Nat]],
			F *Arrow2[Nat, Nat, A], y *Vec[A, DimN], finite Fact) {
			// The map the transfer law is applied at. The goal states its
			// β-reduct, so no slot of the goal spells it and it is pinned
			// by name where the law is applied; its obligations are stated
			// below in the law's own words.
			pairWithY := a.TermAs[Fun[Fun[Nat, A], A]]("λu:(num → A). ⟪u, y⟫_n")

			fixesNeutral := a.Have(
				"the form annihilates the vector the fold starts from, "+
					"landing on the element the ring's own fold starts from",
				"⟪neutral_elem(vec_add), y⟫_n = neutral_elem(R.add)",
				// The neutral stands unapplied under the form, so its
				// reading enters as a rewrite rather than as a premise.
				Simp(Fwd(vec_space.NeutralVecAdd)),
				By(Normalized, ZeroLeft, comm_ring.NeutralAdd, ring))
			crossesOp := a.Have(
				"and the form splits over a vector sum, which is the map crossing the operation",
				"∀u v:(num → A). ⟪u + v, y⟫_n = ⟪u, y⟫_n + ⟪v, y⟫_n",
				By(AddLeft, ring))

			// What the mechanism asks of each of the two operations —
			// that it folds — is read off the ring where the law is
			// applied: the two structure laws under the ring hypothesis.
			a.Show(
				"so the transfer law carries the fold to the fold of the pairings, which is the claim",
				By(
					vec_space.MonoidalVecAdd.Read(ring),
					comm_ring.MonoidalAdd.Read(ring),
					fixesNeutral,
					crossesOp,
					finite,
					Where(monoidal.Homomorphic, "h", pairWithY)))
		}),
})}

// ---------------------------------------------------------------
// The adjoint
// ---------------------------------------------------------------

// AdjointVec — the adjoint's value is a vector of the dimension it is
// taken at, and nothing about the map or the vector is spent proving
// it: an index at or past m fails the definition's guard on its own,
// and the branch taken there is the ring's zero.
var AdjointVec = adjointVecThm{family.Add(registry.ProofEntry{
	Name: "AdjointVec",
	Key:  "prop_3d1c8ed7c6c616d8",
	Build: comm_ring.CommRing.Law("∀m n:num. ∀f:((num → A) → (num → A)). ∀y:(num → A). "+
		"    vec⟨m⟩(adjoint(m, n, f, y))",
		func(a *Argument, ring Fact, m, n *Expr[Nat], f *Arrow[Fun[Nat, A], Fun[Nat, A]], y *Vec[A, DimN]) {
			a.Do(Unfold(vec_space.VecDef))
			i := a.Fix("i")
			past := a.Assume()
			a.Show(
				"an index at or past m is not below m, so the guard fails and the coordinate is the ring's zero",
				Unfold(AdjointDef),
				By(past, At(nat_order.NotLessThan, i, m)))
		}),
})}

// AdjointWorks — the identity the construction was built for. Both
// sides descend to one fold over the coordinates of x, and the proof is
// the two descents meeting there.
//
// On the left, x is read through the standard basis. That is the one
// place membership in dimension m is spent, and the reason the
// statement carries it: without it the left side consults f at indices
// the right side never looks at, and the identity fails. Linearity then
// carries f through the fold and takes each coordinate out of its
// summand, the form crosses the fold, and the coordinates come back out
// of the form. On the right, the fold is the form against the adjoint
// with the definition of the form read off, and the adjoint's
// coordinate inside the range is the form at the image of the basis
// vector there. That last step is where a fold's congruence earns its
// restriction to the index set: the definition's guard is decided by
// the range and by nothing else, so the summands agree exactly where
// the fold reads them.
var AdjointWorks = adjointWorksThm{family.Add(registry.ProofEntry{
	Name: "AdjointWorks",
	Key:  "prop_9b14ab6e71fa8606",
	Build: comm_ring.CommRing.Law(Statement{
		Binders: "∀m n:num. ∀f:((num → A) → num → A). ∀x y:(num → A).",
		Hypotheses: []string{
			"vec_linear(f)",
			"vec⟨m⟩(x)",
		},
		Conclusion: "⟪f(x), y⟫_n = ⟪x, adjoint(m, n, f, y)⟫_m",
	},
		func(a *Argument, ring Fact, m, n *Expr[Nat], f *Arrow[Fun[Nat, A], Fun[Nat, A]],
			x *Vec[A, DimM], y *Vec[A, DimN], linear Fact, member Fact) {
			finite := a.Have(
				"the index set both folds run over is finite",
				"finite({i:num | i < m})",
				Cite(num_segment.FiniteBelowStrict))

			// The half of linearity this argument spends — the other half
			// rides inside LinearIterate — and the reading of x that makes
			// a fold of the left side at all. The reading is the one place
			// membership in dimension m is spent.
			homogeneous := a.Have(
				"f commutes with the scalar action",
				"∀c:A. ∀u:(num → A). f(c • u) = c • f(u)",
				By(linear, vec_space.VecLinearDef))
			expansion := a.Have(
				"and x is the sum of its coordinates against the standard basis",
				"x = Σ_{i<m} x(i) • basis_vector(i)",
				By(member, vec_space.BasisExpansion, ring))

			coordinate := a.Have(
				"inside the range the adjoint's guard holds, so its "+
					"coordinate there is the form at the image of the basis vector",
				"∀k:num. k ∈ {i:num | i < m} ⇒ x(k) * ⟪f(basis_vector(k)), y⟫_n = x(k) * adjoint(m, n, f, y)(k)",
				Derive(func(b *Argument) {
					b.Fix("k")
					inRange := b.Assume()
					b.Show(
						"the guard the definition asks about is the range condition itself",
						Unfold(AdjointDef),
						BySets(inRange))
				}))

			right := a.Have(
				"so the form against the adjoint is the fold of those forms against the coordinates of x",
				"Σ_{i<m} x(i) * ⟪f(basis_vector(i)), y⟫_n = ⟪x, adjoint(m, n, f, y)⟫_m",
				CalcEq(
					Leg(
						a.Term("Σ_{i<m} x(i) * adjoint(m, n, f, y)(i)"),
						"the summands agree on the index set, which is everywhere the fold reads them",
						By(coordinate, comm_ring.MonoidalAdd, ring, monoidal.Congruence)),
					FinalLeg(
						"and that fold is the form against the adjoint, read at its definition",
						Unfold(DotDef)),
				))

			a.Show(
				"and the form at the image of x descends to the same fold",
				CalcEq(
					Leg(
						a.Term("⟪f(Σ_{i<m} x(i) • basis_vector(i)), y⟫_n"),
						"read x through the basis",
						By(expansion)),
					Leg(
						a.Term("⟪Σ_{i<m} f(x(i) • basis_vector(i)), y⟫_n"),
						"a linear map carries that sum to the sum of the images",
						Congr(),
						By(linear, finite, vec_space.LinearIterate, ring)),
					Leg(
						a.Term("⟪Σ_{i<m} x(i) • f(basis_vector(i)), y⟫_n"),
						"and takes the coordinate out of every summand, so the two families of summands are one family",
						Congr(),
						Funext(),
						By(homogeneous)),
					Leg(
						a.Term("Σ_{i<m} ⟪x(i) • f(basis_vector(i)), y⟫_n"),
						"the form crosses the fold",
						By(finite, IterateLeft, ring)),
					Leg(
						a.Term("Σ_{i<m} x(i) * ⟪f(basis_vector(i)), y⟫_n"),
						"and gives up the coordinate on each summand",
						Congr(),
						Funext(),
						By(SmulLeft, ring)),
					FinalLeg(
						"which is the form against the adjoint",
						By(right)),
				))
		}),
})}

// AdjointLinear — the adjoint is linear, and nothing about the map it is
// taken of is spent showing it. Inside the range each coordinate is the
// form read at a FIXED first argument — the image of a basis vector — so
// the two halves linearity asks for are the form's additivity and its
// homogeneity in the SECOND argument, and the map never comes up. Past
// the range both sides are built from the ring's zero, which is its own
// sum and absorbs any scalar. That is why the member carries no
// hypothesis on the map: the adjoint is built out of the argument the
// form is linear in, whatever the map does to the other one.
var AdjointLinear = adjointLinearThm{family.Add(registry.ProofEntry{
	Name: "AdjointLinear",
	Key:  "prop_f3854b81ea8d7b1f",
	Build: comm_ring.CommRing.Law("∀m n:num. ∀f:((num → A) → (num → A)). vec_linear(adjoint(m, n, f))",
		func(a *Argument, ring Fact, m, n *Expr[Nat], f *Arrow[Fun[Nat, A], Fun[Nat, A]]) {
			a.Show(
				"linearity asks two things of a map on sequences, and the coordinates answer both",
				Unfold(vec_space.VecLinearDef),
				SplitConj(
					Case(
						"the adjoint carries a pointwise sum to the pointwise sum",
						// The adjoint's definition is opened as a rule, so that the
						// guard its coordinate carries is decided by the branch's
						// hypothesis as the rule fires.
						Derive(func(b *Argument) {
							b.Fix("u")
							b.Fix("v")
							b.Do(Funext())
							b.Fix("j")
							b.Cases(b.Term("j < m"))
							b.When(
								"j < m: the coordinate is the form at the image of the j-th "+
									"basis vector, where the form is additive in its second argument",
								func(c *Argument, below Fact) {
									c.Show(
										"the form at that image splits over the sum, and the sum is the two coordinates",
										Simp(Fwd(AdjointDef)),
										CalcEq(
											Leg(
												c.Term("⟪f(basis_vector(j)), u⟫_n + ⟪f(basis_vector(j)), v⟫_n"),
												"the form splits over the sum",
												By(AddRight, ring)),
											FinalLeg(
												"and that sum is the two coordinates, each read at j under the same guard",
												Unfold(vec_space.VecAddDef),
												By(below)),
										))
								})
							b.Otherwise(
								"past m: the guard fails on both sides, leaving the ring's zero, which is its own sum",
								Simp(Fwd(AdjointDef), Fwd(vec_space.VecAddDef)),
								By(comm_ring.AddMonoid, ring, comm_monoid.LeftIdentity))
						})),
					Case(
						"and commutes with the scalar action",
						Derive(func(b *Argument) {
							b.Fix("c")
							b.Fix("u")
							b.Do(Funext())
							b.Fix("j")
							b.Cases(b.Term("j < m"))
							b.When(
								"j < m: the coordinate is the form at that same "+
									"image, and a scalar on its second argument comes out",
								func(d *Argument, below Fact) {
									d.Show(
										"the form at that image gives up the scalar, and the multiple is the coordinate",
										Simp(Fwd(AdjointDef)),
										CalcEq(
											Leg(
												d.Term("c * ⟪f(basis_vector(j)), u⟫_n"),
												"the form gives up the scalar",
												By(SmulRight, ring)),
											FinalLeg(
												"and the scalar multiple is the coordinate read at j under the same guard",
												Unfold(vec_space.VecScalarMulDef),
												By(below)),
										))
								})
							b.Otherwise(
								"past m: the guard fails on both sides, leaving the ring's zero, which absorbs the scalar",
								Simp(Fwd(AdjointDef), Fwd(vec_space.VecScalarMulDef)),
								By(comm_ring.MulRightZero, ring))
						})),
				))
		}),
})}

// AdjointInvolutive — taking the adjoint twice gives the map's own
// value back. The construction is closed off here: what the proof
// spends is `AdjointVec`, `AdjointWorks` and `AdjointLinear`, the form's
// symmetry and its nondegeneracy, and the definition is never unfolded.
//
// The form at dimension n separates n-vectors, so it is enough to pair
// both sides against an arbitrary n-vector w. That pairing crosses the
// adjoint twice, once in each direction — first the outer one, whose
// map is the inner adjoint and so is linear for free, then the inner
// one, where f's own linearity and x's membership are spent — and the
// two crossings meet at the form of f(x) against w.
//
// A function equality is not available here and is not true: a vector
// is a sequence, f is a map on all of them, and the double adjoint is
// built only out of what f does below m, so past that the two maps have
// no reason to agree. The third hypothesis is where the dimension of
// f's value enters: it says that at THIS x the image has the dimension
// the outer adjoint is read at, which is all the pointwise statement
// needs. A consumer holding the uniform hypothesis gets it in one step.
var AdjointInvolutive = adjointInvolutiveThm{family.Add(registry.ProofEntry{
	Name: "AdjointInvolutive",
	Key:  "prop_fdd3378c7a350080",
	Build: comm_ring.CommRing.Law(Statement{
		Binders: "∀m n:num. ∀f:((num → A) → num → A). ∀x:(num → A).",
		Hypotheses: []string{
			"vec_linear(f)",
			"vec⟨m⟩(x)",
			"vec⟨n⟩(f(x))",
		},
		Conclusion: "adjoint(n, m, adjoint(m, n, f), x) = f(x)",
	},
		func(a *Argument, ring Fact, m, n *Expr[Nat], f *Arrow[Fun[Nat, A], Fun[Nat, A]],
			x *Vec[A, DimM], linear Fact, member Fact, image Fact) {
			separates := a.Have(
				"the double adjoint's value at x and f(x) are n-vectors, and the form "+
					"tells those apart, so agreeing against every one of them is being equal",
				"adjoint(n, m, adjoint(m, n, f), x) = f(x) ⇔ "+
					"(∀w:(num → A). vec⟨n⟩(w) ⇒ ⟪w, adjoint(n, m, adjoint(m, n, f), x)⟫_n = ⟪w, f(x)⟫_n)",
				By(image, AdjointVec, ring, Nondegenerate))

			agree := a.Have(
				"and they do agree, against every n-vector",
				"∀w:(num → A). vec⟨n⟩(w) ⇒ ⟪w, adjoint(n, m, adjoint(m, n, f), x)⟫_n = ⟪w, f(x)⟫_n",
				Derive(func(b *Argument) {
					b.Fix("w")
					wMember := b.Assume()
					b.Show(
						"crossing each adjoint once turns the one pairing into the other",
						CalcEq(
							Leg(
								b.Term("⟪adjoint(m, n, f, w), x⟫_m"),
								"the outer adjoint is taken OF the inner one, so its map "+
									"at w is that vector — and it is linear whatever f was",
								By(wMember, ring, AdjointWorks, AdjointLinear)),
							Leg(
								b.Term("⟪x, adjoint(m, n, f, w)⟫_m"),
								"the form is symmetric",
								By(ring, Sym)),
							Leg(
								b.Term("⟪f(x), w⟫_n"),
								"and the inner adjoint carries it back to the image of "+
									"x, which is where membership in dimension m is spent",
								By(member, linear, ring, AdjointWorks)),
							FinalLeg(
								"symmetric once more",
								By(ring, Sym)),
						))
				}))

			a.Show(
				"so the two n-vectors are the same one",
				By(agree, separates))
		}),
})}
