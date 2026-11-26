package determinant

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/registry"
)

// CoordinateVectorMember — a coordinate vector lies in the finite free
// module exactly when its entries lie in the carrier and vanish from the
// dimension onward.
var CoordinateVectorMember = coordinateVectorMemberThm{family.Add(registry.ProofEntry{
	Name: "CoordinateVectorMember",
	Key:  "prop_79fb7bfca112cecb",
	Build: family.Theorem("∀R:ring_ops(A). ∀n:num. ∀u:(num → A). "+
		"    u ∈ free_module_record(R, {i:num | i < n}).carrier ⇔ "+
		"    (∀i:num. u(i) ∈ R.carrier ∧ (n ≤ i ⇒ u(i) = R.zero))",
		func(a *Argument, R *Expr[RingOps[A]], n *Expr[Nat], u *Vec[A, DimN]) {
			indices := a.TermAs[Set[Nat]]("{i:num | i < n}")
			a.Show(
				"the support lies among the points below n exactly when the vector vanishes from n on",
				BySets(
					function_module.FiniteSuppMember.At(
						a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier"), indices, u),
					num_segment.FiniteBelowStrict.At(n),
					finite_set.FiniteSubset.At(a.TermAs[Set[Nat]]("fun_support(R.zero, u)"), indices),
					nat_order.NotLessThan))
		}),
})}

// MatrixColumnMapLinear — the column map of a matrix over the ring is a
// linear map of the finite free module to itself: it keeps the module's
// carrier and preserves its sums and scalar multiples. Each row of the image
// is a finite sum of ring elements that vanishes past the last row, and
// distributing the entries over a sum of vectors, or commuting them past a
// scalar, splits that sum or takes the scalar out of it.
var MatrixColumnMapLinear = matrixColumnMapLinearThm{family.Add(registry.ProofEntry{
	Name: "MatrixColumnMapLinear",
	Key:  "prop_c182aec2ff99a76c",
	Build: family.Theorem(Statement{
		Binders:    "∀c:comm_ring_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{"matrix_over(c, n, P)"},
		Conclusion: "module_homomorphism(c, " +
			"    free_module_record(c, {i:num | i < n}), " +
			"    free_module_record(c, {i:num | i < n}), " +
			"    «column map»)",
	}, func(
		a *Argument,
		c comm_ring.CommRingFact[on.C],
		n *Expr[Nat],
		P *Mat[A, DimN, DimN],
		over Fact,
	) {
		R := a.TermAs[RingOps[A]]("c")
		// what the three conditions on the map share: the entries of P, the
		// finite index set below n, and the ring as a module over itself, where
		// each row sum of the image is taken
		indices := a.TermAs[Set[Nat]]("{i:num | i < n}")
		entries := MatrixOverEntries.Read(c).At(n, P)
		finite := num_segment.FiniteBelowStrict.At(n)
		regular := module.RegularModuleOn.Read(c)
		add, zero := a.TermAs[Op[A]]("c.add"), a.TermAs[A]("c.zero")
		// unfolded, the conditions read the free module's record: its carrier is the
		// finite_supp set and its sum and scaling are the pointwise ones
		a.Do(Simp(Fwd(module_homomorphism.ModuleHomomorphismDef)))
		a.Show(
			"the column map preserves the coordinate module and its two operations",
			SplitConjAll(
				Case(
					"the coordinate vectors form a module",
					By(c, free_module.FreeModuleOn.At(R, indices))),
				Case(
					"the column map preserves the coordinate carrier",
					Derive(func(b *Argument) {
						u := b.VecFixAs[A, DimN]("u")
						member := b.Assume()
						terms := b.Have(
							"each row term lies in the ring, and is zero after the last row",
							"∀i k:num. P(i, k) * u(k) ∈ c.carrier ∧ (n ≤ i ⇒ P(i, k) * u(k) = c.zero)",
							Derive(func(d *Argument) {
								d.FixAs[Nat]("i")
								d.FixAs[Nat]("k")
								p, x := d.TermAs[A]("P(i, k)"), d.TermAs[A]("u(k)")
								d.Show(
									"a zero row annihilates each carrier entry of the vector",
									By(
										member,
										over,
										entries,
										CoordinateVectorMember.At(R, n, u),
										comm_ring.MulIn.Read(c).AsFact().At(p, x),
										comm_ring.MulLeftZeroOn.Read(c).AsFact().At(x)))
							}))
						coordinates := b.Have(
							"the image has carrier entries and vanishes from row n on",
							"∀i:num. «column map»(u, i) ∈ c.carrier ∧ (n ≤ i ⇒ «column map»(u, i) = c.zero)",
							Derive(func(d *Argument) {
								i := d.FixAs[Nat]("i")
								summand := d.TermAs[Fun[Nat, A]]("λk:num. P(i, k) * u(k)")
								d.Show(
									"finite sums preserve the carrier and a sum of zeros is zero",
									By(
										terms.At(i),
										finite,
										module.ModuleSumIn.Read(regular).AsFact().At(indices, summand),
										module.ModuleSumZero.Read(regular).AsFact().At(indices, summand)))
							}))
						b.Show(
							"the image is a finite coordinate vector",
							By(coordinates, CoordinateVectorMember.At(R, n, b.VecAs[A, DimN]("«column map»(u)"))))
					})),
				Case(
					"the column map preserves addition",
					Derive(func(b *Argument) {
						u, v := b.VecFixAs[A, DimN]("u"), b.VecFixAs[A, DimN]("v")
						members := b.Assume()
						terms := b.Have(
							"row multiplication distributes over sums",
							"∀i k:num. "+
								"    P(i, k) * u(k) ∈ c.carrier ∧ "+
								"    P(i, k) * v(k) ∈ c.carrier ∧ "+
								"    P(i, k) * (u(k) + v(k)) = P(i, k) * u(k) + P(i, k) * v(k)",
							Derive(func(d *Argument) {
								d.FixAs[Nat]("i")
								d.FixAs[Nat]("k")
								p, x, y := d.TermAs[A]("P(i, k)"), d.TermAs[A]("u(k)"), d.TermAs[A]("v(k)")
								d.Show(
									"the three factors lie in the commutative ring",
									ByArith(
										c,
										members,
										over,
										entries,
										CoordinateVectorMember.At(R, n, u),
										CoordinateVectorMember.At(R, n, v),
										comm_ring.MulIn.Read(c).AsFact().At(p, x),
										comm_ring.MulIn.Read(c).AsFact().At(p, y)))
							}))
						// the module's sum is the pointwise sum, read at each row
						b.Do(Funext())
						i := b.FixAs[Nat]("i")
						f, g :=
							b.TermAs[Fun[Nat, A]]("λk:num. P(i, k) * u(k)"), b.TermAs[Fun[Nat, A]]("λk:num. P(i, k) * v(k)")
						b.Do(Simp(Fwd(function_module.FunAddDef)))
						b.Show(
							"distribute each summand and then split the finite sum",
							CalcEq(
								Leg(
									b.TermAs[A]("module_sum(c.add, c.zero, {k:num | k < n}, λk:num. P(i, k) * u(k) + P(i, k) * v(k))"),
									"distribute the matrix entry across the vector sum",
									By(
										terms.At(i),
										module.ModuleSumCongruence.At(
											add,
											zero,
											indices,
											b.TermAs[Fun[Nat, A]]("λk:num. P(i, k) * (u(k) + v(k))"),
											b.TermAs[Fun[Nat, A]]("λk:num. P(i, k) * u(k) + P(i, k) * v(k)")))),
								FinalLeg(
									"split the sum of the two carrier-valued summands",
									By(terms.At(i), finite, module.ModuleSumAdd.Read(regular).AsFact().At(indices, f, g)))))
					})),
				Case(
					"the column map preserves scalar multiplication",
					Derive(func(b *Argument) {
						scalar := b.FixAs[A]("a")
						u := b.VecFixAs[A, DimN]("u")
						members := b.Assume()
						parts := b.Conjuncts(
							members,
							"a lies in the ring",
							"u lies in the coordinate module")
						am := b.MemberOf[on.C](scalar, parts[0])
						terms := b.Have(
							"row multiplication commutes with scaling",
							"∀i k:num. P(i, k) * u(k) ∈ c.carrier ∧ P(i, k) * (a * u(k)) = a * (P(i, k) * u(k))",
							Derive(func(d *Argument) {
								d.FixAs[Nat]("i")
								d.FixAs[Nat]("k")
								p, x := d.TermAs[A]("P(i, k)"), d.TermAs[A]("u(k)")
								d.Show(
									"the three factors lie in the commutative ring",
									ByArith(
										c,
										members,
										over,
										entries,
										CoordinateVectorMember.At(R, n, u),
										comm_ring.MulIn.Read(c).AsFact().At(p, x)))
							}))
						// the module's scaling is the pointwise one, read at each row
						b.Do(Funext())
						i := b.FixAs[Nat]("i")
						b.Do(Simp(Fwd(function_module.FunSmulDef)))
						b.Show(
							"commute the scalar past each matrix entry and take it outside the sum",
							CalcEq(
								Leg(
									b.TermAs[A]("module_sum(c.add, c.zero, {k:num | k < n}, λk:num. a * (P(i, k) * u(k)))"),
									"commute the scalar past the matrix entry",
									By(
										terms.At(i),
										module.ModuleSumCongruence.At(
											add,
											zero,
											indices,
											b.TermAs[Fun[Nat, A]]("λk:num. P(i, k) * (a * u(k))"),
											b.TermAs[Fun[Nat, A]]("λk:num. a * (P(i, k) * u(k))")))),
								FinalLeg(
									"a scalar factors out of the finite carrier sum",
									By(
										terms.At(i),
										finite,
										module.ModuleSumSmul.Read(regular).At(
											indices,
											am,
											b.TermAs[Fun[Nat, A]]("λk:num. P(i, k) * u(k)"))))))
					})),
			))
	}),
})}

// MatrixColumnMapOnDelta — the column map sends the standard vector at an
// index below the dimension to that column of the matrix: the standard
// vector is that column of the identity (MatrixIdentityColumn), so the row
// sums against it are the matrix times the identity, read at that column.
var MatrixColumnMapOnDelta = matrixColumnMapOnDeltaThm{family.Add(registry.ProofEntry{
	Name: "MatrixColumnMapOnDelta",
	Key:  "prop_ded20bef815babb3",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀P:(num → num → A). ∀j:num.",
		Hypotheses: []string{
			"matrix_over(c, n, P)",
			"j < n",
		},
		Conclusion: "«column map»(delta_at(j)) = transpose(P, j)",
	}, func(
		a *Argument,
		c comm_ring.CommRingFact[on.C],
		n *Expr[Nat],
		P *Mat[A, DimN, DimN],
		j *Expr[Nat],
		given Fact,
	) {
		column := a.Have(
			"column j of the identity is the delta vector at j, j lying below n",
			"(λr:num. matrix_identity(c, n, r, j)) = delta_at(j)",
			By(given, MatrixIdentityColumn.At(a.TermAs[RingOps[A]]("c"), n, j)))
		a.Do(Funext())
		r := a.FixAs[Nat]("r")
		a.Show(
			"the row sum selects column j of P",
			CalcEq(
				Leg(
					a.TermAs[A]("matrix_product(c, n, P, matrix_identity(c, n), r, j)"),
					"so the row sum against it is the row of P times the identity",
					column.RwRev(),
					Simp(Fwd(matrix.MatrixProductDef)),
					Refl()),
				FinalLeg(
					"multiplication by the identity leaves P unchanged",
					By(
						Normalized,
						given,
						MatrixProductRightIdentity.Read(c).At(n, P),
						matrix.TransposeDef.At(P, j, r))),
			))
	}),
})}
