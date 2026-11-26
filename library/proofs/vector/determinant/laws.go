package determinant

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// MatrixOverEntries — a matrix over c is an array whose entries all lie in
// c and vanish outside the n × n block. Unfolded, matrix_over asks for the
// entries inside the block to lie in c, the rows past n to be the zero
// vector and every row to vanish past column n; an entry past the block is
// then c.zero, itself a member of c.
var MatrixOverEntries = matrixOverEntriesThm{family.Add(registry.ProofEntry{
	Name: "MatrixOverEntries",
	Key:  "prop_5d956dcbf26ac891",
	Build: family.Theorem("∀c:comm_ring_on(A). ∀n:num. ∀P:(num → num → A). "+
		"    matrix_over(c, n, P) ⇔ "+
		"    (∀i j:num. P(i, j) ∈ c.carrier) ∧ (∀i j:num. n ≤ i ∨ n ≤ j ⇒ P(i, j) = c.zero)",
		func(a *Argument, c comm_ring.CommRingFact[on.C], n *Expr[Nat], P *Arrow2[Nat, Nat, A]) {
			a.Iff()
			a.Forward(
				"inside the block an entry lies in c by definition, "+
					"and past it the entry is c.zero, which lies in c",
				func(b *Argument, over Fact) {
					block := b.Simplified(
						over,
						Fwd(MatrixOverDef),
						Fwd(matrix.MatrixDef),
						Fwd(vec_space.VecDef),
						Fwd(vec_space.VecZeroDef))
					b.Show(
						"so every entry lies in c, and the entries past the block are zero",
						By(block, comm_ring.ZeroIn.Read(c), nat_order.NotLessThan))
				})
			a.Backward(
				"entries in c that vanish past the block are what matrix_over asks for",
				func(b *Argument, entries Fact) {
					parts := b.Conjuncts(
						entries,
						"every entry lies in c",
						"and the entries past the block are zero")
					inC, outside := parts[0], parts[1]
					b.Show(
						"the rows past n are zero, each row vanishes past column n, and the block's entries lie in c",
						Simp(Fwd(MatrixOverDef), Fwd(matrix.MatrixDef), Fwd(vec_space.VecDef), Fwd(vec_space.VecZeroDef)),
						By(inC, outside))
				})
		}),
})}

// MatrixIdentityOver — the identity matrix is a matrix over c. Its entries
// are c.one and c.zero, both in c, and an entry past the n × n block is off
// the diagonal below n, so it is c.zero (MatrixOverEntries).
var MatrixIdentityOver = matrixIdentityOverThm{family.Add(registry.ProofEntry{
	Name: "MatrixIdentityOver",
	Key:  "prop_b0d1a767c15bbf87",
	Build: family.Theorem("∀c:comm_ring_on(A). ∀n:num. matrix_over(c, n, matrix_identity(c, n))",
		func(a *Argument, c comm_ring.CommRingFact[on.C], n *Expr[Nat]) {
			a.Show(
				"its entries are one or zero, and zero past the block",
				Simp(Fwd(MatrixOverEntries.Read(c)), Fwd(MatrixIdentityDef)),
				SplitConj(
					Case(
						"each entry is one or zero, both in c",
						By(comm_ring.OneIn.Read(c), comm_ring.ZeroIn.Read(c))),
					Case(
						"an entry past the block is off the diagonal below n",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("i")
							b.FixAs[Nat]("j")
							past := b.Assume()
							off := b.Have(
								"a row or a column past n is no diagonal place below n",
								"¬(i < n ∧ i = j)",
								ByArith(past))
							b.Show(
								"so the entry is c.zero",
								By(off))
						})),
				))
		}),
})}

// MatrixIdentityColumn — a column of the identity matrix below n is the
// indicator of its index: both are one at that row and zero at every other.
var MatrixIdentityColumn = matrixIdentityColumnThm{family.Add(registry.ProofEntry{
	Name: "MatrixIdentityColumn",
	Key:  "prop_16536398bf8e3363",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n m:num.",
		Hypotheses: []string{
			"m < n",
		},
		Conclusion: "(λr:num. matrix_identity(R, n, r, m)) = delta_at(R.zero, R.one, m)",
	},
		func(a *Argument, R *Expr[RingOps[A]], n, m *Expr[Nat], below Fact) {
			a.Do(Funext())
			r := a.FixAs[Nat]("r")
			a.Show(
				"both are one at row m and zero at every other row",
				By(
					below,
					MatrixIdentityDef.At(R, n, r, m),
					free_module.DeltaAtDef.At(a.TermAs[A]("R.zero"), a.TermAs[A]("R.one"), m, r)))
		}),
})}

// IndexMapMatrixOver — for a map f fixing every point from n on, the
// matrix whose column s is the basis vector at f(s) is a matrix over c.
// Its entries are c.one and c.zero, both in c, and an entry past the
// n × n block is off the diagonal below n: a row past n is no row below n,
// and f fixes a column past n, so it stays past n (MatrixOverEntries).
var IndexMapMatrixOver = indexMapMatrixOverThm{family.Add(registry.ProofEntry{
	Name: "IndexMapMatrixOver",
	Key:  "prop_ec8e0c8cd3bf0f99",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀f:(num → num).",
		Hypotheses: []string{
			"∀j:num. n ≤ j ⇒ f(j) = j",
		},
		Conclusion: "matrix_over(c, n, λr:num. λs:num. matrix_identity(c, n, r, f(s)))",
	},
		func(a *Argument, c comm_ring.CommRingFact[on.C], n *Expr[Nat], f *Arrow[Nat, Nat], fixed Fact) {
			a.Show(
				"its entries are one or zero, and zero past the block",
				Simp(Fwd(MatrixOverEntries.Read(c)), Fwd(MatrixIdentityDef)),
				SplitConj(
					Case(
						"each entry is one or zero, both in c",
						By(comm_ring.OneIn.Read(c), comm_ring.ZeroIn.Read(c))),
					Case(
						"past the block the entry is off the diagonal below n: a "+
							"row past n is no row below n, and f fixes a column past n",
						Derive(func(d *Argument) {
							d.FixAs[Nat]("i")
							j := d.FixAs[Nat]("j")
							past := d.Assume()
							off := d.Have(
								"the entry lies off the diagonal below n",
								"¬(i < n ∧ i = f(j))",
								ByArith(past, fixed.At(j)))
							d.Show(
								"so it is zero",
								By(off))
						})),
				))
		}),
})}

// LeibnizFactorsIn — the two factors of a Leibniz term of a matrix over
// c, the sign as one or minus one of the ring and the product of the
// entries P(k, q(k)), lie in c. Every entry of P lies in c
// (MatrixOverEntries), and the product is the fold of c's multiplicative
// monoid over the n rows, which keeps c (ModuleSumInMonoid).
var LeibnizFactorsIn = leibnizFactorsInThm{family.Add(registry.ProofEntry{
	Name: "LeibnizFactorsIn",
	Key:  "prop_3f60e64e9b272582",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀P:(num → num → A). ∀q:permutation(num).",
		Hypotheses: []string{
			"matrix_over(c, n, P)",
		},
		Conclusion: "«sign»(q) ∈ c.carrier ∧ " +
			"module_sum(c.mul, c.one, {k:num | k < n}, λk:num. P(k, permutation_map(q, k))) ∈ c.carrier",
	},
		func(
			a *Argument,
			c comm_ring.CommRingFact[on.C],
			n *Expr[Nat],
			P *Arrow2[Nat, Nat, A],
			q *Expr[Permutation[Nat]],
			over Fact,
		) {
			entries := a.Have(
				"every entry of P lies in c",
				"∀i j:num. P(i, j) ∈ c.carrier",
				By(over, MatrixOverEntries.Read(c).At(n, P)))
			sign := a.Have(
				"the sign is one or minus one of c",
				"«sign»(q) ∈ c.carrier",
				By(comm_ring.OneIn.Read(c), comm_ring.NegIn.Read(c)))
			product := a.Have(
				"the product of the entries P(k, q(k)) over the n rows is a finite product of members of c",
				"module_sum(c.mul, c.one, {k:num | k < n}, λk:num. P(k, permutation_map(q, k))) ∈ c.carrier",
				By(
					entries,
					num_segment.FiniteBelowStrict.At(n),
					module.ModuleSumInMonoid.Read(comm_ring.MulMonoidOn.Read(c)).At(
						a.TermAs[Set[Nat]]("{k:num | k < n}"),
						a.TermAs[Fun[Nat, A]]("λk:num. P(k, permutation_map(q, k))"))))
			a.Show(
				"both factors lie in c",
				By(sign, product))
		}),
})}

// SignValueAfterTransposition — the sign of a Leibniz term, read in the
// ring as one or minus one, is negated by composing with a
// transposition. The transposition flips the parity
// (ParityAfterTransposition): when q is even, τ·q is odd and both sides
// are minus one, and when q is odd, τ·q is even and one is minus minus
// one.
var SignValueAfterTransposition = signValueAfterTranspositionThm{family.Add(registry.ProofEntry{
	Name: "SignValueAfterTransposition",
	Key:  "prop_ad99caa580f6df8",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n i j:num. ∀q:permutation(num).",
		Hypotheses: []string{
			"i < n",
			"j < n",
			"i ≠ j",
			"q ∈ symmetric_group({k:num | k < n})",
		},
		Conclusion: "«sign»(transposition(i, j) * q) = -«sign»(q)",
	},
		func(
			a *Argument,
			c comm_ring.CommRingFact[on.C],
			n, i, j *Expr[Nat],
			q *Expr[Permutation[Nat]],
			given Fact,
		) {
			flipped := a.Have(
				"composing with the transposition flips the parity",
				"permutation_even(n, transposition(i, j) * q) ⇔ ¬permutation_even(n, q)",
				By(given, symmetric_group.ParityAfterTransposition.At(n, i, j, q)))
			a.Cases(a.Term("permutation_even(n, q)"))
			a.When(
				"q is even, and τ·q odd",
				func(b *Argument, even Fact) {
					b.Show(
						"so both sides are minus one",
						ByArith(even, flipped))
				})
			a.Otherwise(
				"q is odd, and τ·q even",
				func(b *Argument, odd Fact) {
					b.Show(
						"so the left side is one, and the right side, minus minus one, is one",
						ByArith(c, odd, flipped, comm_ring.OneIn.Read(c)))
				})
		}),
})}

// ReplaceColumnMatrixOver — replacing a column of a matrix over R by a
// vector of the free module on the points below n leaves a matrix over R:
// outside the n×n block the replacement is zero by construction, and
// inside it each entry is the vector's or the matrix's own.
var ReplaceColumnMatrixOver = replaceColumnMatrixOverThm{family.Add(registry.ProofEntry{
	Name: "ReplaceColumnMatrixOver",
	Key:  "prop_b8235c4cdde2be79",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n:num. ∀P:(num → num → A). ∀j:num. ∀u:(num → A).",
		Hypotheses: []string{
			"matrix_over(R, n, P)",
			"u ∈ free_module_record(R, {i:num | i < n}).carrier",
		},
		Conclusion: "matrix_over(R, n, matrix_replace_column(R, n, P, j, u))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n *Expr[Nat],
			P *Arrow2[Nat, Nat, A],
			j *Expr[Nat],
			u *Arrow[Nat, A],
			h Fact,
		) {
			parts := a.Conjuncts(
				h,
				"P is a matrix over R",
				"and u a vector of the free module on the points below n")
			over := parts[0]
			values := a.Have(
				"u takes its values in R's carrier",
				"∀x:num. u(x) ∈ R.carrier",
				By(parts[1], function_module.FiniteSuppMember))
			a.Show(
				"the replacement is zero past row n and past column n, and inside the block an entry of u or of P",
				Simp(Fwd(MatrixOverDef), Fwd(matrix.MatrixDef), Fwd(vec_space.VecDef), Fwd(ColumnReplaceDef)),
				SplitConjAll(
					Case(
						"a row past n is the zero vector",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("i")
							past := b.Assume()
							b.Show(
								"each of its entries is zero",
								Funext(),
								Simp(Fwd(vec_space.VecZeroDef)),
								ByArith(past))
						})),
					Case(
						"an entry past column n is zero",
						ByArith()),
					Case(
						"an entry inside the block is u's or P's, in R's carrier",
						By(values, over, MatrixOverDef.At(R, a.MatAt[A](n, n, "P")))),
				))
		}),
})}

// DeterminantColumnMultilinear — over a commutative ring c the determinant
// of size n is multilinear in the columns: the determinant of a matrix over
// c lies in c, and replacing column j by u + v, or by a • u, splits it the
// same way. A Leibniz term reads column j at exactly one row r, the one its
// permutation p sends to j; with column j replaced by w the term is w(r)
// times the sign and the product of the other rows' entries, none of which
// reads column j. So each term is additive and homogeneous in w, and so is
// their finite sum. Each term lies in c, the matrix staying a matrix over c
// with a vector of the free module in column j (ReplaceColumnMatrixOver) and
// both factors of its terms lying in c (LeibnizFactorsIn).
var DeterminantColumnMultilinear = determinantColumnMultilinearThm{family.Add(registry.ProofEntry{
	Name: "DeterminantColumnMultilinear",
	Key:  "prop_c00f488518811d27",
	Build: family.Theorem(Statement{
		Binders:    "∀c:comm_ring_on(A). ∀n:num.",
		Conclusion: "column_multilinear(c, n, determinant(c, n))",
		Abbrev: Abbrev{
			{Name: "term", Text: "λM:(num → num → A). λp:permutation(num). " +
				"    «sign»(p) * module_sum(c.mul, c.one, {i:num | i < n}, λi:num. M(i, permutation_map(p, i)))"},
		},
	},
		func(a *Argument, c comm_ring.CommRingFact[on.C], n *Expr[Nat]) {
			indices := a.TermAs[Set[Nat]]("{i:num | i < n}")
			finiteIndices := num_segment.FiniteBelowStrict.At(n)
			symmetric := a.TermAs[Set[Permutation[Nat]]]("symmetric_group({i:num | i < n})")
			finitePermutations := a.Have(
				"the points below n have finitely many permutations",
				"finite(symmetric_group({i:num | i < n}))",
				By(finiteIndices, symmetric_group.SymmetricGroupFinite.At(indices)))
			ring := a.TermAs[RingOps[A]]("c")
			zero, carrier := a.TermAs[A]("c.zero"), a.TermAs[Set[A]]("c.carrier")
			vectors := a.Have(
				"the vectors over c on the points below n form a module over c",
				"module_on(c, free_module_record(c, {i:num | i < n}))",
				By(c, free_module.FreeModuleOn.At(ring, indices)))
			regular := module.RegularModuleOn.Read(c)
			termIn := a.Have(
				"a Leibniz term of a matrix over c lies in c: a sign times a finite product of entries",
				"∀Q:(num → num → A). matrix_over(c, n, Q) ⇒ ∀p:permutation(num). «term»(Q, p) ∈ c.carrier",
				Derive(func(b *Argument) {
					Q := b.FixAs[Fun2[Nat, Nat, A]]("Q")
					over := b.Assume()
					p := b.FixAs[Permutation[Nat]]("p")
					b.Show(
						"the sign and the product of the entries p picks both lie in c, which is closed under products",
						By(over, LeibnizFactorsIn.Read(c).At(n, Q, p), comm_ring.MulIn.Read(c)))
				}))
			reads := a.Have(
				"a Leibniz term reads column j at one row r alone, the row "+
					"its permutation sends to j, and P's entries on the other rows",
				Statement{
					Binders: "∀P:(num → num → A). ∀j:num.",
					Hypotheses: []string{
						"matrix_over(c, n, P)",
						"j < n",
					},
					Conclusion: "∀p:permutation(num). " +
						"    p ∈ symmetric_group({i:num | i < n}) ⇒ " +
						"    ∃r:num. " +
						"        module_sum(c.mul, " +
						"            c.one, " +
						"            delete({i:num | i < n}, r), " +
						"            λi:num. P(i, permutation_map(p, i))) ∈ " +
						"        c.carrier ∧ " +
						"        (∀w:(num → A). " +
						"            w ∈ finite_supp(c.zero, c.carrier, {i:num | i < n}) ⇒ " +
						"            module_sum(c.mul, " +
						"                c.one, " +
						"                {i:num | i < n}, " +
						"                λi:num. matrix_replace_column(c, n, P, j, w, i, permutation_map(p, i))) = " +
						"            w(r) * " +
						"            module_sum(c.mul, " +
						"                c.one, " +
						"                delete({i:num | i < n}, r), " +
						"                λi:num. P(i, permutation_map(p, i))))",
				},
				Derive(func(d *Argument) {
					P := d.FixAs[Fun2[Nat, Nat, A]]("P")
					j := d.FixAs[Nat]("j")
					given := d.Conjuncts(
						d.Assume(),
						"P is a matrix over c",
						"and j is a column")
					over, column := given[0], given[1]
					allEntries := d.Have(
						"every entry of P lies in c",
						"∀i k:num. P(i, k) ∈ c.carrier",
						By(over, MatrixOverEntries.Read(c).At(n, P)))
					p := d.FixAs[Permutation[Nat]]("p")
					isPerm := d.Assume()
					onto := d.Have(
						"p maps the naturals onto themselves",
						"image(permutation_map(p), 𝕌) = 𝕌",
						By(symmetric_group.MapBijective.At(p)))
					hit := d.Have(
						"so j is a value of p",
						"j ∈ image(permutation_map(p), 𝕌)",
						onto.Rw(),
						By(set_basic.InUniv))
					r, preimage := d.ObtainAs[Nat](
						"j is p(r) for some r",
						"∃r:num. j = permutation_map(p, r) ∧ r ∈ 𝕌",
						By(
							hit,
							set_basic.InImage.At(d.TermAs[Fun[Nat, Nat]]("permutation_map(p)"), d.TermAs[Set[Nat]]("𝕌"), j)))
					sendsToJ := d.Conjuncts(
						preimage,
						"p sends r to j",
						"and r is a natural number")[0]
					rowBelow := d.Have(
						"r lies below n: p fixes every number past n, and j is below n",
						"r < n",
						Derive(func(e *Argument) {
							past := e.SupposeNot()
							fixed := e.Have(
								"then p fixes r",
								"permutation_map(p, r) = r",
								By(past, isPerm, symmetric_group.InSymmetricGroup.At(indices, p)))
							e.Show(
								"so j = r would lie past n",
								ByArith(past, column, fixed, sendsToJ))
						}))
					oneToOne := d.Unfolded(d.Have(
						"p is one to one",
						"injective_on(𝕌, permutation_map(p))",
						By(symmetric_group.MapBijective.At(p))), functions.InjectiveOnDef)
					others := d.Have(
						"every other row reads a column below n other than j, p being one to one",
						"∀k:num. k ∈ delete({i:num | i < n}, r) ⇒ permutation_map(p, k) < n ∧ permutation_map(p, k) ≠ j",
						Derive(func(e *Argument) {
							k := e.FixAs[Nat]("k")
							inRest := e.Assume()
							other := e.Have(
								"k lies below n and is not r",
								"k < n ∧ k ≠ r",
								By(inRest, set_basic.InDelete.At(indices, k, r)))
							e.Show(
								"so p(k) lies below n and is not p(r) = j",
								SplitConj(
									Case(
										"p maps the points below n to points below n",
										By(isPerm, other, symmetric_group.SymmetricGroupMapsInto.At(indices, p, k))),
									Case(
										"and p(k) = j = p(r) would force k = r",
										Derive(func(f *Argument) {
											hitsJ := f.SupposeNot()
											f.Show(
												"so k would be r, which it is not",
												By(hitsJ, other, sendsToJ, oneToOne.At(k, r), set_basic.InUniv))
										})),
								))
						}))
					rest := d.TermAs[Set[Nat]]("delete({i:num | i < n}, r)")
					finiteRest := d.Have(
						"the other rows are finitely many",
						"finite(delete({i:num | i < n}, r))",
						By(finiteIndices, finite_set.FiniteDeleteImp.At(indices, r)))
					restIn := d.Have(
						"the product of the other rows' entries lies in c",
						"module_sum(c.mul, c.one, delete({i:num | i < n}, r), λi:num. P(i, permutation_map(p, i))) ∈ "+
							"c.carrier",
						By(
							allEntries,
							finiteRest,
							module.ModuleSumInMonoid.Read(comm_ring.MulMonoidOn.Read(c)).At(
								rest, d.TermAs[Fun[Nat, A]]("λi:num. P(i, permutation_map(p, i))"))))
					linear := d.Have(
						"with column j replaced by any w over c, the product of the entries p picks reads w once, at row r",
						Statement{
							Binders: "∀w:(num → A).",
							Hypotheses: []string{
								"w ∈ finite_supp(c.zero, c.carrier, {i:num | i < n})",
							},
							Conclusion: "module_sum(c.mul, " +
								"    c.one, " +
								"    {i:num | i < n}, " +
								"    λi:num. matrix_replace_column(c, n, P, j, w, i, permutation_map(p, i))) = " +
								"w(r) * module_sum(c.mul, c.one, delete({i:num | i < n}, r), λi:num. P(i, permutation_map(p, i)))",
						},
						Derive(func(e *Argument) {
							w := e.FixAs[Fun[Nat, A]]("w")
							wIn := e.Assume()
							factors := e.TermAs[Fun[Nat, A]](
								"λi:num. matrix_replace_column(c, n, P, j, w, i, permutation_map(p, i))")
							factorsIn := e.Have(
								"every factor of the product lies in c, the replaced matrix being a matrix over c",
								"∀i:num. matrix_replace_column(c, n, P, j, w, i, permutation_map(p, i)) ∈ c.carrier",
								By(
									wIn,
									over,
									ReplaceColumnMatrixOver.At(ring, n, P, j, w),
									MatrixOverEntries.Read(c).At(
										n, e.TermAs[Fun2[Nat, Nat, A]]("matrix_replace_column(c, n, P, j, w)"))))
							atR := e.Have(
								"at row r the replaced matrix reads w(r)",
								"matrix_replace_column(c, n, P, j, w, r, permutation_map(p, r)) = w(r)",
								sendsToJ.RwRev(),
								Simp(Fwd(ColumnReplaceDef)),
								By(rowBelow, column))
							agree := e.Have(
								"off row r the replaced matrix agrees with P",
								Statement{
									Binders: "∀k:num.",
									Hypotheses: []string{
										"k ∈ delete({i:num | i < n}, r)",
									},
									Conclusion: "matrix_replace_column(c, n, P, j, w, k, permutation_map(p, k)) = " +
										"P(k, permutation_map(p, k))",
								},
								Derive(func(f *Argument) {
									k := f.FixAs[Nat]("k")
									inRest := f.Assume()
									bounds := f.Have(
										"k and p(k) lie below n, and p(k) is not j",
										"k < n ∧ permutation_map(p, k) < n ∧ permutation_map(p, k) ≠ j",
										By(inRest, others.At(k), set_basic.InDelete.At(indices, k, r)))
									f.Show(
										"so the entry at (k, p(k)) is P's",
										Simp(Fwd(ColumnReplaceDef)),
										By(bounds))
								}))
							e.Show(
								"the factor at row r splits off the product, and the rest is P's",
								CalcEq(
									Leg(
										e.TermAs[A](
											"matrix_replace_column(c, n, P, j, w, r, permutation_map(p, r)) * "+
												"module_sum(c.mul, "+
												"    c.one, "+
												"    delete({i:num | i < n}, r), "+
												"    λi:num. matrix_replace_column(c, n, P, j, w, i, permutation_map(p, i)))"),
										"r lies below n, so its factor splits off the product",
										By(
											rowBelow,
											finiteIndices,
											factorsIn,
											module.ModuleSumDeleteMonoid.Read(comm_ring.MulMonoidOn.Read(c)).At(indices, r, factors))),
									Leg(
										e.TermAs[A](
											"w(r) * "+
												"module_sum(c.mul, "+
												"    c.one, "+
												"    delete({i:num | i < n}, r), "+
												"    λi:num. matrix_replace_column(c, n, P, j, w, i, permutation_map(p, i)))"),
										"that factor is w(r)",
										By(atR)),
									FinalLeg(
										"and off row r those factors are P's",
										By(
											agree,
											module.ModuleSumCongruence.At(e.TermAs[Op[A]]("c.mul"), e.TermAs[A]("c.one"), rest, factors,
												e.TermAs[Fun[Nat, A]]("λi:num. P(i, permutation_map(p, i))")))),
								))
						}))
					d.Show(
						"so r is that row",
						Witness(r),
						By(restIn, linear))
				}))
			a.Show(
				"so the determinant is multilinear in the columns",
				Unfold(ColumnMultilinearDef),
				SplitConjAll(
					Case(
						"a matrix over c has its determinant in c, a finite sum of terms in c",
						Derive(func(b *Argument) {
							P := b.FixAs[Fun2[Nat, Nat, A]]("P")
							over := b.Assume()
							b.Show(
								"the Leibniz sum runs over the finitely many permutations, each term in c",
								Unfold(DeterminantDef),
								By(
									finitePermutations,
									over,
									termIn.At(P),
									module.ModuleSumInMonoid.Read(comm_ring.AddMonoidOn.Read(c)).At(symmetric,
										b.TermAs[Fun[Permutation[Nat], A]]("«term»(P)"))))
						})),
					Case(
						"replacing column j by u + v splits the determinant term by term",
						Derive(func(b *Argument) {
							P := b.FixAs[Fun2[Nat, Nat, A]]("P")
							j := b.FixAs[Nat]("j")
							u := b.FixAs[Fun[Nat, A]]("u")
							v := b.FixAs[Fun[Nat, A]]("v")
							given := b.Conjuncts(
								b.Assume(),
								"P is a matrix over c",
								"j is a column",
								"u is a vector over c",
								"and so is v")
							over, uVec, vVec := given[0], given[2], given[3]
							uIn := b.Have(
								"every coordinate of u lies in c",
								"∀x:num. u(x) ∈ c.carrier",
								By(uVec, function_module.FiniteSuppMember.At(zero, carrier, indices, u)))
							vIn := b.Have(
								"and of v",
								"∀x:num. v(x) ∈ c.carrier",
								By(vVec, function_module.FiniteSuppMember.At(zero, carrier, indices, v)))
							sumVec := b.Have(
								"so u + v is a vector over c",
								"fun_add(u, v) ∈ finite_supp(c.zero, c.carrier, {i:num | i < n})",
								By(uVec, vVec, group.MulIn.Read(module.AddGroupOn.Read(vectors))))
							perTerm := b.Have(
								"each Leibniz term reads the new column once, at the row "+
									"its permutation sends to j, so it is additive in that column",
								Statement{
									Binders: "∀p:permutation(num).",
									Hypotheses: []string{
										"p ∈ symmetric_group({i:num | i < n})",
									},
									Conclusion: "«term»(matrix_replace_column(c, n, P, j, fun_add(u, v)), p) = " +
										"«term»(matrix_replace_column(c, n, P, j, u), p) + «term»(matrix_replace_column(c, n, P, j, v), p)",
								},
								Derive(func(d *Argument) {
									p := d.FixAs[Permutation[Nat]]("p")
									pInGroup := d.Assume()
									r, row := d.UnpackAs[Nat](GroupPremises(given[0], given[1], pInGroup, reads.At(P, j, p)), "r")
									parts := d.Conjuncts(
										row,
										"the other rows' product lies in c",
										"and the product of the entries p picks reads column j at row r")
									restIn, linear := parts[0], parts[1]
									d.Show(
										"so u + v enters the term as u(r) + v(r)",
										Simp(Fwd(linear), Fwd(sumVec)),
										Simp(Fwd(function_module.FunAddDef)),
										ByArith(c, over, LeibnizFactorsIn.Read(c).At(n, P, p), uIn.At(r), vIn.At(r), restIn))
								}))
							replacedU := b.TermAs[Fun2[Nat, Nat, A]]("matrix_replace_column(c, n, P, j, u)")
							replacedV := b.TermAs[Fun2[Nat, Nat, A]]("matrix_replace_column(c, n, P, j, v)")
							termsU := b.TermAs[Fun[Permutation[Nat], A]]("«term»(matrix_replace_column(c, n, P, j, u))")
							termsV := b.TermAs[Fun[Permutation[Nat], A]]("«term»(matrix_replace_column(c, n, P, j, v))")
							b.Show(
								"summing the term identities over the permutations",
								Unfold(DeterminantDef),
								CalcEq(
									Leg(
										b.TermAs[A](
											"module_sum(c.add, "+
												"    c.zero, "+
												"    symmetric_group({i:num | i < n}), "+
												"    λp:permutation(num). "+
												"        «term»(matrix_replace_column(c, n, P, j, u), p) + "+
												"        «term»(matrix_replace_column(c, n, P, j, v), p))"),
										"each term is its u-term plus its v-term",
										By(perTerm, module.ModuleSumCongruence)),
									FinalLeg(
										"and a finite sum of sums of terms in c is the sum of the two sums",
										By(
											finitePermutations,
											over,
											uVec,
											ReplaceColumnMatrixOver.At(ring, n, P, j, u),
											termIn.At(replacedU),
											vVec,
											ReplaceColumnMatrixOver.At(ring, n, P, j, v),
											termIn.At(replacedV),
											module.ModuleSumAdd.Read(regular).At(symmetric, termsU, termsV))),
								))
						})),
					Case(
						"replacing column j by a • u multiplies the determinant by a, term by term",
						Derive(func(b *Argument) {
							P := b.FixAs[Fun2[Nat, Nat, A]]("P")
							j := b.FixAs[Nat]("j")
							u := b.FixAs[Fun[Nat, A]]("u")
							scalar := b.FixAs[A]("a")
							given := b.Conjuncts(
								b.Assume(),
								"P is a matrix over c",
								"j is a column",
								"u is a vector over c",
								"and a is a scalar")
							over, uVec, scalarIn := given[0], given[2], given[3]
							uIn := b.Have(
								"every coordinate of u lies in c",
								"∀x:num. u(x) ∈ c.carrier",
								By(uVec, function_module.FiniteSuppMember.At(zero, carrier, indices, u)))
							scaledVec := b.Have(
								"so a • u is a vector over c",
								"fun_smul(a, u) ∈ finite_supp(c.zero, c.carrier, {i:num | i < n})",
								By(uVec, scalarIn, module.SmulIn.Read(vectors)))
							perTerm := b.Have(
								"each Leibniz term reads the new column once, at the row its "+
									"permutation sends to j, so it is homogeneous in that column",
								Statement{
									Binders: "∀p:permutation(num).",
									Hypotheses: []string{
										"p ∈ symmetric_group({i:num | i < n})",
									},
									Conclusion: "«term»(matrix_replace_column(c, n, P, j, fun_smul(a, u)), p) = " +
										"a * «term»(matrix_replace_column(c, n, P, j, u), p)",
								},
								Derive(func(d *Argument) {
									p := d.FixAs[Permutation[Nat]]("p")
									pInGroup := d.Assume()
									r, row := d.UnpackAs[Nat](GroupPremises(given[0], given[1], pInGroup, reads.At(P, j, p)), "r")
									parts := d.Conjuncts(
										row,
										"the other rows' product lies in c",
										"and the product of the entries p picks reads column j at row r")
									restIn, linear := parts[0], parts[1]
									d.Show(
										"so a • u enters the term as a * u(r)",
										Simp(Fwd(linear), Fwd(scaledVec)),
										Simp(Fwd(function_module.FunSmulDef)),
										ByArith(c, over, LeibnizFactorsIn.Read(c).At(n, P, p), uIn.At(r), scalarIn, restIn))
								}))
							replacedU := b.TermAs[Fun2[Nat, Nat, A]]("matrix_replace_column(c, n, P, j, u)")
							termsU := b.TermAs[Fun[Permutation[Nat], A]]("«term»(matrix_replace_column(c, n, P, j, u))")
							b.Show(
								"summing the term identities over the permutations",
								Unfold(DeterminantDef),
								CalcEq(
									Leg(
										b.TermAs[A](
											"module_sum(c.add, "+
												"    c.zero, "+
												"    symmetric_group({i:num | i < n}), "+
												"    λp:permutation(num). a * «term»(matrix_replace_column(c, n, P, j, u), p))"),
										"each term is a times its u-term",
										By(perTerm, module.ModuleSumCongruence)),
									FinalLeg(
										"and a passes out of a finite sum of terms in c",
										By(
											finitePermutations,
											over,
											uVec,
											ReplaceColumnMatrixOver.At(ring, n, P, j, u),
											termIn.At(replacedU),
											module.ModuleSumSmul.Read(regular).At(symmetric, b.MemberOf[on.C](scalar, scalarIn), termsU))),
								))
						})),
				))
		}),
})}

// DeterminantInCarrier — the determinant of a matrix over c lies in c: it
// is the first clause of the determinant's multilinearity
// (DeterminantColumnMultilinear).
var DeterminantInCarrier = determinantInCarrierThm{family.Add(registry.ProofEntry{
	Name: "DeterminantInCarrier",
	Key:  "prop_d5ee41a324702076",
	Build: family.Theorem(Statement{
		Binders:    "∀c:comm_ring_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{"matrix_over(c, n, P)"},
		Conclusion: "determinant(c, n, P) ∈ c.carrier",
	}, func(
		a *Argument,
		c comm_ring.CommRingFact[on.C],
		n *Expr[Nat],
		P *Arrow2[Nat, Nat, A],
		over Fact,
	) {
		a.Show(
			"the determinant is multilinear in the columns, and a multilinear form takes its values in c",
			By(
				over,
				DeterminantColumnMultilinear.Read(c).At(n),
				ColumnMultilinearDef.At(
					a.TermAs[RingOps[A]]("c"), n, a.TermAs[Fun[Fun2[Nat, Nat, A], A]]("determinant(c, n)"))))
	}),
})}

// DeterminantEqualColumns — a matrix over c with two equal columns has
// determinant zero, in every characteristic. Swapping the two columns
// leaves P as it is, so P's term at τ·q has the product of its term at q
// and the opposite sign (SignValueAfterTransposition). The permutations
// split into the even ones E and the odd ones O, and q ↦ τ·q maps E onto
// O one to one, so the sum over O is the sum over E of the terms at τ·q,
// minus the sum over E: the two halves cancel term by term, and no
// division by two is needed.
var DeterminantEqualColumns = determinantEqualColumnsThm{family.Add(registry.ProofEntry{
	Name: "DeterminantEqualColumns",
	Key:  "prop_446726b91b02e2cd",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀P:(num → num → A). ∀i j:num.",
		Hypotheses: []string{
			"matrix_over(c, n, P)",
			"i < n",
			"j < n",
			"i ≠ j",
			"transpose(P, i) = transpose(P, j)",
		},
		Conclusion: "determinant(c, n, P) = c.zero",
		Abbrev: Abbrev{
			{Name: "S", Text: "symmetric_group({k:num | k < n})"},
			{Name: "term", Text: "λq:permutation(num). " +
				"    «sign»(q) * module_sum(c.mul, c.one, {k:num | k < n}, λk:num. P(k, permutation_map(q, k)))"},
		},
	},
		func(
			a *Argument,
			c comm_ring.CommRingFact[on.C],
			n *Expr[Nat],
			P *Arrow2[Nat, Nat, A],
			i, j *Expr[Nat],
			given Fact,
		) {
			regular := module.RegularModuleOn.Read(c)
			term := a.TermAs[Fun[Permutation[Nat], A]]("«term»")
			indices := a.TermAs[Set[Nat]]("{k:num | k < n}")
			symmetric := a.TermAs[Set[Permutation[Nat]]]("«S»")
			tau := a.TermAs[Permutation[Nat]]("transposition(i, j)")
			permutationGroup := a.TermAs[group.GroupOps[Permutation[Nat]]]("permutation_group")
			finite := a.Have(
				"there are finitely many permutations of the points below n",
				"finite(«S»)",
				By(num_segment.FiniteBelowStrict.At(n), symmetric_group.SymmetricGroupFinite.At(indices)))
			undo := a.Have(
				"τ undoes itself",
				"∀q:permutation(num). transposition(i, j) * (transposition(i, j) * q) = q",
				a.ForEach(func(q *Expr[Permutation[Nat]]) Action {
					return By(
						group.Assoc.Read(symmetric_group.SymmetricGroup).At(tau, tau, q),
						symmetric_group.TranspositionSelfInverse.At(i, j),
						group.LeftIdentity.Read(symmetric_group.SymmetricGroup).At(q))
				}))
			stays := a.Have(
				"τ·q permutes the points below n when q does: their permutations are a subgroup holding τ",
				"∀q:permutation(num). q ∈ «S» ⇒ transposition(i, j) * q ∈ «S»",
				a.ForEach(func(q *Expr[Permutation[Nat]]) Action {
					return By(
						given,
						group.SubgroupMul.At(permutationGroup, symmetric, tau, q),
						symmetric_group.SymmetricGroupSubgroup.At(indices),
						symmetric_group.TranspositionInSymmetricGroup.At(indices, i, j))
				}))
			shift := a.TermAs[Fun[Permutation[Nat], Permutation[Nat]]](
				"λq:permutation(num). transposition(i, j) * q")
			columns := a.Have(
				"columns i and j of P are one column",
				"∀r:num. P(r, i) = P(r, j)",
				a.ForEach(func(r *Expr[Nat]) Action {
					return By(given, matrix.TransposeDef.At(P, i, r), matrix.TransposeDef.At(P, j, r))
				}))
			fixed := a.Have(
				"so swapping them leaves every entry of P where it is",
				"∀r x:num. P(r, permutation_map(transposition(i, j), x)) = P(r, x)",
				By(columns, symmetric_group.MapTransposition))
			sameProduct := a.Have(
				"so P's product at τ·q is its product at q",
				"∀q:permutation(num). "+
					"    module_sum(c.mul, "+
					"        c.one, "+
					"        {k:num | k < n}, "+
					"        λk:num. P(k, permutation_map(transposition(i, j) * q, k))) = "+
					"    module_sum(c.mul, c.one, {k:num | k < n}, λk:num. P(k, permutation_map(q, k)))",
				Simp(Fwd(symmetric_group.MapCompose), Fwd(fixed)),
				Basic())
			terms := a.Have(
				"every Leibniz term of P lies in c",
				"∀q:permutation(num). «term»(q) ∈ c.carrier",
				a.ForEach(func(q *Expr[Permutation[Nat]]) Action {
					return By(given, LeibnizFactorsIn.Read(c).At(n, P, q), comm_ring.MulIn.Read(c))
				}))
			opposite := a.Have(
				"so P's term at τ·q is minus its term at q",
				"∀q:permutation(num). q ∈ «S» ⇒ «term»(transposition(i, j) * q) = -«term»(q)",
				Derive(func(b *Argument) {
					q := b.FixAs[Permutation[Nat]]("q")
					inS := b.Assume()
					factors := b.Have(
						"the factors of q's term lie in c, and τ·q has the opposite sign",
						"«sign»(q) ∈ c.carrier ∧ "+
							"module_sum(c.mul, c.one, {k:num | k < n}, λk:num. P(k, permutation_map(q, k))) ∈ c.carrier ∧ "+
							"«sign»(transposition(i, j) * q) = -«sign»(q)",
						By(
							given,
							inS,
							LeibnizFactorsIn.Read(c).At(n, P, q),
							SignValueAfterTransposition.Read(c).At(n, i, j, q)))
					b.Show(
						"so the two terms are opposite, τ·q having the same product",
						ByArith(c, factors, sameProduct.At(q)))
				}))
			even, evenDef := a.LetAs[Set[Permutation[Nat]]](
				"E", "{q:permutation(num) | q ∈ «S» ∧ permutation_even(n, q)}")
			odd, oddDef := a.LetAs[Set[Permutation[Nat]]](
				"O", "{q:permutation(num) | q ∈ «S» ∧ ¬permutation_even(n, q)}")
			split := a.Have(
				"a permutation of the points below n is even or odd",
				"«S» = E ∪ O",
				BySets(evenDef, oddDef))
			apart := a.Have(
				"and never both",
				"disjoint(E, O)",
				BySets(evenDef, oddDef))
			finiteParts := a.Have(
				"so the even and the odd ones are finitely many",
				"finite(E) ∧ finite(O)",
				By(finite, split, finite_set.FiniteUnion.At(even, odd)))
			exchanged := a.Have(
				"τ· sends an even permutation to an odd one and an odd one to an even one",
				"∀q:permutation(num). "+
					"    (q ∈ E ⇒ transposition(i, j) * q ∈ O) ∧ (q ∈ O ⇒ transposition(i, j) * q ∈ E)",
				Derive(func(b *Argument) {
					q := b.FixAs[Permutation[Nat]]("q")
					toOdd := b.Have(
						"an even q goes to an odd τ·q",
						"q ∈ E ⇒ transposition(i, j) * q ∈ O",
						Derive(func(d *Argument) {
							inE := d.Assume()
							evenQ := d.Have(
								"q permutes the points below n and is even",
								"q ∈ «S» ∧ permutation_even(n, q)",
								BySets(evenDef, inE))
							oddImage := d.Have(
								"so τ·q permutes them and is odd",
								"transposition(i, j) * q ∈ «S» ∧ ¬permutation_even(n, transposition(i, j) * q)",
								By(given, evenQ, stays.At(q), symmetric_group.ParityAfterTransposition.At(n, i, j, q)))
							d.Show(
								"so τ·q lies in O",
								BySets(oddDef, oddImage))
						}))
					toEven := b.Have(
						"an odd q goes to an even τ·q",
						"q ∈ O ⇒ transposition(i, j) * q ∈ E",
						Derive(func(d *Argument) {
							inO := d.Assume()
							oddQ := d.Have(
								"q permutes the points below n and is odd",
								"q ∈ «S» ∧ ¬permutation_even(n, q)",
								BySets(oddDef, inO))
							evenImage := d.Have(
								"so τ·q permutes them and is even",
								"transposition(i, j) * q ∈ «S» ∧ permutation_even(n, transposition(i, j) * q)",
								By(given, oddQ, stays.At(q), symmetric_group.ParityAfterTransposition.At(n, i, j, q)))
							d.Show(
								"so τ·q lies in E",
								BySets(evenDef, evenImage))
						}))
					b.Show(
						"so τ· exchanges the even and the odd permutations",
						By(toOdd, toEven))
				}))
			onto := a.Have(
				"so q ↦ τ·q maps E onto O",
				"image(λq:permutation(num). transposition(i, j) * q, E) = O",
				BySets(undo, exchanged))
			oneToOne := a.Have(
				"one to one, τ undoing it",
				"injective_on(E, λq:permutation(num). transposition(i, j) * q)",
				BySets(undo, functions.InjectiveOnDef))
			oppositeOnE := a.Have(
				"in particular on E",
				"∀q:permutation(num). q ∈ E ⇒ «term»(transposition(i, j) * q) = -«term»(q)",
				BySets(opposite, evenDef))
			evenSum := a.Have(
				"the sum over E lies in c",
				"module_sum(c.add, c.zero, E, «term») ∈ c.carrier",
				By(finiteParts, terms, module.ModuleSumIn.Read(regular).At(even, term)))
			oddSum := a.Have(
				"the sum over the odd permutations is minus the sum over the even ones",
				"module_sum(c.add, c.zero, O, «term») = -module_sum(c.add, c.zero, E, «term»)",
				CalcEq(
					Leg(
						a.TermAs[A]("module_sum(c.add, c.zero, E, λq:permutation(num). «term»(transposition(i, j) * q))"),
						"the odd permutations are the τ·q for q even, each once",
						By(finiteParts, terms, onto, oneToOne, module.ModuleSumImage.Read(regular).At(even, shift, term))),
					Leg(
						a.TermAs[A]("module_sum(c.add, c.zero, E, λq:permutation(num). -«term»(q))"),
						"paired terms are opposite",
						By(
							oppositeOnE,
							module.ModuleSumCongruence.At(
								a.TermAs[Op[A]]("c.add"),
								a.TermAs[A]("c.zero"),
								even,
								a.TermAs[Fun[Permutation[Nat], A]]("λq:permutation(num). «term»(transposition(i, j) * q)"),
								a.TermAs[Fun[Permutation[Nat], A]]("λq:permutation(num). -«term»(q)")))),
					FinalLeg(
						"a sum of negatives is the negative of the sum",
						By(finiteParts, terms, module.ModuleSumNeg.Read(regular).At(even, term))),
				))
			a.Show(
				"the sums over the even and the odd permutations cancel",
				CalcEq(
					Leg(
						a.TermAs[A]("module_sum(c.add, c.zero, «S», «term»)"),
						"by definition",
						Simp(Fwd(DeterminantDef)),
						Basic()),
					Leg(
						a.TermAs[A]("module_sum(c.add, c.zero, E ∪ O, «term»)"),
						"a permutation is even or odd",
						split.Rw(),
						Basic()),
					Leg(
						a.TermAs[A]("module_sum(c.add, c.zero, E, «term») + module_sum(c.add, c.zero, O, «term»)"),
						"and never both",
						By(finiteParts, apart, terms, module.ModuleSumDisjointUnion.Read(regular).At(even, odd, term))),
					FinalLeg(
						"and a member of c plus its negative is zero",
						oddSum.Rw(),
						ByArith(c, evenSum)),
				))
		}),
})}

// AlternatingFormScalarMultiple — a multiple t·F of an alternating form F by
// a member t of c is alternating: t·F takes its values in c, its additivity
// and homogeneity in each column are F's multiplied through by t, and where
// F vanishes so does t·F.
var AlternatingFormScalarMultiple = alternatingFormScalarMultipleThm{family.Add(registry.ProofEntry{
	Name: "AlternatingFormScalarMultiple",
	Key:  "prop_56203d0edaac2e11",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀F:((num → num → A) → A). ∀t:A.",
		Hypotheses: []string{
			"alternating_form(c, n, F)",
			"t ∈ c.carrier",
		},
		Conclusion: "alternating_form(c, n, λQ:(num → num → A). t * F(Q))",
	},
		func(
			a *Argument,
			c comm_ring.CommRingFact[on.C],
			n *Expr[Nat],
			F *Arrow[Fun2[Nat, Nat, A], A],
			t *Expr[A],
			h Fact,
		) {
			parts := a.Conjuncts(
				h,
				"F is an alternating form",
				"and t lies in c")
			tIn := parts[1]
			form := a.Conjuncts(
				a.Unfolded(parts[0], AlternatingFormDef),
				"F is multilinear in the columns",
				"and vanishes when two columns agree")
			multilinear := a.Conjuncts(
				a.Unfolded(form[0], ColumnMultilinearDef),
				"F takes its values in c",
				"is additive in each column",
				"and homogeneous in each column")
			values, additive, homogeneous, vanishes := multilinear[0], multilinear[1], multilinear[2], form[1]
			a.Show(
				"t·F is multilinear in the columns and vanishes when two columns agree",
				Simp(Fwd(AlternatingFormDef), Fwd(ColumnMultilinearDef)),
				SplitConjAll(
					Case(
						"t·F takes its values in c",
						By(comm_ring.MulIn.Read(c), values, tIn)),
					Case(
						"t·F is additive in each column",
						Derive(func(b *Argument) {
							b.FixAs[Fun2[Nat, Nat, A]]("P")
							b.FixAs[Nat]("j")
							b.FixAs[Fun[Nat, A]]("u")
							b.FixAs[Fun[Nat, A]]("v")
							guard := b.Assume()
							members := b.Have(
								"F at the two replaced matrices lies in c",
								"F(matrix_replace_column(c, n, P, j, u)) ∈ c.carrier ∧ "+
									"F(matrix_replace_column(c, n, P, j, v)) ∈ c.carrier",
								By(values, guard, ReplaceColumnMatrixOver))
							sum := b.Have(
								"F is additive in column j",
								"F(matrix_replace_column(c, n, P, j, fun_add(u, v))) = "+
									"F(matrix_replace_column(c, n, P, j, u)) + F(matrix_replace_column(c, n, P, j, v))",
								By(guard, additive))
							b.Show(
								"so t·F is, t distributing over the sum",
								sum.Rw(),
								ByArith(c, tIn, members))
						})),
					Case(
						"t·F is homogeneous in each column",
						Derive(func(b *Argument) {
							b.FixAs[Fun2[Nat, Nat, A]]("P")
							b.FixAs[Nat]("j")
							b.FixAs[Fun[Nat, A]]("u")
							b.FixAs[A]("a")
							guard := b.Assume()
							member := b.Have(
								"F at the replaced matrix lies in c",
								"F(matrix_replace_column(c, n, P, j, u)) ∈ c.carrier",
								By(values, guard, ReplaceColumnMatrixOver))
							scaled := b.Have(
								"F is homogeneous in column j",
								"F(matrix_replace_column(c, n, P, j, fun_smul(a, u))) = "+
									"a * F(matrix_replace_column(c, n, P, j, u))",
								By(guard, homogeneous))
							b.Show(
								"so t·F is, the two scalars commuting",
								scaled.Rw(),
								ByArith(c, tIn, member, guard))
						})),
					Case(
						"t·F vanishes where F does",
						Derive(func(b *Argument) {
							b.FixAs[Fun2[Nat, Nat, A]]("P")
							b.FixAs[Nat]("i")
							b.FixAs[Nat]("j")
							guard := b.Assume()
							zero := b.Have(
								"F vanishes at P, two of its columns agreeing",
								"F(P) = c.zero",
								By(guard, vanishes))
							b.Show(
								"and t times zero is zero",
								zero.Rw(),
								ByArith(c, tIn))
						})),
				))
		}),
})}

// AlternatingFormSwapColumns — exchanging two columns of a matrix changes
// the sign of an alternating form. With x put in column i and y in column j
// of P, the form is additive in x and in y and vanishes when x = y; at
// x = y = u + v, u and v the columns i and j of P, its four terms leave
// F(P) + F(P with the columns exchanged) = 0.
var AlternatingFormSwapColumns = alternatingFormSwapColumnsThm{family.Add(registry.ProofEntry{
	Name: "AlternatingFormSwapColumns",
	Key:  "prop_97b0e7920e573629",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀F:((num → num → A) → A). ∀P:(num → num → A). ∀i j:num.",
		Hypotheses: []string{
			"alternating_form(c, n, F)",
			"matrix_over(c, n, P)",
			"i < n",
			"j < n",
			"i ≠ j",
		},
		Conclusion: "F(λr:num. λs:num. P(r, permutation_map(transposition(i, j), s))) = -F(P)",
		Abbrev: Abbrev{
			{Name: "Fᵢⱼ", Text: "λx:(num → A). λy:(num → A). " +
				"    F(matrix_replace_column(c, n, matrix_replace_column(c, n, P, i, x), j, y))"},
		},
	},
		func(
			a *Argument,
			c comm_ring.CommRingFact[on.C],
			n *Expr[Nat],
			F *Arrow[Fun2[Nat, Nat, A], A],
			P *Arrow2[Nat, Nat, A],
			i, j *Expr[Nat],
			h Fact,
		) {
			parts := a.Conjuncts(
				h,
				"F is an alternating form",
				"P is a matrix over c",
				"i lies below n",
				"so does j",
				"and i is not j")
			over, iBelow, jBelow, distinct := parts[1], parts[2], parts[3], parts[4]
			form := a.Conjuncts(
				a.Unfolded(parts[0], AlternatingFormDef),
				"F is multilinear in the columns",
				"and vanishes when two columns agree")
			multilinear := a.Conjuncts(
				a.Unfolded(form[0], ColumnMultilinearDef),
				"F takes its values in c",
				"is additive in each column",
				"and homogeneous in each column")
			values, additive, vanishes := multilinear[0], multilinear[1], form[1]
			ring := a.TermAs[RingOps[A]]("c")

			entries := a.Have(
				"every entry of P lies in c",
				"∀r s:num. P(r, s) ∈ c.carrier",
				By(over, MatrixOverEntries.Read(c).At(n, P)))
			outside := a.Have(
				"and P vanishes outside the n×n block",
				"∀r s:num. ¬(r < n ∧ s < n) ⇒ P(r, s) = c.zero",
				By(over, MatrixOverEntries.Read(c).At(n, P), nat_order.NotLessThan))
			points := a.TermAs[Set[Nat]]("{k:num | k < n}")
			columns := a.Have(
				"every column of P lies in the free module on the points below n",
				"∀s:num. transpose(P, s) ∈ free_module_record(c, {k:num | k < n}).carrier",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("s")
					support := b.Have(
						"column s is zero off the points below n",
						"fun_support(c.zero, λx:num. P(x, s)) ⊆ {k:num | k < n}",
						BySets(outside))
					b.Show(
						"so it is finitely supported below n, and its entries lie in c",
						Simp(
							Fwd(free_module.FreeModuleRecordDef),
							Fwd(function_module.FiniteSuppMember),
							Fwd(matrix.TransposeDef)),
						SplitConjAll(
							Case(
								"its support is finite, inside the points below n",
								By(support, finite_set.FiniteSubset, num_segment.FiniteBelowStrict.At(n))),
							Case(
								"its support lies below n",
								By(support)),
							Case(
								"its entries lie in c",
								By(entries)),
						))
				}))
			freeModule := a.Have(
				"the free module on the points below n is a module over c",
				"module_on(c, free_module_record(c, {k:num | k < n}))",
				By(c, free_module.FreeModuleOn.At(ring, points)))
			u, v := a.TermAs[Fun[Nat, A]]("transpose(P, i)"), a.TermAs[Fun[Nat, A]]("transpose(P, j)")
			w := a.TermAs[Fun[Nat, A]]("fun_add(transpose(P, i), transpose(P, j))")
			sum := a.Have(
				"so does the sum of the columns i and j",
				"fun_add(transpose(P, i), transpose(P, j)) ∈ free_module_record(c, {k:num | k < n}).carrier",
				By(group.MulIn.Read(module.AddGroupOn.Read(freeModule)), columns.At(i), columns.At(j)))

			replacedIn := a.Have(
				"F at P with two vectors of the free module put in columns i and j lies in c",
				Statement{
					Binders: "∀x y:(num → A).",
					Hypotheses: []string{
						"x ∈ free_module_record(c, {k:num | k < n}).carrier",
						"y ∈ free_module_record(c, {k:num | k < n}).carrier",
					},
					Conclusion: "«Fᵢⱼ»(x, y) ∈ c.carrier",
				},
				By(values, over, ReplaceColumnMatrixOver))
			exchange := a.Have(
				"filling the distinct columns i and j can be done in either order",
				"∀x y:(num → A). "+
					"    matrix_replace_column(c, n, matrix_replace_column(c, n, P, i, x), j, y) = "+
					"    matrix_replace_column(c, n, matrix_replace_column(c, n, P, j, y), i, x)",
				Derive(func(b *Argument) {
					b.FixAs[Fun[Nat, A]]("x")
					b.FixAs[Fun[Nat, A]]("y")
					b.Show(
						"entry by entry the two fillings agree",
						Funext(),
						Simp(Fwd(ColumnReplaceDef)),
						By(distinct))
				}))
			inJ := a.Have(
				"F is additive in the vector put in column j",
				Statement{
					Binders: "∀x y z:(num → A).",
					Hypotheses: []string{
						"x ∈ free_module_record(c, {k:num | k < n}).carrier",
						"y ∈ free_module_record(c, {k:num | k < n}).carrier",
						"z ∈ free_module_record(c, {k:num | k < n}).carrier",
					},
					Conclusion: "«Fᵢⱼ»(x, fun_add(y, z)) = «Fᵢⱼ»(x, y) + «Fᵢⱼ»(x, z)",
				},
				By(additive, jBelow, over, ReplaceColumnMatrixOver))
			inI := a.Have(
				"and in the vector put in column i, column i being filled last once the fillings are exchanged",
				Statement{
					Binders: "∀x y z:(num → A).",
					Hypotheses: []string{
						"x ∈ free_module_record(c, {k:num | k < n}).carrier",
						"y ∈ free_module_record(c, {k:num | k < n}).carrier",
						"z ∈ free_module_record(c, {k:num | k < n}).carrier",
					},
					Conclusion: "«Fᵢⱼ»(fun_add(x, y), z) = «Fᵢⱼ»(x, z) + «Fᵢⱼ»(y, z)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[Nat, A]]("x")
					b.FixAs[Fun[Nat, A]]("y")
					b.FixAs[Fun[Nat, A]]("z")
					guard := b.Assume()
					b.Show(
						"F is additive in column i of P with column j filled",
						Simp(Fwd(exchange)),
						By(additive, iBelow, guard, over, ReplaceColumnMatrixOver))
				}))
			diagonal := a.Have(
				"F vanishes when the same vector fills columns i and j",
				"∀x:(num → A). x ∈ free_module_record(c, {k:num | k < n}).carrier ⇒ «Fᵢⱼ»(x, x) = c.zero",
				Derive(func(b *Argument) {
					b.FixAs[Fun[Nat, A]]("x")
					member := b.Assume()
					same := b.Have(
						"columns i and j of that matrix are both x, cut off at n",
						"transpose(matrix_replace_column(c, n, matrix_replace_column(c, n, P, i, x), j, x), i) = "+
							"transpose(matrix_replace_column(c, n, matrix_replace_column(c, n, P, i, x), j, x), j)",
						Funext(),
						Simp(Fwd(matrix.TransposeDef), Fwd(ColumnReplaceDef)),
						By(iBelow, jBelow))
					b.Show(
						"so F vanishes there",
						By(vanishes, distinct, iBelow, jBelow, same, member, over, ReplaceColumnMatrixOver))
				}))
			own := a.Have(
				"filling columns i and j with P's own columns gives P back",
				"matrix_replace_column(c, "+
					"    n, "+
					"    matrix_replace_column(c, n, P, i, transpose(P, i)), "+
					"    j, "+
					"    transpose(P, j)) = "+
					"P",
				Funext(),
				Simp(Fwd(ColumnReplaceDef), Fwd(matrix.TransposeDef)),
				By(outside))
			exchanged := a.Have(
				"filling them with P's columns exchanged gives P with columns i and j exchanged",
				"matrix_replace_column(c, "+
					"    n, "+
					"    matrix_replace_column(c, n, P, i, transpose(P, j)), "+
					"    j, "+
					"    transpose(P, i)) = "+
					"(λr:num. λs:num. P(r, permutation_map(transposition(i, j), s)))",
				Funext(),
				Simp(Fwd(ColumnReplaceDef), Fwd(matrix.TransposeDef), Fwd(symmetric_group.MapTransposition)),
				By(outside, distinct, iBelow, jBelow))

			firstColumn := a.Have(
				"u + v in both columns gives zero, and expanding column i splits it in two",
				"«Fᵢⱼ»(transpose(P, i), fun_add(transpose(P, i), transpose(P, j))) + "+
					"«Fᵢⱼ»(transpose(P, j), fun_add(transpose(P, i), transpose(P, j))) = "+
					"c.zero",
				By(columns.At(i), columns.At(j), sum, diagonal.At(w), inI.At(u, v, w)))
			mixed := a.Have(
				"so the two mixed terms cancel",
				"«Fᵢⱼ»(transpose(P, i), transpose(P, j)) + «Fᵢⱼ»(transpose(P, j), transpose(P, i)) = c.zero",
				CalcEq(
					Leg(
						a.TermAs[A]("«Fᵢⱼ»(transpose(P, i), transpose(P, i)) + "+
							"«Fᵢⱼ»(transpose(P, i), transpose(P, j)) + "+
							"(«Fᵢⱼ»(transpose(P, j), transpose(P, i)) + «Fᵢⱼ»(transpose(P, j), transpose(P, j)))"),
						"add the two terms with a repeated column, both zero",
						ByArith(
							c,
							columns.At(i),
							columns.At(j),
							diagonal.At(u),
							diagonal.At(v),
							replacedIn.At(u, v),
							replacedIn.At(v, u))),
					Leg(
						a.TermAs[A]("«Fᵢⱼ»(transpose(P, i), fun_add(transpose(P, i), transpose(P, j))) + "+
							"«Fᵢⱼ»(transpose(P, j), fun_add(transpose(P, i), transpose(P, j)))"),
						"the four terms are the expansion of u + v in column j",
						ByArith(
							c,
							columns.At(i),
							columns.At(j),
							inJ.At(u, u, v),
							inJ.At(v, u, v),
							replacedIn.At(u, u),
							replacedIn.At(u, v),
							replacedIn.At(v, u),
							replacedIn.At(v, v))),
					FinalLeg(
						"which vanishes, u + v filling column j",
						By(firstColumn)),
				))
			ownValue := a.Have(
				"the first of them is F(P)",
				"«Fᵢⱼ»(transpose(P, i), transpose(P, j)) = F(P)",
				own.Rw(),
				Basic())
			a.Show(
				"so F at P with the columns exchanged is -F(P)",
				exchanged.RwRev(),
				ownValue.RwRev(),
				ByArith(c, mixed, columns.At(i), columns.At(j), replacedIn.At(u, v), replacedIn.At(v, u)))
		}),
})}

// DeterminantAlternating — the determinant is an alternating form of the
// columns, and swapping two columns negates it: multilinearity is
// DeterminantColumnMultilinear, the vanishing on two equal columns is
// DeterminantEqualColumns, and a swap of two columns negates every
// alternating form (AlternatingFormSwapColumns).
var DeterminantAlternating = determinantAlternatingThm{family.Add(registry.ProofEntry{
	Name:    "DeterminantAlternating",
	Key:     "prop_29abaf282ca594b6",
	Reading: "The equation d=-d alone does not imply d=0 in characteristic two.",
	Build: family.Theorem("∀c:comm_ring_on(A). ∀n:num. "+
		"    alternating_form(c, n, determinant(c, n)) ∧ "+
		"    (∀P:(num → num → A). ∀i j:num. "+
		"        matrix_over(c, n, P) ∧ i < n ∧ j < n ∧ i ≠ j ⇒ "+
		"        determinant(c, n, λr:num. λs:num. P(r, permutation_map(transposition(i, j), s))) = "+
		"        -determinant(c, n, P))",
		func(a *Argument, c comm_ring.CommRingFact[on.C], n *Expr[Nat]) {
			alternating := a.Have(
				"multilinear in the columns and vanishing on two equal ones, the determinant is alternating",
				"alternating_form(c, n, determinant(c, n))",
				By(
					DeterminantEqualColumns.Read(c).AsFact().At(n),
					DeterminantColumnMultilinear.Read(c).At(n),
					AlternatingFormDef))
			a.Show(
				"and a swap of two columns negates it, as it negates every alternating form",
				By(
					alternating,
					AlternatingFormSwapColumns.Read(c).AsFact().At(
						n, a.TermAs[Fun[Fun2[Nat, Nat, A], A]]("determinant(c, n)"))))
		}),
})}

// DeterminantTranspose — a matrix over c and its transpose have the same
// determinant. The transpose's Leibniz term at p is P's term at p⁻¹, its
// product of entries reindexed by p⁻¹ and p⁻¹ having the parity of p; and
// inversion permutes the permutations of the points below n, so the two
// Leibniz sums agree.
var DeterminantTranspose = determinantTransposeThm{family.Add(registry.ProofEntry{
	Name: "DeterminantTranspose",
	Key:  "prop_fe780735680674d",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{
			"matrix_over(c, n, P)",
		},
		Conclusion: "determinant(c, n, transpose(P)) = determinant(c, n, P)",
		Abbrev: Abbrev{
			{Name: "S", Text: "symmetric_group({i:num | i < n})"},
			{Name: "term", Text: "λq:permutation(num). " +
				"    «sign»(q) * module_sum(c.mul, c.one, {i:num | i < n}, λi:num. P(i, permutation_map(q, i)))"},
		},
	},
		func(
			a *Argument,
			c comm_ring.CommRingFact[on.C],
			n *Expr[Nat],
			P *Arrow2[Nat, Nat, A],
			over Fact,
		) {
			indices := a.TermAs[Set[Nat]]("{i:num | i < n}")
			symmetric := a.TermAs[Set[Permutation[Nat]]]("«S»")
			permutationGroup := a.TermAs[group.GroupOps[Permutation[Nat]]]("permutation_group")
			inverseIn := a.Have(
				"the permutations of the points below n are a subgroup, so they hold their inverses",
				"∀p:permutation(num). p ∈ «S» ⇒ permutation_inverse(p) ∈ «S»",
				By(
					At(group.SubgroupInv.Inst[Permutation[Nat]](), permutationGroup, symmetric),
					symmetric_group.SymmetricGroupSubgroup.At(indices)))
			reindexed := a.Have(
				"reindexed by p⁻¹, the product of the entries "+
					"P(p(i), i) is the product of the entries P(i, p⁻¹(i))",
				Statement{
					Binders: "∀p:permutation(num).",
					Hypotheses: []string{
						"p ∈ «S»",
					},
					Conclusion: "module_sum(c.mul, c.one, {i:num | i < n}, λi:num. P(permutation_map(p, i), i)) = " +
						"module_sum(c.mul, " +
						"    c.one, " +
						"    {i:num | i < n}, " +
						"    λi:num. P(i, permutation_map(permutation_inverse(p), i)))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Permutation[Nat]]("p")
					pIn := b.Assume()
					inverse := b.TermAs[Permutation[Nat]]("permutation_inverse(p)")
					reindex := b.TermAs[Fun[Nat, Nat]]("permutation_map(permutation_inverse(p))")
					into := b.Have(
						"p⁻¹ sends the points below n below n",
						"∀i:num. i < n ⇒ permutation_map(permutation_inverse(p), i) < n",
						By(pIn, inverseIn, At(symmetric_group.SymmetricGroupMapsInto.Inst[Nat](), indices, inverse)))
					injective := b.Have(
						"and is one to one on them, being one to one outright",
						"injective_on({i:num | i < n}, permutation_map(permutation_inverse(p)))",
						By(
							symmetric_group.MapBijective.At(inverse),
							functions.InjectiveOnSubset.At(reindex, indices, b.TermAs[Set[Nat]]("𝕌")),
							set_order.SubsetUniv))
					b.Show(
						"so reindexing the product by p⁻¹ leaves it as it is, and p undoes p⁻¹",
						CalcEq(
							Leg(
								b.TermAs[A](
									"module_sum(c.mul, "+
										"    c.one, "+
										"    {i:num | i < n}, "+
										"    λi:num. "+
										"        P(permutation_map(p, permutation_map(permutation_inverse(p), i)), "+
										"            permutation_map(permutation_inverse(p), i)))"),
								"a product over the points below n is unchanged when p⁻¹ is applied to its indices first",
								By(
									over,
									MatrixOverEntries.Read(c).At(n, P),
									into,
									injective,
									module.ModuleSumReindex.Read(comm_ring.MulMonoidOn.Read(c)).At(
										n, reindex, b.TermAs[Fun[Nat, A]]("λi:num. P(permutation_map(p, i), i)")))),
							FinalLeg(
								"and p sends p⁻¹(i) back to i",
								Simp(Fwd(symmetric_group.MapInverseRight))),
						))
				}))
			terms := a.Have(
				"every Leibniz term of P lies in c",
				"∀q:permutation(num). «term»(q) ∈ c.carrier",
				a.ForEach(func(q *Expr[Permutation[Nat]]) Action {
					return By(over, LeibnizFactorsIn.Read(c).At(n, P, q), comm_ring.MulIn.Read(c))
				}))
			onto := a.Have(
				"inversion maps the permutations of the points below "+
					"n onto themselves, each the inverse of its inverse",
				"image(permutation_inverse, «S») = «S»",
				BySets(inverseIn, group.InvInv.Read(symmetric_group.SymmetricGroup)))
			oneToOne := a.Have(
				"one to one, inversion undoing itself",
				"injective_on(«S», permutation_inverse)",
				By(group.InvInv.Read(symmetric_group.SymmetricGroup), functions.InjectiveOnDef))
			a.Show(
				"so the transpose and P have one Leibniz sum",
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(c.add, "+
								"    c.zero, "+
								"    «S», "+
								"    λp:permutation(num). "+
								"        «sign»(p) * "+
								"        module_sum(c.mul, c.one, {i:num | i < n}, λi:num. P(permutation_map(p, i), i)))"),
						"the transpose's Leibniz term at p reads the entries P(p(i), i)",
						Simp(Fwd(DeterminantDef), Fwd(matrix.TransposeDef))),
					Leg(
						a.TermAs[A]("module_sum(c.add, c.zero, «S», λp:permutation(num). «term»(permutation_inverse(p)))"),
						"which is P's term at p⁻¹: its product reindexed, and p⁻¹ of the parity of p",
						By(reindexed, symmetric_group.PermutationParityInverse, module.ModuleSumCongruence)),
					Leg(
						a.TermAs[A]("module_sum(c.add, c.zero, «S», «term»)"),
						"inversion permutes the permutations of the points below n",
						By(
							num_segment.FiniteBelowStrict.At(n),
							symmetric_group.SymmetricGroupFinite.At(indices),
							terms,
							onto,
							oneToOne,
							module.ModuleSumImage.Read(module.RegularModuleOn.Read(c)).At(
								symmetric,
								a.TermAs[Fun[Permutation[Nat], Permutation[Nat]]]("permutation_inverse"),
								a.TermAs[Fun[Permutation[Nat], A]]("«term»")))),
					FinalLeg(
						"and that is P's Leibniz sum",
						Simp(Fwd(DeterminantDef))),
				))
		}),
})}
