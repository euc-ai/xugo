package linear_determinant

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// BasisChangeCompose — changing coordinates from a basis e of M to a basis
// g of a submodule S, and from g to vectors f of S, composes to the change
// from e to f: inside the square the coordinate at e(i) is a linear
// functional on S, which expands f(j) along the basis g weighted by the
// g-coordinates of f(j), and its values at the g(k) and those weights are
// the entries of the two matrices; outside it every product has a zero
// factor, and the change from e to f is the zero padding.
var BasisChangeCompose = basisChangeComposeThm{family.Add(registry.ProofEntry{
	Name: "BasisChangeCompose",
	Key:  "prop_4add41e3216239bb",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀S:set(B). ∀n:num. ∀e g f:(num → B).",
		Hypotheses: []string{
			"module_on(R, M)",
			"submodule(R, M, S)",
			"indexed_module_basis(R, M, n, e)",
			"indexed_module_basis(R, restrict_module(M, S), n, g)",
			"∀j:num. j < n ⇒ f(j) ∈ S",
		},
		Conclusion: "matrix_product(R, " +
			"    n, " +
			"    basis_change_matrix(R, M, n, e, g), " +
			"    basis_change_matrix(R, restrict_module(M, S), n, g, f)) = " +
			"basis_change_matrix(R, M, n, e, f)",
	}, func(
		a *Argument,
		R *Expr[module_record.RingOps[A]],
		M *Expr[ModuleOps[A, B]],
		S *Expr[Set[B]],
		n *Expr[Nat],
		e, g, f *Arrow[Nat, B],
		given Fact,
	) {
		parts := a.Conjuncts(
			given,
			"module_on(R, M)",
			"submodule(R, M, S)",
			"indexed_module_basis(R, M, n, e)",
			"indexed_module_basis(R, restrict_module(M, S), n, g)",
			"∀j:num. j < n ⇒ f(j) ∈ S")
		onM, sub, eIndexed, gIndexed, fIn := parts[0], parts[1], parts[2], parts[3], parts[4]
		W, wDef := a.LetAs[ModuleOps[A, B]]("W", "restrict_module(M, S)")
		I, iDef := a.LetAs[Set[Nat]]("I", "{i:num | i < n}")
		E, eDef := a.LetAs[Set[B]]("E", "{e(i):B | i:num | i < n}")
		G, gDef := a.LetAs[Set[B]]("G", "{g(i):B | i:num | i < n}")
		P, pDef := a.LetAs[Fun2[Nat, Nat, A]]("P", "basis_change_matrix(R, M, n, e, g)")
		Q, qDef := a.LetAs[Fun2[Nat, Nat, A]]("Q", "basis_change_matrix(R, W, n, g, f)")
		bDef := a.Let("Bmat", a.TermAs[Fun2[Nat, Nat, A]]("basis_change_matrix(R, M, n, e, f)"))
		ops := a.Have(
			"restriction keeps the module operations",
			"W.add = M.add ∧ W.zero = M.zero ∧ W.smul = M.smul ∧ W.carrier = S",
			Simp(
				Fwd(wDef),
				Fwd(module_record.RestrictModuleDef),
				Fwd(module_record.ModAddDef),
				Fwd(module_record.ModZeroDef),
				Fwd(module_record.ModSmulDef),
				Fwd(module_record.ModCarrierDef)),
			Basic())
		structure := a.Have(
			"the restriction is a module over the same commutative ring",
			"module_on(R, W) ∧ S ⊆ M.carrier ∧ comm_ring_on(R)",
			By(
				Normalized,
				wDef,
				onM,
				sub,
				submodule.SubmoduleModuleOn,
				submodule.SubmoduleSubset,
				module.RingOn))
		bases := a.Have(
			"the indexed images are bases",
			"injective_on(I, e) ∧ module_basis(R, M, E) ∧ injective_on(I, g) ∧ module_basis(R, W, G)",
			By(
				iDef,
				eDef,
				gDef,
				eIndexed,
				gIndexed,
				linear_independence.IndexedModuleBasisDef.At(R, M, n, e),
				linear_independence.IndexedModuleBasisDef.At(R, W, n, g)))
		images := a.Have(
			"the basis sets are the indexed images",
			"E = image(e, I) ∧ G = image(g, I)",
			BySets(iDef, eDef, gDef))
		finite := a.Have(
			"all indexing sets are finite",
			"finite(I) ∧ finite(E) ∧ finite(G)",
			By(
				iDef,
				images,
				num_segment.FiniteBelowStrict.At(n),
				finite_set.FiniteImage.At(e, I),
				finite_set.FiniteImage.At(g, I)))
		carrier := a.Have(
			"basis sets lie in their module carriers",
			"E ⊆ M.carrier ∧ G ⊆ W.carrier",
			By(
				bases,
				linear_independence.ModuleBasisDef.At(R, M, E),
				linear_independence.ModuleBasisDef.At(R, W, G),
				linear_independence.IndependentInCarrier.At(R, M, E),
				linear_independence.IndependentInCarrier.At(R, W, G)))
		points := a.Have(
			"the indexed vectors lie in their required carriers",
			Statement{
				Binders: "∀i:num.",
				Hypotheses: []string{
					"i < n",
				},
				Conclusion: "e(i) ∈ E ∧ " +
					"e(i) ∈ M.carrier ∧ " +
					"g(i) ∈ G ∧ " +
					"g(i) ∈ W.carrier ∧ " +
					"g(i) ∈ M.carrier ∧ " +
					"f(i) ∈ W.carrier ∧ " +
					"f(i) ∈ M.carrier",
			},
			BySets(Normalized, eDef, gDef, carrier, ops, structure, fIn))
		entries := a.Have(
			"each matrix entry is the relevant basis coordinate",
			"∀i j:num. "+
				"    P(i, j) = COND(i < n ∧ j < n, module_basis_coordinates(R, M, E, g(j), e(i)), R.zero) ∧ "+
				"    Q(i, j) = COND(i < n ∧ j < n, module_basis_coordinates(R, W, G, f(j), g(i)), R.zero) ∧ "+
				"    Bmat(i, j) = COND(i < n ∧ j < n, module_basis_coordinates(R, M, E, f(j), e(i)), R.zero)",
			Derive(func(b *Argument) {
				i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
				b.Show(
					"read the three coordinate matrices",
					By(
						pDef,
						qDef,
						bDef,
						eDef,
						gDef,
						BasisChangeMatrixDef.At(R, M, n, e, g, i, j),
						BasisChangeMatrixDef.At(R, W, n, g, f, i, j),
						BasisChangeMatrixDef.At(R, M, n, e, f, i, j)))
			}))
		regular := a.TermAs[ModuleOps[A, A]]("regular_module(R)")
		regularOps := a.Have(
			"the regular module uses the ring operations",
			"regular_module(R).add = R.add ∧ "+
				"regular_module(R).zero = R.zero ∧ "+
				"regular_module(R).smul = R.mul ∧ "+
				"regular_module(R).carrier = R.carrier",
			Simp(
				Fwd(module_record.RegularModuleDef),
				Fwd(module_record.ModAddDef),
				Fwd(module_record.ModZeroDef),
				Fwd(module_record.ModSmulDef),
				Fwd(module_record.ModCarrierDef)),
			Basic())
		scalarEntries := a.Have(
			"finite-square entries are scalars",
			"∀i j:num. i < n ∧ j < n ⇒ P(i, j) ∈ R.carrier ∧ Q(i, j) ∈ R.carrier",
			Derive(func(b *Argument) {
				i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
				inside := b.Assume()
				b.Show(
					"basis coordinate coefficients are scalars",
					By(
						Normalized,
						inside,
						onM,
						structure,
						finite,
						bases,
						points.At(i),
						points.At(j),
						entries.At(i, j),
						module_dimension.BasisCoordinatesSpec.At(R, M, E, g.Apply(j)),
						module_dimension.BasisCoordinatesSpec.At(R, W, G, f.Apply(j))))
			}))
		padding := a.Have(
			"all three matrices vanish outside the finite square",
			"∀i j:num. ¬(i < n ∧ j < n) ⇒ P(i, j) = R.zero ∧ Q(i, j) = R.zero ∧ Bmat(i, j) = R.zero",
			By(Normalized, entries))
		pointwise := a.Have(
			"matrix multiplication composes the coordinate changes",
			"∀i j:num. matrix_product(R, n, P, Q, i, j) = Bmat(i, j)",
			Derive(func(b *Argument) {
				i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
				b.Cases(b.TermAs[Bool]("i < n ∧ j < n"))
				b.When(
					"inside the finite square",
					func(c *Argument, inside Fact) {
						h, hDef := c.LetAs[Fun[B, A]]("h", "λv:B. module_basis_coordinates(R, M, E, v, e(i))")
						linear := c.Have(
							"the ambient e coordinate is linear",
							"module_homomorphism(R, M, regular_module(R), h)",
							By(
								hDef,
								onM,
								finite,
								bases,
								inside,
								points.At(i),
								module_dimension.BasisCoordinateLinear.At(R, M, E, e.Apply(i))))
						restricted := c.Have(
							"restrict the coordinate map to W",
							"module_homomorphism(R, W, regular_module(R), h)",
							By(Normalized, wDef, linear, sub, module_homomorphism.HomRestrictSource.At(R, M, regular, h, S)))
						expanded := c.Have(
							"the linear functional h expands f(j) along the basis g of W",
							"h(f(j)) = "+
								"module_sum(R.add, R.zero, I, λk:num. h(g(k)) * module_basis_coordinates(R, W, G, f(j), g(k)))",
							By(
								iDef,
								gDef,
								wDef,
								structure,
								gIndexed,
								inside,
								points.At(j),
								restricted,
								module_dimension.IndexedFunctionalExpansion.At(R, W, n, g, f.Apply(j), h)))
						products := c.Have(
							"each summand is a product of the two matrices' entries",
							"∀k:num. k ∈ I ⇒ h(g(k)) * module_basis_coordinates(R, W, G, f(j), g(k)) = P(i, k) * Q(k, j)",
							Derive(func(d *Argument) {
								k := d.FixAs[Nat]("k")
								inI := d.Assume()
								below := d.Have(
									"the summation index lies below n",
									"k < n",
									BySets(iDef, inI))
								d.Show(
									"the two factors are the entries P(i, k) and Q(k, j)",
									By(hDef, below, inside, entries.At(i, k), entries.At(k, j)))
							}))
						product := c.Have(
							"the scalar sum is the matrix product",
							"matrix_product(R, n, P, Q, i, j) = h(f(j))",
							By(
								expanded,
								products,
								module.ModuleSumCongruence.At(
									c.TermAs[Op[A]]("R.add"),
									c.TermAs[A]("R.zero"),
									I,
									c.TermAs[Fun[Nat, A]]("λk:num. h(g(k)) * module_basis_coordinates(R, W, G, f(j), g(k))"),
									c.TermAs[Fun[Nat, A]]("λk:num. P(i, k) * Q(k, j)")),
								iDef,
								matrix.MatrixProductDef.At(R, n, P, Q, i, j)))
						entry := c.Have(
							"the ambient coordinate of f(j) is the direct entry",
							"h(f(j)) = Bmat(i, j)",
							By(Normalized, hDef, inside, entries.At(i, j)))
						c.Show(
							"the product equals the direct coordinate change",
							By(Normalized, product, entry))
					})
				b.Otherwise(
					"outside the finite square",
					func(c *Argument, outside Fact) {
						ring := c.Have(
							"the scalar ring is commutative",
							"comm_ring_on(R)",
							By(structure))
						zeroTerms := c.Have(
							"each product has a zero factor",
							"∀k:num. k ∈ I ⇒ P(i, k) * Q(k, j) = R.zero",
							Derive(func(d *Argument) {
								k := d.FixAs[Nat]("k")
								d.Assume()
								factors := d.Have(
									"at least one factor is padded zero",
									"P(i, k) ∈ R.carrier ∧ Q(k, j) ∈ R.carrier ∧ (P(i, k) = R.zero ∨ Q(k, j) = R.zero)",
									BySets(
										Normalized,
										comm_ring.ZeroIn.Read(ring),
										outside,
										scalarEntries.At(i, k),
										scalarEntries.At(k, j),
										padding.At(i, k),
										padding.At(k, j)))
								d.Show(
									"multiplication by zero vanishes",
									By(
										Normalized,
										factors,
										comm_ring.MulLeftZeroOn.Read(ring).AsFact().At(d.TermAs[A]("Q(k, j)")),
										comm_ring.MulRightZeroOn.Read(ring).AsFact().At(d.TermAs[A]("P(i, k)"))))
							}))
						zeroSum := c.Have(
							"the product sum is zero",
							"module_sum(R.add, R.zero, I, λk:num. P(i, k) * Q(k, j)) = R.zero",
							By(
								module.RegularModuleOn.Read(ring),
								finite,
								zeroTerms,
								regularOps,
								module.ModuleSumZero.At(R, regular, I, c.TermAs[Fun[Nat, A]]("λk:num. P(i, k) * Q(k, j)"))))
						c.Show(
							"the product has the same zero padding",
							By(zeroSum, iDef, outside, padding.At(i, j), matrix.MatrixProductDef.At(R, n, P, Q, i, j)))
					})
			}))
		a.Show(
			"the matrices agree at every pair of indices",
			By(Normalized, pointwise))
	}),
})}

// BasisChangeIdentity — the change of coordinates from an indexed basis to
// itself is the identity matrix: the coordinates of a basis vector are its
// Kronecker delta, and injective indexing turns the delta on vectors into
// the delta on indices.
var BasisChangeIdentity = basisChangeIdentityThm{family.Add(registry.ProofEntry{
	Name: "BasisChangeIdentity",
	Key:  "prop_ba647632eaca05d3",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀e:(num → B).",
		Hypotheses: []string{
			"module_on(R, M)",
			"indexed_module_basis(R, M, n, e)",
		},
		Conclusion: "basis_change_matrix(R, M, n, e, e) = matrix_identity(R, n)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		M *Expr[ModuleOps[A, B]],
		n *Expr[Nat],
		e *Vec[B, DimN],
		given Fact,
	) {
		a.Do(Funext())
		a.FixAs[Nat]("i")
		a.FixAs[Nat]("j")
		a.Do(Simp(Fwd(BasisChangeMatrixDef), Fwd(determinant.MatrixIdentityDef)))
		a.Cases(a.Term("i < n ∧ j < n"))
		a.When(
			"the active entries are the coordinate delta",
			func(b *Argument, active Fact) {
				E := b.TermAs[Set[B]]("{e(k):B | k:num | k < n}")
				basisVectors := b.Have(
					"e(i) and e(j) are basis vectors",
					"e(i) ∈ {e(k):B | k:num | k < n} ∧ e(j) ∈ {e(k):B | k:num | k < n}",
					BySets(active))
				delta := b.Have(
					"a basis vector has the corresponding delta coordinates",
					"module_basis_coordinates(R, M, {e(k):B | k:num | k < n}, e(j), e(i)) = "+
						"COND(e(i) = e(j), R.one, R.zero)",
					By(
						active,
						given,
						basisVectors,
						linear_independence.IndexedBasisImage.At(R, M, n, e),
						module_dimension.BasisCoordinateDelta.At(R, M, E, b.TermAs[B]("e(j)"))))
				injective := b.Have(
					"equal indexed basis vectors have equal indices",
					"e(i) = e(j) ⇔ i = j",
					BySets(
						active,
						given,
						linear_independence.IndexedModuleBasisDef.At(R, M, n, e),
						functions.InjectiveOnDef.At(b.TermAs[Set[Nat]]("{i:num | i < n}"), e)))
				b.Show(
					"the delta is the identity matrix entry",
					By(delta, injective, active))
			})
		a.Otherwise(
			"outside the active square both entries are zero",
			func(b *Argument, outside Fact) {
				b.Show(
					"the zero padding agrees",
					By(Normalized, outside))
			})
	}),
})}

// BasisChangeMatrixOver — the matrix of coordinates of vectors h of M in an
// indexed basis e is a matrix over R: past the n × n square it is the zero
// padding, and inside it an entry is a coordinate of h(j) at a basis
// vector, a scalar.
var BasisChangeMatrixOver = basisChangeMatrixOverThm{family.Add(registry.ProofEntry{
	Name: "BasisChangeMatrixOver",
	Key:  "prop_5d8e183867578026",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀e h:(num → B).",
		Hypotheses: []string{
			"module_on(R, M)",
			"indexed_module_basis(R, M, n, e)",
			"∀j:num. j < n ⇒ h(j) ∈ M.carrier",
		},
		Conclusion: "matrix_over(R, n, basis_change_matrix(R, M, n, e, h))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		M *Expr[ModuleOps[A, B]],
		n *Expr[Nat],
		e, h *Vec[B, DimN],
		given Fact,
	) {
		a.Do(Simp(
			Fwd(determinant.MatrixOverDef),
			Fwd(matrix.MatrixDef),
			Fwd(vec_space.VecDef),
			Fwd(vec_space.VecZeroDef),
			Fwd(BasisChangeMatrixDef),
			Rev(nat_order.NotLessThan)), SplitConj(
			Case(
				"the coordinate matrix is zero beyond its row and column bounds",
				By(given)),
			Case(
				"each active entry is a scalar coordinate",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					b.FixAs[Nat]("j")
					active := b.Assume()
					basisVector := b.Have(
						"e(i) is one of the basis vectors",
						"e(i) ∈ {e(k):B | k:num | k < n}",
						BySets(active))
					b.Show(
						"the coordinate of h(j) at e(i) belongs to R",
						By(
							active,
							given,
							basisVector,
							linear_independence.IndexedBasisImage.At(R, M, n, e),
							module_dimension.BasisCoordinatesSpec.At(
								R, M, b.TermAs[Set[B]]("{e(k):B | k:num | k < n}"), b.TermAs[B]("h(j)"))))
				}))))
	}),
})}

// BasisChangeInverse — the coordinate changes between two indexed bases e
// and h of M, there and back, are inverse matrices over R: M is a submodule
// of itself, so changing from e to h and back composes to the change from e
// to itself (BasisChangeCompose), which is the identity matrix
// (BasisChangeIdentity), and each change is a matrix over R
// (BasisChangeMatrixOver).
var BasisChangeInverse = basisChangeInverseThm{family.Add(registry.ProofEntry{
	Name: "BasisChangeInverse",
	Key:  "prop_34c3fd1018611682",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀e h:(num → B).",
		Hypotheses: []string{
			"module_on(R, M)",
			"indexed_module_basis(R, M, n, e)",
			"indexed_module_basis(R, M, n, h)",
		},
		Conclusion: "matrix_product(R, " +
			"    n, " +
			"    basis_change_matrix(R, M, n, e, h), " +
			"    basis_change_matrix(R, M, n, h, e)) = " +
			"matrix_identity(R, n) ∧ " +
			"matrix_over(R, n, basis_change_matrix(R, M, n, e, h)) ∧ " +
			"matrix_over(R, n, basis_change_matrix(R, M, n, h, e))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		M *Expr[ModuleOps[A, B]],
		n *Expr[Nat],
		e, h *Vec[B, DimN],
		given Fact,
	) {
		parts := a.Conjuncts(
			given,
			"M is a module over R",
			"e is an indexed basis of M",
			"h is an indexed basis of M")
		onM, eBasis, hBasis := parts[0], parts[1], parts[2]
		whole := a.Have(
			"M's carrier is a submodule of M, and M restricted to its carrier is M",
			"submodule(R, M, M.carrier) ∧ restrict_module(M, M.carrier) = M",
			By(submodule.CarrierSubmodule.Read(onM), module_record.RestrictModuleCarrier.At(M)))
		inM := a.Have(
			"the e and h vectors lie in M",
			"(∀j:num. j < n ⇒ e(j) ∈ M.carrier) ∧ (∀j:num. j < n ⇒ h(j) ∈ M.carrier)",
			By(
				onM,
				eBasis,
				hBasis,
				At(linear_independence.IndexedBasisInCarrier, R, M, n, e),
				At(linear_independence.IndexedBasisInCarrier, R, M, n, h)))
		hWhole := a.Have(
			"h is a basis of M restricted to its carrier",
			"indexed_module_basis(R, restrict_module(M, M.carrier), n, h)",
			By(Normalized, whole, hBasis))
		composed := a.Have(
			"changing from e to h and back is the change from e to itself",
			"matrix_product(R, "+
				"    n, "+
				"    basis_change_matrix(R, M, n, e, h), "+
				"    basis_change_matrix(R, restrict_module(M, M.carrier), n, h, e)) = "+
				"basis_change_matrix(R, M, n, e, e)",
			By(
				onM,
				whole,
				eBasis,
				hWhole,
				inM,
				BasisChangeCompose.At(R, M, a.TermAs[Set[B]]("M.carrier"), n, e, h, e)))
		a.Show(
			"which is the identity matrix, and both changes are matrices over R",
			By(
				Normalized,
				onM,
				eBasis,
				hBasis,
				whole,
				composed,
				inM,
				BasisChangeIdentity.At(R, M, n, e),
				BasisChangeMatrixOver.At(R, M, n, e, h),
				BasisChangeMatrixOver.At(R, M, n, h, e)))
	}),
})}

// ModuleBasisMatrixAsChange — the matrix of an endomorphism f in an indexed
// basis e is the coordinate-change matrix from e to the images f(e(j)) of the
// basis vectors: both definitions give the coordinate of f(e(j)) at e(i)
// inside the n × n square and the zero padding outside it.
var ModuleBasisMatrixAsChange = moduleBasisMatrixAsChangeThm{family.Add(registry.ProofEntry{
	Name: "ModuleBasisMatrixAsChange",
	Key:  "prop_aae5b23b8f1f69c7",
	Build: family.Theorem("∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀e:(num → B). ∀f:(B → B). "+
		"    module_basis_matrix(R, M, n, e, f) = basis_change_matrix(R, M, n, e, λj:num. f(e(j)))",
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			n *Expr[Nat],
			e *Vec[B, DimN],
			f *Arrow[B, B],
		) {
			a.Show(
				"the endomorphism matrix is its coordinate-change matrix",
				Simp(Fwd(ModuleBasisMatrixDef), Fwd(BasisChangeMatrixDef)),
				Refl())
		}),
})}

// LinearDeterminantFromBasis — the determinant of an endomorphism f is the
// determinant of its matrix in any indexed finite basis, and a scalar of K:
// the determinant is chosen as the matrix determinant in some indexed
// basis, which the given basis e shows exists; the chosen basis has e's
// length n, two indexed bases over a field having one length; the
// coordinate-change matrices between the two bases are inverse to each
// other and conjugate the two matrices of f, so the two determinants agree;
// and the determinant of a matrix over K's ring lies in K.
var LinearDeterminantFromBasis = linearDeterminantFromBasisThm{family.Add(registry.ProofEntry{
	Name: "LinearDeterminantFromBasis",
	Key:  "prop_aeae5f02e0d41e6",
	Build: family.Sections(Statement{
		Binders: "∀K:field_on(A). ∀M:module_ops(A, B). ∀f:(B → B). ∀n:num. ∀e:(num → B).",
		Hypotheses: []string{
			"module_on(field_ring(K), M)",
			"module_homomorphism(field_ring(K), M, M, f)",
			"indexed_module_basis(field_ring(K), M, n, e)",
		},
		Conclusion: "module_determinant(field_ring(K), M, f) = " +
			"determinant(field_ring(K), n, module_basis_matrix(field_ring(K), M, n, e, f)) ∧ " +
			"module_determinant(field_ring(K), M, f) ∈ K.carrier",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			matrixExtensionality := ctx.Lemma(Statement{
				Binders: "∀R:ring_ops(A). ∀n:num. ∀P Q:(num → num → A).",
				Hypotheses: []string{
					"matrix_over(R, n, P)",
					"matrix_over(R, n, Q)",
					"∀i j:num. i < n ∧ j < n ⇒ P(i, j) = Q(i, j)",
				},
				Conclusion: "P = Q",
			},
				func(a *Argument, R *Expr[RingOps[A]], n *Expr[Nat], P, Q *Mat[A, DimN, DimN], given Fact) {
					a.Do(Funext())
					i, j := a.FixAs[Nat]("i"), a.FixAs[Nat]("j")
					zero := a.TermAs[A]("R.zero")
					a.Show(
						"outside the active square both matrices vanish",
						By(
							Normalized,
							given,
							determinant.MatrixOverDef.At(R, P),
							determinant.MatrixOverDef.At(R, Q),
							matrix.MatrixDef.At(zero, P),
							matrix.MatrixDef.At(zero, Q),
							vec_space.VecDef.At(zero, a.VecAs[A, DimN]("P(i)")),
							vec_space.VecDef.At(zero, a.VecAs[A, DimN]("Q(i)")),
							vec_space.VecZeroDef.At(zero, j),
							nat_order.NotLessThan.At(i, n),
							nat_order.NotLessThan.At(j, n)))
				})

			coordinateProduct := ctx.Lemma(Statement{
				Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀e h t:(num → B). ∀f:(B → B).",
				Hypotheses: []string{
					"module_on(R, M)",
					"indexed_module_basis(R, M, n, e)",
					"indexed_module_basis(R, M, n, h)",
					"∀j:num. j < n ⇒ t(j) ∈ M.carrier",
					"module_homomorphism(R, M, M, f)",
				},
				Conclusion: "matrix_product(R, " +
					"    n, " +
					"    basis_change_matrix(R, M, n, e, λk:num. f(h(k))), " +
					"    basis_change_matrix(R, M, n, h, t)) = " +
					"basis_change_matrix(R, M, n, e, λj:num. f(t(j)))",
			},
				func(
					a *Argument,
					R *Expr[RingOps[A]],
					M *Expr[ModuleOps[A, B]],
					n *Expr[Nat],
					e, h, t *Vec[B, DimN],
					f *Arrow[B, B],
					given Fact,
				) {
					images := a.Have(
						"f carries the intermediate basis and the target vectors into M",
						"(∀j:num. j < n ⇒ f(h(j)) ∈ M.carrier) ∧ (∀j:num. j < n ⇒ f(t(j)) ∈ M.carrier)",
						By(
							given,
							At(linear_independence.IndexedBasisInCarrier, R, M, n, h),
							module_homomorphism.ModuleHomomorphismDef.At(R, M, M, f)))
					fh := a.VecAs[B, DimN]("λk:num. f(h(k))")
					ft := a.VecAs[B, DimN]("λj:num. f(t(j))")
					P := a.MatAs[A, DimN, DimN]("basis_change_matrix(R, M, n, e, λk:num. f(h(k)))")
					Q := a.MatAs[A, DimN, DimN]("basis_change_matrix(R, M, n, h, t)")
					T := a.MatAs[A, DimN, DimN]("basis_change_matrix(R, M, n, e, λj:num. f(t(j)))")
					over := a.Have(
						"all three coordinate matrices are over R",
						"matrix_over(R, n, basis_change_matrix(R, M, n, e, λk:num. f(h(k)))) ∧ "+
							"matrix_over(R, n, basis_change_matrix(R, M, n, h, t)) ∧ "+
							"matrix_over(R, n, basis_change_matrix(R, M, n, e, λj:num. f(t(j))))",
						By(
							images,
							given,
							BasisChangeMatrixOver.At(R, M, n, e, fh),
							BasisChangeMatrixOver.At(R, M, n, h, t),
							BasisChangeMatrixOver.At(R, M, n, e, ft)))
					activeEntries := a.Have(
						"the active entries are the mapped coordinate expansion",
						Statement{
							Binders: "∀i j:num.",
							Hypotheses: []string{
								"i < n",
								"j < n",
							},
							Conclusion: "matrix_product(R, " +
								"    n, " +
								"    basis_change_matrix(R, M, n, e, λk:num. f(h(k))), " +
								"    basis_change_matrix(R, M, n, h, t), " +
								"    i, " +
								"    j) = " +
								"basis_change_matrix(R, M, n, e, λk:num. f(t(k)), i, j)",
						},
						Derive(func(b *Argument) {
							b.FixAs[Nat]("i")
							b.FixAs[Nat]("j")
							active := b.Assume()
							b.Do(Simp(Fwd(matrix.MatrixProductDef), Fwd(BasisChangeMatrixDef)))
							summands := b.Have(
								"within the sum both coordinate entries are active",
								Statement{
									Binders: "∀k:num.",
									Hypotheses: []string{
										"k < n",
									},
									Conclusion: "COND(i < n ∧ k < n, " +
										"    module_basis_coordinates(R, M, {e(r):B | r:num | r < n}, f(h(k)), e(i)), " +
										"    R.zero) * " +
										"COND(k < n ∧ j < n, " +
										"    module_basis_coordinates(R, M, {h(r):B | r:num | r < n}, t(j), h(k)), " +
										"    R.zero) = " +
										"module_basis_coordinates(R, M, {e(r):B | r:num | r < n}, f(h(k)), e(i)) * " +
										"module_basis_coordinates(R, M, {h(r):B | r:num | r < n}, t(j), h(k))",
								},
								By(active))
							padded := b.TermAs[Fun[Nat, A]](
								"λk:num. " +
									"    COND(i < n ∧ k < n, " +
									"        module_basis_coordinates(R, M, {e(r):B | r:num | r < n}, f(h(k)), e(i)), " +
									"        R.zero) * " +
									"    COND(k < n ∧ j < n, " +
									"        module_basis_coordinates(R, M, {h(r):B | r:num | r < n}, t(j), h(k)), " +
									"        R.zero)")
							coefficients := b.TermAs[Fun[Nat, A]](
								"λk:num. " +
									"    module_basis_coordinates(R, M, {e(r):B | r:num | r < n}, f(h(k)), e(i)) * " +
									"    module_basis_coordinates(R, M, {h(r):B | r:num | r < n}, t(j), h(k))")
							E := b.TermAs[Set[B]]("{e(k):B | k:num | k < n}")
							basisVector := b.Have(
								"e(i) is one of the basis vectors",
								"e(i) ∈ {e(k):B | k:num | k < n}",
								BySets(active))
							b.Show(
								"the finite sum computes the coordinate of f(t(j))",
								By(
									summands,
									active,
									given,
									basisVector,
									linear_independence.IndexedBasisImage.At(R, M, n, e),
									module_dimension.IndexedImageCoordinates.At(
										R, M, E, n, h, f, b.TermAs[B]("t(j)"), b.TermAs[B]("e(i)")),
									module.ModuleSumCongruence.At(
										b.TermAs[Op[A]]("R.add"),
										b.TermAs[A]("R.zero"),
										b.TermAs[Set[Nat]]("{k:num | k < n}"),
										padded,
										coefficients)))
						}))
					a.Show(
						"the product is determined by those active entries",
						By(
							activeEntries,
							given,
							over,
							module.RingOn.At(R, M),
							determinant.MatrixProductOver.At(R, n, P, Q),
							At(
								matrixExtensionality,
								R,
								n,
								a.MatAs[A, DimN, DimN](
									"matrix_product(R, "+
										"    n, "+
										"    basis_change_matrix(R, M, n, e, λk:num. f(h(k))), "+
										"    basis_change_matrix(R, M, n, h, t))"),
								T)))
				})

			basisMatrixConjugacy := ctx.Lemma(Statement{
				Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀e h:(num → B). ∀f:(B → B).",
				Hypotheses: []string{
					"module_on(R, M)",
					"indexed_module_basis(R, M, n, e)",
					"indexed_module_basis(R, M, n, h)",
					"module_homomorphism(R, M, M, f)",
				},
				Conclusion: "module_basis_matrix(R, M, n, h, f) = " +
					"matrix_product(R, " +
					"    n, " +
					"    basis_change_matrix(R, M, n, h, e), " +
					"    matrix_product(R, " +
					"        n, " +
					"        module_basis_matrix(R, M, n, e, f), " +
					"        basis_change_matrix(R, M, n, e, h))) ∧ " +
					"matrix_over(R, n, module_basis_matrix(R, M, n, e, f)) ∧ " +
					"matrix_over(R, n, module_basis_matrix(R, M, n, h, f))",
			},
				func(
					a *Argument,
					R *Expr[RingOps[A]],
					M *Expr[ModuleOps[A, B]],
					n *Expr[Nat],
					e, h *Vec[B, DimN],
					f *Arrow[B, B],
					given Fact,
				) {
					images := a.Have(
						"f preserves the carrier and the identity is linear",
						"(∀j:num. j < n ⇒ f(e(j)) ∈ M.carrier) ∧ "+
							"(∀j:num. j < n ⇒ f(h(j)) ∈ M.carrier) ∧ "+
							"module_homomorphism(R, M, M, λx:B. x)",
						By(
							Normalized,
							given,
							At(linear_independence.IndexedBasisInCarrier, R, M, n, e),
							At(linear_independence.IndexedBasisInCarrier, R, M, n, h),
							module_homomorphism.ModuleHomomorphismDef.At(R, M, M, f),
							module_homomorphism.HomIdentity.At(R, M),
							functions.IdentityApply))
					firstChange := a.Have(
						"apply f to the h-vectors expressed in e-coordinates",
						"matrix_product(R, n, module_basis_matrix(R, M, n, e, f), basis_change_matrix(R, M, n, e, h)) = "+
							"basis_change_matrix(R, M, n, e, λj:num. f(h(j)))",
						By(
							given,
							At(linear_independence.IndexedBasisInCarrier, R, M, n, h),
							ModuleBasisMatrixAsChange.At(R, M, n, e, f),
							At(coordinateProduct, R, M, n, e, e, h, f)))
					fe := a.VecAs[B, DimN]("λj:num. f(e(j))")
					fh := a.VecAs[B, DimN]("λj:num. f(h(j))")
					a.Show(
						"convert the resulting e-coordinates into h-coordinates",
						By(
							firstChange,
							images,
							given,
							At(coordinateProduct, R, M, n, h, e, fh, a.TermAs[Fun[B, B]]("λx:B. x")),
							BasisChangeMatrixOver.At(R, M, n, e, fe),
							BasisChangeMatrixOver.At(R, M, n, h, fh),
							ModuleBasisMatrixAsChange.At(R, M, n, e, f),
							ModuleBasisMatrixAsChange.At(R, M, n, h, f)))
				})

			basisDeterminantIndependent := ctx.Lemma(Statement{
				Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀e h:(num → B). ∀f:(B → B).",
				Hypotheses: []string{
					"module_on(R, M)",
					"indexed_module_basis(R, M, n, e)",
					"indexed_module_basis(R, M, n, h)",
					"module_homomorphism(R, M, M, f)",
				},
				Conclusion: "determinant(R, n, module_basis_matrix(R, M, n, h, f)) = " +
					"determinant(R, n, module_basis_matrix(R, M, n, e, f))",
			},
				func(
					a *Argument,
					R *Expr[RingOps[A]],
					M *Expr[ModuleOps[A, B]],
					n *Expr[Nat],
					e, h *Vec[B, DimN],
					f *Arrow[B, B],
					given Fact,
				) {
					P := a.MatAs[A, DimN, DimN]("module_basis_matrix(R, M, n, e, f)")
					U := a.MatAs[A, DimN, DimN]("basis_change_matrix(R, M, n, h, e)")
					Q := a.MatAs[A, DimN, DimN]("basis_change_matrix(R, M, n, e, h)")
					a.Show(
						"inverse coordinate changes preserve the determinant",
						By(
							given,
							BasisChangeInverse.At(R, M, n, h, e),
							At(basisMatrixConjugacy, R, M, n, e, h, f),
							module.RingOn.At(R, M),
							determinant.DeterminantChangeBasis.At(R, n, P, U, Q)))
				})

			return ctx.Theorem(headline,
				func(
					a *Argument,
					K field.FieldFact[on.K],
					M *Expr[ModuleOps[A, B]],
					f *Arrow[B, B],
					n *Expr[Nat],
					e *Vec[B, DimN],
					given Fact,
				) {
					R := a.TermAs[RingOps[A]]("field_ring(K)")
					P := a.MatAs[A, DimN, DimN]("module_basis_matrix(field_ring(K), M, n, e, f)")
					possible := a.Have(
						"the displayed indexed basis witnesses the defining choice",
						"∃a:A. ∃m:num. ∃h:(num → B). "+
							"    indexed_module_basis(field_ring(K), M, m, h) ∧ "+
							"    a = determinant(field_ring(K), m, module_basis_matrix(field_ring(K), M, m, h, f))",
						Derive(func(b *Argument) {
							b.Take(b.TermAs[A]("determinant(field_ring(K), n, module_basis_matrix(field_ring(K), M, n, e, f))"))
							b.Take(n)
							b.Take(e)
							b.Show(
								"this basis gives that scalar",
								By(given))
						}))
					selected := a.Have(
						"the chosen scalar is the determinant in an indexed basis",
						"∃m:num. ∃h:(num → B). "+
							"    indexed_module_basis(field_ring(K), M, m, h) ∧ "+
							"    module_determinant(field_ring(K), M, f) = "+
							"    determinant(field_ring(K), m, module_basis_matrix(field_ring(K), M, m, h, f))",
						Simp(Fwd(ModuleDeterminantDef)),
						By(possible))
					m, h, chosen := a.Unpack2As[Nat, Fun[Nat, B]](selected, "m", "h")
					size := a.Have(
						"the selected indexed basis has size n",
						"m = n",
						By(
							given,
							chosen,
							field.FieldRingSubfield.Read(K),
							module_dimension.IndexedBasisSizeUnique.At(R, M, a.TermAs[Fun[A, A]]("K.inv"), n, m, e, h)))
					value := a.Have(
						"basis independence identifies the selected scalar",
						"module_determinant(field_ring(K), M, f) = "+
							"determinant(field_ring(K), n, module_basis_matrix(field_ring(K), M, n, e, f))",
						By(size, given, chosen, At(basisDeterminantIndependent, R, M, n, e, h, f)))
					scalar := a.Have(
						"the displayed determinant belongs to the scalar ring",
						"determinant(field_ring(K), n, module_basis_matrix(field_ring(K), M, n, e, f)) ∈ "+
							"field_ring(K).carrier",
						By(
							K,
							given,
							At(basisMatrixConjugacy, R, M, n, e, e, f),
							field.RingOn.Read(K),
							determinant.DeterminantInCarrier.At(R, n, P)))
					carrier := a.Have(
						"the field ring has the field carrier",
						"field_ring(K).carrier = K.carrier",
						Simp(Fwd(field.FieldRingDef), Fwd(module_record.RingCarrierDef)),
						Refl())
					a.Show(
						"the common determinant is a scalar of K",
						By(value, carrier, scalar))
				})
		}),
})}

var LinearDeterminantCompose = linearDeterminantComposeThm{family.Add(registry.ProofEntry{
	Name: "LinearDeterminantCompose",
	Key:  "prop_1082e7cca0d3fcf",
	Deps: []registry.EntryLike{
		LinearDeterminantFromBasis,
		determinant.DeterminantMultiplicative,
		determinant.DeterminantIdentity,
	},
	Build: family.Card(Statement{
		Binders: "∀K:field_on(A). ∀M:module_ops(A, B). ∀f g:(B → B).",
		Hypotheses: []string{
			"module_on(field_ring(K), M)",
			"finite_dimensional(field_ring(K), M)",
			"module_homomorphism(field_ring(K), M, M, f)",
			"module_homomorphism(field_ring(K), M, M, g)",
		},
		Conclusion: "module_determinant(field_ring(K), M, λx:B. f(g(x))) = " +
			"module_determinant(field_ring(K), M, f) * module_determinant(field_ring(K), M, g) ∧ " +
			"module_determinant(field_ring(K), M, λx:B. x) = K.one",
	},
		"In one finite basis, composition is matrix multiplication and identity "+
			"is the identity matrix. Apply the corresponding determinant laws."),
})}

var LinearDeterminantScalar = linearDeterminantScalarThm{family.Add(registry.ProofEntry{
	Name: "LinearDeterminantScalar",
	Key:  "prop_8a7fe3b3cbf89916",
	Deps: []registry.EntryLike{
		LinearDeterminantFromBasis,
		determinant.DeterminantTriangular,
		module_dimension.DimBasis,
	},
	Build: family.Card(Statement{
		Binders: "∀K:field_on(A). ∀M:module_ops(A, B). ∀a:A.",
		Hypotheses: []string{
			"module_on(field_ring(K), M)",
			"finite_dimensional(field_ring(K), M)",
			"a ∈ K.carrier",
		},
		Conclusion: "module_determinant(field_ring(K), M, M.smul(a)) = " +
			"monoid_pow(K.mul, K.one, a, module_dim(field_ring(K), M))",
	},
		"The scalar map has a diagonal matrix with a on each diagonal entry. "+
			"Triangular determinant and basis cardinality give a to the dimension."),
})}
