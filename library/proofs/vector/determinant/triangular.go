package determinant

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// DeterminantTriangular — the determinant of an upper triangular matrix
// is its diagonal product: every other permutation p sends some row r
// below the diagonal, and the product of the entries p picks, its factor
// at row r singled out (ModuleSumDeleteMonoid), is zero times a member of c.
var DeterminantTriangular = determinantTriangularThm{family.Add(registry.ProofEntry{
	Name: "DeterminantTriangular",
	Key:  "prop_f7a93f93facfca59",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{
			"matrix_over(c, n, P)",
			"∀i j:num. j < i ∧ i < n ⇒ P(i, j) = c.zero",
		},
		Conclusion: "determinant(c, n, P) = module_sum(c.mul, c.one, {i:num | i < n}, λi:num. P(i, i))",
	}, func(
		a *Argument,
		c comm_ring.CommRingFact[on.C],
		n *Expr[Nat],
		P *Mat[A, DimN, DimN],
		given Fact,
	) {
		hypotheses := a.Conjuncts(
			given,
			"P is a matrix over c",
			"and it vanishes below the diagonal")
		over, lower := hypotheses[0], hypotheses[1]
		indices := a.TermAs[Set[Nat]]("{i:num | i < n}")
		entries := a.Have(
			"every matrix entry lies in the ring carrier",
			"∀i j:num. P(i, j) ∈ c.carrier",
			By(over, MatrixOverEntries.Read(c).At(n, P)))
		finite := a.Have(
			"the index set and its supported permutation group are finite",
			"finite({i:num | i < n}) ∧ finite(symmetric_group({i:num | i < n}))",
			By(num_segment.FiniteBelowStrict.At(n), symmetric_group.SymmetricGroupFinite.At(indices)))
		term, termDef := a.LetAs[Fun[Permutation[Nat], A]](
			"term",
			"λp:permutation(num). "+
				"    «sign»(p) * module_sum(c.mul, c.one, {i:num | i < n}, λi:num. P(i, permutation_map(p, i)))")
		termsIn := a.Have(
			"each signed term lies in the carrier",
			"∀p:permutation(num). term(p) ∈ c.carrier",
			Derive(func(b *Argument) {
				p := b.FixAs[Permutation[Nat]]()
				b.Show(
					"its sign and its product of entries lie in c, which is closed under products",
					By(over, termDef, LeibnizFactorsIn.Read(c).At(n, P, p), comm_ring.MulIn.Read(c)))
			}))
		multiplicative := comm_ring.MulMonoidOn.Read(c)
		identity := a.TermAs[Permutation[Nat]]("permutation_identity")
		identityIn := a.Have(
			"the identity permutation is supported on the index set: "+
				"the permutations of the points below n are a subgroup",
			"permutation_identity ∈ symmetric_group({i:num | i < n})",
			By(
				group.SubgroupOne.At(
					a.TermAs[group.GroupOps[Permutation[Nat]]]("permutation_group"),
					a.TermAs[Set[Permutation[Nat]]]("symmetric_group({i:num | i < n})")),
				symmetric_group.SymmetricGroupSubgroup.At(indices)))
		vanishes := a.Have(
			"every supported nonidentity permutation contributes zero",
			Statement{
				Binders: "∀p:permutation(num).",
				Hypotheses: []string{
					"p ∈ symmetric_group({i:num | i < n})",
					"p ≠ permutation_identity",
				},
				Conclusion: "term(p) = c.zero",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[Permutation[Nat]]()
				nonidentity := b.Assume()
				r, below := b.ObtainAs[Nat](
					"p sends some row r below the diagonal",
					"∃r:num. r < n ∧ permutation_map(p, r) < r",
					By(nonidentity, symmetric_group.PermutationMovesSomePointDown.At(n, p)))
				factors := b.TermAs[Fun[Nat, A]]("λi:num. P(i, permutation_map(p, i))")
				zeroEntry := b.Have(
					"the entry p picks in row r lies below the diagonal, so it is zero",
					"P(r, permutation_map(p, r)) = c.zero",
					By(below, lower))
				restIn := b.Have(
					"the product over the other rows lies in c",
					"module_sum(c.mul, c.one, delete({i:num | i < n}, r), λi:num. P(i, permutation_map(p, i))) ∈ "+
						"c.carrier",
					By(
						entries,
						finite,
						finite_set.FiniteDeleteImp.At(indices, r),
						module.ModuleSumInMonoid.Read(multiplicative).At(
							b.TermAs[Set[Nat]]("delete({i:num | i < n}, r)"), factors)))
				zeroProduct := b.Have(
					"so the product of the entries p picks is zero, row r's factor singled out",
					"module_sum(c.mul, c.one, {i:num | i < n}, λi:num. P(i, permutation_map(p, i))) = c.zero",
					By(
						below,
						entries,
						finite,
						zeroEntry,
						restIn,
						module.ModuleSumDeleteMonoid.Read(multiplicative).At(indices, r, factors),
						comm_ring.MulLeftZeroOn.Read(c)))
				b.Show(
					"either sign times the zero product is zero",
					By(
						zeroProduct,
						termDef,
						comm_ring.OneIn.Read(c),
						comm_ring.NegIn.Read(c),
						comm_ring.MulRightZeroOn.Read(c)))
			}))
		identityTerm := a.Have(
			"the identity summand is exactly the diagonal product",
			"term(permutation_identity) = module_sum(c.mul, c.one, {i:num | i < n}, λi:num. P(i, i))",
			Derive(func(b *Argument) {
				b.Do(termDef.Rw(), Simp(
					Fwd(symmetric_group.MapIdentity.Inst[Nat]()),
					Fwd(symmetric_group.PermutationIdentityEven)))
				diagonalIn := b.Have(
					"the diagonal product lies in the carrier",
					"module_sum(c.mul, c.one, {i:num | i < n}, λi:num. P(i, i)) ∈ c.carrier",
					By(
						entries,
						finite,
						module.ModuleSumInMonoid.Read(multiplicative).At(
							indices, b.TermAs[Fun[Nat, A]]("λi:num. P(i, i)"))))
				b.Show(
					"multiplication by the sign one leaves that product unchanged",
					ByArith(c, diagonalIn))
			}))
		soleTerm := a.Have(
			"the finite Leibniz sum has only its identity term",
			"module_sum(c.add, c.zero, symmetric_group({i:num | i < n}), term) = term(permutation_identity)",
			By(
				termsIn,
				vanishes,
				finite,
				identityIn,
				module.ModuleSumSingle.Read(module.RegularModuleOn.Read(c)).AsFact().At(
					a.TermAs[Set[Permutation[Nat]]]("symmetric_group({i:num | i < n})"), identity, term)))
		a.Show(
			"evaluating the surviving identity term gives the diagonal product",
			Simp(Fwd(DeterminantDef), Rev(termDef), Fwd(soleTerm), Fwd(identityTerm)),
			Basic())
	}),
})}

// DeterminantIdentity — the identity matrix has determinant one: it is
// upper triangular, so its determinant is the product of its diagonal
// entries (DeterminantTriangular), each of them one, and a finite product
// of ones is one (ModuleSumIdentityMonoid), the empty product at n = 0
// among them.
var DeterminantIdentity = determinantIdentityThm{family.Add(registry.ProofEntry{
	Name: "DeterminantIdentity",
	Key:  "prop_91e7c27796281504",
	Build: family.Theorem(
		"∀c:comm_ring_on(A). ∀n:num. determinant(c, n, matrix_identity(c, n)) = c.one",
		determinantIdentity),
})}

func determinantIdentity(a *Argument, c comm_ring.CommRingFact[on.C], n *Expr[Nat]) {
	upper := a.Have(
		"every entry strictly below the diagonal is zero",
		"∀i j:num. j < i ∧ i < n ⇒ matrix_identity(c, n, i, j) = c.zero",
		Derive(func(b *Argument) {
			b.FixAs[Nat]("i")
			b.FixAs[Nat]("j")
			below := b.Assume()
			distinct := b.Have(
				"a below-diagonal entry has distinct indices",
				"i ≠ j",
				ByArith(below))
			b.Show(
				"the off-diagonal entry is zero",
				Simp(Fwd(MatrixIdentityDef)),
				By(distinct))
		}))
	unitDiagonal := a.Have(
		"the diagonal has finitely many entries below n, all equal to one",
		"finite({i:num | i < n}) ∧ (∀i:num. i ∈ {j:num | j < n} ⇒ matrix_identity(c, n, i, i) = c.one)",
		Simp(Fwd(MatrixIdentityDef)),
		BySets(num_segment.FiniteBelowStrict.At(n)))
	identity := a.MatAs[A, DimN, DimN]("matrix_identity(c, n)")
	a.Show(
		"the triangular formula reduces the determinant to a product of ones",
		CalcEq(Leg(
			a.TermAs[A]("module_sum(c.mul, c.one, {i:num | i < n}, λi:num. matrix_identity(c, n, i, i))"),
			"evaluate the upper triangular determinant",
			By(upper, MatrixIdentityOver.Read(c).At(n), DeterminantTriangular.Read(c).At(n, identity))),
			FinalLeg(
				"the finite product of its diagonal ones is one",
				By(
					unitDiagonal,
					module.ModuleSumIdentityMonoid.Read(comm_ring.MulMonoidOn.Read(c)).At(
						a.TermAs[Set[Nat]]("{i:num | i < n}"),
						a.TermAs[Fun[Nat, A]]("λi:num. matrix_identity(c, n, i, i)"))))))
}
