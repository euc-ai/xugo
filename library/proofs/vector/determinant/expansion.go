package determinant

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/registry"
)

// ColumnMultilinearHom — a form multilinear in the columns is linear in
// each column: with the other columns of P held fixed, u ↦ F(P with column
// j replaced by u) is a homomorphism from the free module on the points
// below n to c. Both are modules; a vector put in column j gives a matrix
// over c, where F takes its values; and the map's additivity and
// homogeneity are F's in column j.
var ColumnMultilinearHom = columnMultilinearHomThm{family.Add(registry.ProofEntry{
	Name: "ColumnMultilinearHom",
	Key:  "prop_6738c649b6c5ddd7",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀F:((num → num → A) → A). ∀P:(num → num → A). ∀j:num.",
		Hypotheses: []string{
			"column_multilinear(c, n, F)",
			"matrix_over(c, n, P)",
			"j < n",
		},
		Conclusion: "module_homomorphism(c, " +
			"    free_module_record(c, {i:num | i < n}), " +
			"    regular_module(c), " +
			"    λu:(num → A). F(matrix_replace_column(c, n, P, j, u)))",
	},
		func(
			a *Argument,
			c comm_ring.CommRingFact[on.C],
			n *Expr[Nat],
			F *Arrow[Fun2[Nat, Nat, A], A],
			P *Arrow2[Nat, Nat, A],
			j *Expr[Nat],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"F is multilinear in the columns",
				"P is a matrix over c",
				"and j is a column")
			over, isColumn := parts[1], parts[2]
			multilinear := a.Conjuncts(
				a.Unfolded(parts[0], ColumnMultilinearDef),
				"F takes its values in c",
				"is additive in each column",
				"and homogeneous in each column")
			a.Show(
				"the map has the five parts of a module homomorphism",
				Unfold(module_homomorphism.ModuleHomomorphismDef),
				SplitConjAll(
					Case(
						"the vectors over c on the points below n form a module over c",
						By(c, free_module.FreeModuleOn)),
					Case(
						"and so does c itself",
						By(module.RegularModuleOn.Read(c))),
					Case(
						"a vector put in column j gives a matrix over c, where F takes its values in c",
						By(multilinear[0], over, ReplaceColumnMatrixOver)),
					Case(
						"the map is additive, F being additive in column j",
						By(multilinear[1], isColumn, over)),
					Case(
						"and homogeneous, F being homogeneous in column j",
						By(multilinear[2], isColumn, over)),
				))
		}),
})}

// MultilinearColumnExpansion — a form multilinear in the columns expands
// along any column j in the standard basis. As a function h of column j, F
// is linear on the free module on the points below n (ColumnMultilinearHom),
// and column j of P is a vector of that module, P vanishing outside the
// n × n block. So F(P), which is h at column j of P, is the sum over the
// column's support of its entries times h at the indicators (FreeHomExpand).
// The support lies below n and the terms below n off it vanish, so the sum
// runs over all m < n; and for m below n the indicator of m is the basis
// vector e_m, column m of the identity (MatrixIdentityColumn).
var MultilinearColumnExpansion = multilinearColumnExpansionThm{family.Add(registry.ProofEntry{
	Name: "MultilinearColumnExpansion",
	Key:  "prop_d738f37aabd9978e",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀F:((num → num → A) → A). ∀P:(num → num → A). ∀j:num.",
		Hypotheses: []string{
			"column_multilinear(c, n, F)",
			"matrix_over(c, n, P)",
			"j < n",
		},
		Conclusion: "F(P) = " +
			"module_sum(c.add, " +
			"    c.zero, " +
			"    {m:num | m < n}, " +
			"    λm:num. P(m, j) * F(matrix_replace_column(c, n, P, j, λr:num. matrix_identity(c, n, r, m))))",
		Abbrev: Abbrev{
			{Name: "h", Text: "λu:(num → A). F(matrix_replace_column(c, n, P, j, u))"},
			{Name: "d", Text: "λx:num. P(x, j) * F(matrix_replace_column(c, n, P, j, delta_at(x)))"},
		},
	},
		func(
			a *Argument,
			c comm_ring.CommRingFact[on.C],
			n *Expr[Nat],
			F *Arrow[Fun2[Nat, Nat, A], A],
			P *Arrow2[Nat, Nat, A],
			j *Expr[Nat],
			given Fact,
		) {
			over := a.Conjuncts(
				given,
				"F is multilinear in the columns",
				"P is a matrix over c",
				"and j is a column")[1]
			entries := MatrixOverEntries.Read(c).At(n, P)
			points := a.TermAs[Set[Nat]]("{i:num | i < n}")
			regular := module.RegularModuleOn.Read(c)
			linear := a.Have(
				"as a function of its column j, F is linear on the vectors over c on the points below n",
				"module_homomorphism(c, free_module_record(c, {i:num | i < n}), regular_module(c), «h»)",
				By(c, given, ColumnMultilinearHom))
			outside := a.Have(
				"P vanishes outside the n × n block",
				"∀r s:num. ¬(r < n ∧ s < n) ⇒ P(r, s) = c.zero",
				By(over, entries, nat_order.NotLessThan))
			below := a.Have(
				"so column j of P vanishes from row n on",
				"fun_support(c.zero, λx:num. P(x, j)) ⊆ {i:num | i < n}",
				BySets(outside))
			column := a.Have(
				"column j of P is a vector over c on the points below n",
				"(λr:num. P(r, j)) ∈ finite_supp(c.zero, c.carrier, {i:num | i < n})",
				By(
					below,
					over,
					function_module.FiniteSuppMember,
					finite_set.FiniteSubset,
					num_segment.FiniteBelowStrict.At(n),
					entries))
			images := a.Have(
				"F at P with the indicator of a point below n in column j lies in c",
				"∀x:num. x < n ⇒ F(matrix_replace_column(c, n, P, j, delta_at(x))) ∈ c.carrier",
				By(module_homomorphism.HomIn.Read(linear), At(free_module.DeltaAtIn.Read(c), points)))
			terms := a.Have(
				"and so does its product with P(x, j)",
				"∀x:num. x < n ⇒ P(x, j) * F(matrix_replace_column(c, n, P, j, delta_at(x))) ∈ c.carrier",
				By(images, over, entries, comm_ring.MulIn.Read(c)))
			vanish := a.Have(
				"which vanishes where P(x, j) does",
				Statement{
					Binders:    "∀x:num.",
					Hypotheses: []string{"x < n", "P(x, j) = c.zero"},
					Conclusion: "P(x, j) * F(matrix_replace_column(c, n, P, j, delta_at(x))) = c.zero",
				},
				By(images, comm_ring.MulLeftZeroOn.Read(c)))
			whole := a.Have(
				"P with its own column j put back is P, both vanishing past the block",
				"matrix_replace_column(c, n, P, j, λr:num. P(r, j)) = P",
				Simp(Fwd(ColumnReplaceDef)),
				By(outside))
			a.Show(
				"F at P is h at column j of P, expanded over its support, then over the points below n",
				CalcEq(
					Leg(
						a.TermAs[A]("F(matrix_replace_column(c, n, P, j, λr:num. P(r, j)))"),
						"P is its own matrix with column j put back",
						By(Normalized, whole)),
					Leg(
						a.TermAs[A]("module_sum(c.add, c.zero, fun_support(c.zero, λx:num. P(x, j)), «d»)"),
						"h at column j is the sum over its support of its entries times h at the indicators",
						By(
							linear,
							column,
							free_module.FreeHomExpand.Read(regular).At(
								points, a.TermAs[Fun[Fun[Nat, A], A]]("«h»"), a.TermAs[Fun[Nat, A]]("λr:num. P(r, j)")))),
					Leg(
						a.TermAs[A]("module_sum(c.add, c.zero, {m:num | m < n}, «d»)"),
						"the support lies below n, and the terms below n off it vanish",
						BySets(
							terms,
							vanish,
							below,
							module.ModuleSumSupport.Read(regular).At(
								points, a.TermAs[Set[Nat]]("fun_support(c.zero, λx:num. P(x, j))"), a.TermAs[Fun[Nat, A]]("«d»")),
							num_segment.FiniteBelowStrict.At(n))),
					FinalLeg(
						"and below n the indicator of m is the basis vector e_m, column m of the identity",
						By(
							At(MatrixIdentityColumn, a.TermAs[RingOps[A]]("c"), n),
							module.ModuleSumCongruence.At(
								a.TermAs[Op[A]]("c.add"),
								a.TermAs[A]("c.zero"),
								a.TermAs[Set[Nat]]("{m:num | m < n}"),
								a.TermAs[Fun[Nat, A]]("«d»"),
								a.TermAs[Fun[Nat, A]](
									"λm:num. P(m, j) * F(matrix_replace_column(c, n, P, j, λr:num. matrix_identity(c, n, r, m)))")))),
				))
		}),
})}

// PinnedMapsExtension — a map pinned at k sends every point below k below
// n and fixes every point from k on. The maps pinned at k + 1 are exactly
// the maps pinned at k with their value at k reset to a point m below n,
// and each comes from one pair (f, m) only. A reset map stays below n
// before k + 1, by m at k and by f below k, and fixes the points past k as
// f does. A map g pinned at k + 1 is the reset of g with k put back at k,
// paired with g(k). Two pairs with one reset agree at k, where the reset is
// the point, and off k, where it is the map, both maps sending k to k.
var PinnedMapsExtension = pinnedMapsExtensionThm{family.Add(registry.ProofEntry{
	Name: "PinnedMapsExtension",
	Key:  "prop_941813f0442b953d",
	Build: family.Theorem(Statement{
		Binders: "∀n k:num.",
		Conclusion: "image(«reset», set_cross(«pinned»(k), {m:num | m < n})) = «pinned»(suc(k)) ∧ " +
			"injective_on(set_cross(«pinned»(k), {m:num | m < n}), «reset»)",
		Abbrev: Abbrev{
			{Name: "reset", Text: "λp:prod(num → num, num). λj:num. COND(j = k, snd(p), fst(p)(j))"},
		},
	},
		func(a *Argument, n, k *Expr[Nat]) {
			pairsBelow := a.TermAs[Set[Prod[Fun[Nat, Nat], Nat]]]("set_cross(«pinned»(k), {m:num | m < n})")
			reset := a.TermAs[Fun[Prod[Fun[Nat, Nat], Nat], Fun[Nat, Nat]]]("«reset»")
			into := a.Have(
				"a map pinned at k, reset at k to a point below n, is pinned at k + 1",
				"image(«reset», set_cross(«pinned»(k), {m:num | m < n})) ⊆ «pinned»(suc(k))",
				Unfold(set_basic.SubsetDef),
				Simp(Fwd(set_image.ForallInImage)),
				Derive(func(b *Argument) {
					b.FixAs[Prod[Fun[Nat, Nat], Nat]]("p")
					inPairs := b.Assume()
					parts := b.Conjuncts(
						b.Have(
							"the map of p sends the points below k below n and fixes the rest, and its point lies below n",
							"(∀j:num. j < k ⇒ fst(p)(j) < n) ∧ (∀j:num. k ≤ j ⇒ fst(p)(j) = j) ∧ snd(p) < n",
							By(inPairs, set_product.InCrossProjections)),
						"below k the map stays below n",
						"from k on it fixes every point",
						"and the point lies below n")
					bounded, fixed, point := parts[0], parts[1], parts[2]
					lower := b.Have(
						"below k + 1 the reset map is the point at k and the map below k, both below n",
						"∀j:num. j < suc(k) ⇒ COND(j = k, snd(p), fst(p)(j)) < n",
						b.ForEach(func(j *Expr[Nat]) Action {
							return By(bounded.At(j), point, nat_order.LessThanSucClause.At(j, k))
						}))
					upper := b.Have(
						"from k + 1 on, past k, the reset map is the map of p, which fixes every point there",
						"∀j:num. suc(k) ≤ j ⇒ COND(j = k, snd(p), fst(p)(j)) = j",
						b.ForEach(func(j *Expr[Nat]) Action {
							return ByArith(
								fixed.At(j),
								nat_order.SucLessEqIffLessThan.At(k, j),
								nat_order.LessEqOfLessThan.At(k, j))
						}))
					b.Show(
						"so the reset map is pinned at k + 1",
						By(lower, upper))
				}))
			onto := a.Have(
				"a map pinned at k + 1 is the reset of itself with k put back at k, paired with its value at k",
				"«pinned»(suc(k)) ⊆ image(«reset», set_cross(«pinned»(k), {m:num | m < n}))",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					b.FixAs[Fun[Nat, Nat]]("g")
					member := b.Assume()
					parts := b.Conjuncts(
						b.Have(
							"g sends the points below k + 1 below n and fixes the rest",
							"(∀j:num. j < suc(k) ⇒ g(j) < n) ∧ (∀j:num. suc(k) ≤ j ⇒ g(j) = j)",
							By(member)),
						"below k + 1 g stays below n",
						"and from k + 1 on it fixes every point")
					bounded, fixed := parts[0], parts[1]
					lower := b.Have(
						"with k put back at k, g still sends the points below k below n",
						"∀j:num. j < k ⇒ COND(j = k, k, g(j)) < n",
						b.ForEach(func(j *Expr[Nat]) Action {
							return ByArith(bounded.At(j), nat_order.LessThanSucClause.At(j, k))
						}))
					upper := b.Have(
						"and fixes every point from k on: k by the reset, the points past k as g does",
						"∀j:num. k ≤ j ⇒ COND(j = k, k, g(j)) = j",
						b.ForEach(func(j *Expr[Nat]) Action {
							return By(fixed.At(j), nat_order.SucLessEqIffLessThan.At(k, j), nat_order.LessEqSplit.At(k, j))
						}))
					point := b.Have(
						"the value of g at k lies below n",
						"g(k) < n",
						By(bounded.At(k), nat_order.LessThanSucClause.At(k, k)))
					first, value := b.TermAs[Fun[Nat, Nat]]("λj:num. COND(j = k, k, g(j))"), b.TermAs[Nat]("g(k)")
					source := b.TermAs[Prod[Fun[Nat, Nat], Nat]]("(λj:num. COND(j = k, k, g(j)), g(k))")
					inPairs := b.Have(
						"so g with k put back, paired with g(k), is a pair of the product",
						"(λj:num. COND(j = k, k, g(j)), g(k)) ∈ set_cross(«pinned»(k), {m:num | m < n})",
						By(lower, upper, point, set_product.InCross))
					back := b.Have(
						"and its reset at k puts g(k) back at k, which is g",
						"«reset»((λj:num. COND(j = k, k, g(j)), g(k))) = g",
						By(pairs.Fst.At(first, value), pairs.Snd.At(first, value)))
					b.Show(
						"so g is a reset of a pair of the product",
						By(back, inPairs, set_image.FunInImage.At(reset, pairsBelow, source)))
				}))
			separates := a.Have(
				"two pairs with one reset are one pair",
				"injective_on(set_cross(«pinned»(k), {m:num | m < n}), «reset»)",
				Unfold(functions.InjectiveOnDef),
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[Fun[Nat, Nat], Nat]]("p")
					q := b.FixAs[Prod[Fun[Nat, Nat], Nat]]("q")
					given := b.Conjuncts(
						b.Assume(),
						"p lies in the product",
						"so does q",
						"and their resets at k agree")
					maps := b.Have(
						"the maps of p and q are pinned at k",
						"fst(p) ∈ «pinned»(k) ∧ fst(q) ∈ «pinned»(k)",
						By(given[0], given[1], set_product.InCrossProjections))
					atK := b.Have(
						"so both send k to k",
						"fst(p)(k) = k ∧ fst(q)(k) = k",
						By(maps, nat_order.LessEqRefl))
					b.Show(
						"the resets agree at k, where they are the points, and off k, where they are the maps",
						By(given[2], atK, pairs.PairEta.At(p), pairs.PairEta.At(q), pairs.PairEq))
				}))
			image := a.Have(
				"each side lies in the other",
				"image(«reset», set_cross(«pinned»(k), {m:num | m < n})) = «pinned»(suc(k))",
				By(into, onto, set_order.SubsetAntisym))
			a.Show(
				"the resets fill the maps pinned at k + 1, each once",
				By(image, separates))
		}),
})}

// PinnedMapsFinite — finitely many maps are pinned at k. By induction on k:
// a map pinned at 0 is the identity; and the maps pinned at k + 1 are the
// image of the maps pinned at k paired with the points below n
// (PinnedMapsExtension), a finite product.
var PinnedMapsFinite = pinnedMapsFiniteThm{family.Add(registry.ProofEntry{
	Name: "PinnedMapsFinite",
	Key:  "prop_644941360d4b7a2b",
	Build: family.Theorem(Statement{
		Binders:    "∀n k:num.",
		Conclusion: "finite(«pinned»(k))",
	},
		func(a *Argument, n *Expr[Nat]) {
			a.Induct("k")
			a.Base(
				"a map pinned at 0 is the identity, a single map",
				func(b *Argument) {
					identity := b.Have(
						"every map pinned at 0 is the identity",
						"«pinned»(0) ⊆ {λj:num. j}",
						BySets(nat_order.ZeroLessEq))
					b.Show(
						"so there is at most one",
						By(identity, finite_set.FiniteSubset, finite_set.FiniteSing))
				})
			a.Step(
				"the maps pinned at k + 1 are the image of the maps pinned at k paired with the points below n",
				func(b *Argument, ih Fact) {
					k := b.TermAs[Nat]("k")
					resets := b.Conjuncts(
						PinnedMapsExtension.At(n, k),
						"the resets at k are the maps pinned at k + 1",
						"each reached once")
					b.Show(
						"an image of a product of two finite sets is finite",
						resets[0].RwRev(),
						By(ih, num_segment.FiniteBelowStrict.At(n), finite_set.FiniteProduct, finite_set.FiniteImage))
				})
		}),
})}

// MultilinearMapExpansion — a form F multilinear in the columns, at a matrix
// P over c, is the sum over the maps f pinned at n of the product of the
// entries P(f(j), j) times F at the matrix whose column j is the basis
// vector at f(j). By induction on k ≤ n, F(P) is the sum over the maps
// pinned at k of w(k, f), the product of the entries P(f(j), j) below k,
// times F at Q(k, f), P with each column j < k replaced by the basis vector
// at f(j). At k = 0 the identity is the one such map, its product is empty
// and Q(0, ·) is P. From k to k + 1, F at Q(k, f) expands along column k
// (MultilinearColumnExpansion) into the terms P(m, k) times F at
// Q(k + 1, reset(k, f, m)), where reset(k, f, m) is f with its value at k
// reset to m, and P(m, k) joins the product; the double sum over f and m is
// a sum over the pairs (f, m), which the reset carries one to one onto the
// maps pinned at k + 1 (PinnedMapsExtension). At k = n a column past n is
// zero in P and in the basis matrix alike.
var MultilinearMapExpansion = multilinearMapExpansionThm{family.Add(registry.ProofEntry{
	Name: "MultilinearMapExpansion",
	Key:  "prop_93a6760d87ad03f2",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀F:((num → num → A) → A). ∀P:(num → num → A).",
		Hypotheses: []string{
			"column_multilinear(c, n, F)",
			"matrix_over(c, n, P)",
		},
		Conclusion: "F(P) = " +
			"module_sum(c.add, " +
			"    c.zero, " +
			"    «pinned»(n), " +
			"    λf:num → num. " +
			"        module_sum(c.mul, c.one, {j:num | j < n}, λj:num. P(f(j), j)) * " +
			"        F(λr:num. λs:num. matrix_identity(c, n, r, f(s))))",
		Abbrev: Abbrev{
			{Name: "w", Text: "λk:num. λf:num → num. " +
				"    module_sum(c.mul, c.one, {j:num | j < k}, λj:num. P(f(j), j))"},
			{Name: "Q", Text: "λk:num. λf:num → num. λr:num. λs:num. " +
				"    COND(s < k, matrix_identity(c, n, r, f(s)), P(r, s))"},
			{Name: "reset", Text: "λk:num. λf:num → num. λm:num. λj:num. COND(j = k, m, f(j))"},
			{Name: "e", Text: "λm:num. λr:num. matrix_identity(c, n, r, m)"},
		},
	},
		func(
			a *Argument,
			c comm_ring.CommRingFact[on.C],
			n *Expr[Nat],
			F *Arrow[Fun2[Nat, Nat, A], A],
			P *Arrow2[Nat, Nat, A],
			h Fact,
		) {
			parts := a.Conjuncts(
				h,
				"F is multilinear in the columns",
				"and P is a matrix over c")
			multilinear, over := parts[0], parts[1]
			values := a.Conjuncts(
				a.Unfolded(multilinear, ColumnMultilinearDef),
				"F takes its values in c",
				"is additive in each column",
				"and homogeneous in each column")[0]
			ring := a.TermAs[RingOps[A]]("c")
			regular := module.RegularModuleOn.Read(c)
			entries := a.Have(
				"every entry of P lies in c",
				"∀r s:num. P(r, s) ∈ c.carrier",
				By(over, MatrixOverEntries.Read(c).At(n, P)))
			outside := a.Have(
				"P vanishes outside the n × n block",
				"∀r s:num. ¬(r < n ∧ s < n) ⇒ P(r, s) = c.zero",
				By(over, MatrixOverEntries.Read(c).At(n, P), nat_order.NotLessThan))
			qOver := a.Have(
				"for k ≤ n, Q(k, f) is a matrix over c",
				"∀k:num. ∀f:(num → num). k ≤ n ⇒ matrix_over(c, n, «Q»(k, f))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					b.FixAs[Fun[Nat, Nat]]("f")
					upTo := b.Assume()
					b.Show(
						"its entries are one, zero or P's, and past the block zero",
						Simp(Fwd(MatrixOverEntries.Read(c)), Fwd(MatrixIdentityDef)),
						SplitConj(
							Case(
								"each entry is one, zero or an entry of P, all in c",
								By(entries, comm_ring.OneIn.Read(c), comm_ring.ZeroIn.Read(c))),
							Case(
								"past the block a replaced column is off the diagonal below n, and an entry of P is zero",
								By(upTo, outside, nat_order.NotLessThan, nat_order.LessThanLessEqTrans)),
						))
				}))
			weightIn := a.Have(
				"each product w(k, f) of entries of P lies in c",
				"∀k:num. ∀f:num → num. «w»(k, f) ∈ c.carrier",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					b.FixAs[Fun[Nat, Nat]]("f")
					b.Show(
						"a finite product of entries of P, all in c",
						By(
							entries,
							num_segment.FiniteBelowStrict.At(k),
							module.ModuleSumInMonoid.Read(comm_ring.MulMonoidOn.Read(c))))
				}))
			termIn := a.Have(
				"for k ≤ n each term w(k, f) times F at Q(k, f) lies in c",
				"∀k:num. ∀f:(num → num). k ≤ n ⇒ «w»(k, f) * F(«Q»(k, f)) ∈ c.carrier",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					f := b.FixAs[Fun[Nat, Nat]]("f")
					upTo := b.Assume()
					b.Show(
						"the product lies in c, and so does F at a matrix over c",
						By(weightIn.At(k, f), values, qOver.At(k, f), upTo, comm_ring.MulIn.Read(c)))
				}))
			replaced := a.Have(
				"column k of Q(k, f) replaced by the basis vector at m is Q(k + 1, reset(k, f, m))",
				Statement{
					Binders:    "∀k:num. ∀f:num → num. ∀m:num.",
					Hypotheses: []string{"k < n"},
					Conclusion: "matrix_replace_column(c, n, «Q»(k, f), k, «e»(m)) = «Q»(suc(k), «reset»(k, f, m))",
				},
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					b.FixAs[Fun[Nat, Nat]]("f")
					m := b.FixAs[Nat]("m")
					below := b.Assume()
					b.Show(
						"entry by entry, by the column's place against k",
						Funext(),
						Simp(Fwd(ColumnReplaceDef)),
						Derive(func(d *Argument) {
							r := d.FixAs[Nat]("r")
							s := d.FixAs[Nat]("s")
							d.Cases(d.Term("s = k"))
							d.When(
								"column k is the basis vector at m on both sides, and zero past row n",
								func(e *Argument, atK Fact) {
									e.Show(
										"both sides are the basis vector at m",
										By(
											Normalized,
											below,
											atK,
											MatrixIdentityDef.At(ring, n, r, m),
											nat_order.LessThanSucClause.At(k, k)))
								})
							d.Otherwise(
								"off column k both sides are Q(k, f), the reset map agreeing with f",
								func(e *Argument, offK Fact) {
									e.Show(
										"past the block a basis column lies below n and an entry of P vanishes",
										By(
											Normalized,
											offK,
											outside.At(r, s),
											below,
											MatrixIdentityDef.At(ring, n, r, e.TermAs[Nat]("f(s)")),
											nat_order.LessThanSucClause.At(s, k),
											nat_order.LessThanTrans.At(s, k, n)))
								})
						}))
				}))
			weight := a.Have(
				"resetting f to m at k makes the product below k + 1 the product below k times P(m, k)",
				"∀k:num. ∀f:num → num. ∀m:num. «w»(suc(k), «reset»(k, f, m)) = P(m, k) * «w»(k, f)",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					b.FixAs[Fun[Nat, Nat]]("f")
					b.FixAs[Nat]("m")
					agree := b.Have(
						"below k the reset map is f",
						"∀j:num. j < k ⇒ P(COND(j = k, m, f(j)), j) = P(f(j), j)",
						b.ForEach(func(_ *Expr[Nat]) Action { return ByArith() }))
					lower := b.Have(
						"so its product below k is the product of f",
						"module_sum(c.mul, c.one, {j:num | j < k}, λj:num. P(COND(j = k, m, f(j)), j)) = «w»(k, f)",
						By(agree, module.ModuleSumCongruence))
					b.Show(
						"the points below k + 1 are k laid into those below k, where the new factor is P(m, k)",
						Simp(Fwd(num_segment.BelowStrictClauses)),
						By(
							lower,
							entries,
							num_segment.FiniteBelowStrict.At(k),
							nat_order.LessThanIrrefl.At(k),
							module.ModuleSumInsertMonoid.Read(comm_ring.MulMonoidOn.Read(c)).At(
								b.TermAs[Set[Nat]]("{j:num | j < k}"),
								k,
								b.TermAs[Fun[Nat, A]]("λj:num. P(COND(j = k, m, f(j)), j)"))))
				}))
			alongColumn := a.Have(
				"F at Q(k, f) expands along column k, which is column k of P",
				Statement{
					Binders:    "∀k:num. ∀f:num → num.",
					Hypotheses: []string{"k < n"},
					Conclusion: "F(«Q»(k, f)) = " +
						"module_sum(c.add, c.zero, {m:num | m < n}, λm:num. P(m, k) * F(«Q»(suc(k), «reset»(k, f, m))))",
				},
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					f := b.FixAs[Fun[Nat, Nat]]("f")
					below := b.Assume()
					expand := b.Have(
						"F, multilinear in the columns, expands along column k of the matrix Q(k, f) over c",
						"F(«Q»(k, f)) = "+
							"module_sum(c.add, "+
							"    c.zero, "+
							"    {m:num | m < n}, "+
							"    λm:num. "+
							"        «Q»(k, f, m, k) * "+
							"        F(matrix_replace_column(c, n, «Q»(k, f), k, λr:num. matrix_identity(c, n, r, m))))",
						By(
							below,
							multilinear,
							qOver.At(k, f),
							nat_order.LessEqOfLessThan.At(k, n),
							MultilinearColumnExpansion.Read(c).At(n, F, b.TermAs[Fun2[Nat, Nat, A]]("«Q»(k, f)"), k)))
					resetTerms := b.Have(
						"column k of Q(k, f) is P's, and with it replaced by the "+
							"basis vector at m the matrix is Q(k + 1, reset(k, f, m))",
						Statement{
							Binders:    "∀m:num.",
							Hypotheses: []string{"m ∈ {m:num | m < n}"},
							Conclusion: "«Q»(k, f, m, k) * " +
								"F(matrix_replace_column(c, n, «Q»(k, f), k, λr:num. matrix_identity(c, n, r, m))) = " +
								"P(m, k) * F(«Q»(suc(k), «reset»(k, f, m)))",
						},
						b.ForEach(func(m *Expr[Nat]) Action {
							return By(replaced.At(k, f, m), below, nat_order.LessThanIrrefl.At(k))
						}))
					b.Show(
						"so the expansion is the sum of the terms at the reset maps",
						expand.Rw(),
						By(resetTerms, module.ModuleSumCongruence))
				}))
			perTerm := a.Have(
				"w(k, f) times F at Q(k, f) is the sum over m < n of the terms at k + 1 of reset(k, f, m)",
				Statement{
					Binders:    "∀k:num. ∀f:num → num.",
					Hypotheses: []string{"k < n"},
					Conclusion: "«w»(k, f) * F(«Q»(k, f)) = " +
						"module_sum(c.add, " +
						"    c.zero, " +
						"    {m:num | m < n}, " +
						"    λm:num. «w»(suc(k), «reset»(k, f, m)) * F(«Q»(suc(k), «reset»(k, f, m))))",
				},
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					f := b.FixAs[Fun[Nat, Nat]]("f")
					below := b.Assume()
					next := b.TermAs[Nat]("suc(k)")
					summands := b.Have(
						"each term P(m, k) times F at Q(k + 1, reset(k, f, m)) lies in c",
						"∀m:num. m ∈ {m:num | m < n} ⇒ P(m, k) * F(«Q»(suc(k), «reset»(k, f, m))) ∈ c.carrier",
						Derive(func(d *Argument) {
							m := d.FixAs[Nat]("m")
							d.Show(
								"an entry of P times F at a matrix over c",
								By(
									entries.At(m, k),
									values,
									qOver.At(next, d.TermAs[Fun[Nat, Nat]]("«reset»(k, f, m)")),
									below,
									nat_order.SucLessEqIffLessThan.At(k, n),
									comm_ring.MulIn.Read(c)))
						}))
					regroup := b.Have(
						"w(k, f) times P(m, k) is the product below k + 1 of reset(k, f, m)",
						Statement{
							Binders:    "∀m:num.",
							Hypotheses: []string{"m ∈ {m:num | m < n}"},
							Conclusion: "«w»(k, f) * (P(m, k) * F(«Q»(suc(k), «reset»(k, f, m)))) = " +
								"«w»(suc(k), «reset»(k, f, m)) * F(«Q»(suc(k), «reset»(k, f, m)))",
						},
						Derive(func(d *Argument) {
							m := d.FixAs[Nat]("m")
							resetMap := d.TermAs[Fun[Nat, Nat]]("«reset»(k, f, m)")
							d.Show(
								"the ring regroups the three factors",
								ByArith(
									c,
									weight.At(k, f, m),
									weightIn.At(k, f),
									entries.At(m, k),
									values.At(d.TermAs[Fun2[Nat, Nat, A]]("«Q»(suc(k), «reset»(k, f, m))")),
									qOver.At(next, resetMap),
									below,
									nat_order.SucLessEqIffLessThan.At(k, n)))
						}))
					weightK := b.MemberOf[on.C](b.TermAs[A]("«w»(k, f)"), weightIn.At(k, f))
					b.Show(
						"expand F along column k and carry w(k, f) into the sum",
						CalcEq(
							Leg(
								b.TermAs[A](
									"«w»(k, f) * "+
										"module_sum(c.add, c.zero, {m:num | m < n}, λm:num. P(m, k) * F(«Q»(suc(k), «reset»(k, f, m))))"),
								"F at Q(k, f) expands along column k",
								By(alongColumn.At(k, f), below)),
							Leg(
								b.TermAs[A](
									"module_sum(c.add, "+
										"    c.zero, "+
										"    {m:num | m < n}, "+
										"    λm:num. «w»(k, f) * (P(m, k) * F(«Q»(suc(k), «reset»(k, f, m)))))"),
								"w(k, f) goes through the finite sum",
								By(
									summands,
									num_segment.FiniteBelowStrict.At(n),
									module.ModuleSumSmul.Read(regular).At(
										b.TermAs[Set[Nat]]("{m:num | m < n}"),
										weightK,
										b.TermAs[Fun[Nat, A]]("λm:num. P(m, k) * F(«Q»(suc(k), «reset»(k, f, m)))")))),
							FinalLeg(
								"and each term regroups into the term at k + 1",
								By(regroup, module.ModuleSumCongruence)),
						))
				}))
			expansion := a.Have(
				"by induction on k, F(P) is the sum over the maps pinned at k of w(k, f) times F at Q(k, f)",
				Statement{
					Binders:    "∀k:num.",
					Hypotheses: []string{"k ≤ n"},
					Conclusion: "F(P) = module_sum(c.add, c.zero, «pinned»(k), λf:num → num. «w»(k, f) * F(«Q»(k, f)))",
				},
				Derive(func(d *Argument) {
					d.Induct("k")
					d.Base(
						"a map pinned at 0 is the identity, whose product is empty and whose Q(0, ·) is P",
						func(b *Argument) {
							upTo := b.Assume()
							identity := b.TermAs[Fun[Nat, Nat]]("λj:num. j")
							noneReplaced := b.Have(
								"with no column replaced, Q(0, ·) is P",
								"«Q»(0, λj:num. j) = P",
								By(nat_order.LessThanZeroClause))
							emptyProduct := b.Have(
								"and the empty product is one",
								"«w»(0, λj:num. j) = c.one",
								Simp(Fwd(num_segment.BelowStrictClauses)),
								Cite(module.ModuleSumEmpty))
							only := b.Conjuncts(
								b.Have(
									"the identity is the one map pinned at 0",
									"(λj:num. j) ∈ «pinned»(0) ∧ (∀y:num → num. y ∈ «pinned»(0) ⇒ y = (λj:num. j))",
									BySets(nat_order.ZeroLessEq, nat_order.LessThanZeroClause)),
								"the identity is pinned at 0",
								"and every map pinned at 0 is the identity")
							finite := b.Have(
								"so there are finitely many",
								"finite(«pinned»(0))",
								By(PinnedMapsFinite.At(n, b.TermAs[Nat]("0"))))
							termsIn := b.Have(
								"each term over them lies in c",
								"∀y:(num → num). y ∈ «pinned»(0) ⇒ «w»(0, y) * F(«Q»(0, y)) ∈ c.carrier",
								By(termIn, upTo))
							offIdentity := b.Have(
								"and the terms off the identity vanish, there being none",
								"∀y:(num → num). y ∈ «pinned»(0) ∧ y ≠ (λj:num. j) ⇒ «w»(0, y) * F(«Q»(0, y)) = c.zero",
								By(only[1]))
							single := b.Have(
								"so the sum is its term at the identity",
								"module_sum(c.add, c.zero, «pinned»(0), λf:num → num. «w»(0, f) * F(«Q»(0, f))) = "+
									"«w»(0, λj:num. j) * F(«Q»(0, λj:num. j))",
								By(
									finite,
									only[0],
									termsIn,
									offIdentity,
									module.ModuleSumSingle.Read(regular).At(
										b.TermAs[Set[Fun[Nat, Nat]]]("«pinned»(0)"),
										identity,
										b.TermAs[Fun[Fun[Nat, Nat], A]]("λf:num → num. «w»(0, f) * F(«Q»(0, f))"))))
							b.Show(
								"which is one times F(P)",
								ByArith(c, single, emptyProduct, noneReplaced, values, over))
						})
					d.Step(
						"each term splits along column k over the resets at k, which are the maps pinned at k + 1",
						func(b *Argument, ih Fact) {
							k := b.TermAs[Nat]("k")
							bound := b.Assume()
							below := b.Have(
								"k lies below n",
								"k < n",
								ByArith(bound))
							upTo := b.Have(
								"so k is at most n",
								"k ≤ n",
								ByArith(bound))
							resets := b.Conjuncts(
								PinnedMapsExtension.At(n, k),
								"the resets at k of the pairs are the maps pinned at k + 1",
								"and the reset tells the pairs apart")
							maps := b.TermAs[Set[Fun[Nat, Nat]]]("«pinned»(k)")
							points := b.TermAs[Set[Nat]]("{m:num | m < n}")
							finite := b.Have(
								"finitely many maps are pinned at k",
								"finite(«pinned»(k))",
								By(PinnedMapsFinite.At(n, k)))
							pairsFinite := b.Have(
								"so they make finitely many pairs with the points below n",
								"finite(set_cross(«pinned»(k), {m:num | m < n}))",
								By(finite, num_segment.FiniteBelowStrict.At(n), finite_set.FiniteProduct.At(maps, points)))
							nextIn := b.Have(
								"every term at k + 1 lies in c",
								"∀f:num → num. «w»(suc(k), f) * F(«Q»(suc(k), f)) ∈ c.carrier",
								By(termIn, bound))
							termAsSum := b.Have(
								"each term over the maps pinned at k is a sum over m < n",
								Statement{
									Binders:    "∀f:num → num.",
									Hypotheses: []string{"f ∈ «pinned»(k)"},
									Conclusion: "«w»(k, f) * F(«Q»(k, f)) = " +
										"module_sum(c.add, " +
										"    c.zero, " +
										"    {m:num | m < n}, " +
										"    λm:num. «w»(suc(k), «reset»(k, f, m)) * F(«Q»(suc(k), «reset»(k, f, m))))",
								},
								By(perTerm, below))
							b.Show(
								"the double sum is a sum over the pairs, carried one to one onto the maps pinned at k + 1",
								CalcEq(
									Leg(
										b.TermAs[A]("module_sum(c.add, c.zero, «pinned»(k), λf:num → num. «w»(k, f) * F(«Q»(k, f)))"),
										"the claim at k",
										By(ih, upTo)),
									Leg(
										b.TermAs[A](
											"module_sum(c.add, "+
												"    c.zero, "+
												"    «pinned»(k), "+
												"    λf:num → num. "+
												"        module_sum(c.add, "+
												"            c.zero, "+
												"            {m:num | m < n}, "+
												"            λm:num. «w»(suc(k), «reset»(k, f, m)) * F(«Q»(suc(k), «reset»(k, f, m)))))"),
										"each term splits over the resets at k",
										By(termAsSum, module.ModuleSumCongruence)),
									Leg(
										b.TermAs[A](
											"module_sum(c.add, "+
												"    c.zero, "+
												"    set_cross(«pinned»(k), {m:num | m < n}), "+
												"    λp:prod(num → num, num). "+
												"        «w»(suc(k), «reset»(k, fst(p), snd(p))) * F(«Q»(suc(k), «reset»(k, fst(p), snd(p)))))"),
										"a double sum is a sum over the pairs",
										By(
											finite,
											nextIn,
											num_segment.FiniteBelowStrict.At(n),
											module.ModuleSumCross.Read(regular).At(maps, points,
												b.TermAs[Fun2[Fun[Nat, Nat], Nat, A]](
													"λf:num → num. λm:num. «w»(suc(k), «reset»(k, f, m)) * F(«Q»(suc(k), «reset»(k, f, m)))")))),
									Leg(
										b.TermAs[A](
											"module_sum(c.add, "+
												"    c.zero, "+
												"    image(λp:prod(num → num, num). «reset»(k, fst(p), snd(p)), "+
												"        set_cross(«pinned»(k), {m:num | m < n})), "+
												"    λf:num → num. «w»(suc(k), f) * F(«Q»(suc(k), f)))"),
										"the reset at k is one to one on the pairs",
										By(
											pairsFinite,
											nextIn,
											resets[1],
											module.ModuleSumImage.Read(regular).At(
												b.TermAs[Set[Prod[Fun[Nat, Nat], Nat]]]("set_cross(«pinned»(k), {m:num | m < n})"),
												b.TermAs[Fun[Prod[Fun[Nat, Nat], Nat], Fun[Nat, Nat]]](
													"λp:prod(num → num, num). «reset»(k, fst(p), snd(p))"),
												b.TermAs[Fun[Fun[Nat, Nat], A]]("λf:num → num. «w»(suc(k), f) * F(«Q»(suc(k), f))")))),
									FinalLeg(
										"and its image is the maps pinned at k + 1",
										By(resets[0])),
								))
						})
				}))
			atN := a.Have(
				"at k = n",
				"F(P) = module_sum(c.add, c.zero, «pinned»(n), λf:num → num. «w»(n, f) * F(«Q»(n, f)))",
				By(expansion, nat_order.LessEqRefl.At(n)))
			basisMatrix := a.Have(
				"for a map pinned at n, every column of Q(n, f) is "+
					"the basis vector at f(s), past n both being zero",
				"∀f:(num → num). f ∈ «pinned»(n) ⇒ «Q»(n, f) = λr:num. λs:num. matrix_identity(c, n, r, f(s))",
				Derive(func(b *Argument) {
					b.FixAs[Fun[Nat, Nat]]("f")
					member := b.Assume()
					fixed := b.Have(
						"f fixes every point from n on",
						"∀j:num. n ≤ j ⇒ f(j) = j",
						By(member))
					b.Show(
						"entry by entry, by the column's place against n",
						Funext(),
						Derive(func(d *Argument) {
							r := d.FixAs[Nat]("r")
							s := d.FixAs[Nat]("s")
							d.Cases(d.Term("s < n"))
							d.When(
								"below column n the column of Q(n, f) is the basis vector at f(s)",
								func(e *Argument, inside Fact) {
									e.Show(
										"by its definition",
										By(inside))
								})
							d.Otherwise(
								"past column n the entry of P is zero, and so is the basis vector at f(s) = s ≥ n",
								func(e *Argument, past Fact) {
									e.Show(
										"both sides are zero",
										By(
											past,
											fixed.At(s),
											outside.At(r, s),
											MatrixIdentityDef.At(ring, n, r, s),
											nat_order.NotLessThan.At(s, n)))
								})
						}))
				}))
			termwise := a.Have(
				"so each term at n is the product of the entries P(f(j), j) times F at the basis matrix of f",
				Statement{
					Binders:    "∀f:num → num.",
					Hypotheses: []string{"f ∈ «pinned»(n)"},
					Conclusion: "«w»(n, f) * F(«Q»(n, f)) = " +
						"module_sum(c.mul, c.one, {j:num | j < n}, λj:num. P(f(j), j)) * " +
						"F(λr:num. λs:num. matrix_identity(c, n, r, f(s)))",
				},
				By(basisMatrix))
			a.Show(
				"F(P) is the sum over the maps pinned at n",
				atN.Rw(),
				By(termwise, module.ModuleSumCongruence))
		}),
})}

// AlternatingFormPermutationExpansion — an alternating form F at a matrix P
// over c is the sum over the permutations p of the points below n of the
// product of the entries P(p(j), j) times F at the permutation matrix of p,
// whose column s is the basis vector at p(s). Expanding every column in the
// standard basis writes F(P) as the sum over the maps f pinned at n of the
// product w(f) of the entries P(f(j), j) times F at the matrix E(f) whose
// column s is the basis vector at f(s) (MultilinearMapExpansion). A map that is not one to one on the
// points below n sends two of them to one point, so E(f) has two equal
// columns and F vanishes there; a map that is one to one there is the map of
// a permutation (FiniteInjectionPermutation). So the sum runs over the maps of
// the permutations alone, and permutation_map, one to one, re-indexes it as a
// sum over the permutations, where E(p's map) is p's permutation matrix.
var AlternatingFormPermutationExpansion = alternatingFormPermutationExpansionThm{family.Add(registry.ProofEntry{
	Name: "AlternatingFormPermutationExpansion",
	Key:  "prop_119a749c8dbcb481",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀F:((num → num → A) → A). ∀P:(num → num → A).",
		Hypotheses: []string{
			"alternating_form(c, n, F)",
			"matrix_over(c, n, P)",
		},
		Conclusion: "F(P) = " +
			"module_sum(c.add, " +
			"    c.zero, " +
			"    symmetric_group({i:num | i < n}), " +
			"    λp:permutation(num). " +
			"        module_sum(c.mul, c.one, {j:num | j < n}, λj:num. P(permutation_map(p, j), j)) * " +
			"        F(permutation_matrix(c, n, p)))",
		Abbrev: Abbrev{
			{Name: "w", Text: "λf:num → num. module_sum(c.mul, c.one, {j:num | j < n}, λj:num. P(f(j), j))"},
			{Name: "E", Text: "λf:num → num. λr:num. λs:num. matrix_identity(c, n, r, f(s))"},
		},
	},
		func(
			a *Argument,
			c comm_ring.CommRingFact[on.C],
			n *Expr[Nat],
			F *Arrow[Fun2[Nat, Nat, A], A],
			P *Arrow2[Nat, Nat, A],
			h Fact,
		) {
			parts := a.Conjuncts(
				h,
				"F is an alternating form",
				"and P is a matrix over c")
			over := parts[1]
			form := a.Conjuncts(
				a.Unfolded(parts[0], AlternatingFormDef),
				"F is multilinear in the columns",
				"and vanishes when two columns agree")
			multilinear, alternates := form[0], form[1]
			values := a.Conjuncts(
				a.Unfolded(multilinear, ColumnMultilinearDef),
				"F takes its values in c",
				"is additive in each column",
				"and homogeneous in each column")[0]
			regular := module.RegularModuleOn.Read(c)
			points := a.TermAs[Set[Nat]]("{i:num | i < n}")
			permutations := a.TermAs[Set[Permutation[Nat]]]("symmetric_group({i:num | i < n})")
			permutationMap := a.TermAs[Fun[Permutation[Nat], Fun[Nat, Nat]]]("permutation_map")
			fixedMaps := a.TermAs[Set[Fun[Nat, Nat]]]("«pinned»(n)")
			mapsOfPermutations := a.TermAs[Set[Fun[Nat, Nat]]](
				"image(permutation_map, symmetric_group({i:num | i < n}))")
			summand := a.TermAs[Fun[Fun[Nat, Nat], A]]("λf:num → num. «w»(f) * F(«E»(f))")

			entries := a.Have(
				"every entry of P lies in c",
				"∀r s:num. P(r, s) ∈ c.carrier",
				By(over, MatrixOverEntries.Read(c).At(n, P)))
			basisOver := a.Have(
				"for a map f pinned at n, E(f) is a matrix over c",
				"∀f:(num → num). f ∈ «pinned»(n) ⇒ matrix_over(c, n, «E»(f))",
				Derive(func(b *Argument) {
					f := b.FixAs[Fun[Nat, Nat]]("f")
					member := b.Assume()
					fixed := b.Have(
						"f fixes every point from n on",
						"∀j:num. n ≤ j ⇒ f(j) = j",
						By(member))
					b.Show(
						"so E(f), whose column s is the basis vector at f(s), is over c",
						By(fixed, IndexMapMatrixOver.Read(c).At(n, f)))
				}))
			weightIn := a.Have(
				"each product w(f) of entries of P lies in c",
				"∀f:num → num. «w»(f) ∈ c.carrier",
				By(
					entries,
					num_segment.FiniteBelowStrict.At(n),
					module.ModuleSumInMonoid.Read(comm_ring.MulMonoidOn.Read(c))))
			termIn := a.Have(
				"for a map f pinned at n, the term w(f) times F at E(f) lies in c",
				"∀f:(num → num). f ∈ «pinned»(n) ⇒ «w»(f) * F(«E»(f)) ∈ c.carrier",
				By(weightIn, values, basisOver, comm_ring.MulIn.Read(c)))

			mapsInto := a.Have(
				"the map of a permutation of the points below n is pinned at n",
				"∀p:permutation(num). p ∈ symmetric_group({i:num | i < n}) ⇒ permutation_map(p) ∈ «pinned»(n)",
				Derive(func(b *Argument) {
					p := b.FixAs[Permutation[Nat]]("p")
					permutes := b.Assume()
					keeps := b.Have(
						"p keeps the points below n below n",
						"∀j:num. j < n ⇒ permutation_map(p, j) < n",
						b.ForEach(func(j *Expr[Nat]) Action {
							return By(permutes, symmetric_group.SymmetricGroupMapsInto.At(points, p, j))
						}))
					fixes := b.Have(
						"and moves no point from n on",
						"∀j:num. n ≤ j ⇒ permutation_map(p, j) = j",
						By(permutes, symmetric_group.InSymmetricGroup, nat_order.NotLessThan))
					b.Show(
						"so its map is pinned at n",
						By(keeps, fixes))
				}))
			permutationMaps := a.Have(
				"so the maps of the permutations lie among the maps pinned at n",
				"image(permutation_map, symmetric_group({i:num | i < n})) ⊆ «pinned»(n)",
				By(mapsInto, set_image.ImageSubsetIff))

			vanishes := a.Have(
				"the term of a map pinned at n that is no permutation's map vanishes",
				Statement{
					Binders: "∀f:num → num.",
					Hypotheses: []string{
						"f ∈ «pinned»(n)",
						"f ∉ image(permutation_map, symmetric_group({i:num | i < n}))",
					},
					Conclusion: "«w»(f) * F(«E»(f)) = c.zero",
				},
				Derive(func(b *Argument) {
					f := b.FixAs[Fun[Nat, Nat]]("f")
					given := b.Conjuncts(
						b.Assume(),
						"f is pinned at n",
						"and is no permutation's map")
					member, noPermutation := given[0], given[1]
					keeps := b.Have(
						"f keeps the points below n among them",
						"∀x:num. x ∈ {i:num | i < n} ⇒ f(x) ∈ {i:num | i < n}",
						BySets(member))
					fixes := b.Have(
						"and fixes every point outside them",
						"∀x:num. x ∉ {i:num | i < n} ⇒ f(x) = x",
						BySets(member, nat_order.NotLessThan))
					repeats := b.Unless(
						b.Term("injective_on({i:num | i < n}, f)"),
						"were f one to one on the points below n, it would be a permutation's map",
						Given(func(e *Argument, oneToOne Fact) {
							p, permutation := e.ObtainAs[Permutation[Nat]](
								"one to one on the finitely many points below n, keeping them "+
									"and fixing the rest, f is the map of a permutation p of them",
								"∃p:permutation(num). p ∈ symmetric_group({i:num | i < n}) ∧ permutation_map(p) = f",
								By(
									keeps,
									oneToOne,
									fixes,
									symmetric_group.FiniteInjectionPermutation,
									num_segment.FiniteBelowStrict.At(n)))
							e.Show(
								"so f lies in the image of permutation_map, which it does not",
								By(noPermutation, permutation, set_image.FunInImage.At(permutationMap, permutations, p)))
						}))
					_, _, collision := b.Obtain2(
						"so two distinct points s₁ and s₂ below n have one image under f",
						"∃s₁ s₂:num. s₁ ∈ {i:num | i < n} ∧ s₂ ∈ {i:num | i < n} ∧ f(s₁) = f(s₂) ∧ s₁ ≠ s₂",
						By(b.Unfolded(repeats, functions.InjectiveOnDef)))
					sameColumns := b.Have(
						"so columns s₁ and s₂ of E(f) are one basis vector",
						"transpose(«E»(f), s₁) = transpose(«E»(f), s₂)",
						Funext(),
						Simp(Fwd(matrix.TransposeDef)),
						By(collision))
					zero := b.Have(
						"F vanishes at E(f), a matrix over c with two equal columns",
						"F(«E»(f)) = c.zero",
						By(alternates, basisOver.At(f), member, collision, sameColumns))
					b.Show(
						"so the term is w(f) times zero",
						zero.Rw(),
						By(weightIn.At(f), comm_ring.MulRightZeroOn.Read(c)))
				}))

			determinedByMap := a.Have(
				"a permutation is determined by its map",
				"injective_on(symmetric_group({i:num | i < n}), permutation_map)",
				Unfold(functions.InjectiveOnDef),
				By(symmetric_group.PermutationEq))
			finite := a.Have(
				"there are finitely many permutations of the points below n",
				"finite(symmetric_group({i:num | i < n}))",
				By(symmetric_group.SymmetricGroupFinite.At(points), num_segment.FiniteBelowStrict.At(n)))
			permutationTermsIn := a.Have(
				"the term at the map of a permutation lies in c",
				Statement{
					Binders:    "∀p:permutation(num).",
					Hypotheses: []string{"p ∈ symmetric_group({i:num | i < n})"},
					Conclusion: "«w»(permutation_map(p)) * F(«E»(permutation_map(p))) ∈ c.carrier",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[Permutation[Nat]]("p")
					b.Show(
						"the map of p is pinned at n",
						By(termIn.At(b.TermAs[Fun[Nat, Nat]]("permutation_map(p)")), mapsInto.At(p)))
				}))

			a.Show(
				"F(P) is the sum over the maps pinned at n, then over "+
					"the maps of the permutations, then over the permutations",
				Simp(Fwd(PermutationMatrixDef)),
				CalcEq(
					Leg(
						a.TermAs[A]("module_sum(c.add, c.zero, «pinned»(n), λf:num → num. «w»(f) * F(«E»(f)))"),
						"F expands over the columns of P in the standard basis",
						By(multilinear, over, MultilinearMapExpansion.Read(c).At(n, F, P))),
					Leg(
						a.TermAs[A](
							"module_sum(c.add, "+
								"    c.zero, "+
								"    image(permutation_map, symmetric_group({i:num | i < n})), "+
								"    λf:num → num. «w»(f) * F(«E»(f)))"),
						"the terms vanish off the maps of the permutations",
						By(
							PinnedMapsFinite.At(n, n),
							permutationMaps,
							termIn,
							vanishes,
							module.ModuleSumSupport.Read(regular).At(fixedMaps, mapsOfPermutations, summand))),
					FinalLeg(
						"permutation_map, one to one on the permutations, carries the sum to them",
						By(
							finite,
							determinedByMap,
							permutationTermsIn,
							module.ModuleSumImage.Read(regular).At(permutations, permutationMap, summand))),
				))
		}),
})}

// AlternatingFormUniversal — an alternating form is its value at the
// identity times the determinant. F(I)·det is alternating, a multiple of
// the alternating determinant, and agrees with F at the identity, where the
// determinant is one. Two alternating forms that agree at the identity agree
// at every permutation matrix: by induction on k, at every permutation of
// the points below k, one that fixes every point from k on. A permutation q
// of the points below k + 1 fixes k, or q composed with the transposition of
// k and the point q sends to k does; that transposition exchanges two
// columns of q's matrix, which flips the sign of both forms. The two
// forms expand over the permutations with the same coefficients, so they
// agree at P.
var AlternatingFormUniversal = alternatingFormUniversalThm{family.Add(registry.ProofEntry{
	Name: "AlternatingFormUniversal",
	Key:  "prop_ab1532c2bec1607a",
	Build: family.Sections(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀F:((num → num → A) → A). ∀P:(num → num → A).",
		Hypotheses: []string{
			"alternating_form(c, n, F)",
			"matrix_over(c, n, P)",
		},
		Conclusion: "F(P) = F(matrix_identity(c, n)) * determinant(c, n, P)",
		Abbrev: Abbrev{
			{Name: "summandsMultiple", Text: "λp:permutation(num). " +
				"    module_sum(c.mul, c.one, {j:num | j < n}, λj:num. P(permutation_map(p, j), j)) * " +
				"    (F(matrix_identity(c, n)) * determinant(c, n, permutation_matrix(c, n, p)))"},
			{Name: "summandsF", Text: "λp:permutation(num). " +
				"    module_sum(c.mul, c.one, {j:num | j < n}, λj:num. P(permutation_map(p, j), j)) * " +
				"    F(permutation_matrix(c, n, p))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// permutationMatrix — the permutation matrix of p, whose column s is the
		// basis vector at p(s), is a matrix over c.
		permutationMatrix := ctx.Lemma(Statement{
			Binders:    "∀c:comm_ring_on(A). ∀n:num. ∀p:permutation(num).",
			Hypotheses: []string{"p ∈ symmetric_group({i:num | i < n})"},
			Conclusion: "matrix_over(c, n, permutation_matrix(c, n, p))",
		},
			func(
				a *Argument,
				c comm_ring.CommRingFact[on.C],
				n *Expr[Nat],
				p *Expr[Permutation[Nat]],
				permutes Fact,
			) {
				fixes := a.Have(
					"p fixes every point from n on",
					"∀j:num. n ≤ j ⇒ permutation_map(p, j) = j",
					By(permutes, symmetric_group.InSymmetricGroup, nat_order.NotLessThan))
				a.Show(
					"so its matrix, whose column s is the basis vector at p(s), is over c",
					Simp(Fwd(PermutationMatrixDef)),
					By(fixes, IndexMapMatrixOver.Read(c).At(n, a.TermAs[Fun[Nat, Nat]]("permutation_map(p)"))))
			})

		// agreement — two alternating forms that agree at the identity agree
		// at every permutation matrix.
		agreement := ctx.Lemma(Statement{
			Binders: "∀c:comm_ring_on(A). ∀n:num. ∀F G:((num → num → A) → A).",
			Hypotheses: []string{
				"alternating_form(c, n, F)",
				"alternating_form(c, n, G)",
				"F(matrix_identity(c, n)) = G(matrix_identity(c, n))",
			},
			Conclusion: "∀p:permutation(num). " +
				"    p ∈ symmetric_group({i:num | i < n}) ⇒ " +
				"    F(permutation_matrix(c, n, p)) = G(permutation_matrix(c, n, p))",
		}, func(
			a *Argument,
			c comm_ring.CommRingFact[on.C],
			n *Expr[Nat],
			F, G *Arrow[Fun2[Nat, Nat, A], A],
			h Fact,
		) {
			parts := a.Conjuncts(
				h,
				"F is an alternating form",
				"so is G",
				"and the two agree at the identity")
			formF, formG, atIdentity := parts[0], parts[1], parts[2]
			ring := a.TermAs[RingOps[A]]("c")
			values := a.Have(
				"both forms take their values in c",
				"∀P:(num → num → A). matrix_over(c, n, P) ⇒ F(P) ∈ c.carrier ∧ G(P) ∈ c.carrier",
				By(
					formF,
					formG,
					AlternatingFormDef.At(ring, n, F),
					AlternatingFormDef.At(ring, n, G),
					ColumnMultilinearDef.At(ring, n, F),
					ColumnMultilinearDef.At(ring, n, G)))
			below := a.Have(
				"they agree at every permutation of the points below k, for k up to n, by induction on k",
				Statement{
					Binders:    "∀k:num.",
					Hypotheses: []string{"k ≤ n"},
					Conclusion: "∀q:permutation(num). " +
						"    q ∈ symmetric_group({i:num | i < k}) ⇒ " +
						"    F(permutation_matrix(c, n, q)) = G(permutation_matrix(c, n, q))",
				},
				Derive(func(d *Argument) {
					d.Induct("k")
					d.Base(
						"a permutation of no points is the identity, and its matrix the identity matrix",
						func(b *Argument) {
							b.Assume()
							b.FixAs[Permutation[Nat]]("q")
							permutes := b.Assume()
							identity := b.Simplified(
								permutes,
								Fwd(num_segment.BelowStrictClauses),
								Fwd(symmetric_group.SymmetricGroupEmpty),
								Fwd(set_basic.InSing))
							b.Show(
								"so both sides are the forms at the identity",
								Simp(Fwd(identity), Fwd(PermutationMatrixDef), Fwd(symmetric_group.MapIdentity)),
								By(atIdentity))
						})
					d.Step(
						"q permutes the points below k + 1: it fixes k, or a "+
							"transposition of two columns turns it into one that does",
						func(b *Argument, ih Fact) {
							k := b.TermAs[Nat]("k")
							bound := b.Assume()
							q := b.FixAs[Permutation[Nat]]("q")
							permutes := b.Assume()
							kBelow := b.Have(
								"k lies below n",
								"k < n",
								ByArith(bound))
							beyond := b.Have(
								"q fixes every point past k",
								"∀x:num. ¬(x < suc(k)) ⇒ permutation_map(q, x) = x",
								By(permutes, symmetric_group.InSymmetricGroup))
							within := b.Have(
								"the points below k + 1 lie below n",
								"{i:num | i < suc(k)} ⊆ {i:num | i < n}",
								Unfold(set_basic.SubsetDef),
								ByArith(bound))
							onN := b.Have(
								"so q permutes the points below n",
								"q ∈ symmetric_group({i:num | i < n})",
								BySets(
									permutes,
									within,
									symmetric_group.SymmetricGroupMono.At(
										b.TermAs[Set[Nat]]("{i:num | i < suc(k)}"), b.TermAs[Set[Nat]]("{i:num | i < n}"))))
							members := b.Have(
								"both forms at q's matrix lie in c",
								"F(permutation_matrix(c, n, q)) ∈ c.carrier ∧ G(permutation_matrix(c, n, q)) ∈ c.carrier",
								By(values, onN, Read(permutationMatrix, c).At(n, q)))
							movesK := b.Unless(
								b.Term("permutation_map(q, k) = k"),
								"where q fixes k as well, it permutes the points below k",
								Given(func(e *Argument, fixesK Fact) {
									fixesFromK := e.Have(
										"q fixes every point from k on",
										"∀x:num. ¬(x < k) ⇒ permutation_map(q, x) = x",
										By(Normalized, beyond, fixesK, nat_order.LessThanSucClause))
									upTo := e.Have(
										"k is at most n",
										"k ≤ n",
										ByArith(bound))
									e.Show(
										"the forms agree there by the hypothesis at k",
										By(fixesFromK, upTo, ih, symmetric_group.InSymmetricGroup))
								}))
							j, sent := b.ObtainAs[Nat](
								"q is onto, so some point j is sent to k",
								"∃j:num. permutation_map(q, j) = k",
								By(
									symmetric_group.MapBijective.At(q),
									set_basic.InImage.At(b.TermAs[Fun[Nat, Nat]]("permutation_map(q)"), b.TermAs[Set[Nat]]("𝕌"), k),
									set_basic.InUniv.At(k)))
							jBelow := b.Have(
								"j lies below k, q fixing every point past k",
								"j < k",
								By(movesK, beyond.At(j), sent, nat_order.LessThanSucClause.At(j, k)))
							composite := b.Have(
								"q after the transposition of k and j fixes every point from k on",
								"∀x:num. ¬(x < k) ⇒ permutation_map(q * transposition(k, j), x) = x",
								Derive(func(g *Argument) {
									x := g.FixAs[Nat]("x")
									outside := g.Assume()
									g.Show(
										"k goes to j and on to k, and every other point from k on stays put",
										Simp(Fwd(symmetric_group.MapCompose), Fwd(symmetric_group.MapTransposition)),
										By(outside, beyond.At(x), jBelow, sent, nat_order.LessThanSucClause.At(x, k)))
								}))
							columnBounds := b.Have(
								"k is at most n, j lies below n, and the two differ",
								"k ≤ n ∧ j < n ∧ k ≠ j",
								ByArith(jBelow, kBelow))
							atComposite := b.Have(
								"the forms agree at the composite by the hypothesis at k",
								"F(permutation_matrix(c, n, q * transposition(k, j))) = "+
									"G(permutation_matrix(c, n, q * transposition(k, j)))",
								By(composite, columnBounds, ih, symmetric_group.InSymmetricGroup))
							qMatrix := b.TermAs[Fun2[Nat, Nat, A]]("permutation_matrix(c, n, q)")
							exchanged := b.Have(
								"the composite's matrix is q's with columns k and j exchanged",
								"permutation_matrix(c, n, q * transposition(k, j)) = "+
									"(λr:num. λs:num. permutation_matrix(c, n, q, r, permutation_map(transposition(k, j), s)))",
								Funext(),
								Simp(Fwd(PermutationMatrixDef), Fwd(symmetric_group.MapCompose)),
								Basic())
							flips := b.Have(
								"exchanging columns k and j of q's matrix changes the sign of each form",
								"F(λr:num. λs:num. permutation_matrix(c, n, q, r, permutation_map(transposition(k, j), s))) = "+
									"-F(permutation_matrix(c, n, q)) ∧ "+
									"G(λr:num. λs:num. permutation_matrix(c, n, q, r, permutation_map(transposition(k, j), s))) = "+
									"-G(permutation_matrix(c, n, q))",
								By(
									kBelow,
									onN,
									columnBounds,
									formF,
									formG,
									AlternatingFormSwapColumns.Read(c).At(n, F, qMatrix, k, j),
									AlternatingFormSwapColumns.Read(c).At(n, G, qMatrix, k, j),
									Read(permutationMatrix, c).At(n, q)))
							negated := b.Simplified(atComposite, Fwd(exchanged), Fwd(flips))
							b.Show(
								"so -F and -G agree at q's matrix, and so do F and G",
								ByArith(c, negated, members))
						})
				}))
			a.Show(
				"at k = n they agree at every permutation of the points below n",
				By(below.At(n), nat_order.LessEqRefl.At(n)))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			c comm_ring.CommRingFact[on.C],
			n *Expr[Nat],
			F *Arrow[Fun2[Nat, Nat, A], A],
			P *Arrow2[Nat, Nat, A],
			h Fact,
		) {
			parts := a.Conjuncts(
				h,
				"F is an alternating form",
				"and P is a matrix over c")
			formF, over := parts[0], parts[1]
			ring := a.TermAs[RingOps[A]]("c")
			alternating := a.Have(
				"the determinant is an alternating form",
				"alternating_form(c, n, determinant(c, n))",
				By(DeterminantAlternating.Read(c).At(n)))
			identityValue := a.Have(
				"F at the identity matrix, a matrix over c, lies in c",
				"F(matrix_identity(c, n)) ∈ c.carrier",
				By(
					formF,
					MatrixIdentityOver.Read(c).At(n),
					AlternatingFormDef.At(ring, n, F),
					ColumnMultilinearDef.At(ring, n, F)))
			scaled := a.Have(
				"F(I) times the determinant is an alternating form",
				"alternating_form(c, n, λQ:(num → num → A). F(matrix_identity(c, n)) * determinant(c, n, Q))",
				By(
					alternating,
					AlternatingFormScalarMultiple.Read(c).At(
						n,
						a.TermAs[Fun[Fun2[Nat, Nat, A], A]]("determinant(c, n)"),
						a.MemberOf[on.C](a.TermAs[A]("F(matrix_identity(c, n))"), identityValue))))
			sameAtIdentity := a.Have(
				"it agrees with F at the identity, whose determinant is one",
				"F(matrix_identity(c, n)) = F(matrix_identity(c, n)) * determinant(c, n, matrix_identity(c, n))",
				Simp(Fwd(DeterminantIdentity.Read(c))),
				ByArith(c, identityValue))
			multiple := a.TermAs[Fun[Fun2[Nat, Nat, A], A]](
				"λQ:(num → num → A). F(matrix_identity(c, n)) * determinant(c, n, Q)")
			onPermutations := a.Have(
				"so the two agree at every permutation matrix",
				Statement{
					Binders:    "∀p:permutation(num).",
					Hypotheses: []string{"p ∈ symmetric_group({i:num | i < n})"},
					Conclusion: "F(permutation_matrix(c, n, p)) = " +
						"F(matrix_identity(c, n)) * determinant(c, n, permutation_matrix(c, n, p))",
				},
				By(sameAtIdentity, formF, scaled, Read(agreement, c).At(n, F, multiple)))
			// the summands of the two expansions over the permutations, spelled alike in the claim and in its cite
			expansions := a.Have(
				"so the two expansions over the permutations agree term by term",
				"module_sum(c.add, c.zero, symmetric_group({i:num | i < n}), «summandsF») = "+
					"module_sum(c.add, c.zero, symmetric_group({i:num | i < n}), «summandsMultiple»)",
				By(
					onPermutations,
					module.ModuleSumCongruence.At(
						a.TermAs[Op[A]]("c.add"),
						a.TermAs[A]("c.zero"),
						a.TermAs[Set[Permutation[Nat]]]("symmetric_group({i:num | i < n})"),
						a.TermAs[Fun[Permutation[Nat], A]]("«summandsF»"),
						a.TermAs[Fun[Permutation[Nat], A]]("«summandsMultiple»"))))
			a.Show(
				"F(P) and F(I)·det(P) are those two expansions",
				By(
					expansions,
					formF,
					scaled,
					over,
					AlternatingFormPermutationExpansion.Read(c).At(n, F, P),
					AlternatingFormPermutationExpansion.Read(c).At(n, multiple, P)))
		})
	}),
})}
