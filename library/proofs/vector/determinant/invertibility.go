package determinant

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/registry"
)

// DeterminantDependentColumns — over an integral domain, a matrix whose
// columns combine to zero with weights not all zero has determinant zero.
// Let Q be the identity with column j replaced by the weights. Column j of
// P·Q is the vanishing combination, so expanding det(P·Q) along it gives
// zero. Expanding det Q along the same column leaves the term of e_j alone,
// every other basis vector repeating a column of the identity, so
// det Q = w(j). Multiplicativity gives det P · w(j) = 0, and as w(j) ≠ 0
// and a domain has no zero divisors, det P = 0.
var DeterminantDependentColumns = determinantDependentColumnsThm{family.Add(registry.ProofEntry{
	Name: "DeterminantDependentColumns",
	Key:  "prop_2d1318364ba3f534",
	Build: family.Theorem(Statement{
		Binders: "∀R:integral_domain_on(A). ∀n:num. ∀P:(num → num → A). ∀w:(num → A). ∀j:num.",
		Hypotheses: []string{
			"matrix_over(R, n, P)",
			"∀k:num. k < n ⇒ w(k) ∈ R.carrier",
			"j < n",
			"w(j) ≠ R.zero",
			"∀r:num. r < n ⇒ module_sum(R.add, R.zero, {k:num | k < n}, λk:num. P(r, k) * w(k)) = R.zero",
		},
		Conclusion: "determinant(R, n, P) = R.zero",
		Abbrev: Abbrev{
			{Name: "Q", Text: "matrix_replace_column(R, n, matrix_identity(R, n), j, w)"},
			{Name: "PQ", Text: "matrix_product(R, n, P, «Q»)"},
			{Name: "e", Text: "λm:num. λr:num. matrix_identity(R, n, r, m)"},
			{Name: "moved", Text: "λm:num. λr:num. λs:num. matrix_identity(R, n, r, COND(s = j, m, s))"},
		},
	},
		func(
			a *Argument,
			R integral_domain.IntegralDomainFact[on.R],
			n *Expr[Nat],
			P *Arrow2[Nat, Nat, A],
			w *Arrow[Nat, A],
			j *Expr[Nat],
			over, weights, jBelow, nonzero, kernel Fact,
		) {
			c := integral_domain.Ring.Read(R)
			regular := module.RegularModuleOn.Read(c)
			ring := a.TermAs[RingOps[A]]("R")
			det := a.TermAs[Fun[Fun2[Nat, Nat, A], A]]("determinant(R, n)")
			Q := a.TermAs[Fun2[Nat, Nat, A]]("«Q»")
			PQ := a.TermAs[Fun2[Nat, Nat, A]]("«PQ»")
			below := a.TermAs[Set[Nat]]("{m:num | m < n}")
			multilinear := DeterminantColumnMultilinear.Read(c).At(n)
			replacedOver := a.Have(
				"Q, the identity with its column j replaced by the weights, is a matrix over R",
				"matrix_over(R, n, «Q»)",
				Simp(Fwd(MatrixOverEntries.Read(c)), Fwd(ColumnReplaceDef), Fwd(MatrixIdentityDef)),
				By(comm_ring.ZeroIn.Read(c), comm_ring.OneIn.Read(c), weights, nat_order.NotLessThan))
			detQ := a.Have(
				"along column j only the basis vector e_j survives, so det Q = w(j)",
				"determinant(R, n, «Q») = w(j)",
				Derive(func(b *Argument) {
					expandQ := b.Have(
						"expanded along column j, det Q sums Q(m, j) times det Q with column j replaced by e_m",
						"determinant(R, n, «Q») = "+
							"module_sum(R.add, "+
							"    R.zero, "+
							"    {m:num | m < n}, "+
							"    λm:num. «Q»(m, j) * determinant(R, n, matrix_replace_column(R, n, «Q», j, «e»(m))))",
						By(jBelow, replacedOver, multilinear, MultilinearColumnExpansion.Read(c).At(n, det, Q, j)))
					moved := b.Have(
						"Q with column j replaced by e_m is the identity with column m copied into column j",
						"∀m:num. m < n ⇒ matrix_replace_column(R, n, «Q», j, «e»(m)) = «moved»(m)",
						Derive(func(d *Argument) {
							d.FixAs[Nat]("m")
							mBelow := d.Assume()
							d.Show(
								"the two agree entry by entry",
								Simp(Fwd(ColumnReplaceDef), Fwd(MatrixIdentityDef)),
								By(jBelow, mBelow))
						}))
					movedOver := b.Have(
						"each such matrix is a matrix over R, its columns being basis vectors",
						"∀m:num. matrix_over(R, n, «moved»(m))",
						Derive(func(d *Argument) {
							d.FixAs[Nat]("m")
							fixed := d.Have(
								"sending j to m fixes every point from n on",
								"∀s:num. n ≤ s ⇒ COND(s = j, m, s) = s",
								By(jBelow, nat_order.NotLessThan))
							d.Show(
								"an index-map matrix is a matrix over R",
								By(fixed, IndexMapMatrixOver.Read(c).At(n, d.TermAs[Fun[Nat, Nat]]("λs:num. COND(s = j, m, s)"))))
						}))
					repeated := b.Have(
						"for m ≠ j its columns j and m are both e_m, so its determinant is zero",
						"∀m:num. m < n ∧ m ≠ j ⇒ determinant(R, n, «moved»(m)) = R.zero",
						Derive(func(d *Argument) {
							m := d.FixAs[Nat]("m")
							given := d.Assume()
							d.Show(
								"columns j and m agree, read as rows j and m of the transpose, so the determinant is zero",
								By(
									movedOver.At(m),
									jBelow,
									given,
									DeterminantEqualColumns.Read(c).At(n, d.TermAs[Fun2[Nat, Nat, A]]("«moved»(m)"), j, m),
									matrix.TransposeDef))
						}))
					unmoved := b.Have(
						"for m = j nothing moves: it is the identity",
						"«moved»(j) = matrix_identity(R, n)",
						Derive(func(d *Argument) {
							d.Do(Funext())
							d.FixAs[Nat]("r")
							s := d.FixAs[Nat]("s")
							d.Cases(Equal(s, j))
							d.When(
								"column j stays column j",
								func(e *Argument, atJ Fact) {
									e.Show(
										"its entry is the identity's",
										By(Normalized, atJ))
								})
							d.Otherwise(
								"every other column stays put",
								func(e *Argument, offJ Fact) {
									e.Show(
										"its entry is the identity's",
										By(offJ))
								})
						}))
					identityOne := b.Have(
						"so its determinant is one",
						"determinant(R, n, «moved»(j)) = R.one",
						By(unmoved, DeterminantIdentity.Read(c).At(n)))
					terms := b.Have(
						"each term Q(m, j) times the determinant of the moved identity lies in R",
						"∀m:num. m < n ⇒ «Q»(m, j) * determinant(R, n, «moved»(m)) ∈ R.carrier",
						Derive(func(d *Argument) {
							m := d.FixAs[Nat]("m")
							mBelow := d.Assume()
							entry, value := d.TermAs[A]("«Q»(m, j)"), d.TermAs[A]("determinant(R, n, «moved»(m))")
							d.Show(
								"a product of members of R",
								By(
									mBelow,
									replacedOver,
									movedOver.At(m),
									MatrixOverEntries.Read(c).At(n, Q),
									DeterminantInCarrier.Read(c).At(n, d.TermAs[Fun2[Nat, Nat, A]]("«moved»(m)")),
									comm_ring.MulIn.Read(c).AsFact().At(entry, value)))
						}))
					offTerms := b.Have(
						"and it vanishes for m ≠ j",
						"∀m:num. m < n ∧ m ≠ j ⇒ «Q»(m, j) * determinant(R, n, «moved»(m)) = R.zero",
						Derive(func(d *Argument) {
							m := d.FixAs[Nat]("m")
							given := d.Assume()
							entry := d.TermAs[A]("«Q»(m, j)")
							d.Show(
								"a multiple of zero is zero",
								By(
									given,
									replacedOver,
									repeated.At(m),
									MatrixOverEntries.Read(c).At(n, Q),
									comm_ring.MulRightZeroOn.Read(c).AsFact().At(entry)))
						}))
					pointwise := b.Have(
						"term by term, the replaced matrices are the moved identities",
						Statement{
							Binders:    "∀m:num.",
							Hypotheses: []string{"m < n"},
							Conclusion: "«Q»(m, j) * determinant(R, n, matrix_replace_column(R, n, «Q», j, «e»(m))) = " +
								"«Q»(m, j) * determinant(R, n, «moved»(m))",
						},
						Derive(func(d *Argument) {
							m := d.FixAs[Nat]("m")
							mBelow := d.Assume()
							d.Show(
								"rewrite the matrix",
								By(moved.At(m), mBelow))
						}))
					b.Show(
						"expand det Q along column j and keep the one term that survives",
						CalcEq(
							Leg(
								b.TermAs[A](
									"module_sum(R.add, "+
										"    R.zero, "+
										"    {m:num | m < n}, "+
										"    λm:num. «Q»(m, j) * determinant(R, n, matrix_replace_column(R, n, «Q», j, «e»(m))))"),
								"expand along column j",
								By(expandQ)),
							Leg(
								b.TermAs[A](
									"module_sum(R.add, R.zero, {m:num | m < n}, λm:num. «Q»(m, j) * determinant(R, n, «moved»(m)))"),
								"the replaced matrices are the moved identities",
								By(
									pointwise,
									module.ModuleSumCongruence.At(
										b.TermAs[Op[A]]("R.add"),
										b.TermAs[A]("R.zero"),
										below,
										b.TermAs[Fun[Nat, A]](
											"λm:num. «Q»(m, j) * determinant(R, n, matrix_replace_column(R, n, «Q», j, «e»(m)))"),
										b.TermAs[Fun[Nat, A]]("λm:num. «Q»(m, j) * determinant(R, n, «moved»(m))")))),
							Leg(
								b.TermAs[A]("«Q»(j, j) * determinant(R, n, «moved»(j))"),
								"only the term m = j survives",
								By(
									terms,
									offTerms,
									jBelow,
									num_segment.FiniteBelowStrict.At(n),
									module.ModuleSumSingle.Read(regular).At(
										below, j, b.TermAs[Fun[Nat, A]]("λm:num. «Q»(m, j) * determinant(R, n, «moved»(m))")))),
							FinalLeg(
								"Q(j, j) = w(j) and the determinant is one",
								ByArith(
									c,
									identityOne,
									jBelow,
									weights.At(j),
									ColumnReplaceDef.At(ring, n, b.TermAs[Fun2[Nat, Nat, A]]("matrix_identity(R, n)"), j, w, j, j))),
						))
				}))
			productZero := a.Have(
				"column j of P·Q is the vanishing combination, so det(P·Q) = 0",
				"determinant(R, n, «PQ») = R.zero",
				Derive(func(b *Argument) {
					productOver := b.Have(
						"P·Q is a matrix over R",
						"matrix_over(R, n, «PQ»)",
						By(over, replacedOver, MatrixProductOver.Read(c).At(n, P, Q)))
					expandPQ := b.Have(
						"expanded along column j, det(P·Q) sums its column-j entries times determinants",
						"determinant(R, n, «PQ») = "+
							"module_sum(R.add, "+
							"    R.zero, "+
							"    {m:num | m < n}, "+
							"    λm:num. «PQ»(m, j) * determinant(R, n, matrix_replace_column(R, n, «PQ», j, «e»(m))))",
						By(jBelow, productOver, multilinear, MultilinearColumnExpansion.Read(c).At(n, det, PQ, j)))
					columnZero := b.Have(
						"column j of P·Q is the combination of P's columns with the weights, zero",
						"∀m:num. m < n ⇒ «PQ»(m, j) = R.zero",
						Derive(func(d *Argument) {
							m := d.FixAs[Nat]("m")
							mBelow := d.Assume()
							d.Show(
								"Q's column j is the weights",
								Simp(Fwd(matrix.MatrixProductDef)),
								By(
									kernel.At(m),
									mBelow,
									jBelow,
									module.ModuleSumCongruence.At(
										d.TermAs[Op[A]]("R.add"),
										d.TermAs[A]("R.zero"),
										d.TermAs[Set[Nat]]("{k:num | k < n}"),
										d.TermAs[Fun[Nat, A]]("λk:num. P(m, k) * «Q»(k, j)"),
										d.TermAs[Fun[Nat, A]]("λk:num. P(m, k) * w(k)")),
									ColumnReplaceDef))
						}))
					productTerms := b.Have(
						"so every term of the expansion of det(P·Q) is zero",
						Statement{
							Binders:    "∀m:num.",
							Hypotheses: []string{"m < n"},
							Conclusion: "«PQ»(m, j) * determinant(R, n, matrix_replace_column(R, n, «PQ», j, «e»(m))) = R.zero",
						},
						Derive(func(d *Argument) {
							m := d.FixAs[Nat]("m")
							mBelow := d.Assume()
							indicator := d.TermAs[Fun[Nat, A]]("delta_at(m)")
							replaced := d.TermAs[Fun2[Nat, Nat, A]]("matrix_replace_column(R, n, «PQ», j, «e»(m))")
							replacedOverL := d.Have(
								"replacing column j of P·Q by e_m, the indicator of m, leaves a matrix over R",
								"matrix_over(R, n, matrix_replace_column(R, n, «PQ», j, «e»(m)))",
								By(
									mBelow,
									MatrixIdentityColumn.At(ring, n, m),
									productOver,
									free_module.DeltaAtIn.Read(c).At(below, m),
									ReplaceColumnMatrixOver.At(ring, n, PQ, j, indicator)))
							d.Show(
								"zero times a determinant over R is zero",
								By(
									columnZero.At(m),
									mBelow,
									replacedOverL,
									DeterminantInCarrier.Read(c).At(n, replaced),
									comm_ring.MulLeftZeroOn.Read(c).AsFact().At(
										d.TermAs[A]("determinant(R, n, matrix_replace_column(R, n, «PQ», j, «e»(m)))"))))
						}))
					b.Show(
						"expand det(P·Q) along column j: every term is zero",
						By(
							expandPQ,
							productTerms,
							num_segment.FiniteBelowStrict.At(n),
							module.ModuleSumZero.Read(regular).At(
								below,
								b.TermAs[Fun[Nat, A]](
									"λm:num. «PQ»(m, j) * determinant(R, n, matrix_replace_column(R, n, «PQ», j, «e»(m)))"))))
				}))
			detPIn := a.Have(
				"det P lies in R",
				"determinant(R, n, P) ∈ R.carrier",
				By(over, DeterminantInCarrier.Read(c).At(n, P)))
			weightIn := a.Have(
				"w(j) lies in R",
				"w(j) ∈ R.carrier",
				By(jBelow, weights.At(j)))
			a.Show(
				"det P · w(j) = det(P·Q) = 0 and w(j) ≠ 0, so det P = 0",
				By(
					nonzero,
					productZero,
					detQ,
					over,
					replacedOver,
					DeterminantMultiplicative.Read(c).At(n, P, Q),
					integral_domain.NoZeroDivisors.Read(R).At(
						a.MemberOf[on.R](a.TermAs[A]("determinant(R, n, P)"), detPIn),
						a.MemberOf[on.R](w.Apply(j), weightIn))))
		}),
})}

// DeterminantZeroIffDependent — over a field, the determinant is nonzero
// exactly when the columns form a basis and exactly when the matrix has a
// two-sided inverse. A vector the column map sends to zero weights the
// columns to a vanishing combination, so a nonzero determinant makes the
// map injective. The map sends the standard basis to the columns, so they
// are independent; and they are n distinct vectors, since two equal columns
// would make the determinant zero, so they fill the dimension and form a
// basis. A column basis makes the map onto, and a linear section of it is
// represented by a matrix Q with P·Q = I. Multiplicativity gives
// det(P) ≠ 0 from P·Q = I, so the column map of P is injective and Q is
// also a left inverse.
var DeterminantZeroIffDependent = determinantZeroIffDependentThm{family.Add(registry.ProofEntry{
	Name: "DeterminantZeroIffDependent",
	Key:  "prop_1c0ed6f7e3f45f8a",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{
			"matrix_over(field_ring(L), n, P)",
		},
		Conclusion: "(«det P ≠ 0» ⇔ " +
			"    module_basis(field_ring(L), " +
			"        free_module_record(field_ring(L), {i:num | i < n}), " +
			"        {transpose(P, j) | j:num | j < n})) ∧ " +
			"(«det P ≠ 0» ⇔ " +
			"    ∃Q:(num → num → A). " +
			"        matrix_over(field_ring(L), n, Q) ∧ " +
			"        matrix_product(field_ring(L), n, P, Q) = matrix_identity(field_ring(L), n) ∧ " +
			"        matrix_product(field_ring(L), n, Q, P) = matrix_identity(field_ring(L), n))",
		Abbrev: Abbrev{
			{Name: "det P ≠ 0", Text: "determinant(field_ring(L), n, P) ≠ L.zero"},
		},
	}, determinantZeroIffDependent),
})}

// matrixColumnMapOnBasis — the column map of P carries the standard basis
// onto the set of columns of P.
func matrixColumnMapOnBasis(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders:    "∀c:comm_ring_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{"matrix_over(c, n, P)"},
		Conclusion: "image(«column map», image(delta_at, {i:num | i < n})) = " +
			"{transpose(P, j) | j:num | j < n}",
	}, func(
		a *Argument,
		c comm_ring.CommRingFact[on.C],
		n *Expr[Nat],
		P *Mat[A, DimN, DimN],
		over Fact,
	) {
		indices := a.TermAs[Set[Nat]]("{i:num | i < n}")
		agreement := a.Have(
			"the column map sends each standard vector to its column",
			"∀j:num. j ∈ {i:num | i < n} ⇒ «column map»(delta_at(j)) = transpose(P, j)",
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				inI := b.Assume()
				b.Show(
					"read the column map on the standard vector",
					BySets(inI, over, MatrixColumnMapOnDelta.Read(c).At(n, P, j)))
			}))
		a.Show(
			"take the images of the two agreeing index maps",
			CalcEq(
				Leg(
					a.TermAs[Set[Fun[Nat, A]]]("image(transpose(P), {i:num | i < n})"),
					"the standard vector at j goes to column j",
					Simp(Rev(set_image.ImageCompose), Fwd(functions.ComposeApply)),
					By(
						agreement,
						set_image.ImageCongruence.At(
							a.TermAs[Fun[Nat, Fun[Nat, A]]]("λj:num. «column map»(delta_at(j))"),
							a.TermAs[Fun[Nat, Fun[Nat, A]]]("transpose(P)"),
							indices))),
				FinalLeg(
					"the image of the column index map is the column set",
					BySets()),
			))
	})
}

// determinantColumnMapInjective — over an integral domain, a nonzero
// determinant makes the column map one to one.
func determinantColumnMapInjective(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀R:integral_domain_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{
			"matrix_over(R, n, P)",
			"determinant(R, n, P) ≠ R.zero",
		},
		Conclusion: "injective_on(free_module_record(R, {i:num | i < n}).carrier, " +
			"    λw:(num → A). λr:num. module_sum(R.add, R.zero, {k:num | k < n}, λk:num. P(r, k) * w(k)))",
	}, func(
		a *Argument,
		R integral_domain.IntegralDomainFact[on.R],
		n *Expr[Nat],
		P *Mat[A, DimN, DimN],
		given Fact,
	) {
		c := integral_domain.Ring.Read(R)
		ring := a.TermAs[RingOps[A]]("R")
		linear := a.Simplified(GroupPremises(given, MatrixColumnMapLinear.Read(c).At(n, P)))
		_, iDef := a.LetAs[Set[Nat]]("I", "{i:num | i < n}")
		_, vDef := a.LetAs[module_record.ModuleOps[A, Fun[Nat, A]]]("V", "free_module_record(R, I)")
		_, tDef := a.LetAs[Fun[Fun[Nat, A], Fun[Nat, A]]](
			"T", "λw:(num → A). λr:num. module_sum(R.add, R.zero, I, λk:num. P(r, k) * w(k))")
		zeroKernel := a.Have(
			"a vanishing column combination has only zero coefficients",
			"∀u:(num → A). u ∈ V.carrier ∧ T(u) = V.zero ⇒ u = V.zero",
			Derive(func(b *Argument) {
				u := b.VecFixAs[A, DimN]("u")
				kernel := b.Assume()
				coordinates := b.Have(
					"the coefficient vector has scalar entries and vanishes from n on",
					"∀i:num. u(i) ∈ R.carrier ∧ (n ≤ i ⇒ u(i) = R.zero)",
					vDef.Rw(),
					iDef.Rw(),
					By(kernel, CoordinateVectorMember.At(ring, n, u)))
				relation := b.Have(
					"the kernel equation is a zero relation in every row below n",
					"∀r:num. r < n ⇒ module_sum(R.add, R.zero, {k:num | k < n}, λk:num. P(r, k) * u(k)) = R.zero",
					tDef.Rw(),
					vDef.Rw(),
					iDef.Rw(),
					Derive(func(d *Argument) {
						d.Do(kernel.Simp(
							Fwd(free_module.FreeModuleRecordDef),
							Fwd(module_record.ModZeroDef),
							Fwd(function_module.FunZeroDef)))
						d.Show(
							"read the zero function coordinatewise",
							By(kernel))
					}))
				coefficients := b.Have(
					"every coefficient below n is zero",
					"∀j:num. j < n ⇒ u(j) = R.zero",
					Derive(func(d *Argument) {
						j := d.FixAs[Nat]("j")
						below := d.Assume()
						d.Show(
							"a nonzero coefficient would make the determinant vanish",
							By(relation, coordinates, below, given, DeterminantDependentColumns.Read(R).At(n, P, u, j)))
					}))
				b.Show(
					"the vector vanishes below n and from n on",
					vDef.Rw(),
					Simp(
						Fwd(free_module.FreeModuleRecordDef),
						Fwd(module_record.ModZeroDef),
						Fwd(function_module.FunZeroDef)),
					Funext(),
					Derive(func(d *Argument) {
						x := d.FixAs[Nat]("x")
						d.Show(
							"each coordinate is zero",
							By(coefficients.At(x), coordinates.At(x), nat_order.NotLessThan.At(x, n)))
					}))
			}))
		kernel := a.Have(
			"the kernel is the singleton zero vector",
			"group_kernel(V.zero, V.carrier, T) = {V.zero}",
			Simp(Fwd(group_homomorphism.GroupKernelDef)),
			BySets(
				module_homomorphism.HomZero.Read(linear),
				group.OneIn.Read(module.AddGroupOn.Read(module_homomorphism.HomSource.Read(linear))),
				zeroKernel))
		a.Show(
			"a linear map with trivial kernel is injective",
			By(module_homomorphism.KernelTrivialIffInjective.Read(linear), kernel))
	})
}

// determinantColumnsBasis — over a field, a nonzero determinant makes the
// columns a basis of the coordinate module.
func determinantColumnsBasis(
	ctx *Script,
	columnMapOnBasis, columnMapInjective *GoalStackNode,
) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀L:field_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{
			"matrix_over(field_ring(L), n, P)",
			"determinant(field_ring(L), n, P) ≠ L.zero",
		},
		Conclusion: "module_basis(field_ring(L), " +
			"    free_module_record(field_ring(L), {i:num | i < n}), " +
			"    {transpose(P, j) | j:num | j < n})",
	}, func(a *Argument, L field.FieldFact[on.L], n *Expr[Nat], P *Mat[A, DimN, DimN], given Fact) {
		c := field.RingOn.Read(L)
		R := a.TermAs[RingOps[A]]("field_ring(L)")
		columnsInjective := a.Have(
			"distinct indices below n give distinct columns",
			"injective_on({i:num | i < n}, transpose(P))",
			Simp(Fwd(functions.InjectiveOnDef)),
			Derive(func(b *Argument) {
				x, y := b.FixAs[Nat]("x"), b.FixAs[Nat]("y")
				equal := b.Assume()
				b.Show(
					"equal distinct columns would force determinant zero",
					By(L, equal, given, DeterminantEqualColumns.Read(c).At(n, P, x, y)))
			}))
		linear := a.Simplified(GroupPremises(given, MatrixColumnMapLinear.Read(c).At(n, P)))
		image := a.Simplified(GroupPremises(given, Read(columnMapOnBasis, c).At(n, P)))
		I, iDef := a.LetAs[Set[Nat]]("I", "{i:num | i < n}")
		standard := a.Simplified(free_module.DeltaAtBasis.Read(c).At(I))
		V, vDef := a.LetAs[module_record.ModuleOps[A, Fun[Nat, A]]](
			"V", "free_module_record(field_ring(L), I)")
		T, tDef := a.LetAs[Fun[Fun[Nat, A], Fun[Nat, A]]](
			"T", "λw:(num → A). λr:num. module_sum(L.add, L.zero, I, λk:num. P(r, k) * w(k))")
		E, _ := a.LetAs[Set[Fun[Nat, A]]]("E", "image(delta_at(L.zero, L.one), I)")
		C, cDef := a.LetAs[Set[Fun[Nat, A]]]("C", "{transpose(P, j) | j:num | j < n}")
		injective := a.Have(
			"its kernel is trivial because the determinant is nonzero",
			"injective_on(V.carrier, T)",
			vDef.Rw(),
			By(
				tDef,
				iDef,
				given,
				Read(columnMapInjective, integral_domain.FieldIntegralDomain.Read(L)).At(n, P)))
		independent := a.Have(
			"the injective linear image of the standard basis is independent",
			"module_independent(field_ring(L), V, C)",
			By(
				Normalized,
				image,
				linear,
				injective,
				standard,
				linear_independence.ModuleBasisDef.At(R, V, E),
				linear_independence.IndependentImage.At(R, V, V, T, E)))
		dimension := a.Have(
			"the coordinate module has dimension n",
			"finite_dimensional(field_ring(L), V) ∧ module_dim(field_ring(L), V) = n",
			By(
				iDef,
				vDef,
				field.FieldRingSubfield.Read(L),
				num_segment.HasSizeBelowStrict.At(n),
				cardinality.HasSizeDef.At(I, n),
				module_dimension.FreeModuleFiniteDim.At(R, a.TermAs[Fun[A, A]]("L.inv"), I)))
		columnsImage := a.Have(
			"the column set is the image of the column index map",
			"image(transpose(P), I) = C",
			BySets(cDef, iDef))
		size := a.Have(
			"the distinct columns number n",
			"has_size(C, n)",
			By(
				columnsImage,
				iDef,
				columnsInjective,
				num_segment.HasSizeBelowStrict.At(n),
				cardinality.HasSizeImageInj.At(a.TermAs[Fun[Nat, Fun[Nat, A]]]("transpose(P)"), I, n)))
		onV := a.Have(
			"V is a module over the field's ring",
			"module_on(field_ring(L), V)",
			By(Normalized, vDef, c, free_module.FreeModuleOn.At(R, I)))
		a.Show(
			"an independent set of the full dimension is a basis",
			By(
				Normalized,
				size,
				dimension,
				independent,
				field.FieldRingSubfield.Read(L),
				module_dimension.IndependentFullBasis.Read(onV).At(a.TermAs[Fun[A, A]]("L.inv"), C)))
	})
}

// determinantRightInverseNonzero — over an integral domain, a matrix with a
// right inverse has nonzero determinant.
func determinantRightInverseNonzero(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀R:integral_domain_on(A). ∀n:num. ∀P Q:(num → num → A).",
		Hypotheses: []string{
			"matrix_over(R, n, P)",
			"matrix_over(R, n, Q)",
			"matrix_product(R, n, P, Q) = matrix_identity(R, n)",
		},
		Conclusion: "determinant(R, n, P) ≠ R.zero",
	}, func(
		a *Argument,
		R integral_domain.IntegralDomainFact[on.R],
		n *Expr[Nat],
		P, Q *Mat[A, DimN, DimN],
		given Fact,
	) {
		c := integral_domain.Ring.Read(R)
		a.Show(
			"det P times det Q is one, so det P cannot be zero",
			By(
				Normalized,
				given,
				DeterminantMultiplicative.Read(c).At(n, P, Q),
				DeterminantIdentity.Read(c).At(n),
				DeterminantInCarrier.Read(c).At(n, Q),
				comm_ring.MulLeftZeroOn.Read(c).AsFact().At(a.TermAs[A]("determinant(R, n, Q)")),
				integral_domain.OneNotZero.Read(R)))
	})
}

// matrixIdentityByColumns — a matrix over c whose columns below n are the
// standard vectors is the identity.
func matrixIdentityByColumns(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀Q:(num → num → A).",
		Hypotheses: []string{
			"matrix_over(c, n, Q)",
			"∀j:num. j < n ⇒ transpose(Q, j) = delta_at(j)",
		},
		Conclusion: "Q = matrix_identity(c, n)",
	}, func(
		a *Argument,
		c comm_ring.CommRingFact[on.C],
		n *Expr[Nat],
		Q *Mat[A, DimN, DimN],
		given Fact,
	) {
		parts := a.Conjuncts(
			given,
			"Q is a matrix over c",
			"its columns below n are standard basis vectors")
		over, columns := parts[0], parts[1]
		R := a.TermAs[RingOps[A]]("c")
		a.Do(Funext())
		i, j := a.FixAs[Nat]("i"), a.FixAs[Nat]("j")
		a.Cases(a.TermAs[Bool]("j < n"))
		a.When(
			"a column below n is the matching identity column",
			func(b *Argument, below Fact) {
				b.Show(
					"its entries are the delta values",
					By(
						Normalized,
						columns.At(j),
						below,
						matrix.TransposeDef.At(Q, j, i),
						MatrixIdentityColumn.At(R, n, j)))
			})
		a.Otherwise(
			"a column from n on is zero in both matrices",
			func(b *Argument, outside Fact) {
				b.Show(
					"both entries vanish",
					By(
						outside,
						over,
						MatrixOverEntries.Read(c).At(n, Q),
						nat_order.NotLessThan.At(j, n),
						MatrixIdentityDef.At(R, n, i, j)))
			})
	})
}

// matrixColumnMapSection — over a field, a column basis gives the column map
// a linear right inverse.
func matrixColumnMapSection(ctx *Script, columnMapOnBasis *GoalStackNode) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀L:field_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{
			"matrix_over(field_ring(L), n, P)",
			"module_basis(field_ring(L), «Lⁿ», {transpose(P, j) | j:num | j < n})",
		},
		Conclusion: "∃g:((num → A) → num → A). " +
			"    module_homomorphism(field_ring(L), «Lⁿ», «Lⁿ», g) ∧ " +
			"    (∀w:(num → A). " +
			"        w ∈ «Lⁿ».carrier ⇒ " +
			"        (λu:(num → A). λr:num. " +
			"            module_sum(L.add, L.zero, {k:num | k < n}, λk:num. P(r, k) * u(k)))(g(w)) = " +
			"        w)",
		Abbrev: Abbrev{
			{Name: "Lⁿ", Text: "free_module_record(field_ring(L), {i:num | i < n})"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], n *Expr[Nat], P *Mat[A, DimN, DimN], given Fact) {
		c := field.RingOn.Read(L)
		R := a.TermAs[RingOps[A]]("field_ring(L)")
		linear := a.Simplified(GroupPremises(given, MatrixColumnMapLinear.Read(c).At(n, P)))
		basisImage := a.Simplified(GroupPremises(given, Read(columnMapOnBasis, c).At(n, P)))
		I, _ := a.LetAs[Set[Nat]]("I", "{i:num | i < n}")
		standard := a.Simplified(free_module.DeltaAtBasis.Read(c).At(I))
		V, _ := a.LetAs[module_record.ModuleOps[A, Fun[Nat, A]]](
			"V", "free_module_record(field_ring(L), I)")
		T, _ := a.LetAs[Fun[Fun[Nat, A], Fun[Nat, A]]](
			"T", "λw:(num → A). λr:num. module_sum(L.add, L.zero, I, λk:num. P(r, k) * w(k))")
		E, _ := a.LetAs[Set[Fun[Nat, A]]]("E", "image(delta_at(L.zero, L.one), I)")
		C, _ := a.LetAs[Set[Fun[Nat, A]]]("C", "{transpose(P, j) | j:num | j < n}")
		onto := a.Have(
			"the column map is onto because its basis image spans",
			"image(T, V.carrier) = V.carrier",
			By(
				Normalized,
				basisImage,
				linear,
				standard,
				given,
				linear_independence.ModuleBasisDef.At(R, V, E),
				linear_independence.ModuleBasisDef.At(R, V, C),
				linear_independence.BasisInCarrier.At(R, V, E),
				linear_independence.HomSpan.At(R, V, V, T, E)))
		a.Show(
			"an onto linear map over a field has a linear right inverse",
			By(linear, onto, module_dimension.LinearMapSection.Read(L).At(V, V, T)))
	})
}

// matrixOfSection — the matrix of a linear right inverse of the column map
// is a right inverse of P.
func matrixOfSection(ctx *Script, identityByColumns *GoalStackNode) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀P:(num → num → A). ∀g:((num → A) → num → A).",
		Hypotheses: []string{
			"matrix_over(c, n, P)",
			"module_homomorphism(c, «cⁿ», «cⁿ», g)",
			"∀w:(num → A). w ∈ «cⁿ».carrier ⇒ «column map»(g(w)) = w",
		},
		Conclusion: "∃Q:(num → num → A). " +
			"    matrix_over(c, n, Q) ∧ matrix_product(c, n, P, Q) = matrix_identity(c, n)",
		Abbrev: Abbrev{
			{Name: "cⁿ", Text: "free_module_record(c, {i:num | i < n})"},
		},
	}, func(
		a *Argument,
		c comm_ring.CommRingFact[on.C],
		n *Expr[Nat],
		P *Mat[A, DimN, DimN],
		g *Arrow[Fun[Nat, A], Fun[Nat, A]],
		over, gLinear, rightInverse Fact,
	) {
		R := a.TermAs[RingOps[A]]("c")
		I, iDef := a.LetAs[Set[Nat]]("I", "{i:num | i < n}")
		_, vDef := a.LetAs[module_record.ModuleOps[A, Fun[Nat, A]]]("V", "free_module_record(c, I)")
		_, tDef := a.LetAs[Fun[Fun[Nat, A], Fun[Nat, A]]](
			"T", "λw:(num → A). λr:num. module_sum(c.add, c.zero, I, λk:num. P(r, k) * w(k))")
		// Q is the matrix of g: its column s is g(delta_at(s)) for s < n, and zero from n on.
		Q, qDef := a.LetAs[Fun2[Nat, Nat, A]](
			"Q", "λr:num. λs:num. COND(s < n, g(delta_at(c.zero, c.one, s), r), c.zero)")
		a.Take(Q)
		carrier := a.Have(
			"V consists of the supported coordinate vectors",
			"V.carrier = finite_supp(c.zero, c.carrier, I)",
			Simp(Fwd(vDef), Fwd(free_module.FreeModuleRecordDef), Fwd(module_record.ModCarrierDef)),
			Basic())
		basisValues := a.Have(
			"standard vectors and their g-images lie in V",
			Statement{
				Binders: "∀j:num.", Hypotheses: []string{"j ∈ I"},
				Conclusion: "delta_at(c.zero, c.one, j) ∈ V.carrier ∧ g(delta_at(c.zero, c.one, j)) ∈ V.carrier",
			},
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				inI := b.Assume()
				delta := b.VecAs[A, DimN]("delta_at(c.zero, c.one, j)")
				b.Show(
					"g preserves the coordinate carrier",
					By(
						inI,
						carrier,
						free_module.DeltaAtIn.Read(c).At(I, j),
						module_homomorphism.HomIn.Read(gLinear).AsFact().At(delta)))
			}))
		coordinates := a.Have(
			"the g-images have scalar entries and vanish from row n on",
			Statement{
				Binders: "∀j:num.", Hypotheses: []string{"j ∈ I"},
				Conclusion: "∀i:num. " +
					"    g(delta_at(c.zero, c.one, j), i) ∈ c.carrier ∧ " +
					"    (n ≤ i ⇒ g(delta_at(c.zero, c.one, j), i) = c.zero)",
			},
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				inI := b.Assume()
				b.Show(
					"read the coordinates of each g-image",
					By(
						Normalized,
						inI,
						carrier,
						iDef,
						basisValues.At(j),
						CoordinateVectorMember.At(R, n, b.VecAs[A, DimN]("g(delta_at(c.zero, c.one, j))"))))
			}))
		entries := a.Have(
			"Q has carrier entries and finite square support",
			"∀i j:num. Q(i, j) ∈ c.carrier ∧ (n ≤ i ∨ n ≤ j ⇒ Q(i, j) = c.zero)",
			Derive(func(b *Argument) {
				i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
				b.Do(Simp(Fwd(qDef)))
				b.Cases(b.TermAs[Bool]("j < n"))
				b.When(
					"a column below n is a coordinate vector",
					func(d *Argument, below Fact) {
						d.Show(
							"its scalar entries vanish after row n",
							BySets(Normalized, below, iDef, coordinates.At(j, i), nat_order.NotLessThan.At(j, n)))
					})
				b.Otherwise(
					"every column from n on is zero",
					func(d *Argument, outside Fact) {
						d.Show(
							"zero is a scalar and is zero outside the square",
							By(outside, comm_ring.ZeroIn.Read(c)))
					})
			}))
		qOver := a.Have(
			"Q is a matrix over c",
			"matrix_over(c, n, Q)",
			By(entries, MatrixOverEntries.Read(c).At(n, Q)))
		qColumns := a.Have(
			"the columns of Q below n are the g-images of standard vectors",
			"∀j:num. j ∈ I ⇒ transpose(Q, j) = g(delta_at(c.zero, c.one, j))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("j")
				inI := b.Assume()
				b.Show(
					"read the column definition",
					Simp(Fwd(matrix.TransposeDef), Fwd(qDef)),
					BySets(Normalized, inI, iDef))
			}))
		productColumns := a.Have(
			"a column of P times Q is the column map on the corresponding Q column",
			"∀j:num. transpose(matrix_product(c, n, P, Q), j) = T(transpose(Q, j))",
			Simp(Fwd(tDef), Fwd(iDef), Fwd(matrix.TransposeDef), Fwd(matrix.MatrixProductDef)),
			Basic())
		rightColumns := a.Have(
			"P times Q has the identity's columns below n",
			"∀j:num. j < n ⇒ transpose(matrix_product(c, n, P, Q), j) = delta_at(c.zero, c.one, j)",
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				below := b.Assume()
				b.Show(
					"the chosen right inverse returns the standard vector",
					BySets(
						below,
						iDef,
						tDef,
						productColumns.At(j),
						qColumns.At(j),
						rightInverse.At(b.VecAs[A, DimN]("delta_at(c.zero, c.one, j)")),
						basisValues.At(j)))
			}))
		PQ := a.MatAs[A, DimN, DimN]("matrix_product(c, n, P, Q)")
		rightProduct := a.Have(
			"Q is a right inverse of P",
			"matrix_product(c, n, P, Q) = matrix_identity(c, n)",
			By(
				rightColumns,
				over,
				qOver,
				MatrixProductOver.Read(c).At(n, P, Q),
				Read(identityByColumns, c).At(n, PQ)))
		a.Show(
			"Q is a matrix over c and a right inverse of P",
			By(qOver, rightProduct))
	})
}

// matrixRightInverseIsLeft — over an integral domain, a right inverse of P
// is also a left inverse.
func matrixRightInverseIsLeft(
	ctx *Script,
	columnMapInjective, rightNonzero, identityByColumns *GoalStackNode,
) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀R:integral_domain_on(A). ∀n:num. ∀P Q:(num → num → A).",
		Hypotheses: []string{
			"matrix_over(R, n, P)",
			"matrix_over(R, n, Q)",
			"matrix_product(R, n, P, Q) = matrix_identity(R, n)",
		},
		Conclusion: "matrix_product(R, n, Q, P) = matrix_identity(R, n)",
	}, func(
		a *Argument,
		R integral_domain.IntegralDomainFact[on.R],
		n *Expr[Nat],
		P, Q *Mat[A, DimN, DimN],
		over, qOver, rightProduct Fact,
	) {
		c := integral_domain.Ring.Read(R)
		ring := a.TermAs[RingOps[A]]("R")
		I, iDef := a.LetAs[Set[Nat]]("I", "{i:num | i < n}")
		V, vDef := a.LetAs[module_record.ModuleOps[A, Fun[Nat, A]]]("V", "free_module_record(R, I)")
		T, tDef := a.LetAs[Fun[Fun[Nat, A], Fun[Nat, A]]](
			"T", "λw:(num → A). λr:num. module_sum(R.add, R.zero, I, λk:num. P(r, k) * w(k))")
		S, sDef := a.LetAs[Fun[Fun[Nat, A], Fun[Nat, A]]](
			"S", "λw:(num → A). λr:num. module_sum(R.add, R.zero, I, λk:num. Q(r, k) * w(k))")
		linear := a.Have(
			"the column map of P is linear",
			"module_homomorphism(R, V, V, T)",
			By(tDef, iDef, vDef, over, MatrixColumnMapLinear.Read(c).At(n, P)))
		qLinear := a.Have(
			"and so is the column map of Q",
			"module_homomorphism(R, V, V, S)",
			By(sDef, iDef, vDef, qOver, MatrixColumnMapLinear.Read(c).At(n, Q)))
		carrier := a.Have(
			"V consists of the supported coordinate vectors",
			"V.carrier = finite_supp(R.zero, R.carrier, I)",
			Simp(Fwd(vDef), Fwd(free_module.FreeModuleRecordDef), Fwd(module_record.ModCarrierDef)),
			Basic())
		nonzero := a.Have(
			"a right inverse makes the determinant nonzero",
			"determinant(R, n, P) ≠ R.zero",
			By(over, qOver, rightProduct, Read(rightNonzero, R).At(n, P, Q)))
		injective := a.Have(
			"the column map of P is therefore injective",
			"injective_on(V.carrier, T)",
			By(tDef, iDef, carrier, over, nonzero, Read(columnMapInjective, R).At(n, P)))
		productColumns := a.Have(
			"a column of P times Q is the column map of P on the corresponding Q column",
			"∀j:num. transpose(matrix_product(R, n, P, Q), j) = T(transpose(Q, j))",
			Simp(Fwd(tDef), Fwd(iDef), Fwd(matrix.TransposeDef), Fwd(matrix.MatrixProductDef)),
			Basic())
		identityColumns := a.Have(
			"the identity's columns below n are the standard vectors",
			"∀j:num. j < n ⇒ transpose(matrix_identity(R, n), j) = delta_at(R.zero, R.one, j)",
			a.ForEach(func(j *Expr[Nat]) Action {
				return By(Normalized, matrix.TransposeDef, MatrixIdentityColumn.At(ring, n, j))
			}))
		onStandard := a.Have(
			"the column map of P undoes the column map of Q on each standard vector",
			"∀j:num. j ∈ I ⇒ T(S(delta_at(R.zero, R.one, j))) = delta_at(R.zero, R.one, j)",
			iDef.Rw(),
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				below := b.Assume()
				b.Show(
					"S sends e_j to column j of Q, and T sends that to column j of P times Q, the identity",
					By(
						below,
						sDef,
						iDef,
						qOver,
						rightProduct,
						productColumns.At(j),
						identityColumns.At(j),
						MatrixColumnMapOnDelta.Read(c).At(n, Q, j)))
			}))
		compositeLinear := a.Have(
			"T after S is linear, the composite read pointwise",
			"module_homomorphism(R, V, V, λw:(num → A). T(S(w)))",
			By(qLinear, linear, module_homomorphism.HomCompose.At(ring, V, V, V, S, T), functions.ComposeApply))
		identityLinear := a.Have(
			"and so is the identity of V",
			"module_homomorphism(R, V, V, λw:(num → A). w)",
			By(
				module_homomorphism.HomSource.Read(qLinear),
				module_homomorphism.HomIdentity.At(ring, V),
				functions.IdentityApply))
		rightInverse := a.Have(
			"T undoes S on all of V",
			"∀v:(num → A). v ∈ V.carrier ⇒ T(S(v)) = v",
			Derive(func(b *Argument) {
				v := b.VecFixAs[A, DimN]("v")
				inV := b.Assume()
				b.Show(
					"linear maps out of a free module agree when they agree on its standard basis",
					By(
						inV,
						vDef,
						carrier,
						onStandard,
						compositeLinear,
						identityLinear,
						module_homomorphism.HomSource.Read(qLinear),
						free_module.FreeLiftUnique.At(
							ring,
							V,
							I,
							b.TermAs[Fun[Fun[Nat, A], Fun[Nat, A]]]("λw:(num → A). T(S(w))"),
							b.TermAs[Fun[Fun[Nat, A], Fun[Nat, A]]]("λw:(num → A). w"),
							v)))
			}))
		leftInverse := a.Have(
			"S undoes T on V as well",
			"∀w:(num → A). w ∈ V.carrier ⇒ S(T(w)) = w",
			Derive(func(b *Argument) {
				w := b.VecFixAs[A, DimN]("w")
				inV := b.Assume()
				injectivity := b.Unfolded(injective, functions.InjectiveOnDef)
				Tw := b.VecAs[A, DimN]("T(w)")
				STw := b.VecAs[A, DimN]("S(T(w))")
				b.Show(
					"T sends S(T(w)) and w to T(w), and T is injective",
					By(
						inV,
						injectivity.At(STw, w),
						rightInverse.At(Tw),
						module_homomorphism.HomIn.Read(linear).AsFact().At(w),
						module_homomorphism.HomIn.Read(qLinear).AsFact().At(Tw)))
			}))
		oppositeColumns := a.Have(
			"a column of Q times P is the column map of Q on the corresponding P column",
			"∀j:num. transpose(matrix_product(R, n, Q, P), j) = S(transpose(P, j))",
			Simp(Fwd(sDef), Fwd(iDef), Fwd(matrix.TransposeDef), Fwd(matrix.MatrixProductDef)),
			Basic())
		leftColumns := a.Have(
			"Q times P has the identity's columns below n",
			"∀j:num. j < n ⇒ transpose(matrix_product(R, n, Q, P), j) = delta_at(R.zero, R.one, j)",
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				below := b.Assume()
				delta := b.VecAs[A, DimN]("delta_at(R.zero, R.one, j)")
				b.Show(
					"column j of P is T(e_j), and S sends it back to e_j",
					By(
						below,
						tDef,
						iDef,
						carrier,
						over,
						oppositeColumns.At(j),
						leftInverse.At(delta),
						MatrixColumnMapOnDelta.Read(c).At(n, P, j),
						free_module.DeltaAtIn.Read(c).At(b.TermAs[Set[Nat]]("{i:num | i < n}"), j)))
			}))
		QP := a.MatAs[A, DimN, DimN]("matrix_product(R, n, Q, P)")
		a.Show(
			"Q is a left inverse of P",
			By(
				over,
				qOver,
				leftColumns,
				MatrixProductOver.Read(c).At(n, Q, P),
				Read(identityByColumns, c).At(n, QP)))
	})
}

// matrixColumnBasisInverse — over a field, a column basis gives P a
// two-sided inverse.
func matrixColumnBasisInverse(
	ctx *Script,
	columnMapSection, sectionMatrix, rightInverseIsLeft *GoalStackNode,
) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀L:field_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{
			"matrix_over(field_ring(L), n, P)",
			"module_basis(field_ring(L), " +
				"    free_module_record(field_ring(L), {i:num | i < n}), " +
				"    {transpose(P, j) | j:num | j < n})",
		},
		Conclusion: "∃Q:(num → num → A). " +
			"    matrix_over(field_ring(L), n, Q) ∧ " +
			"    matrix_product(field_ring(L), n, P, Q) = matrix_identity(field_ring(L), n) ∧ " +
			"    matrix_product(field_ring(L), n, Q, P) = matrix_identity(field_ring(L), n)",
	}, func(a *Argument, L field.FieldFact[on.L], n *Expr[Nat], P *Mat[A, DimN, DimN], given Fact) {
		g, section := a.UnpackAs[Fun[Fun[Nat, A], Fun[Nat, A]]](
			GroupPremises(given, Read(columnMapSection, L).At(n, P)),
			"g")
		Q, rightInverse := a.UnpackAs[Fun2[Nat, Nat, A]](
			GroupPremises(given, section, Read(sectionMatrix, field.RingOn.Read(L)).At(n, P, g)),
			"Q")
		a.Take(Q)
		a.Show(
			"a right inverse of P is also a left inverse",
			By(
				given,
				rightInverse,
				Read(rightInverseIsLeft, integral_domain.FieldIntegralDomain.Read(L)).At(n, P, Q)))
	})
}

// determinantZeroIffDependent — the cycle: a nonzero determinant gives a
// column basis, a column basis a two-sided inverse, and a right inverse a
// nonzero determinant. Its lemmas read the column map's facts at the ring
// and respell them in the names I for the points below n, V for the
// coordinate module, T for the column map, E for the standard basis and C
// for the column set.
func determinantZeroIffDependent(ctx *Script, headline string) *GoalStackNode {
	columnMapOnBasis := matrixColumnMapOnBasis(ctx)
	columnMapInjective := determinantColumnMapInjective(ctx)
	columnsBasis := determinantColumnsBasis(ctx, columnMapOnBasis, columnMapInjective)
	rightNonzero := determinantRightInverseNonzero(ctx)
	identityByColumns := matrixIdentityByColumns(ctx)
	columnMapSection := matrixColumnMapSection(ctx, columnMapOnBasis)
	sectionMatrix := matrixOfSection(ctx, identityByColumns)
	rightInverseIsLeft := matrixRightInverseIsLeft(
		ctx, columnMapInjective, rightNonzero, identityByColumns)
	columnsInverse := matrixColumnBasisInverse(ctx, columnMapSection, sectionMatrix, rightInverseIsLeft)
	return ctx.Theorem(headline, func(
		a *Argument,
		L field.FieldFact[on.L],
		n *Expr[Nat],
		P *Mat[A, DimN, DimN],
		over Fact,
	) {
		a.Show(
			"a nonzero determinant gives a column basis, a column basis gives a "+
				"two-sided inverse, and a two-sided inverse gives a nonzero determinant",
			By(
				over,
				Read(columnsBasis, L).At(n, P),
				Read(columnsInverse, L).At(n, P),
				Read(rightNonzero, integral_domain.FieldIntegralDomain.Read(L)).At(n, P)))
	})
}
