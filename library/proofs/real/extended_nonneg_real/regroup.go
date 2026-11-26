// regroup.go — a double series regrouped along a map of its index pairs:
// of extended nonnegative reals along any map, an enumeration's inverse
// among them, and of absolutely summable reals along a map with finite
// fibres.

package extended_nonneg_real

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// SeriesSingleton — a series supported at one index sums to its value
// there, including when that value is infinity.
var SeriesSingleton = seriesSingletonThm{family.Add(registry.ProofEntry{
	Name: "SeriesSingleton",
	Key:  "prop_1f03ea628dfc51ba",
	Build: family.Theorem("∀x:extended_nonneg_real. ∀N:num. "+
		"    extended_series(λn:num. COND(n = N, x, &0)) = x",
		func(arg *Argument, x *Expr[ExtendedNonnegReal], N *Expr[Nat]) {
			spike := arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. COND(n = N, x, &0)")
			tail := arg.Have(
				"every term past N vanishes",
				"∀n:num. N < n ⇒ COND(n = N, x, &0) = &0",
				By(nat_order.LessThanIrrefl))
			arg.Show(
				"only the supported term contributes",
				CalcEq(
					Leg(
						arg.TermAs[ExtendedNonnegReal]("Σ_{i∈0 .. N} COND(i = N, x, &0)"),
						"the tail contributes zero",
						By(tail, SeriesEventuallyZero.At(spike, N))),
					FinalLeg(
						"the finite segment contains just the supported term",
						Derive(func(a *Argument) {
							nonzero := a.Unless(
								a.Term("N = 0"),
								"the segment at zero contains its single supported term",
								Given(func(b *Argument, atZero Fact) {
									b.Show(
										"its one term is x",
										By(atZero, SumSegmentZero))
								}))
							end := a.Have(
								"the predecessor's successor is N",
								"N - 1 + 1 = N",
								ByArith(nonzero))
							excluded := a.Have(
								"the prefix excludes N",
								"∀i:num. i ∈ 0 .. N - 1 ⇒ i ≠ N",
								ByArith(nonzero, num_segment.MembershipFromZero))
							prefix := a.Have(
								"the prefix sums to zero",
								"Σ_{i∈0 .. N - 1} COND(i = N, x, &0) = &0",
								By(excluded, ExtendedSumZero.At(spike, a.TermAs[Set[Nat]]("0 .. N - 1"))))
							a.Show(
								"peeling the final term leaves zero plus x",
								By(prefix, end, SumSegmentPeel.At(spike, a.TermAs[Nat]("N - 1")), AddZero, AddComm))
						}))))
		}),
})}

// SeriesRegroup — a double series of extended nonnegative reals summed
// fibre by fibre of a map φ of its index pairs has the sum it has row by
// row.
var SeriesRegroup = seriesRegroupThm{family.Add(registry.ProofEntry{
	Name: "SeriesRegroup",
	Key:  "prop_7f756107dd154fee",
	Build: family.Theorem("∀a:(num → num → extended_nonneg_real). ∀φ:(num → num → num). "+
		"    extended_series(λk:num. "+
		"            extended_series(λm:num. extended_series(λn:num. COND(φ(m, n) = k, a(m, n), &0)))) = "+
		"    extended_series(λm:num. extended_series(λn:num. a(m, n)))",
		func(arg *Argument, a *Arrow2[Nat, Nat, ExtendedNonnegReal], φ *Arrow2[Nat, Nat, Nat]) {
			rows := arg.Have(
				"each row has the same sum in either order",
				"∀m:num. "+
					"    extended_series(λk:num. extended_series(λn:num. COND(φ(m, n) = k, a(m, n), &0))) = "+
					"    extended_series(λn:num. extended_series(λk:num. COND(φ(m, n) = k, a(m, n), &0)))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("m")
					b.Show(
						"exchange the two indices of this row",
						By(SeriesExchange.At(
							b.TermAs[Fun2[Nat, Nat, ExtendedNonnegReal]]("λk:num. λn:num. COND(φ(m, n) = k, a(m, n), &0)"))))
				}))
			singletons := arg.Have(
				"each pair contributes at its own fibre index",
				"∀m n:num. extended_series(λk:num. COND(φ(m, n) = k, a(m, n), &0)) = a(m, n)",
				Derive(func(b *Argument) {
					m := b.FixAs[Nat]("m")
					n := b.FixAs[Nat]("n")
					b.Show(
						"the series over the fibre index is a singleton",
						By(SeriesSingleton.At(a.Apply(m, n), φ.Apply(m, n))))
				}))
			arg.Show(
				"exchange the fibre index inward, then sum each pair's singleton series",
				CalcEq(
					Leg(
						arg.TermAs[ExtendedNonnegReal](
							"extended_series( "+
								"    λm:num. extended_series(λk:num. extended_series(λn:num. COND(φ(m, n) = k, a(m, n), &0))))"),
						"exchange the fibre and row indices",
						By(SeriesExchange.At(arg.TermAs[Fun2[Nat, Nat, ExtendedNonnegReal]](
							"λk:num. λm:num. extended_series(λn:num. COND(φ(m, n) = k, a(m, n), &0))")))),
					Leg(
						arg.TermAs[ExtendedNonnegReal](
							"extended_series( "+
								"    λm:num. extended_series(λn:num. extended_series(λk:num. COND(φ(m, n) = k, a(m, n), &0))))"),
						"exchange the fibre and column indices in each row",
						By(rows)),
					FinalLeg(
						"the fibre index has one supported value for each pair",
						By(singletons))))
		}),
	Reading: "No finiteness is asked of the fibres: sums in [0, " +
		"∞] always exist, and an infinite fibre contributes its series.",
})}

// SeriesFinitePairs — a double series supported on finitely many index
// pairs equals the finite sum over those pairs. A fresh pair adds its
// two-coordinate singleton series to the old support.
var SeriesFinitePairs = seriesFinitePairsThm{family.Add(registry.ProofEntry{
	Name: "SeriesFinitePairs",
	Key:  "prop_1d11b062196b1bc1",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(prod(num, num)). ∀a:(num → num → extended_nonneg_real).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "extended_series(λm:num. extended_series(λn:num. COND((m, n) ∈ s, a(m, n), &0))) = " +
			"Σ_{p∈s} a(fst(p), snd(p))",
	}, func(
		arg *Argument,
		s *Expr[Set[Prod[Nat, Nat]]],
		a *Arrow2[Nat, Nat, ExtendedNonnegReal],
		finite Fact,
	) {
		arg.Show(
			"insert the finitely many supported pairs",
			ByInduction(finite_set.FiniteInductFresh, finite,
				Case(
					"empty support gives two zero series and the empty sum",
					Unfold(set_basic.SetMemberDef),
					Simp(Fwd(SumClauses), Fwd(set_basic.EmptySetDef), Fwd(SeriesZero)),
					Basic()),
				Case(
					"a fresh pair adds its value to both sums",
					Derive(func(b *Argument) {
						x := b.FixAs[Prod[Nat, Nat]]("x")
						t := b.FixAs[Set[Prod[Nat, Nat]]]("t")
						step := b.Assume()
						parts := b.Conjuncts(
							step,
							"the old support has its finite sum",
							"the new pair is fresh",
							"the old support is finite")
						separate := b.Have(
							"separate the new pair's spike from the old support",
							"∀m n:num. "+
								"    COND((m, n) ∈ insert(x, t), a(m, n), &0) = "+
								"    COND(n = snd(x), COND(m = fst(x), a(fst(x), snd(x)), &0), &0) + COND((m, n) ∈ t, a(m, n), &0)",
							Derive(func(c *Argument) {
								m := c.FixAs[Nat]("m")
								n := c.FixAs[Nat]("n")
								c.Show(
									"freshness keeps the spike disjoint from the old support",
									By(
										parts[1],
										set_basic.SetMemberDef,
										set_basic.InsertDef.At(x, t, c.TermAs[Prod[Nat, Nat]]("(m, n)")),
										pairs.PairEta.At(x),
										pairs.PairEq.At(m, n, c.TermAs[Nat]("fst(x)"), c.TermAs[Nat]("snd(x)")),
										AddZero,
										AddComm))
							}))
						b.Show(
							"split each series, collapse the spike on both axes, and use the old sum",
							Simp(Fwd(separate)),
							Simp(Fwd(SeriesAdd), Fwd(SeriesSingleton), Fwd(SumClauses)),
							By(parts[0]))
					}))))
	}),
})}

// SeriesPairing — summing a double series along an enumeration σ of its
// index pairs gives the iterated sum: the regrouping along σ's inverse,
// whose fibres are single points.
var SeriesPairing = seriesPairingThm{family.Add(registry.ProofEntry{
	Name: "SeriesPairing",
	Key:  "prop_9329c3f011abe0cf",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → num → extended_nonneg_real). ∀σ:(num → prod(num, num)).",
		Hypotheses: []string{
			"injective_on(𝕌, σ)",
			"image(σ, 𝕌) = 𝕌",
		},
		Conclusion: "extended_series(λk:num. a(fst(σ(k)), snd(σ(k)))) = " +
			"extended_series(λm:num. extended_series(λn:num. a(m, n)))",
	}, func(
		arg *Argument,
		a *Arrow2[Nat, Nat, ExtendedNonnegReal],
		σ *Arrow[Nat, Prod[Nat, Nat]],
		injective, onto Fact,
	) {
		universe := arg.TermAs[Set[Nat]]("𝕌")
		φ, φDef := arg.LetAs[Fun2[Nat, Nat, Nat]]("φ", "λm:num. λn:num. inverse_on(𝕌, σ, (m, n))")
		fibre := arg.Have(
			"the fibre of φ over k is the one pair σ(k)",
			"∀m n k:num. φ(m, n) = k ⇔ (m, n) ∈ {σ(k)}",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("m")
				b.FixAs[Nat]("n")
				k := b.FixAs[Nat]("k")
				pair := b.TermAs[Prod[Nat, Nat]]("(m, n)")
				b.Show(
					"σ undoes φ on every pair, and φ undoes σ on every index",
					By(
						φDef,
						onto,
						injective,
						functions.InverseOnRight.At(universe, σ, pair),
						functions.InverseOnLeft.At(universe, σ, k),
						set_basic.InUniv.At(pair),
						set_basic.InUniv.At(k),
						set_basic.InSing.At(pair, σ.Apply(k))))
			}))
		single := arg.Have(
			"each fibre's double series is its one term",
			"∀k:num. "+
				"    extended_series(λm:num. extended_series(λn:num. COND(φ(m, n) = k, a(m, n), &0))) = "+
				"    a(fst(σ(k)), snd(σ(k)))",
			Derive(func(b *Argument) {
				k := b.FixAs[Nat]("k")
				b.Show(
					"a series supported on the singleton {σ(k)} is its finite sum there, the one term",
					Simp(Fwd(fibre)),
					By(
						finite_set.FiniteSing.At(σ.Apply(k)),
						SeriesFinitePairs.At(b.TermAs[Set[Prod[Nat, Nat]]]("{σ(k)}"), a),
						monoidal.Sing.Read(MonoidalAdd),
						ExtendedSumDef))
			}))
		arg.Show(
			"regroup along φ, each fibre contributing its one term",
			By(single, SeriesRegroup.At(a, φ)))
	}),
})}

// NonnegativeSummableRegroup — a nonnegative double series with summable
// row sums has the same real sum when grouped into finite fibres.
var NonnegativeSummableRegroup = nonnegativeSummableRegroupThm{family.Add(registry.ProofEntry{
	Name: "NonnegativeSummableRegroup",
	Key:  "prop_3f56a760e9550887",
	Build: family.Theorem(Statement{
		Binders: "∀u:(num → num → real). ∀φ:(num → num → num). ∀R:(num → real). ∀T:real.",
		Hypotheses: []string{
			"∀m n:num. &0 ≤ u(m, n)",
			"∀m:num. real_sums(λn:num. u(m, n), R(m))",
			"real_sums(R, T)",
			"∀k:num. finite(«fibre»(k))",
		},
		Conclusion: "real_sums(«regrouped», T)",
		Abbrev: Abbrev{
			{Name: "regrouped", Text: "λk:num. Σ_{p∈«fibre»(k)} u(fst(p), snd(p))"},
		},
	}, func(
		arg *Argument,
		u *Arrow2[Nat, Nat, Real],
		φ *Arrow2[Nat, Nat, Nat],
		R *Arrow[Nat, Real],
		T *Expr[Real],
		hypotheses Fact,
	) {
		parts := arg.Conjuncts(
			hypotheses,
			"the terms are nonnegative",
			"each row has its real sum",
			"the row sums have total T",
			"each fibre is finite")
		nonnegative, rowSums, totalSum, finiteFibres := parts[0], parts[1], parts[2], parts[3]
		zeroSeries := arg.TermAs[Fun[Nat, Real]]("λn:num. &0")
		zero := arg.TermAs[Real]("&0")
		rowNonnegative := arg.Have(
			"the row sums are nonnegative",
			"∀m:num. &0 ≤ R(m)",
			Derive(func(b *Argument) {
				m := b.FixAs[Nat]("m")
				b.Show(
					"compare this row with the zero series",
					By(
						nonnegative.At(m),
						rowSums.At(m),
						real_series.SumsZero,
						real_series.SumsLessEq.At(
							zeroSeries, b.TermAs[Fun[Nat, Real]]("λn:num. u(m, n)"), zero, R.Apply(m))))
			}))
		totalNonnegative := arg.Have(
			"the total is nonnegative",
			"&0 ≤ T",
			By(
				rowNonnegative,
				totalSum,
				real_series.SumsZero,
				real_series.SumsLessEq.At(zeroSeries, R, zero, T)))
		rowImages := arg.Have(
			"each extended row is the embedding of its real sum",
			"∀m:num. extended_series(λn:num. extended_of_real(u(m, n))) = extended_of_real(R(m))",
			Derive(func(b *Argument) {
				m := b.FixAs[Nat]("m")
				b.Show(
					"embed the known real row sum",
					By(
						nonnegative.At(m),
						rowSums.At(m),
						SeriesOfReal.At(b.TermAs[Fun[Nat, Real]]("λn:num. u(m, n)"), R.Apply(m))))
			}))
		totalImage := arg.Have(
			"the extended double series has the embedded total T",
			"extended_series(λm:num. extended_series(λn:num. extended_of_real(u(m, n)))) = extended_of_real(T)",
			Simp(Fwd(rowImages)),
			By(rowNonnegative, totalSum, SeriesOfReal.At(R, T)))
		fibreNonnegative := arg.Have(
			"the fibre sums are nonnegative",
			"∀k:num. &0 ≤ «regrouped»(k)",
			By(nonnegative, real_sum.Nonneg))
		fibreImages := arg.Have(
			"each finite fibre series embeds its finite real sum",
			"∀k:num. "+
				"    extended_series( "+
				"        λm:num. extended_series(λn:num. COND(φ(m, n) = k, extended_of_real(u(m, n)), &0))) = "+
				"    extended_of_real(«regrouped»(k))",
			Derive(func(b *Argument) {
				k := b.FixAs[Nat]("k")
				b.Show(
					"sum on the finite fibre, then carry the finite sum through the embedding",
					CalcEq(
						Leg(
							b.TermAs[ExtendedNonnegReal]("Σ_{p∈«fibre»(k)} extended_of_real(u(fst(p), snd(p)))"),
							"the finite-pair support is exactly this fibre",
							Derive(func(c *Argument) {
								inFibre := c.Have(
									"the pair lies in the fibre precisely at this index",
									"∀m n:num. (m, n) ∈ «fibre»(k) ⇔ φ(m, n) = k",
									BySets(pairs.Fst, pairs.Snd))
								finitePairs := c.Simplified(
									GroupPremises(finiteFibres.At(k),
										SeriesFinitePairs.At(c.TermAs[Set[Prod[Nat, Nat]]]("«fibre»(k)"),
											c.TermAs[Fun2[Nat, Nat, ExtendedNonnegReal]]("λm:num. λn:num. extended_of_real(u(m, n))"))),
									Fwd(inFibre))
								c.Show(
									"read the finite-pair identity on this fibre",
									By(finitePairs))
							})),
						FinalLeg(
							"embedding preserves this finite nonnegative sum",
							By(
								finiteFibres.At(k),
								nonnegative,
								SumOfReal.At(
									b.TermAs[Fun[Prod[Nat, Nat], Real]]("λp:prod(num, num). u(fst(p), snd(p))"),
									b.TermAs[Set[Prod[Nat, Nat]]]("«fibre»(k)"))))))
			}))
		regroupedImage := arg.Have(
			"the regrouped extended series has the same embedded total",
			"extended_series(λk:num. extended_of_real(«regrouped»(k))) = extended_of_real(T)",
			Simp(Rev(fibreImages)),
			By(
				totalImage,
				SeriesRegroup.At(
					arg.TermAs[Fun2[Nat, Nat, ExtendedNonnegReal]]("λm:num. λn:num. extended_of_real(u(m, n))"), φ)))
		arg.Show(
			"read the finite total back as the real sum T",
			By(
				fibreNonnegative,
				regroupedImage,
				totalNonnegative,
				OfRealNotInfinity.At(T),
				SeriesFinite.At(arg.TermAs[Fun[Nat, Real]]("«regrouped»")),
				ToRealOfReal.At(T)))
	}),
})}

// AbsolutelySummableRegroup — an absolutely convergent double series of
// reals has the same sum taken row by row and taken along the fibres of a
// map with finite fibres.
var AbsolutelySummableRegroup = absolutelySummableRegroupThm{family.Add(registry.ProofEntry{
	Name: "AbsolutelySummableRegroup",
	Key:  "prop_2427fe90b558d3df",
	Build: family.Theorem(Statement{
		Binders: "∀u:(num → num → real). ∀φ:(num → num → num). ∀R:(num → real). ∀T:real.",
		Hypotheses: []string{
			"∀m:num. real_sums(λn:num. |u(m, n)|, R(m))",
			"real_sums(R, T)",
			"∀k:num. finite(«fibre»(k))",
		},
		Conclusion: "∃r:(num → real). ∃S:real. " +
			"    (∀m:num. real_sums(λn:num. u(m, n), r(m))) ∧ " +
			"    real_sums(r, S) ∧ " +
			"    real_sums(λk:num. Σ_{p∈«fibre»(k)} u(fst(p), snd(p)), S)",
		Abbrev: Abbrev{
			{Name: "positive", Text: "λm:num. λn:num. max(u(m, n), &0)"},
			{Name: "negative", Text: "λm:num. λn:num. max(-u(m, n), &0)"},
		},
	}, func(
		arg *Argument,
		u *Arrow2[Nat, Nat, Real],
		φ *Arrow2[Nat, Nat, Nat],
		R *Arrow[Nat, Real],
		T *Expr[Real],
		hypotheses Fact,
	) {
		parts := arg.Conjuncts(
			hypotheses,
			"the absolute rows sum to R",
			"R sums to T",
			"the fibres are finite")
		absoluteRows, absoluteTotal, finiteFibres := parts[0], parts[1], parts[2]
		zero := arg.TermAs[Real]("&0")
		zeroSeries := arg.TermAs[Fun[Nat, Real]]("λn:num. &0")
		start := arg.TermAs[Nat]("0")
		dominated := arg.Have(
			"every nonnegative part dominated by the absolute terms can be summed in either grouping",
			Statement{
				Binders:    "∀v:(num → num → real).",
				Hypotheses: []string{"∀m n:num. &0 ≤ v(m, n) ∧ v(m, n) ≤ |u(m, n)|"},
				Conclusion: "∃V:(num → real). ∃A:real. " +
					"    (∀m:num. real_sums(λn:num. v(m, n), V(m))) ∧ " +
					"    real_sums(V, A) ∧ " +
					"    real_sums(λk:num. Σ_{p∈«fibre»(k)} v(fst(p), snd(p)), A)",
			},
			Derive(func(b *Argument) {
				v := b.FixAs[Fun2[Nat, Nat, Real]]("v")
				bounded := b.Assume()
				rowExists := b.Have(
					"each dominated row converges by comparison",
					"∀m:num. ∃s:real. real_sums(λn:num. v(m, n), s)",
					Derive(func(c *Argument) {
						m := c.FixAs[Nat]("m")
						c.Show(
							"compare with the absolute row",
							By(
								bounded.At(m),
								absoluteRows.At(m),
								real_series.Comparison.At(
									c.TermAs[Fun[Nat, Real]]("λn:num. v(m, n)"),
									c.TermAs[Fun[Nat, Real]]("λn:num. |u(m, n)|"),
									R.Apply(m), start),
								real_sgn_abs.AbsFixedIffNonneg))
					}))
				V, rowSums := b.ObtainAs[Fun[Nat, Real]](
					"choose the row sums as a function V",
					"∃V:(num → real). ∀m:num. real_sums(λn:num. v(m, n), V(m))",
					By(rowExists),
					Named("V"))
				rowBounds := b.Have(
					"V lies between zero and the absolute row sums",
					"∀m:num. &0 ≤ V(m) ∧ V(m) ≤ R(m)",
					Derive(func(c *Argument) {
						m := c.FixAs[Nat]("m")
						row := c.TermAs[Fun[Nat, Real]]("λn:num. v(m, n)")
						value := c.TermAs[Real]("V(m)")
						c.Show(
							"compare this row with zero and with its absolute row",
							SplitConj(
								Case(
									"the nonnegative terms have a nonnegative sum",
									By(
										bounded.At(m),
										rowSums.At(m),
										real_series.SumsZero,
										real_series.SumsLessEq.At(zeroSeries, row, zero, value))),
								Case(
									"the sum is at most the absolute row sum",
									By(
										bounded.At(m),
										absoluteRows.At(m),
										rowSums.At(m),
										real_series.SumsLessEq.At(row,
											c.TermAs[Fun[Nat, Real]]("λn:num. |u(m, n)|"), value, R.Apply(m))))))
					}))
				A, total := b.ObtainAs[Real](
					"V converges by comparison with R",
					"∃A:real. real_sums(V, A)",
					By(
						rowBounds,
						absoluteTotal,
						real_series.Comparison.At(V, R, T, start),
						real_sgn_abs.AbsFixedIffNonneg),
					Named("A"))
				b.Take(V)
				b.Take(A)
				b.Show(
					"regroup the dominated nonnegative series",
					By(finiteFibres, bounded, rowSums, total, NonnegativeSummableRegroup.At(v, φ, V, A)))
			}))
		positive := arg.TermAs[Fun2[Nat, Nat, Real]]("«positive»")
		negative := arg.TermAs[Fun2[Nat, Nat, Real]]("«negative»")
		positiveBound := arg.Have(
			"the positive part is nonnegative and dominated by the absolute terms",
			"∀m n:num. &0 ≤ «positive»(m, n) ∧ «positive»(m, n) ≤ |u(m, n)|",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("m")
				b.FixAs[Nat]("n")
				x := b.TermAs[Real]("u(m, n)")
				b.Show(
					"the maximum is below any common upper bound",
					By(
						real_sup_inf.MaxUpperBound.At(x, zero),
						real_sup_inf.MaxLessEq.At(x, zero, b.TermAs[Real]("|u(m, n)|")),
						real_sgn_abs.AbsDominates,
						real_sgn_abs.AbsNonneg))
			}))
		negativeBound := arg.Have(
			"the negative part is nonnegative and has the same absolute bound",
			"∀m n:num. &0 ≤ «negative»(m, n) ∧ «negative»(m, n) ≤ |u(m, n)|",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("m")
				b.FixAs[Nat]("n")
				x := b.TermAs[Real]("-u(m, n)")
				b.Show(
					"negation preserves absolute value",
					By(
						real_sup_inf.MaxUpperBound.At(x, zero),
						real_sup_inf.MaxLessEq.At(x, zero, b.TermAs[Real]("|u(m, n)|")),
						real_sgn_abs.AbsEven,
						real_sgn_abs.AbsDominates,
						real_sgn_abs.AbsNonneg))
			}))
		P, A, positiveSums := arg.Obtain2As[Fun[Nat, Real], Real](
			"sum and regroup the positive part",
			"∃P:(num → real). ∃A:real. "+
				"    (∀m:num. real_sums(λn:num. «positive»(m, n), P(m))) ∧ "+
				"    real_sums(P, A) ∧ "+
				"    real_sums(λk:num. Σ_{p∈«fibre»(k)} «positive»(fst(p), snd(p)), A)",
			By(dominated.At(positive), positiveBound),
			Named("P", "A"))
		Q, B, negativeSums := arg.Obtain2As[Fun[Nat, Real], Real](
			"sum and regroup the negative part",
			"∃Q:(num → real). ∃B:real. "+
				"    (∀m:num. real_sums(λn:num. «negative»(m, n), Q(m))) ∧ "+
				"    real_sums(Q, B) ∧ "+
				"    real_sums(λk:num. Σ_{p∈«fibre»(k)} «negative»(fst(p), snd(p)), B)",
			By(dominated.At(negative), negativeBound),
			Named("Q", "B"))
		decompose := arg.Have(
			"the two nonnegative parts have difference u",
			"∀m n:num. «positive»(m, n) - «negative»(m, n) = u(m, n)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("m")
				b.FixAs[Nat]("n")
				b.Show(
					"subtract the two maxima",
					ByArith(real_sup_inf.RealMaxDef))
			}))
		arg.Take(arg.TermAs[Fun[Nat, Real]]("λm:num. P(m) - Q(m)"))
		arg.Take(arg.TermAs[Real]("A - B"))
		arg.Show(
			"subtract the positive and negative series in both groupings",
			SplitConj(
				Case(
					"the signed rows and their total are differences of the part sums",
					SplitConj(
						Case(
							"each signed row sums to the difference of its part sums",
							Derive(func(b *Argument) {
								b.FixAs[Nat]("m")
								b.Show(
									"subtract this row's two convergent parts",
									By(
										decompose,
										negativeSums,
										positiveSums,
										real_series.SumsSub.At(
											b.TermAs[Fun[Nat, Real]]("λn:num. «positive»(m, n)"),
											b.TermAs[Fun[Nat, Real]]("λn:num. «negative»(m, n)"),
											b.TermAs[Real]("P(m)"), b.TermAs[Real]("Q(m)"))))
							})),
						Case(
							"the row differences sum to A minus B",
							By(negativeSums, positiveSums, real_series.SumsSub.At(P, Q, A, B))))),
				Case(
					"the finite-fibre sums have the same difference of totals",
					Derive(func(b *Argument) {
						fibreDifference := b.Have(
							"each signed fibre sum is the difference of its two nonnegative fibre sums",
							"∀k:num. "+
								"    Σ_{p∈«fibre»(k)} u(fst(p), snd(p)) = "+
								"    (Σ_{p∈«fibre»(k)} «positive»(fst(p), snd(p))) - (Σ_{p∈«fibre»(k)} «negative»(fst(p), snd(p)))",
							Derive(func(c *Argument) {
								k := c.FixAs[Nat]("k")
								linear := c.Simplified(
									GroupPremises(finiteFibres.At(k), real_sum.Sub.At(c.TermAs[Set[Prod[Nat, Nat]]]("«fibre»(k)"),
										c.TermAs[Fun[Prod[Nat, Nat], Real]]("λp:prod(num, num). «positive»(fst(p), snd(p))"),
										c.TermAs[Fun[Prod[Nat, Nat], Real]]("λp:prod(num, num). «negative»(fst(p), snd(p))"))),
									Fwd(decompose))
								c.Show(
									"finite sums preserve subtraction",
									By(linear))
							}))
						b.Show(
							"subtract the regrouped positive and negative series",
							Simp(Fwd(fibreDifference)),
							By(
								negativeSums,
								positiveSums,
								real_series.SumsSub.At(
									b.TermAs[Fun[Nat, Real]]("λk:num. Σ_{p∈«fibre»(k)} «positive»(fst(p), snd(p))"),
									b.TermAs[Fun[Nat, Real]]("λk:num. Σ_{p∈«fibre»(k)} «negative»(fst(p), snd(p))"), A, B)))
					}))))
	}),
	Reading: "The finite fibres make each regrouped term a finite sum of signed reals. " +
		"The fold sums finite nonzero support and returns 0 when that support is infinite. " +
		"Monsky's Lambert expansion reads it at u(n, k) = χ(n + 1)·t^((n + 1)(k + 1)).",
})}
