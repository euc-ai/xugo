// series.go — countable sums in ⟦0, ∞⟧: every series of ⟦0, ∞⟧ terms has
// a sum, the supremum of its partial sums.
//
// Three parts, marked by banners:
//
// - The sum and its bounds
// - Linearity
// - Series of reals, and double series
//
// A sum is read through its two bound properties alone: every partial
// sum lies below it, and it lies below every bound of the partial sums.
// Addition and scaling pass through because the partial sums rise, so
// SupSequenceAdd and SupSequenceScale apply to them; a series of
// nonnegative reals sums in ⟦0, ∞⟧ to the image of its real sum; and a
// double series may be summed in either order.

package extended_nonneg_real

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The sum and its bounds
// ---------------------------------------------------------------------------

// ExtendedSeriesDef — the sum of a series of ⟦0, ∞⟧ terms: the supremum
// of its partial sums, which increase.
var ExtendedSeriesDef = extendedSeriesDefThm{family.Define(registry.DefEntry{
	Name:  "ExtendedSeriesDef",
	Key:   "prop_d1c7f39409353cc3",
	Const: "extended_series",
	Type:  "(num → extended_nonneg_real) → extended_nonneg_real",
	Equations: []string{
		"∀a:(num → extended_nonneg_real). " +
			"    extended_series(a) = extended_sup(image(λn:num. Σ_{i∈0 .. n} a(i), 𝕌))",
	},
	Deps: []registry.EntryLike{ExtendedSupDef, ExtendedSumDef},
})}

// SeriesPartialLe — every partial sum lies below the sum.
var SeriesPartialLe = seriesPartialLeThm{family.Add(registry.ProofEntry{
	Name: "SeriesPartialLe",
	Key:  "prop_36906335bc3ad76c",
	Build: family.Theorem("∀a:(num → extended_nonneg_real). ∀n:num. "+
		"    Σ_{i∈0 .. n} a(i) ≤ extended_series(a)",
		func(arg *Argument, a *Arrow[Nat, ExtendedNonnegReal], n *Expr[Nat]) {
			partial := arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λk:num. Σ_{i∈0 .. k} a(i)")
			arg.Do(Unfold(ExtendedSeriesDef))
			arg.Show(
				"the partial sum is a term of the sequence of partial sums",
				By(SupSequenceUpper.At(partial, n)))
		}),
})}

// SeriesLeast — a bound on every partial sum bounds the sum.
var SeriesLeast = seriesLeastThm{family.Add(registry.ProofEntry{
	Name: "SeriesLeast",
	Key:  "prop_28290095ce597876",
	Build: family.Theorem(Statement{
		Binders:    "∀a:(num → extended_nonneg_real). ∀z:extended_nonneg_real.",
		Hypotheses: []string{"∀n:num. Σ_{i∈0 .. n} a(i) ≤ z"},
		Conclusion: "extended_series(a) ≤ z",
	}, func(arg *Argument, a *Arrow[Nat, ExtendedNonnegReal], z *Expr[ExtendedNonnegReal], bound Fact) {
		partial := arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λk:num. Σ_{i∈0 .. k} a(i)")
		arg.Do(Unfold(ExtendedSeriesDef))
		arg.Show(
			"z bounds the sequence of partial sums",
			By(bound, SupSequenceLeast.At(partial, z)))
	}),
})}

// SeriesEventuallyZero — a series whose terms vanish beyond the index N
// sums to its partial sum up to N. The partial sums up to n ≤ N are parts
// of the one up to N, and past N each adds a zero; so the partial sum up
// to N bounds them all, and it is one of them.
var SeriesEventuallyZero = seriesEventuallyZeroThm{family.Add(registry.ProofEntry{
	Name: "SeriesEventuallyZero",
	Key:  "prop_3d8dd37517f902a",
	Build: family.Theorem(Statement{
		Binders:    "∀a:(num → extended_nonneg_real). ∀N:num.",
		Hypotheses: []string{"∀n:num. N < n ⇒ a(n) = &0"},
		Conclusion: "extended_series(a) = Σ_{i∈0 .. N} a(i)",
	}, func(arg *Argument, a *Arrow[Nat, ExtendedNonnegReal], N *Expr[Nat], vanish Fact) {
		zero := arg.TermAs[Nat]("0")
		upToN := arg.TermAs[Set[Nat]]("0 .. N")
		bounded := arg.Have(
			"no partial sum exceeds the one up to N",
			"∀n:num. Σ_{i∈0 .. n} a(i) ≤ Σ_{i∈0 .. N} a(i)",
			Derive(func(b *Argument) {
				b.Induct("n")
				b.Base(
					"the sum up to 0 is part of the sum up to N",
					By(
						SumSubsetLe.At(a, b.TermAs[Set[Nat]]("0 .. 0"), upToN),
						num_segment.Finite.At(zero, N),
						num_segment.Subset.At(zero, zero, zero, N),
						nat_order.ZeroLessEq))
				b.Step(
					"the sum up to n + 1 still lies below the sum up to N",
					func(c *Argument, ih Fact) {
						c.Do(Simp(Fwd(nat_arith.Add1)))
						next := c.TermAs[Nat]("n + 1")
						c.Cases(c.Term("n + 1 ≤ N"))
						c.When(
							"up to N, the sum up to n + 1 is part of the sum up to N",
							func(d *Argument, within Fact) {
								d.Show(
									"0 .. n + 1 lies inside 0 .. N",
									By(
										within,
										SumSubsetLe.At(a, d.TermAs[Set[Nat]]("0 .. n + 1"), upToN),
										num_segment.Finite.At(zero, N),
										num_segment.Subset.At(zero, next, zero, N),
										nat_order.ZeroLessEq))
							})
						c.Otherwise(
							"past N, the new term is 0",
							func(d *Argument, past Fact) {
								d.Show(
									"so the sum up to n + 1 is the sum up to n",
									By(
										past,
										vanish.At(next),
										ih,
										SumSegmentPeel.At(a, d.TermAs[Nat]("n")),
										AddZero,
										nat_order.NotLessEq))
							})
					})
			}))
		arg.Show(
			"the series lies below that bound and above its partial sum up to N",
			By(bounded, LeAntisym, SeriesLeast, SeriesPartialLe.At(a, N)))
	}),
})}

// SeriesAddLe — a bound z on every partial sum plus y bounds the series
// plus y: the series is the supremum of its partial sums, and adding y
// to the supremum of a nonempty set stays below every bound of the set's
// members plus y.
var SeriesAddLe = seriesAddLeThm{family.Add(registry.ProofEntry{
	Name: "SeriesAddLe",
	Key:  "prop_fbbff8d64618904b",
	Build: family.Theorem(Statement{
		Binders:    "∀a:(num → extended_nonneg_real). ∀y z:extended_nonneg_real.",
		Hypotheses: []string{"∀n:num. Σ_{i∈0 .. n} a(i) + y ≤ z"},
		Conclusion: "extended_series(a) + y ≤ z",
	}, func(
		arg *Argument,
		a *Arrow[Nat, ExtendedNonnegReal],
		y, z *Expr[ExtendedNonnegReal],
		bound Fact,
	) {
		nonempty := arg.Have(
			"the partial sums form a nonempty set",
			"image(λn:num. Σ_{i∈0 .. n} a(i), 𝕌) ≠ ∅",
			BySets())
		each := arg.Have(
			"each partial sum plus y lies below z",
			"∀x:extended_nonneg_real. x ∈ image(λn:num. Σ_{i∈0 .. n} a(i), 𝕌) ⇒ x + y ≤ z",
			By(bound, set_basic.InImage))
		arg.Show(
			"so does their supremum, the series, plus y",
			Unfold(ExtendedSeriesDef),
			By(nonempty, each, SupAddLe))
	}),
})}

// SeriesMono — a series termwise below another sums to no more: each of
// its partial sums lies below the corresponding one, hence below the
// other sum.
var SeriesMono = seriesMonoThm{family.Add(registry.ProofEntry{
	Name: "SeriesMono",
	Key:  "prop_3758b70e41260598",
	Build: family.Theorem(Statement{
		Binders:    "∀a b:(num → extended_nonneg_real).",
		Hypotheses: []string{"∀n:num. a(n) ≤ b(n)"},
		Conclusion: "extended_series(a) ≤ extended_series(b)",
	}, func(arg *Argument, a, b *Arrow[Nat, ExtendedNonnegReal], termwise Fact) {
		partialsBelow := arg.Have(
			"each partial sum of a lies below the sum of b",
			"∀n:num. Σ_{i∈0 .. n} a(i) ≤ extended_series(b)",
			Derive(func(c *Argument) {
				n := c.FixAs[Nat]()
				c.Show(
					"it lies below the partial sum of b, itself below the sum of b",
					By(
						termwise,
						SumMono.At(a, b, c.TermAs[Set[Nat]]("0 .. n")),
						num_segment.Finite,
						SeriesPartialLe.At(b, n),
						LeTrans))
			}))
		arg.Show(
			"so the sum of a does",
			By(partialsBelow, SeriesLeast.At(a, arg.TermAs[ExtendedNonnegReal]("extended_series(b)"))))
	}),
})}

// ---------------------------------------------------------------------------
// Linearity
// ---------------------------------------------------------------------------

// SeriesAdd — two series add termwise. The partial sums of the sum are
// the sums of the partial sums; those rise, so the supremum of their
// sums is the sum of their suprema; and each side lies below the other.
var SeriesAdd = seriesAddThm{family.Add(registry.ProofEntry{
	Name: "SeriesAdd",
	Key:  "prop_292e4db252726eac",
	Build: family.Theorem("∀a b:(num → extended_nonneg_real). "+
		"    extended_series(λn:num. a(n) + b(n)) = extended_series(a) + extended_series(b)",
		func(arg *Argument, a, b *Arrow[Nat, ExtendedNonnegReal]) {
			partialA := arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λk:num. Σ_{i∈0 .. k} a(i)")
			partialB := arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λk:num. Σ_{i∈0 .. k} b(i)")
			sums := arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. a(n) + b(n)")
			seriesA := arg.TermAs[ExtendedNonnegReal]("extended_series(a)")
			seriesB := arg.TermAs[ExtendedNonnegReal]("extended_series(b)")
			rising := arg.Have(
				"partial sums rise: the next one adds a term",
				"∀c:(num → extended_nonneg_real). ∀n:num. Σ_{i∈0 .. n} c(i) ≤ Σ_{i∈0 .. n + 1} c(i)",
				By(SumSegmentPeel, LeAddRight))
			joint := arg.Have(
				"so the supremum of the sums of partial sums is the sum of the series",
				"extended_sup(image(λk:num. Σ_{i∈0 .. k} a(i) + Σ_{i∈0 .. k} b(i), 𝕌)) = "+
					"extended_series(a) + extended_series(b)",
				By(rising, SupSequenceAdd.At(partialA, partialB), ExtendedSeriesDef))
			above := arg.Have(
				"each partial sum of a + b lies below the sum of the series",
				"∀n:num. Σ_{i∈0 .. n} (a(i) + b(i)) ≤ extended_series(a) + extended_series(b)",
				Derive(func(c *Argument) {
					n := c.FixAs[Nat]()
					c.Show(
						"it is the sum of the partial sums of a and b, each below its series",
						By(
							SumAdd.At(a, b, c.TermAs[Set[Nat]]("0 .. n")),
							num_segment.Finite,
							AddLeAdd.At(
								c.TermAs[ExtendedNonnegReal]("Σ_{i∈0 .. n} a(i)"),
								c.TermAs[ExtendedNonnegReal]("Σ_{i∈0 .. n} b(i)"),
								seriesA,
								seriesB),
							SeriesPartialLe.At(a, n),
							SeriesPartialLe.At(b, n)))
				}))
			below := arg.Have(
				"each sum of partial sums lies below the series of a + b",
				"∀n:num. Σ_{i∈0 .. n} a(i) + Σ_{i∈0 .. n} b(i) ≤ extended_series(λn:num. a(n) + b(n))",
				Derive(func(c *Argument) {
					n := c.FixAs[Nat]()
					c.Show(
						"it is a partial sum of a + b",
						By(SumAdd.At(a, b, c.TermAs[Set[Nat]]("0 .. n")), num_segment.Finite, SeriesPartialLe.At(sums, n)))
				}))
			arg.Show(
				"each side lies below the other",
				By(
					joint,
					above,
					below,
					SeriesLeast.At(sums, arg.TermAs[ExtendedNonnegReal]("extended_series(a) + extended_series(b)")),
					SupSequenceLeast.At(
						arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λk:num. Σ_{i∈0 .. k} a(i) + Σ_{i∈0 .. k} b(i)"),
						arg.TermAs[ExtendedNonnegReal]("extended_series(λn:num. a(n) + b(n))")),
					LeAntisym))
		}),
})}

// SeriesScale — a nonnegative real factor moves through a series: the
// partial sums of the scaled series are the scaled partial sums, whose
// supremum is the scaled supremum.
var SeriesScale = seriesScaleThm{family.Add(registry.ProofEntry{
	Name: "SeriesScale",
	Key:  "prop_68535fff713a74de",
	Build: family.Theorem(Statement{
		Binders:    "∀c:real. ∀a:(num → extended_nonneg_real).",
		Hypotheses: []string{"&0 ≤ c"},
		Conclusion: "extended_series(λn:num. extended_of_real(c) * a(n)) = " +
			"extended_of_real(c) * extended_series(a)",
	}, func(arg *Argument, c *Expr[Real], a *Arrow[Nat, ExtendedNonnegReal], nonneg Fact) {
		factor := arg.TermAs[ExtendedNonnegReal]("extended_of_real(c)")
		scaled := arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. extended_of_real(c) * a(n)")
		partial := arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λk:num. Σ_{i∈0 .. k} a(i)")
		seriesA := arg.TermAs[ExtendedNonnegReal]("extended_series(a)")
		joint := arg.Have(
			"the supremum of the scaled partial sums is c times the series",
			"extended_sup(image(λk:num. extended_of_real(c) * Σ_{i∈0 .. k} a(i), 𝕌)) = "+
				"extended_of_real(c) * extended_series(a)",
			By(nonneg, SupSequenceScale.At(c, partial), ExtendedSeriesDef))
		above := arg.Have(
			"each partial sum of the scaled series lies below c times the series",
			"∀n:num. Σ_{i∈0 .. n} extended_of_real(c) * a(i) ≤ extended_of_real(c) * extended_series(a)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]()
				b.Show(
					"it is c times the partial sum of a, which lies below the series",
					By(
						SumScale.At(factor, a, b.TermAs[Set[Nat]]("0 .. n")),
						num_segment.Finite,
						MulLeMono.At(b.TermAs[ExtendedNonnegReal]("Σ_{i∈0 .. n} a(i)"), seriesA, factor),
						SeriesPartialLe.At(a, n)))
			}))
		below := arg.Have(
			"each scaled partial sum lies below the scaled series",
			"∀n:num. "+
				"    extended_of_real(c) * Σ_{i∈0 .. n} a(i) ≤ extended_series(λn:num. extended_of_real(c) * a(n))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]()
				b.Show(
					"it is a partial sum of the scaled series",
					By(
						SumScale.At(factor, a, b.TermAs[Set[Nat]]("0 .. n")),
						num_segment.Finite,
						SeriesPartialLe.At(scaled, n)))
			}))
		arg.Show(
			"each side lies below the other",
			By(
				joint,
				above,
				below,
				SeriesLeast.At(scaled, arg.TermAs[ExtendedNonnegReal]("extended_of_real(c) * extended_series(a)")),
				SupSequenceLeast.At(
					arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λk:num. extended_of_real(c) * Σ_{i∈0 .. k} a(i)"),
					arg.TermAs[ExtendedNonnegReal]("extended_series(λn:num. extended_of_real(c) * a(n))")),
				LeAntisym))
	}),
})}

// SeriesZero — the series of zeros sums to 0: every partial sum is 0.
var SeriesZero = seriesZeroThm{family.Add(registry.ProofEntry{
	Name: "SeriesZero",
	Key:  "prop_69b5d11346ca0e59",
	Build: family.Theorem("extended_series(λn:num. &0) = &0",
		func(a *Argument) {
			zero := a.TermAs[ExtendedNonnegReal]("&0")
			// The summand keeps its name: a bare &0 in a Σ body has no
			// partner to read it into ⟦0, ∞⟧, and reads on the real line.
			partials := a.Have(
				"every partial sum of zeros is 0",
				"∀n:num. Σ_{i∈0 .. n} extended_of_real(&0) = &0",
				By(ExtendedSumZero))
			a.Show(
				"the sum lies below 0, the least value",
				By(
					partials,
					SeriesLeast.At(a.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. &0"), zero),
					LeRefl,
					ZeroLe,
					LeAntisym))
		}),
})}

// ---------------------------------------------------------------------------
// Series of reals, and double series
// ---------------------------------------------------------------------------

// SeriesOfRealPartialLe — when a series of nonnegative reals has a finite
// sum in ⟦0, ∞⟧, every real partial sum lies below the value t of that
// sum: the image of the partial sum is a partial sum of the images, below
// the sum, which is the image of t.
var SeriesOfRealPartialLe = seriesOfRealPartialLeThm{family.Add(registry.ProofEntry{
	Name: "SeriesOfRealPartialLe",
	Key:  "prop_2b26923b3f89e86d",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀n:num.",
		Hypotheses: []string{
			"∀k:num. &0 ≤ a(k)",
			"«imageSum» ≠ extended_infinity",
		},
		Conclusion: "Σ_{i∈0 .. n} a(i) ≤ extended_to_real(«imageSum»)",
		Abbrev: Abbrev{
			{Name: "imageSum", Text: "extended_series(λk:num. extended_of_real(a(k)))"},
		},
	}, func(arg *Argument, a *Arrow[Nat, Real], n *Expr[Nat], nonneg, finite Fact) {
		images := arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λk:num. extended_of_real(a(k))")
		total := arg.TermAs[ExtendedNonnegReal]("«imageSum»")
		arg.Show(
			"the image of the partial sum is a partial sum of the images, below the sum, the image of t",
			By(
				nonneg,
				finite,
				SumOfReal.At(a, arg.TermAs[Set[Nat]]("0 .. n")),
				num_segment.Finite,
				SeriesPartialLe.At(images, n),
				OfRealToReal.At(total),
				ToRealNonneg.At(total),
				OfRealLe.At(
					arg.TermAs[Real]("Σ_{i∈0 .. n} a(i)"), arg.TermAs[Real]("extended_to_real(«imageSum»)"))))
	}),
})}

// SeriesOfReal — a series of nonnegative reals summing to s sums in
// ⟦0, ∞⟧ to the image of s. Each partial sum embeds as the image of the
// real partial sum, below the image of s; and where the extended sum is
// finite its value bounds every real partial sum, hence their limit s.
var SeriesOfReal = seriesOfRealThm{family.Add(registry.ProofEntry{
	Name: "SeriesOfReal",
	Key:  "prop_9c9692340b5f22ca",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀s:real.",
		Hypotheses: []string{
			"∀n:num. &0 ≤ a(n)",
			"real_sums(a, s)",
		},
		Conclusion: "extended_series(λn:num. extended_of_real(a(n))) = extended_of_real(s)",
		Abbrev: Abbrev{
			{Name: "imageSum", Text: "extended_series(λn:num. extended_of_real(a(n)))"},
		},
	}, func(arg *Argument, a *Arrow[Nat, Real], s *Expr[Real], nonneg, sums Fact) {
		images := arg.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. extended_of_real(a(n))")
		partials := arg.Have(
			"each partial sum of the images is the image of the partial sum",
			"∀n:num. Σ_{i∈0 .. n} extended_of_real(a(i)) = extended_of_real(Σ_{i∈0 .. n} a(i))",
			By(nonneg, SumOfReal, num_segment.Finite))
		belowS := arg.Have(
			"the partial sums lie below s",
			"∀n:num. Σ_{i∈0 .. n} a(i) ≤ s",
			By(nonneg, sums, real_series.SumsPartialLessEq))
		sNonneg := arg.Have(
			"s lies above the first partial sum, which is nonnegative",
			"&0 ≤ s",
			ByArith(
				belowS.At(arg.TermAs[Nat]("0")),
				nonneg,
				real_sum.Nonneg.At(arg.TermAs[Set[Nat]]("0 .. 0"), a)))
		above := arg.Have(
			"so the sum of the images lies below the image of s",
			"«imageSum» ≤ extended_of_real(s)",
			By(
				partials,
				belowS,
				sNonneg,
				SeriesLeast.At(images, arg.TermAs[ExtendedNonnegReal]("extended_of_real(s)")),
				OfRealLe))
		reach := arg.Have(
			"and the image of s lies below the sum of the images",
			"extended_of_real(s) ≤ «imageSum»",
			Derive(func(b *Argument) {
				b.Cases(b.Term("«imageSum» = extended_infinity"))
				b.When(
					"an infinite sum lies above everything",
					func(c *Argument, infinite Fact) {
						c.Do(infinite.Rw())
						c.Show(
							"the image of s lies below ∞",
							Cite(LeInfinity))
					})
				b.Otherwise(
					"a finite sum has a value t, which bounds every real partial sum, hence their limit s",
					func(c *Argument, finite Fact) {
						total := c.TermAs[ExtendedNonnegReal]("«imageSum»")
						value := c.TermAs[Real]("extended_to_real(«imageSum»)")
						limitBound := c.Have(
							"every real partial sum lies below t, so their limit s does",
							"s ≤ extended_to_real(«imageSum»)",
							By(
								nonneg,
								finite,
								At(SeriesOfRealPartialLe, a),
								sums,
								real_series.RealSumsDef.At(a, s),
								real_sequences.LimitLessEqBound.At(
									c.TermAs[Fun[Nat, Real]]("λn:num. Σ_{k∈0 .. n} a(k)"),
									s,
									value)))
						c.Show(
							"the image of s lies below the image of t, which is the sum",
							By(finite, limitBound, OfRealToReal.At(total), ToRealNonneg.At(total), OfRealLe.At(s, value)))
					})
			}))
		arg.Show(
			"each side lies below the other",
			By(above, reach, LeAntisym))
	}),
})}

// SeriesFinite — a series of nonnegative reals whose extended sum is
// finite converges to the value of that sum. Its partial sums rise and
// lie below that value, so they converge to their supremum L; and the
// extended sum is then the image of L, whose value is L.
var SeriesFinite = seriesFiniteThm{family.Add(registry.ProofEntry{
	Name: "SeriesFinite",
	Key:  "prop_6afd57dda367d467",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real).",
		Hypotheses: []string{
			"∀n:num. &0 ≤ a(n)",
			"extended_series(λn:num. extended_of_real(a(n))) ≠ extended_infinity",
		},
		Conclusion: "real_sums(a, extended_to_real(extended_series(λn:num. extended_of_real(a(n)))))",
		Abbrev: Abbrev{
			{Name: "imageSum", Text: "extended_series(λn:num. extended_of_real(a(n)))"},
			{Name: "limit", Text: "sup(image(λk:num. Σ_{i∈0 .. k} a(i), 𝕌))"},
		},
	}, func(arg *Argument, a *Arrow[Nat, Real], nonneg, finite Fact) {
		value := arg.TermAs[Real]("extended_to_real(«imageSum»)")
		limit := arg.TermAs[Real]("«limit»")
		rising := arg.Have(
			"the partial sums rise, the terms being nonnegative",
			"∀n:num. Σ_{i∈0 .. n} a(i) ≤ Σ_{i∈0 .. n + 1} a(i)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]()
				one := b.TermAs[Nat]("1")
				b.Show(
					"the segment up to n + 1 extends the one up to n by a nonnegative term",
					By(
						nonneg,
						real_sum.IntervalExtend.At(b.TermAs[Nat]("0"), n, b.TermAs[Nat]("n + 1"), a),
						nat_order.LessEqAdd.At(n, one)))
			}))
		converges := arg.Have(
			"rising, and bounded by the value t of the extended "+
				"sum, the partial sums converge to their supremum",
			"real_sums(a, «limit»)",
			By(
				nonneg,
				finite,
				At(SeriesOfRealPartialLe, a),
				rising,
				real_series.RealSumsDef,
				real_sequences.IncreasingBoundedConvergesToSup.At(
					arg.TermAs[Fun[Nat, Real]]("λk:num. Σ_{i∈0 .. k} a(i)"),
					value)))
		limitNonneg := arg.Have(
			"the limit lies above the first partial sum, which is nonnegative",
			"&0 ≤ «limit»",
			ByArith(
				nonneg,
				converges,
				real_series.SumsPartialLessEq.At(a, limit, arg.TermAs[Nat]("0")),
				real_sum.Nonneg.At(arg.TermAs[Set[Nat]]("0 .. 0"), a)))
		arg.Show(
			"the extended sum is the image of the limit, whose value is the limit",
			By(nonneg, limitNonneg, converges, SeriesOfReal.At(a, limit), ToRealOfReal.At(limit)))
	}),
})}

// SeriesGeometric — the halving series e/2 + e/4 + … sums to e: it is
// e/2 times the powers of a half, which sum to 2.
var SeriesGeometric = seriesGeometricThm{family.Add(registry.ProofEntry{
	Name: "SeriesGeometric",
	Key:  "prop_ef1f227416a4ce91",
	Build: family.Theorem(Statement{
		Binders:    "∀e:real.",
		Hypotheses: []string{"&0 ≤ e"},
		Conclusion: "extended_series(λn:num. extended_of_real(e / real_pow(&2, n + 1))) = " +
			"extended_of_real(e)",
	}, func(arg *Argument, e *Expr[Real], nonneg Fact) {
		half := arg.TermAs[Real]("real_inv(&2)")
		halfFacts := arg.Have(
			"a half is smaller than 1 in size, and 1 minus a half is a half",
			"real_abs(real_inv(&2)) < &1 ∧ real_inv(&1 - real_inv(&2)) = &2",
			ByArith(real_construction.MulLeftInverse.At(arg.TermAs[Real]("&1 - real_inv(&2)"))))
		powersOfHalf := arg.Have(
			"so the powers of a half sum to 2",
			"real_sums(λn:num. real_pow(real_inv(&2), n), &2)",
			By(halfFacts, real_series.Geometric.At(half)))
		halving := arg.Have(
			"each term is e/2 times a power of a half",
			"∀n:num. e / real_pow(&2, n + 1) = e * real_inv(&2) * real_pow(real_inv(&2), n)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]()
				b.Do(Simp(
					Fwd(real_field.RealDivDef),
					Fwd(real_pow.PowAddOne),
					Fwd(field.InvMul.Read(real_field.Field)),
					Rev(real_pow.InvPow)))
				b.Show(
					"the factors regroup",
					By(real_construction.MulAssoc))
			}))
		termsNonneg := arg.Have(
			"the terms are nonnegative",
			"∀n:num. &0 ≤ e / real_pow(&2, n + 1)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]()
				power := b.TermAs[Real]("real_pow(real_inv(&2), n)")
				b.Show(
					"e/2 and the power of a half are nonnegative",
					ByArith(
						halving.At(n),
						nonneg,
						real_pow.PowNonneg.At(half, n),
						real_order_ring.LessEqMulLeft.At(b.TermAs[Real]("e * real_inv(&2)"), b.TermAs[Real]("&0"), power)))
			}))
		twoHalves := arg.Have(
			"e/2 times 2 is e",
			"e * real_inv(&2) * &2 = e",
			ByArith())
		realSum := arg.Have(
			"so the terms sum to e",
			"real_sums(λn:num. e / real_pow(&2, n + 1), e)",
			Simp(Fwd(halving)),
			By(
				twoHalves,
				powersOfHalf,
				real_series.SumsScale.At(
					arg.TermAs[Fun[Nat, Real]]("λn:num. real_pow(real_inv(&2), n)"),
					arg.TermAs[Real]("&2"),
					arg.TermAs[Real]("e * real_inv(&2)"))))
		arg.Show(
			"a series of nonnegative reals sums to the image of its real sum",
			By(
				termsNonneg,
				realSum,
				SeriesOfReal.At(arg.TermAs[Fun[Nat, Real]]("λn:num. e / real_pow(&2, n + 1)"), e)))
	}),
})}

// SeriesSegmentSum — a finite sum of series is the series of the finite
// sums. By induction on the number of rows: one more row adds its series
// on the left, and the series of a termwise sum is the sum of the series
// on the right.
var SeriesSegmentSum = seriesSegmentSumThm{family.Add(registry.ProofEntry{
	Name: "SeriesSegmentSum",
	Key:  "prop_56b9c65f00c8b057",
	Build: family.Theorem("∀a:(num → num → extended_nonneg_real). ∀M:num. "+
		"    Σ_{m∈0 .. M} extended_series(λn:num. a(m, n)) = extended_series(λn:num. Σ_{m∈0 .. M} a(m, n))",
		func(arg *Argument, a *Arrow2[Nat, Nat, ExtendedNonnegReal]) {
			M := arg.Binder("M")
			arg.Induct(M)
			arg.Base(
				"one row: both sides are the series of row 0",
				Simp(Fwd(SumSegmentZero)),
				Refl())
			arg.Step(
				"one more row adds its series to both sides",
				func(b *Argument, previous Fact) {
					b.Do(Simp(Fwd(nat_arith.Add1), Fwd(SumSegmentPeel)))
					b.Show(
						"the series of a termwise sum is the sum of the series",
						By(
							previous,
							SeriesAdd.At(
								b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. Σ_{i∈0 .. M} a(i, n)"),
								b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. a(M + 1, n)"))))
				})
		}),
})}

// SeriesExchange — a double series of ⟦0, ∞⟧ terms sums to the same
// value in either order. The first M + 1 rows sum to the series of the
// column partial sums, each below its column's series; so the row-first
// sum lies below the column-first one, and by symmetry above it.
var SeriesExchange = seriesExchangeThm{family.Add(registry.ProofEntry{
	Name: "SeriesExchange",
	Key:  "prop_e043c07210d23e57",
	Build: family.Sections("∀a:(num → num → extended_nonneg_real). "+
		"    extended_series(λm:num. extended_series(λn:num. a(m, n))) = "+
		"    extended_series(λn:num. extended_series(λm:num. a(m, n)))",
		func(ctx *Script, headline string) *GoalStackNode {
			rowsFirstBelow := ctx.Lemma("∀a:(num → num → extended_nonneg_real). "+
				"    extended_series(λm:num. extended_series(λn:num. a(m, n))) ≤ "+
				"    extended_series(λn:num. extended_series(λm:num. a(m, n)))",
				func(arg *Argument, a *Arrow2[Nat, Nat, ExtendedNonnegReal]) {
					rowsBelow := arg.Have(
						"the first M + 1 rows sum below the column-first series",
						"∀M:num. "+
							"    Σ_{m∈0 .. M} extended_series(λn:num. a(m, n)) ≤ "+
							"    extended_series(λn:num. extended_series(λm:num. a(m, n)))",
						Derive(func(b *Argument) {
							M := b.FixAs[Nat]()
							b.Show(
								"they sum to the series of column partial sums, each below its column's series",
								By(
									SeriesSegmentSum.At(a, M),
									SeriesMono.At(
										b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. Σ_{m∈0 .. M} a(m, n)"),
										b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. extended_series(λm:num. a(m, n))")),
									SeriesPartialLe))
						}))
					arg.Show(
						"so the row-first series lies below it",
						By(rowsBelow, SeriesLeast))
				})
			return ctx.Theorem(headline, func(arg *Argument, a *Arrow2[Nat, Nat, ExtendedNonnegReal]) {
				arg.Show(
					"each order of summation lies below the other",
					By(
						At(rowsFirstBelow, a),
						At(rowsFirstBelow, arg.TermAs[Fun2[Nat, Nat, ExtendedNonnegReal]]("λn:num. λm:num. a(m, n)")),
						LeAntisym))
			})
		}),
})}
