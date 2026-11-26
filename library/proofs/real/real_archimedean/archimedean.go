// archimedean.go — ℕ is unbounded in ℝ, and the restatements of saying
// so; then the first thing the embedding of ℕ says about ℝ as a SET.
//
// README §"The chapter's arc", movements 1–5: the unbounded statement
// itself, its strict form, the property as classically stated, the same
// fact read backwards as a statement about how small 1/n gets, and its
// 1/(n + 1) form. The set-theoretic reading of the same embedding is
// here too: the reals are infinite, because the naturals are and &
// never identifies two of them.

package real_archimedean

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_completeness"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ExistsNumAbove — every real is at or below some natural number.
//
// This is the chapter's one analytic argument and the only place
// completeness is used. Suppose some x had no natural above it. Totality
// reads that as the statement that every &n sits below x, so the
// naturals form a set of reals bounded above, and completeness hands
// them a least upper bound M. But the naturals are closed under adding
// one, so M - &1 bounds them too; M being LEAST then forces M ≤ M - &1,
// and no real satisfies that.
//
// The last step is elementary order algebra rather than anything about
// ℕ: M ≤ M - &1 says M + &1 ≤ M, while &0 < &1 says M < M + &1.
var ExistsNumAbove = existsNumAboveThm{family.Add(registry.ProofEntry{
	Name: "ExistsNumAbove",
	Key:  "prop_c2839f6c8ed9c5ef",
	// Four sections read top-down as the argument above reads: the two order
	// facts the contradiction needs, the completeness application, and the
	// headline that puts them together. The Go locals are how the headline
	// reaches the three lemmas.
	Build: family.Sections("∀x:real. ∃n:num. x ≤ &n",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// No real lies at or below itself minus one.
			notLessEqSubOne := ctx.Lemma("∀M:real. ¬(M ≤ M - &1)",
				func(a *Argument, M Term) {
					step := a.Have(
						"the step up by one is strict, because the unit is positive",
						"M < M + &1",
						// Consumed as a rewrite of the claim rather than as a
						// premise, so it takes no witnesses: ↦ &0 < &1.
						Cite(real_order_ring.LessThanSelfAddRight),
						// which IS that comparison, so the cite closes the claim.
						Cite(real_order_ring.ZeroLessThanOne))

					a.Show(
						"and M₀ ≤ M₀ - &1 says exactly that M₀ + &1 lies at or below M₀",
						By(
							step,
							// ↦ M₀ + &1 ≤ M₀
							real_order_ring.LessEqSubAddLeft,
							// ¬(M₀ < M₀ + &1) ⇔ M₀ + &1 ≤ M₀
							At(real_order_ring.NotLessThan, M, a.Ctx().TermText("M₀ + &1"))))
				})

			// An upper bound for the naturals has one to spare: the naturals
			// contain each n + 1, so a bound on those is a bound on the &n
			// shifted down by the unit.
			boundShiftsDown := ctx.Lemma(Statement{
				Binders: "∀M:real.",
				Hypotheses: []string{
					"∀n:num. &n ≤ M",
				},
				Conclusion: "∀n:num. &n ≤ M - &1",
			},
				func(a *Argument, M Term, bounds Fact) {
					n := a.Fix()
					one := a.Ctx().Numeral(1)

					next := a.Have(
						"n + 1 is a natural too, so the bound covers it",
						"&(n + 1) ≤ M",
						By(bounds))

					a.Show(
						"and the embedding carries that successor to &n₀ + &1",
						By(
							next,
							At(real_construction.OfNumAdd, n, one), // &(n₀ + 1) = &n₀ + &1
							At(real_order_ring.LessEqSubAddLeft, // &n₀ ≤ M₀ - &1 ⇔ &n₀ + &1 ≤ M₀
								v.Embed(n), M, v.Lit(1))))
				})

			// Completeness, applied to the naturals: bounded above, they have a
			// least upper bound. Completeness speaks of a SET of reals, so the
			// step across is naming the set {y | y = &n for some n} and reading
			// its bounds back as bounds on the &n.
			natsHaveLeastBound := ctx.Lemma(
				Statement{
					Binders: "∀x:real.",
					Hypotheses: []string{
						"∀n:num. &n ≤ x",
					},
					Conclusion: "∃M:real. (∀n:num. &n ≤ M) ∧ (∀M₂:real. (∀n:num. &n ≤ M₂) ⇒ M ≤ M₂)",
				},
				func(a *Argument, x Term, bounds Fact) {
					// The set is λy. y is some &n; completeness asks it to be
					// inhabited and bounded above, and &0 and x₀ are the witnesses.
					premises := a.Have(
						"that set is nonempty, &0 being in it, and x₀ bounds it",
						"(∃y:real. ∃n:num. y = &n) ∧ (∃M:real. ∀y:real. (∃n:num. y = &n) ⇒ y ≤ M)",
						By(bounds))

					asSet := a.Have(
						"so it has a least upper bound",
						"∃M:real. "+
							"    (∀y:real. (∃n:num. y = &n) ⇒ y ≤ M) ∧ ∀M₂:real. (∀y:real. (∃n:num. y = &n) ⇒ y ≤ M₂) ⇒ M ≤ M₂",
						By(premises, real_completeness.RealComplete))

					a.Show(
						"and a real bounds every member of that set exactly when it bounds every &n",
						By(Normalized, asSet))
				})

			return ctx.Theorem(headline,
				func(a *Argument, x Term) {
					noneAbove := a.SupposeNot()

					allBelow := a.Have(
						"with no natural above x, totality puts every &n below it",
						"∀n:num. &n ≤ x",
						By(Normalized, noneAbove, real_construction.LessEqTotal))

					M, lub := a.Obtain(
						"so the naturals have a least upper bound M₀",
						"∃M:real. (∀n:num. &n ≤ M) ∧ (∀M₂:real. (∀n:num. &n ≤ M₂) ⇒ M ≤ M₂)",
						By(allBelow, At(natsHaveLeastBound, x)))

					least := a.Have(
						"no real below M bounds the naturals — that is what least says",
						"∀M₂:real. (∀n:num. &n ≤ M₂) ⇒ M ≤ M₂",
						By(lub))

					shifted := a.Have(
						"yet M - &1 bounds them as well",
						"∀n:num. &n ≤ M - &1",
						By(lub, At(boundShiftsDown, M)))

					a.Show(
						"so leastness puts M₀ at or below M₀ - &1, which no real is",
						By(shifted, least.At(v.Sub1(M)), notLessEqSubOne))
				})
		}),
})}

// ExistsNumStrictlyAbove — the strict form: every real is STRICTLY below
// some natural number.
//
// One natural more than a weak bound is a strict one. Adding the unit to
// a bound makes it strict, and the embedding carries the successor —
// &(n + 1) is &n + &1 — so the natural the weak statement produces has
// its own successor to hand over.
var ExistsNumStrictlyAbove = existsNumStrictlyAboveThm{family.Add(registry.ProofEntry{
	Name: "ExistsNumStrictlyAbove",
	Key:  "prop_d503a75f7d96c89e",
	Build: family.Theorem("∀x:real. ∃n:num. x < &n",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())

			n, weak := a.Obtain(
				"x lies at or below some natural",
				"∃n:num. x ≤ &n",
				By(ExistsNumAbove))

			strict := a.Have(
				"one past that bound clears x strictly",
				"x < &(n + 1)",
				By(
					weak,
					// x₀ ≤ &n₀ ⇒ x₀ < &n₀ + &1
					At(real_order_ring.LessThanAddOne, x, v.Embed(n)),
					real_construction.OfNumAdd))

			a.Show(
				"so n₀ + 1 is the natural the statement asks for",
				By(Normalized, strict))
		}),
})}

// ExistsNumBounds — every real lies between −n and n for some natural n:
// some n is at least x and some m at least −x, and n + m, at least each
// of them, bounds x on both sides.
var ExistsNumBounds = existsNumBoundsThm{family.Add(registry.ProofEntry{
	Name: "ExistsNumBounds",
	Key:  "prop_6467009121be742f",
	Build: family.Theorem("∀x:real. ∃n:num. -&n ≤ x ∧ x ≤ &n",
		func(arg *Argument, x *Expr[Real]) {
			n, above := arg.ObtainAs[Nat](
				"some natural n is at least x",
				"∃n:num. x ≤ &n",
				By(ExistsNumAbove.At(x)))
			m, below := arg.ObtainAs[Nat](
				"and some natural m is at least −x",
				"∃m:num. -x ≤ &m",
				By(ExistsNumAbove.At(arg.TermAs[Real]("-x"))))
			arg.Take(arg.TermAs[Nat]("n + m"))
			arg.Show(
				"n + m is at least n and at least m, both being nonnegative",
				ByArith(
					above,
					below,
					real_construction.OfNumAdd.At(n, m),
					real_order_ring.NumNonneg.At(n),
					real_order_ring.NumNonneg.At(m)))
		}),
})}

// Archimedean — the property as it is classically stated: no matter how
// small a positive step x is, some whole number of steps passes any
// target y.
//
// Dividing by the step turns that into a statement about a single real:
// the multiples of x pass y exactly when some natural passes y / x,
// which is the strict form. The positivity of x is what licenses
// multiplying the comparison back through.
var Archimedean = archimedeanThm{family.Add(registry.ProofEntry{
	Name: "Archimedean",
	Key:  "prop_a92c9a82b655e0ee",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"&0 < x",
		},
		Conclusion: "∃n:num. y < &n * x",
	},
		func(a *Argument, x, y Term, pos Fact) {
			v := ops(a.Ctx())

			n, clears := a.Obtain(
				"some natural is strictly above that quotient",
				"∃n:num. y / x < &n",
				By(ExistsNumStrictlyAbove))

			a.Show(
				"x₀ is positive, so that comparison multiplies back through by x₀",
				By(
					Normalized,
					pos,
					clears,
					// &0 < x₀ ⇒ (y₀ / x₀ < &n₀ ⇔ y₀ < &n₀ * x₀)
					At(real_order_field.LessThanDivMulRight, y, v.Embed(n), x)))
		}),
})}

// PosIffExistsSmallInv — the property read backwards: a real is positive
// exactly when some 1/n fits strictly under it.
//
// One direction is nothing but transitivity — 1/n is positive and lies
// below e, so e is positive. The other is the strict form applied to
// 1/e: some natural passes 1/e, and inverting a comparison between
// positives reverses it, so 1/n drops below 1/(1/e), which is e. That
// natural is nonzero because &n has to clear the positive 1/e, and on ℕ
// positivity is non-zeroness.
var PosIffExistsSmallInv = posIffExistsSmallInvThm{family.Add(registry.ProofEntry{
	Name: "PosIffExistsSmallInv",
	Key:  "prop_a17ae212014f0680",
	Build: family.Theorem("∀e:real. &0 < e ⇔ ∃n:num. n ≠ 0 ∧ &0 < real_inv(&n) ∧ real_inv(&n) < e",
		func(a *Argument, e Term) {
			v := ops(a.Ctx())
			zero, zeroNum := v.Lit(0), a.Ctx().Numeral(0)
			invE := v.Invert(e)

			a.Iff()
			a.Forward(
				"the strict form at real_inv(e₀) names the reciprocal",
				func(b *Argument, pos Fact) {
					invPos := b.Have(
						"a positive real has a positive reciprocal",
						"&0 < real_inv(e₀)",
						By(pos, real_order_field.InvPos))

					n, above := b.Obtain(
						"and some natural clears that reciprocal",
						"∃n:num. real_inv(e₀) < &n",
						By(ExistsNumStrictlyAbove))

					embedded := v.Embed(n)
					embedPos := b.Have(
						"&n₀ is positive, sitting above a positive real",
						"&0 < &n₀",
						By(invPos, above, At(real_order_ring.LessThanTrans, zero, invE, embedded)))

					b.Take(n)
					b.Do(SplitConjAll(
						Case(
							"n₀ ≠ 0: on ℕ, positivity IS non-zeroness",
							By(
								embedPos,
								At(real_order_ring.OfNumLessThan, zeroNum, n), // &0 < &n₀ ⇔ 0 < n₀
								nat_order.PosIffNonzero)),

						Case(
							"&0 < real_inv(&n₀): the reciprocal of a positive real",
							By(embedPos, real_order_field.InvPos)),

						Case(
							"real_inv(&n₀) < e₀: inverting real_inv(e₀) < &n₀ reverses it",
							By(
								invPos,
								above,
								// &0 < real_inv(e₀) ∧ real_inv(e₀) < &n₀
								// ⇒ real_inv(&n₀) < real_inv(real_inv(e₀))
								At(real_order_field.InvAntitone, invE, embedded),
								// and inverting twice returns e₀
								field.InvInv.Read(real_field.Field))),
					))
				})
			a.Backward(
				"e₀ inherits the positivity of a reciprocal that lies under it",
				func(b *Argument, small Fact) {
					n, at := b.Unpack(small)
					b.Show(
						"&0 < real_inv(&n₀) and real_inv(&n₀) < e₀ chain",
						By(at, At(real_order_ring.LessThanTrans, zero, v.Invert(v.Embed(n)), e)))
				})
		}),
})}

// ExistsReciprocalBelow — every positive real exceeds some 1/(n + 1): it
// exceeds some 1/m with m ≠ 0, and 1/(m + 1) is smaller still. The
// successor form needs no side condition on n.
var ExistsReciprocalBelow = existsReciprocalBelowThm{family.Add(registry.ProofEntry{
	Name: "ExistsReciprocalBelow",
	Key:  "prop_324c459b1f90bef1",
	Build: family.Theorem(Statement{
		Binders:    "∀e:real.",
		Hypotheses: []string{"&0 < e"},
		Conclusion: "∃n:num. real_inv(&n + &1) < e",
	}, func(a *Argument, e *Expr[Real], positive Fact) {
		m, small := a.ObtainAs[Nat](
			"the Archimedean property puts some 1/m, m ≠ 0, strictly between 0 and e",
			"∃m:num. m ≠ 0 ∧ &0 < real_inv(&m) ∧ real_inv(&m) < e",
			By(positive, PosIffExistsSmallInv.At(e)))
		a.Take(m)
		mReal := a.TermAs[Real]("&m")
		a.Show(
			"1/(m + 1) lies below 1/m, m being positive since 1/m is",
			ByArith(
				small,
				real_order_field.InvPos.At(mReal),
				real_order_field.InvAntitone.At(mReal, a.TermAs[Real]("&m + &1"))))
	}),
})}

// Infinite — the reals are not a finite set.
//
// The naturals are not (num_segment.Infinite), and the embedding &
// never identifies two of them (real_construction.OfNumEq), so it carries them to
// an infinite set of reals; and a set that contains an infinite set is
// infinite itself.
//
// This is the chapter's one member about ℝ as a SET rather than as an
// order, which is why the set chapters enter here and nowhere else in
// the file.
var Infinite = infiniteThm{family.Add(registry.ProofEntry{
	Name: "Infinite",
	Key:  "prop_4e8de0bf272f4112",
	// The two universes are nullary, so each takes its element type
	// from its annotation. The set laws are polymorphic and read here at
	// num and real — the wrappers' explicit instances, grounded in the
	// laws' own stated binder order. The premises meet the goal without a
	// refutation anywhere in the member.
	Build: family.Theorem(Statement{
		Conclusion: "infinite(𝕌⟨A:real⟩)",
	},
		func(a *Argument) {
			v := ops(a.Ctx())
			numbers := a.Ctx().TermText("𝕌⟨A:num⟩")
			reals := a.Ctx().TermText("𝕌⟨A:real⟩")
			embedded := a.Ctx().TermText("image(real_of_num, 𝕌⟨A:num⟩)") // the naturals, as reals

			injective := a.Have(
				"& never identifies two naturals",
				"injective_on(𝕌⟨A:num⟩, real_of_num)",
				Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Real]()))),
				By(real_construction.OfNumEq))

			image := a.Have(
				"& is injective, so it carries the infinite set of naturals to an infinite set of reals",
				"infinite(image(real_of_num, 𝕌⟨A:num⟩))",
				By(
					num_segment.Infinite,
					injective,
					// injective_on(𝕌, &) ⇒ infinite(𝕌) ⇒ infinite(image(&, 𝕌))
					finite_set.InfiniteImageInj.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Real]()).At(
						v.OfNum, numbers)))

			a.Show(
				"and that set lies in ℝ's universe, which is therefore infinite as well",
				By(
					image,
					set_order.SubsetUniv.Inst[Real]().At(embedded), // image(&, 𝕌) ⊆ 𝕌
					// infinite(image(&, 𝕌)) ∧ image(&, 𝕌) ⊆ 𝕌 ⇒ infinite(𝕌)
					finite_set.InfiniteSuperset.Inst[Real]().At(embedded, reals)))
		}),
})}
