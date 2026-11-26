// carrier.go — the chapter: dimensioned tuples with the dimension as a number.
//
// Five parts, marked by banners:
//
// - The carrier's block laws
// - Membership preservation for the carrier operations
// - The carrier's decomposition laws
// - The truncation laws
// - The quantifier-transport laws

package carrier

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The carrier's block laws
// ---------------------------------------------------------------------------
//
// the carrier's block laws: what "same tuple" means, that the high block
// of a concatenation reads back, and that a concatenation determines its
// blocks.
//
// All are term-level TWINS of the statements a development with the
// dimension in the type makes, read
// through one mechanical translation: the type-level dimension of `A^N`
// becomes an ordinary ∀-quantified num, `dimindex` becomes that
// variable, a component read becomes function application, and every
// carrier-typed binder is uniformly relativized by the membership
// `tuple`. The twin literals below are that translation's output.
//
// Statements are written over the chapter's minted constants
// (vocab.go); a body cites a defining equation as
// `a.Ctx().ConstDefNormalized("tuple")` where it consumes one.

// Extensionality — two tuples of the same dimension are equal exactly
// when their active entries agree.
//
// The forward direction is congruence. The backward direction is the
// membership's whole content: past the active range NEITHER tuple says
// anything of its own — both read the junk element, so agreement on
// the range is agreement everywhere, and function extensionality
// closes. This is the law that lets the chapter use plain `=` where
// the cart original leans on its type: the normalization convention is
// doing the work `dimindex` does there.
var Extensionality = extensionalityThm{family.Add(registry.ProofEntry{
	Name: "Extensionality",
	Key:  "prop_b9f66c59c888865a",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀y x:(num → A).",
		Hypotheses: []string{
			"tuple(n, y)",
			"tuple(n, x)",
		},
		Conclusion: "(∀i. ¬(i < n) ∨ y(i) = x(i)) ⇔ y = x",
	},
		func(a *Argument, n, y, x Term, memY, memX Fact) {
			tupleDef := a.Ctx().ConstDefNormalized("tuple")
			backward := a.Have(
				"range agreement forces equality — outside it both read junk",
				"(∀i:num. ¬(i < n) ∨ (y(i) = x(i))) ⇒ y = x",
				Derive(func(b *Argument) {
					agree := b.Assume()
					b.Do(Funext(), By(agree, tupleDef, memY, memX))
				}))
			a.Do(By(backward))
		}),
})}

// HighBlockRoundTrip — reading the high block back off a concatenation
// returns the high tuple.
//
// One computation at every index: the drop is bare precomposition, the
// shifted position can never land in the low block (i + n < n is
// impossible outright — no positivity case), and the offset unshifts
// to the index itself.
var HighBlockRoundTrip = highBlockRoundTripThm{family.Add(registry.ProofEntry{
	Name: "HighBlockRoundTrip",
	Key:  "prop_4d403d9af120c15e",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num. ∀y x:(num → A).",
		Conclusion: "y = tuple_drop(n, tuple_cat(n, x, y))",
	},
		func(a *Argument, n, y, x Term) {
			catDef := a.Ctx().ConstDefNormalized("tuple_cat")
			dropDef := a.Ctx().ConstDefNormalized("tuple_drop")
			dropRead := a.Have(
				"the drop is bare precomposition past the cut",
				"∀i:num. tuple_drop(n, tuple_cat(n, x, y), i) = tuple_cat(n, x, y, i + n)",
				By(dropDef))
			pastCut := a.Have(
				"a shifted index never lands in the low block",
				"∀i:num. ¬(i + n < n)",
				ByArith())
			unshift := a.Have(
				"unshifting is the identity",
				"∀i:num. (i + n) - n = i",
				By(nat_monus.AddSubCancel))
			catRead := a.Have(
				"where the concatenation reads the high tuple, unshifted",
				"∀i:num. tuple_cat(n, x, y, i + n) = y((i + n) - n)",
				By(catDef, pastCut))
			pointwise := a.Have(
				"each index reads the high tuple",
				"∀i:num. tuple_drop(n, tuple_cat(n, x, y), i) = y(i)",
				By(dropRead, catRead, unshift))
			a.Do(Funext(), By(pointwise))
		}),
})}

// ConcatInjectivity — laying two tuples end to end loses nothing: two
// concatenations at one cut are equal exactly when their blocks are.
//
// The backward direction is congruence. Forward, the low tuples are
// recovered on their active range and close through Extensionality at
// the cut n; the high tuples need no extensionality at all — the drop
// side of the equality is total, so reading it at every shifted index
// hands over pointwise agreement EVERYWHERE, and Funext closes
// directly. The low recovery works in the dimension-refined vocabulary
// (vectors.go): Inhabit pairs each tuple with its membership once —
// the phantom checked against what the fact actually says — and the
// Extensionality cite writes no dimension terms: AtVec witnesses with
// its memberships' own dimension, so citing the law at a foreign
// dimension is a compile error rather than a refutation puzzle.
var ConcatInjectivity = concatInjectivityThm{family.Add(registry.ProofEntry{
	Name: "ConcatInjectivity",
	Key:  "prop_119851eca8c419f1",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀y z x w:(num → A).",
		Hypotheses: []string{
			"tuple(n, x)",
			"tuple(n, w)",
		},
		Conclusion: "tuple_cat(n, x, y) = tuple_cat(n, w, z) ⇔ x = w ∧ y = z",
	},
		func(a *Argument, n, y, z, x, w Term, xMem, wMem Fact) {

			catDef := a.Ctx().ConstDefNormalized("tuple_cat")

			xV := Inhabit[A, DimN](x, xMem)
			wV := Inhabit[A, DimN](w, wMem)

			forward := a.Have(
				"equal concatenations force equal blocks",
				"tuple_cat(n, x, y) = tuple_cat(n, w, z) ⇒ x = w ∧ y = z",
				Derive(func(b *Argument) {
					concatsEq := b.Assume()
					pointwise := b.Have(
						"read the equality at every index",
						"∀i:num. tuple_cat(n, x, y, i) = tuple_cat(n, w, z, i)",
						By(Normalized, concatsEq))

					lowLeft := b.Have(
						"an active low index reads the first low tuple",
						"∀i:num. i < n ⇒ tuple_cat(n, x, y, i) = x(i)",
						By(catDef))
					lowRight := b.Have(
						"and the second",
						"∀i:num. i < n ⇒ tuple_cat(n, w, z, i) = w(i)",
						By(catDef))
					lowAgree := b.Have(
						"so the low tuples agree on the active range",
						"∀i:num. ¬(i < n) ∨ (x(i) = w(i))",
						By(pointwise, lowLeft, lowRight))
					lowExt := b.Have(
						"extensionality for the low tuples, at the cut",
						"(∀i:num. ¬(i < n) ∨ (x(i) = w(i))) ⇒ x = w",
						By(Extensionality.AtVec(xV, wV)))
					lowsEq := b.Have(
						"and are equal",
						"x = w",
						By(lowAgree, lowExt))

					pastCut := b.Have(
						"a shifted index never lands in the low block",
						"∀i:num. ¬(i + n < n)",
						ByArith())
					unshift := b.Have(
						"unshifting is the identity",
						"∀i:num. (i + n) - n = i",
						By(nat_monus.AddSubCancel))
					highLeft := b.Have(
						"past the cut the concatenation reads the first high tuple",
						"∀i:num. tuple_cat(n, x, y, i + n) = y(i)",
						By(Normalized, catDef, pastCut, unshift))
					highRight := b.Have(
						"and the second",
						"∀i:num. tuple_cat(n, w, z, i + n) = z(i)",
						By(Normalized, catDef, pastCut, unshift))
					catsAgree := b.Have(
						"the equality read at the shifted indices",
						"∀i:num. tuple_cat(n, x, y, i + n) = tuple_cat(n, w, z, i + n)",
						By(pointwise))
					highAgree := b.Have(
						"so the high tuples agree at every index — the drop side is total",
						"∀i:num. y(i) = z(i)",
						Derive(func(c *Argument) {
							c.Fix()
							left := c.Have(
								"the first high tuple read off the equality",
								"y(i) = tuple_cat(n, w, z, i + n)",
								By(highLeft, catsAgree))
							c.Do(By(Normalized, left, highRight))
						}))
					highsEq := b.Have(
						"and are equal outright",
						"y = z",
						Funext(),
						By(highAgree))

					b.Do(By(lowsEq, highsEq))
				}))
			backward := a.Have(
				"equal blocks force equal concatenations",
				"x = w ∧ y = z ⇒ tuple_cat(n, x, y) = tuple_cat(n, w, z)",
				Derive(func(b *Argument) {
					blocksEq := b.Assume()
					b.Do(Funext(), By(blocksEq, catDef))
				}))
			a.Do(By(forward, backward))
		}),
})}

// ---------------------------------------------------------------------------
// Membership preservation for the carrier operations
// ---------------------------------------------------------------------------
//
// These are native term-level laws rather than twins: their job is to
// let the dimension-refined surface compose evidence, not to mirror a
// type-level statement.

// ConcatClosed — concatenating an n-carrier and an m-carrier produces an
// (n+m)-carrier. Outside the combined active range the low branch is
// impossible; the high branch is outside y's active range after subtracting
// the cut, so both definitions read the shared junk value.
var ConcatClosed = concatClosedThm{family.Add(registry.ProofEntry{
	Name: "ConcatClosed",
	Key:  "prop_c7c4960dcb44aacf",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀x y:(num → A).",
		Hypotheses: []string{
			"tuple(m, y)",
		},
		Conclusion: "tuple(n + m, tuple_cat(n, x, y))",
	},
		func(a *Argument, n, m, x, y Term, yMem Fact) {
			tupleDef := a.Ctx().ConstDefNormalized("tuple")
			catDef := a.Ctx().ConstDefNormalized("tuple_cat")
			// xMem is the typed input's guard but is not logically consumed:
			// outside n+m the low branch is impossible, so only y can be read.
			outsideY := a.Have(
				"the high block reads junk outside its own range",
				"∀j:num. ¬(j < m) ⇒ y(j) = junk",
				By(yMem, tupleDef))
			outsideLow := a.Have(
				"outside the combined range is outside the low block",
				"∀i:num. ¬(i < n + m) ⇒ ¬(i < n)",
				ByArith())
			outsideHigh := a.Have(
				"after removing the cut it is outside the high block",
				"∀i:num. ¬(i < n + m) ⇒ ¬(i - n < m)",
				ByArith())
			highRead := a.Have(
				"the selected high entry is therefore junk",
				"∀i:num. ¬(i < n + m) ⇒ y(i - n) = junk",
				By(outsideY, outsideHigh))
			concatReadsHigh := a.Have(
				"outside the combined range concatenation selects the high block",
				"∀i:num. ¬(i < n + m) ⇒ tuple_cat(n, x, y, i) = y(i - n)",
				By(Normalized, outsideLow, catDef))
			outsideRead := a.Have(
				"the concatenation therefore reads junk outside its combined range",
				"∀i:num. ¬(i < n + m) ⇒ tuple_cat(n, x, y, i) = junk",
				By(Normalized, concatReadsHigh, highRead))
			a.Do(By(outsideRead, tupleDef))
		}),
})}

// ---------------------------------------------------------------------------
// The carrier's decomposition laws
// ---------------------------------------------------------------------------
//
// the carrier's decomposition laws: cutting a tuple into its two blocks
// and laying them back end to end. The drop closure law rounds out
// ConcatClosed above; BlockDecomposition states that the cut loses
// nothing; DecompositionEq reads equality through the blocks; and the
// component laws compute the concatenation's and the drop's individual
// reads.
//
// The UNGUARDED extensionality law — agreement at EVERY index against
// plain equality — has no member here and needs none: the engine's
// normal form identifies a function equation with its pointwise
// ∀-reading, so that statement normalizes to ⊤ and carries no proof
// content. Extensionality above, with agreement only on the
// active range, is where the chapter's extensionality lives.
//
// All are stated over the chapter's minted constants (vocab.go); a
// body cites a defining equation as
// `a.Ctx().ConstDefNormalized("tuple")` where it consumes one. Index
// arithmetic travels through the ℕ chapters' named members — NotLessThan
// turns an else-branch guard into the bound the monus laws consume,
// and the monus laws move reads across the cut.

// DropClosed — dropping the first n entries of an (n+m)-carrier
// produces an m-carrier: ConcatClosed's sibling, and the closure law
// the transport members lean on. An out-of-range index reads the
// source shifted past the cut, where the shifted position is past
// n + m and the source's membership pins it to junk — the drop itself
// has no case of its own.
var DropClosed = dropClosedThm{family.Add(registry.ProofEntry{
	Name: "DropClosed",
	Key:  "prop_bf08aa6b5ed992b6",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀u:(num → A).",
		Hypotheses: []string{
			"tuple(n + m, u)",
		},
		Conclusion: "tuple(m, tuple_drop(n, u))",
	},
		func(a *Argument, n, m, u Term, memU Fact) {
			tupleDef := a.Ctx().ConstDefNormalized("tuple")
			dropDef := a.Ctx().ConstDefNormalized("tuple_drop")
			shifted := a.Have(
				"the drop reads the source, shifted past the cut",
				"∀i:num. tuple_drop(n, u, i) = u(i + n)",
				By(dropDef))
			pastEnd := a.Have(
				"past m the shifted position is past the source's range",
				"∀i:num. ¬(i < m) ⇒ ¬(i + n < m + n)",
				By(nat_order.NotLessThan, nat_order.LessEqAddRightCancel))
			shiftedJunk := a.Have(
				"where the source holds junk",
				"∀i:num. ¬(i + n < m + n) ⇒ u(i + n) = junk",
				By(Normalized, memU, tupleDef, nat_arith.AddSym))
			outsideRead := a.Have(
				"so the drop reads junk outside its own range",
				"∀i:num. ¬(i < m) ⇒ tuple_drop(n, u, i) = junk",
				By(shifted, pastEnd, shiftedJunk))
			a.Do(By(outsideRead, tupleDef))
		}),
})}

// BlockDecomposition — a tuple IS its two blocks laid end to end.
// Pointwise in two regions, exactly the concatenation's own COND: an
// active low index passes through the concatenation into the take and
// out to the tuple itself; everything else lands in the drop, whose
// shifted-unshifted read (i - n) + n = i is nat_monus.SubAddCancel
// under the else branch's own bound n ≤ i. Funext closes.
var BlockDecomposition = blockDecompositionThm{family.Add(registry.ProofEntry{
	Name: "BlockDecomposition",
	Key:  "prop_59c6dcd840b6aa51",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num. ∀z:(num → A).",
		Conclusion: "z = tuple_cat(n, tuple_take(n, z), tuple_drop(n, z))",
	},
		func(a *Argument, n, z Term) {
			catDef := a.Ctx().ConstDefNormalized("tuple_cat")
			takeDef := a.Ctx().ConstDefNormalized("tuple_take")
			dropDef := a.Ctx().ConstDefNormalized("tuple_drop")

			lowTake := a.Have(
				"an active low index passes through the take",
				"∀i:num. i < n ⇒ tuple_take(n, z, i) = z(i)",
				By(takeDef))
			lowCat := a.Have(
				"and the concatenation reads exactly that take",
				"∀i:num. i < n ⇒ tuple_cat(n, tuple_take(n, z), tuple_drop(n, z), i) = tuple_take(n, z, i)",
				By(catDef))
			low := a.Have(
				"so the low block reproduces the tuple",
				"∀i:num. i < n ⇒ z(i) = tuple_cat(n, tuple_take(n, z), tuple_drop(n, z), i)",
				By(lowCat, lowTake))

			elseCat := a.Have(
				"everywhere else the concatenation reads the drop, at the offset",
				"∀i:num. ¬(i < n) ⇒ tuple_cat(n, tuple_take(n, z), tuple_drop(n, z), i) = tuple_drop(n, z, i - n)",
				By(catDef))
			subCancel := a.Have(
				"past the cut the offset unshifts back to the index itself",
				"∀i:num. ¬(i < n) ⇒ (i - n) + n = i",
				By(nat_order.NotLessThan, nat_monus.SubAddCancel))
			highRead := a.Have(
				"the drop reads the source at the shifted offset",
				"∀i:num. tuple_drop(n, z, i - n) = z((i - n) + n)",
				By(dropDef))
			highDrop := a.Have(
				"so past the cut the drop reads the tuple",
				"∀i:num. ¬(i < n) ⇒ tuple_drop(n, z, i - n) = z(i)",
				By(Normalized, highRead, subCancel))
			high := a.Have(
				"and the high block reproduces it",
				"∀i:num. ¬(i < n) ⇒ z(i) = tuple_cat(n, tuple_take(n, z), tuple_drop(n, z), i)",
				By(elseCat, highDrop))

			pointwise := a.Have(
				"each index reads its block",
				"∀i:num. z(i) = tuple_cat(n, tuple_take(n, z), tuple_drop(n, z), i)",
				By(low, high))
			a.Do(Funext(), By(pointwise))
		}),
})}

// DecompositionEq — two tuples of one dimension are equal exactly when
// their blocks at a common cut are. The forward direction is
// congruence. Backward, BlockDecomposition rebuilds each tuple from
// its own blocks, and rewriting the equal blocks across identifies
// the two rebuilt concatenations.
var DecompositionEq = decompositionEqThm{family.Add(registry.ProofEntry{
	Name: "DecompositionEq",
	Key:  "prop_b496246466d3c8c0",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num. ∀x y:(num → A).",
		Conclusion: "x = y ⇔ tuple_take(n, x) = tuple_take(n, y) ∧ tuple_drop(n, x) = tuple_drop(n, y)",
	},
		func(a *Argument, n, x, y Term) {
			catDef := a.Ctx().ConstDefNormalized("tuple_cat")
			takeDef := a.Ctx().ConstDefNormalized("tuple_take")
			dropDef := a.Ctx().ConstDefNormalized("tuple_drop")
			forward := a.Have(
				"equal wholes read equal blocks — congruence, pointwise per block",
				"x = y ⇒ tuple_take(n, x) = tuple_take(n, y) ∧ tuple_drop(n, x) = tuple_drop(n, y)",
				Derive(func(b *Argument) {
					eq := b.Assume()
					takesEq := b.Have(
						"the takes agree at every index",
						"tuple_take(n, x) = tuple_take(n, y)",
						Funext(),
						By(eq, takeDef))
					dropsEq := b.Have(
						"and so do the drops",
						"tuple_drop(n, x) = tuple_drop(n, y)",
						Funext(),
						By(eq, dropDef))
					b.Do(By(takesEq, dropsEq))
				}))
			decompX := a.Have(
				"the first tuple is its blocks laid end to end",
				"x = tuple_cat(n, tuple_take(n, x), tuple_drop(n, x))",
				By(BlockDecomposition))
			decompY := a.Have(
				"and the second is its own",
				"y = tuple_cat(n, tuple_take(n, y), tuple_drop(n, y))",
				By(BlockDecomposition))
			backward := a.Have(
				"equal blocks rebuild equal wholes",
				"tuple_take(n, x) = tuple_take(n, y) ∧ tuple_drop(n, x) = tuple_drop(n, y) ⇒ x = y",
				Derive(func(b *Argument) {
					blocksEq := b.Assume()
					b.Do(Funext(), By(blocksEq, decompX, decompY, catDef))
				}))
			a.Do(By(forward, backward))
		}),
})}

// CatComponent — the concatenation's two component reads: an active
// low index reads the low tuple, an active high index reads the high
// tuple at the offset. Each is one branch of the definition's COND —
// the low guard is the branch condition itself, and the high guard's
// n ≤ i refutes it.
var CatComponent = catComponentThm{family.Add(registry.ProofEntry{
	Name: "CatComponent",
	Key:  "prop_a99677c9333c3f3d",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀i. ∀v u:(num → A).",
		Conclusion: "(¬(i < n) ∨ u(i) = tuple_cat(n, u, v, i)) ∧ " +
			"(¬(i < n + m) ∨ ¬(n ≤ i) ∨ v(i - n) = tuple_cat(n, u, v, i))",
	},
		func(a *Argument, n, m, i, v, u Term) {
			catDef := a.Ctx().ConstDefNormalized("tuple_cat")
			low := a.Have(
				"an active low index is the definition's first branch",
				"i < n ⇒ u(i) = tuple_cat(n, u, v, i)",
				By(catDef))
			pastCut := a.Have(
				"past the cut is past the low block",
				"n ≤ i ⇒ ¬(i < n)",
				By(nat_order.NotLessThan))
			high := a.Have(
				"an active high index is the second branch, at the offset",
				"n ≤ i ⇒ v(i - n) = tuple_cat(n, u, v, i)",
				By(catDef, pastCut))
			a.Do(By(low, high))
		}),
})}

// DropComponent — the drop's component read: every index reads the
// source shifted past the cut, definitionally — the drop is bare
// precomposition.
var DropComponent = dropComponentThm{family.Add(registry.ProofEntry{
	Name: "DropComponent",
	Key:  "prop_29a29bb842b9d9eb",
	Build: family.Theorem(Statement{
		Binders:    "∀n m:num. ∀i. ∀x:(num → A).",
		Conclusion: "¬(i < n) ∨ tuple_drop(m, x, i) = x(i + m)",
	},
		func(a *Argument, n, m, i, x Term) {
			dropDef := a.Ctx().ConstDefNormalized("tuple_drop")
			read := a.Have(
				"the drop is bare precomposition past the cut",
				"tuple_drop(m, x, i) = x(i + m)",
				By(dropDef))
			a.Do(By(read))
		}),
})}

// ---------------------------------------------------------------------------
// The truncation laws
// ---------------------------------------------------------------------------
//
// `tuple_take` is the chapter's normalizer (vocab.go): it truncates any
// function into the n-dimensional carrier. These members are its reading
// rules — an active index sees straight through it (TakeBeta), the
// truncation lands in the carrier (TakeClosed), a carrier member is its
// own truncation (TakeEta), the truncation is THE carrier member agreeing
// with g on the active range (TakeUnique), the low block of a
// concatenation reads back (LowBlockRoundTrip).
//
// TakeBeta and LowBlockRoundTrip are twins, with the walker's
// dimension-positivity guards
// dropped: the guard-free forms are the stronger statements, and no
// proof here needs 1 ≤ n. TakeEta and TakeUnique are take laws in the
// same translation surface; TakeClosed is NATIVE —
// no type-level statement corresponds to it, because there the type
// does the closing.
//
// The low side of a concatenation is the easy one: tuple_take's guard
// IS tuple_cat's low guard, so unlike the high-block laws above
// nothing here shifts an index — this part is COND discharges,
// membership reads, and Funext.

// TakeBeta — inside the active range the truncation is invisible.
// This is tuple_take's in-range COND branch, stated once so every
// consumer reads it as a law rather than re-discharging the COND.
// g is arbitrary — no membership is asked, because none is needed:
// what the truncation does OUTSIDE the range is not this law's
// business.
var TakeBeta = takeBetaThm{family.Add(registry.ProofEntry{
	Name: "TakeBeta",
	Key:  "prop_a6ebc33dcfe960e8",
	Build: family.Theorem("∀n:num. ∀i. ∀g:(num → A). ¬(i < n) ∨ g(i) = tuple_take(n, g, i)",
		func(a *Argument, n, i, g Term) {
			takeDef := a.Ctx().ConstDefNormalized("tuple_take")
			a.Do(By(takeDef))
		}),
})}

// TakeClosed — truncation lands in the carrier, unconditionally:
// outside the active range the truncation reads junk by its own
// definition, and that is the whole of what membership asks. This is
// the closure law that lets the dimension-refined surface treat
// tuple_take(n, g) as an n-carrier for ANY g — the companion of
// ConcatClosed above, and native like it.
var TakeClosed = takeClosedThm{family.Add(registry.ProofEntry{
	Name: "TakeClosed",
	Key:  "prop_fe3e7cea1eb2a560",
	Build: family.Theorem("∀n:num. ∀g:(num → A). tuple(n, tuple_take(n, g))",
		func(a *Argument, n, g Term) {
			tupleDef := a.Ctx().ConstDefNormalized("tuple")
			takeDef := a.Ctx().ConstDefNormalized("tuple_take")
			outside := a.Have(
				"outside the active range the truncation reads junk by definition",
				"∀i:num. ¬(i < n) ⇒ tuple_take(n, g, i) = junk",
				By(takeDef))
			a.Do(By(outside, tupleDef))
		}),
})}

// TakeEta — a carrier member is its own truncation. In range the
// truncation reads g back; outside, the truncation is junk by
// definition and g is junk by membership — the one place the
// antecedent is consumed. Function extensionality closes.
var TakeEta = takeEtaThm{family.Add(registry.ProofEntry{
	Name: "TakeEta",
	Key:  "prop_ef4b58001fac1d6a",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀g:(num → A).",
		Hypotheses: []string{
			"tuple(n, g)",
		},
		Conclusion: "g = tuple_take(n, λi. g(i))",
	},
		func(a *Argument, n, g Term, mem Fact) {
			tupleDef := a.Ctx().ConstDefNormalized("tuple")
			takeDef := a.Ctx().ConstDefNormalized("tuple_take")
			inRange := a.Have(
				"an active index reads back through the truncation",
				"∀i:num. i < n ⇒ g(i) = tuple_take(n, λj.g(j), i)",
				By(Normalized, takeDef))
			outRange := a.Have(
				"outside the range both sides are junk — the truncation by definition, g by membership",
				"∀i:num. ¬(i < n) ⇒ g(i) = tuple_take(n, λj.g(j), i)",
				By(Normalized, takeDef, tupleDef, mem))
			pointwise := a.Have(
				"each index agrees",
				"∀i:num. g(i) = tuple_take(n, λj.g(j), i)",
				By(inRange, outRange))
			a.Do(Funext(), By(pointwise))
		}),
})}

// TakeUnique — tuple_take(n, g) is THE carrier member agreeing with g
// on the active range. Forward, f = tuple_take(n, g) hands each active
// entry to TakeBeta. Backward — Extensionality's argument at one
// remove — range agreement is agreement everywhere: in range the
// truncation reads g, which agrees with f; outside it both read junk
// (the truncation by definition, f by membership), and function
// extensionality closes.
var TakeUnique = takeUniqueThm{family.Add(registry.ProofEntry{
	Name: "TakeUnique",
	Key:  "prop_4099721cdb74b634",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀g f:(num → A).",
		Hypotheses: []string{
			"tuple(n, f)",
		},
		Conclusion: "(∀i. ¬(i < n) ∨ g(i) = f(i)) ⇔ f = tuple_take(n, g)",
	},
		func(a *Argument, n, g, f Term, memF Fact) {
			tupleDef := a.Ctx().ConstDefNormalized("tuple")
			takeDef := a.Ctx().ConstDefNormalized("tuple_take")
			forward := a.Have(
				"the truncation's active entries are g's",
				"f = tuple_take(n, g) ⇒ (∀i:num. ¬(i < n) ∨ (g(i) = f(i)))",
				Derive(func(b *Argument) {
					eq := b.Assume()
					b.Do(By(eq, TakeBeta))
				}))
			backward := a.Have(
				"range agreement pins f to the truncation",
				"(∀i:num. ¬(i < n) ∨ (g(i) = f(i))) ⇒ f = tuple_take(n, g)",
				Derive(func(b *Argument) {
					agree := b.Assume()
					inRange := b.Have(
						"in range the truncation reads g, which agrees with f",
						"∀i:num. i < n ⇒ tuple_take(n, g, i) = f(i)",
						By(Normalized, agree, takeDef))
					outRange := b.Have(
						"outside it both read junk — the truncation by definition, f by membership",
						"∀i:num. ¬(i < n) ⇒ tuple_take(n, g, i) = f(i)",
						By(takeDef, tupleDef, memF))
					pointwise := b.Have(
						"each entry of the truncation is f's",
						"∀i:num. tuple_take(n, g, i) = f(i)",
						By(inRange, outRange))
					b.Do(Funext(), By(pointwise))
				}))
			a.Do(By(forward, backward))
		}),
})}

// LowBlockRoundTrip — reading the low block back off a concatenation
// returns the low tuple: HighBlockRoundTrip's sibling, without the
// arithmetic. The truncation's guard IS the concatenation's low guard,
// so an active index reads straight through both CONDs to x — no index
// ever shifts. Outside the range the truncation is junk by definition
// and x holds junk by membership.
var LowBlockRoundTrip = lowBlockRoundTripThm{family.Add(registry.ProofEntry{
	Name: "LowBlockRoundTrip",
	Key:  "prop_2d92815126157148",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀y x:(num → A).",
		Hypotheses: []string{
			"tuple(n, x)",
		},
		Conclusion: "x = tuple_take(n, tuple_cat(n, x, y))",
	},
		func(a *Argument, n, y, x Term, memX Fact) {
			tupleDef := a.Ctx().ConstDefNormalized("tuple")
			catDef := a.Ctx().ConstDefNormalized("tuple_cat")
			takeDef := a.Ctx().ConstDefNormalized("tuple_take")
			takeReads := a.Have(
				"an active index reads through the truncation",
				"∀i:num. i < n ⇒ tuple_take(n, tuple_cat(n, x, y), i) = tuple_cat(n, x, y, i)",
				By(takeDef))
			catReads := a.Have(
				"where the concatenation reads the low tuple",
				"∀i:num. i < n ⇒ tuple_cat(n, x, y, i) = x(i)",
				By(catDef))
			outRange := a.Have(
				"outside the range the truncation is junk, and so is x, by membership",
				"∀i:num. ¬(i < n) ⇒ tuple_take(n, tuple_cat(n, x, y), i) = x(i)",
				By(takeDef, tupleDef, memX))
			pointwise := a.Have(
				"each index reads the low tuple",
				"∀i:num. tuple_take(n, tuple_cat(n, x, y), i) = x(i)",
				By(takeReads, catReads, outRange))
			a.Do(Funext(), By(pointwise))
		}),
})}

// ---------------------------------------------------------------------------
// The quantifier-transport laws
// ---------------------------------------------------------------------------
//
// the quantifier-transport laws: quantifying over a tuple of the sum
// dimension is quantifying over its pair of blocks, universally and
// existentially. These are the STRONG, width-guard-free forms — the
// predicate binder Q ranges over ALL predicates on the carrier,
// unrelativized.
//
// Both members ride the same four facts, in the two directions' natural
// split: toward the sum dimension, a concatenation of inhabited blocks
// inhabits it (ConcatClosed); toward the blocks, an inhabited tuple's
// blocks inhabit their own dimensions (TakeClosed, DropClosed) and the
// tuple IS those blocks laid end to end (BlockDecomposition) — the
// equality that carries Q between the tuple and the concatenation by
// congruence.

// ForallBlocks — a statement about every pair of inhabited blocks is a
// statement about every inhabited tuple of the sum dimension.
//
// Toward the sum dimension, an inhabited tuple hands its own blocks to
// the hypothesis — they inhabit their dimensions by TakeClosed and
// DropClosed — and Q, granted at their concatenation, travels back to
// the tuple itself along BlockDecomposition's equality. Toward the
// blocks, a concatenation of inhabited blocks inhabits the sum
// dimension (ConcatClosed), which is all the hypothesis asks.
var ForallBlocks = forallBlocksThm{family.Add(registry.ProofEntry{
	Name: "ForallBlocks",
	Key:  "prop_5476bc2e66cc708b",
	Build: family.Theorem("∀n m:num. ∀Q:((num → A) → bool). "+
		"    (∀x:(num → A). tuple(n, x) ⇒ ∀y:(num → A). tuple(m, y) ⇒ Q(tuple_cat(n, x, y))) ⇔ "+
		"    ∀p:(num → A). tuple(n + m, p) ⇒ Q(p)",
		func(a *Argument, n, m, Q Term) {
			forward := a.Have(
				"blockwise universality reaches every tuple of the sum dimension",
				"(∀x:(num → A). tuple(n, x) ⇒ ∀y:(num → A). tuple(m, y) ⇒ Q(tuple_cat(n, x, y))) ⇒ "+
					"∀p:(num → A). tuple(n + m, p) ⇒ Q(p)",
				Derive(func(b *Argument) {
					blockwise := b.Assume()
					b.Fix()
					memP := b.Assume()
					lowMem := b.Have(
						"the tuple's low block inhabits the cut",
						"tuple(n, tuple_take(n, p))",
						By(TakeClosed))
					highMem := b.Have(
						"and its high block the rest",
						"tuple(m, tuple_drop(n, p))",
						By(DropClosed, memP))
					atBlocks := b.Have(
						"so the hypothesis speaks at their concatenation",
						"Q(tuple_cat(n, tuple_take(n, p), tuple_drop(n, p)))",
						By(blockwise, lowMem, highMem))
					decomp := b.Have(
						"which is the tuple itself",
						"p = tuple_cat(n, tuple_take(n, p), tuple_drop(n, p))",
						By(BlockDecomposition))
					b.Do(By(Normalized, atBlocks, decomp))
				}))
			backward := a.Have(
				"and universality at the sum dimension already speaks at every concatenation",
				"(∀p:(num → A). tuple(n + m, p) ⇒ Q(p)) ⇒ "+
					"∀x:(num → A). tuple(n, x) ⇒ ∀y:(num → A). tuple(m, y) ⇒ Q(tuple_cat(n, x, y))",
				Derive(func(b *Argument) {
					atSum := b.Assume()
					b.Fix()
					b.Assume()
					b.Fix()
					memY := b.Assume()
					catMem := b.Have(
						"a concatenation of inhabited blocks inhabits the sum dimension",
						"tuple(n + m, tuple_cat(n, x, y))",
						By(ConcatClosed, memY))
					b.Do(By(atSum, catMem))
				}))
			a.Do(By(forward, backward))
		}),
})}

// ExistsBlocks — the ∃ mirror: some pair of inhabited blocks satisfies
// Q at its concatenation exactly when some inhabited tuple of the sum
// dimension satisfies Q.
//
// Toward the sum dimension the concatenation is the witness, inhabiting
// it by ConcatClosed. Toward the blocks the tuple's own blocks are the
// witnesses — TakeClosed and DropClosed give their memberships, and Q
// reaches their concatenation from the tuple along BlockDecomposition's
// equality, by congruence.
var ExistsBlocks = existsBlocksThm{family.Add(registry.ProofEntry{
	Name: "ExistsBlocks",
	Key:  "prop_acd8da04b7ffaca6",
	Build: family.Theorem("∀n m:num. ∀Q:((num → A) → bool). "+
		"    (∃x:(num → A). tuple(n, x) ∧ (∃y:(num → A). tuple(m, y) ∧ Q(tuple_cat(n, x, y)))) ⇔ "+
		"    ∃p:(num → A). tuple(n + m, p) ∧ Q(p)",
		func(a *Argument, n, m, Q Term) {
			forward := a.Have(
				"an inhabited pair of blocks hands over its concatenation",
				Statement{
					Hypotheses: []string{
						"∃x:(num → A). tuple(n, x) ∧ (∃y:(num → A). tuple(m, y) ∧ Q(tuple_cat(n, x, y)))",
					},
					Conclusion: "∃p:(num → A). tuple(n + m, p) ∧ Q(p)",
				},
				Derive(func(b *Argument) {
					blocks := b.Assume()
					_, low := b.Unpack(blocks)
					_, high := b.Obtain(
						"the low membership peels off the pair",
						"(∃y:(num → var:A).(tuple(m, y) ∧ Q(tuple_cat(n, x, y))))",
						By(low))
					catMem := b.Have(
						"their concatenation inhabits the sum dimension",
						"tuple(n + m, tuple_cat(n, x, y))",
						By(low, high, ConcatClosed))
					b.Take(b.Term("tuple_cat(n, x, y)"))
					b.Do(By(catMem, high))
				}))
			backward := a.Have(
				"and an inhabited tuple of the sum dimension is such a pair — its own blocks",
				Statement{
					Hypotheses: []string{
						"∃p:(num → A). tuple(n + m, p) ∧ Q(p)",
					},
					Conclusion: "∃x:(num → A). tuple(n, x) ∧ (∃y:(num → A). tuple(m, y) ∧ Q(tuple_cat(n, x, y)))",
				},
				Derive(func(b *Argument) {
					whole := b.Assume()
					_, tuplewise := b.Unpack(whole)
					lowMem := b.Have(
						"its low block inhabits the cut",
						"tuple(n, tuple_take(n, p))",
						By(TakeClosed))
					highMem := b.Have(
						"and its high block the rest",
						"tuple(m, tuple_drop(n, p))",
						By(DropClosed, tuplewise))
					decomp := b.Have(
						"the tuple is its blocks laid end to end",
						"p = tuple_cat(n, tuple_take(n, p), tuple_drop(n, p))",
						By(BlockDecomposition, tuplewise))
					qAtCat := b.Have(
						"so Q, holding at the tuple, holds at that concatenation",
						"Q(tuple_cat(n, tuple_take(n, p), tuple_drop(n, p)))",
						By(Normalized, tuplewise, decomp))
					b.Do(By(lowMem, highMem, qAtCat))
				}))
			a.Do(By(forward, backward))
		}),
})}
