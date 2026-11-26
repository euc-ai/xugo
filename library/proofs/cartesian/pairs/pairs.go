// pairs.go — the chapter: the binary cartesian product.
//
// Five parts, marked by banners:
//
// - The two facts that pin the product type down
// - Reading the components back off a pair
// - Saying a pair thing componentwise
// - The paired abstraction
// - Currying, and the quantifiers that cannot see it

package pairs

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The two facts that pin the product type down
// ---------------------------------------------------------------------------
//
// PairEq says a pair determines its components — read left to right it
// is what makes the projections well defined at all, read right to
// left it is the congruence every equation between pairs is built by.
// PairSurjective says the type is not too big: `prod(A, B)` holds
// nothing beyond the pairs `(x, y)`, which is what licenses assuming a
// pair HAS components, and so what every later case analysis rests on.
//
// Neither cites another theorem: both inputs are the two facts the
// type definition comes with (definitions.go's ProdDef).

// PairEq — two pairs are equal exactly when their components are.
//
// The proof descends to the encoding and comes straight back. Reading
// the two graphs at the SAME point (a, b) is what turns an equation
// between pairs into one between components: the left graph is
// reflexively true there, so the right one is true there too, and what
// the right graph says at (a, b) is `a = x ∧ b = y`.
//
// No theorem is cited anywhere — the argument's only input is
// the type definition's membership fact (ProdDef.Membership).
//
// One local renaming: the statements bind `a`, and that is the name a
// reader needs, so the deduction context here is `arg` rather than the
// corpus's usual `a`.
var PairEq = pairEqThm{family.Add(registry.ProofEntry{
	Name:     "PairEq",
	Key:      "prop_2362d7381149344a",
	ServesAs: "pair_injective",
	Build: family.Sections("∀a:A. ∀b:B. ∀x:A. ∀y:B. (a, b) = (x, y) ⇔ a = x ∧ b = y",
		func(ctx *Script, headline string) *GoalStackNode {
			op := ops(ctx)

			roundTrip := ctx.Lemma("∀x:A. ∀y:B. dest_prod(mk_prod(mk_pair(x, y))) = mk_pair(x, y)",
				func(arg *Argument, x, y Term) {
					arg.Show(
						"mk_pair(x, y) is a representative, the existential being witnessed "+
							"by x and y themselves — so ProdDef.Membership's other side holds",
						By(Normalized, At(ProdDef.Membership, op.GraphOf(x, y))))
				})

			// The same fact read at a point. Unfolding mk_pair is the whole
			// step: it closes the goal outright, both sides becoming the
			// same predicate applied to (u, v).
			graphAt := ctx.Lemma("∀x:A. ∀y:B. ∀u:A. ∀v:B. "+
				"    dest_prod(mk_prod(mk_pair(x, y)), u, v) ⇔ u = x ∧ v = y",
				func(arg *Argument, x, y, u, v Term) {
					arg.Show(
						"the round trip, read at (u, v) with mk_pair unfolded",
						// Bare, because this cite REWRITES the goal rather than
						// installing: ↦ mk_pair(x₀, y₀, u₀, v₀) ⇔ u₀ = x₀ ∧ v₀ = y₀.
						// Ground witnesses panic the specialize here.
						Cite(roundTrip),
						Unfold(MkPairDef))
				})

			return ctx.Theorem(headline, func(arg *Argument, a, b, x, y Term) {
				arg.Iff()
				// Bare, not a By: the only premise is the split's own
				// hypothesis, so there is no deduction to name.
				arg.Forward(
					"equal pairs give equal components, read at (a, b)",
					func(d *Argument) {
						// `(a, b)` is mk_prod of its graph by definition,
						// which is what lets the graph readings meet the
						// assumption — and turns the assumption into this.
						d.Do(Unfold(PairDef))
						assumed := d.Hyp(MakeProp(
							op.MkProd.Apply(op.GraphOf(a, b)).Eq(
								op.MkProd.Apply(op.GraphOf(x, y)))))
						// Broadcast: the goal is a conjunction, and the same
						// two readings close each component.
						d.Show(
							"the graphs agree at (a, b), where the left is reflexively true and the right says a = x ∧ b = y",
							By(Normalized, Broadcast, assumed, At(graphAt, a, b, a, b), At(graphAt, x, y, a, b)))
					})
				arg.Backward(
					"equal components give equal pairs, pairing being a function",
					Basic(),
					CnfRefute())
			})
		}),
})}

// PairSurjective — every element of the product type is a pair.
//
// One descent and one return. Going down, `p` carries a predicate
// dest_prod(p); membership taken there says that predicate is a
// representative exactly when it survives the round trip, and the
// retraction at `p` is what makes it survive. So dest_prod(p) IS
// mk_pair(x, y) for some x and y — and those are the components,
// because applying mk_prod to that equation turns its left side back
// into `p` and its right side into `(x, y)`, which is why the proof
// unfolds `,` before it closes.
//
// Like PairEq, it cites no other theorem: both inputs are the two
// facts the type definition comes with.
var PairSurjective = pairSurjectiveThm{family.Add(registry.ProofEntry{
	Name: "PairSurjective",
	Key:  "prop_7c1b60978251e49c",
	Build: family.Theorem("∀p:prod(A, B). ∃x:A. ∃y:B. p = (x, y)",
		func(a *Argument, p Term) {
			op := ops(a.Ctx())

			a.Show(
				"ProdDef.Membership at p's own predicate, whose round trip "+
					"the ProdDef.Retraction supplies, produces the two components",
				Unfold(PairDef),
				By(Normalized, At(ProdDef.Membership, op.GraphOfPair(p)), At(ProdDef.Retraction, p)))
		}),
})}

// ---------------------------------------------------------------------------
// Reading the components back off a pair
// ---------------------------------------------------------------------------
//
// The type's two axioms say that a pair determines its components and that every
// element of the type is a pair. This part turns those two facts into
// maps: fst and snd recover the components, PairEta says that
// recovering them loses nothing, and PairInjectiveLeft and
// PairInjectiveRight read PairEq as a property of maps.
//
// Both projections are choice terms — fst(p) is `εu. ∃z. p = (u, z)`,
// snd(p) the same one slot over — so each proof has one thing to do:
// show that at a literal pair the predicate being chosen from has a
// single candidate. That is `firstComponent` / `secondComponent`
// below, and each is PairEq read as a characterization of one slot.
//
// The two are spelled out separately rather than factored through a
// shared ε-collapse lemma: two short proofs one slot apart read better
// than one abstraction over both.

// Fst — the first projection undoes pairing.
//
// The choice `fst((x, y))` ranges over the u for which (x, y) is (u, z)
// for some z. By PairEq that pins both slots at once, and the second is
// satisfiable — z := y — so the condition on u is exactly u = x. A
// choice with one candidate is that candidate.
var Fst = fstThm{family.Add(registry.ProofEntry{
	Name: "Fst",
	Key:  "prop_23b5f55b31cff19b",
	// The spec-definition compiler reads the pair-projection rows by
	// NAME (env.LibraryThms["fst_of_pair"] — proof.SpecFstName), a by-name
	// resolution convention an entry's own chosen name cannot meet;
	// ServesAs makes a read of that name a read of this entry (the
	// <T>_INDUCT channel, same rationale).
	ServesAs: "fst_of_pair",
	Build: family.Sections("∀x:A. ∀y:B. fst((x, y)) = x",
		func(ctx *Script, headline string) *GoalStackNode {
			firstComponent := ctx.Lemma("∀x:A. ∀y:B. ∀u:A. (∃z:B. (x, y) = (u, z)) ⇔ u = x",
				func(arg *Argument, x, y, u Term) {
					arg.Show(
						"componentwise equality splits the pair equation "+
							"into u = x and z = y, the second of which y witnesses",
						By(PairEq))
				})

			return ctx.Theorem(headline, func(arg *Argument, x, y Term) {
				// fst unfolds to the choice `εu. ∃z. (x, y) = (u, z)`;
				// rewriting the predicate under it leaves a choice over
				// `u = x`, which is why the cite closes here rather than
				// installing.
				arg.Show(
					"the choice is over a predicate holding of x and of nothing else",
					Unfold(FstDef),
					Cite(firstComponent))
			})
		}),
})}

// Snd — the second projection undoes pairing.
//
// Fst's argument in the other component: the choice `snd((x, y))`
// ranges over the u for which (x, y) is (z, u) for some z, PairEq pins
// u = y with z := x satisfiable, and the single candidate is y.
var Snd = sndThm{family.Add(registry.ProofEntry{
	Name: "Snd",
	Key:  "prop_e5f6155ed9f7aa36",
	// See Fst.ServesAs — the spec compiler's by-name read of the
	// second projection row.
	ServesAs: "snd_of_pair",
	Build: family.Sections("∀x:A. ∀y:B. snd((x, y)) = y",
		func(ctx *Script, headline string) *GoalStackNode {
			secondComponent := ctx.Lemma("∀x:A. ∀y u:B. (∃z:A. (x, y) = (z, u)) ⇔ u = y",
				func(arg *Argument, x, y, u Term) {
					arg.Show(
						"componentwise equality splits the pair equation "+
							"into z = x and u = y, the first of which x witnesses",
						By(PairEq))
				})

			return ctx.Theorem(headline, func(arg *Argument, x, y Term) {
				arg.Show(
					"the choice is over a predicate holding of y and of nothing else",
					Unfold(SndDef),
					Cite(secondComponent))
			})
		}),
})}

// PairEta — a pair is the pair of its components.
//
// The converse reading of the two projections, and what makes them a
// decomposition rather than merely two maps out of the type: nothing
// is lost on the way down. The proof is the only case analysis the
// product type admits — p is SOME pair, by PairSurjective — after
// which each projection names one of its components.
var PairEta = pairEtaThm{family.Add(registry.ProofEntry{
	Name: "PairEta",
	Key:  "prop_7691f1e94d58c941",
	Build: family.Theorem("∀p:prod(A, B). (fst(p), snd(p)) = p",
		func(a *Argument, p Term) {
			x, y, isPair := a.Obtain2(
				"p has components, every element of the product type being a pair",
				"∃x:A. ∃y:B. p = (x, y)",
				By(PairSurjective))

			a.Show(
				"the projections of (x, y) are x and y, so the pair of them is p again",
				By(Normalized, isPair, At(Fst, x, y), At(Snd, x, y)))
		}),
})}

// PairInjectiveLeft — pairing with a fixed second component is one-to-one:
// (x, b) = (y, b) only when x = y, a pair determining its components (PairEq).
var PairInjectiveLeft = pairInjectiveLeftThm{family.Add(registry.ProofEntry{
	Name: "PairInjectiveLeft",
	Key:  "prop_f4d45a91ad1d168c",
	Build: family.Theorem("∀b:B. ∀s:set(A). injective_on(s, λx:A. (x, b))",
		func(arg *Argument, b *Expr[B], s *Expr[Set[A]]) {
			arg.Show(
				"two pairs with one second component are equal only when their first components are",
				By(functions.InjectiveOnDef, PairEq))
		}),
})}

// PairInjectiveRight — pairing with a fixed first component is one-to-one:
// (a, x) = (a, y) only when x = y, a pair determining its components (PairEq).
var PairInjectiveRight = pairInjectiveRightThm{family.Add(registry.ProofEntry{
	Name: "PairInjectiveRight",
	Key:  "prop_919ba4bca8ca46cb",
	Build: family.Theorem("∀a:A. ∀t:set(B). injective_on(t, λy:B. (a, y))",
		func(arg *Argument, a *Expr[A], t *Expr[Set[B]]) {
			arg.Show(
				"two pairs with one first component are equal only when their second components are",
				By(functions.InjectiveOnDef, PairEq))
		}),
})}

// ---------------------------------------------------------------------------
// Saying a pair thing componentwise
// ---------------------------------------------------------------------------
//
// The projections give a pair's components names. This part turns that into the
// right to REPLACE a variable ranging over pairs by two variables
// ranging over components: the product type's induction and recursion
// principles, and the transports that carry a quantifier over pairs to
// a pair of quantifiers over components.
//
// Every member here rests on one fact and it is always the same one: a
// pair IS the pair of its components, which is PairEta. So a statement
// about an arbitrary p is already a statement about an arbitrary
// literal pair, and once that equation is available the two readings
// are interchangeable — which is why four of these six proofs are a
// single justified step. The exceptions are the recursion principle,
// which has to exhibit a function, and the transport for functions
// INTO a product, where the exchange happens under a λ and so needs
// its own pointwise statement first.
//
// The ∀ and ∃ form of each transport is stated and proved separately
// rather than factored through a duality helper: each is one line, and
// a line saying which quantifier it dualizes reads better than an
// abstraction over both.
//
// Naming note: the argument receiver is `a` throughout, except in
// ForallPairFun, whose statements bind a point variable named `a` —
// there the receivers are `arg` and, in the nested branches, `b`.

// pairInduct — to prove something of every pair it is enough to prove
// it of every literal pairing.
//
// The product type's induction principle, and weaker than any of the
// transports below: it is one half of ForallPair, the half that goes
// from the literal pairings to the arbitrary p. Nothing here recurses —
// the type has one constructor and no depth — so the whole content is
// that p is not some third thing besides a pairing.
var pairInduct = pairInductThm{family.Add(registry.ProofEntry{
	Name: "pairInduct",
	Key:  "prop_128c119c80d97230",
	Build: family.Theorem(Statement{
		Binders: "∀P:(prod(A, B) → bool). ∀p:prod(A, B).",
		Hypotheses: []string{
			"∀x:A. ∀y:B. P((x, y))",
		},
		Conclusion: "P(p)",
	},
		func(a *Argument, P Term, componentwise Fact) {
			a.Show(
				"p is the pairing of its own components, and that is a pairing the hypothesis speaks about",
				By(componentwise, PairEta))
		}),
})}

// PairRecursion — every two-argument function factors through the
// product type.
//
// The recursion principle: a function of a pair may be DEFINED by what
// it does to a pair of components. There is nothing to recurse on, so
// the recursor is written down outright — take the components of the
// argument and feed them to f — and the only thing to check is that at
// a literal pairing the components taken are the ones put in.
var PairRecursion = pairRecursionThm{family.Add(registry.ProofEntry{
	Name: "PairRecursion",
	Key:  "prop_c33b4fb149c9f96a",
	Build: family.Theorem("∀f:(A → B → C). ∃g:(prod(A, B) → C). ∀x:A. ∀y:B. g((x, y)) = f(x, y)",
		func(a *Argument, f *TermWrapper) {
			op := ops(a.Ctx())

			// g := λp. f(fst(p), snd(p)) — take the argument apart, then
			// apply f to the two pieces.
			p := a.Ctx().Var("p", ProdType(MakeVarType("A"), MakeVarType("B")))
			a.Take(p.To(f.Apply(op.Fst.Apply(p), op.Snd.Apply(p))))

			// Both projection facts meet this goal as REWRITES — the pairing
			// they speak about is already sitting under f, one slot each — so
			// they are cited bare and each drives the goal one step. The
			// states below are what each cite LEAVES; the goal β-reduces
			// before the first of them, and the rewriter reorients the
			// equation as it goes, so the two sides trade places once.
			//
			//	⊢ ∀x y. (λp. f(fst(p), snd(p)))((x, y)) = f(x, y)
			a.Show(
				"at the pairing (x, y) the components taken back out are x and y again, so g((x, y)) is f(x, y)",
				Cite(Fst), // ↦ ∀y x. f(x, y) = f(x, snd((x, y)))
				Cite(Snd), // ↦ closed
			)
		}),
})}

// ForallPair — a universal statement about pairs may be read
// componentwise.
//
// The transport every later chapter uses to state a pair fact in the
// variables it is really about. Both directions are the same
// observation: the pairs are exactly the values of the type, so
// quantifying over one is quantifying over the other.
var ForallPair = forallPairThm{family.Add(registry.ProofEntry{
	Name: "ForallPair",
	Key:  "prop_6826e4d5c26817d4",
	Build: family.Theorem("∀P:(prod(A, B) → bool). (∀p:prod(A, B). P(p)) ⇔ ∀x:A. ∀y:B. P((x, y))",
		func(a *Argument, P Term) {
			a.Show(
				"the arbitrary p of the left side and the arbitrary pairing of the "+
					"right side are the same value, PairEta being the identification",
				By(PairEta))
		}),
})}

// existsPair — ForallPair with the quantifier dualized.
//
// A witness among the pairs is a pair of witnesses among the
// components, and back: the pair produced on either side is the same
// value read two ways.
var existsPair = existsPairThm{family.Add(registry.ProofEntry{
	Name: "existsPair",
	Key:  "prop_e21950b94de62d6b",
	Build: family.Theorem("∀P:(prod(A, B) → bool). (∃p:prod(A, B). P(p)) ⇔ ∃x:A. ∃y:B. P((x, y))",
		func(a *Argument, P Term) {
			a.Show(
				"a witnessing p is the pairing of its components, and a "+
					"witnessing pair of components pairs up — PairEta both ways",
				By(PairEta))
		}),
})}

// ForallPairFun — a universal statement about functions INTO a product
// may be read as one about a pair of functions.
//
// ForallPair one level up, and the one member of this part where that
// costs more than a citation: the two readings of a VALUE are
// interchangeable outright, but the two readings of a FUNCTION differ
// under a λ, so the identification has to be made pointwise first.
// That is `pointwise` below. With it, the direction that has something
// to do is the one producing an arbitrary f: it instantiates the
// componentwise hypothesis at f's own two projections. The other
// direction is the ∀-hypothesis read at one componentwise function.
var ForallPairFun = forallPairFunThm{family.Add(registry.ProofEntry{
	Name: "ForallPairFun",
	Key:  "prop_5e384e05ac144b63",
	Build: family.Sections("∀P:((A → prod(B, C)) → bool). "+
		"    (∀f:(A → prod(B, C)). P(f)) ⇔ ∀g:(A → B). ∀h:(A → C). P(λa:A. (g(a), h(a)))",
		func(ctx *Script, headline string) *GoalStackNode {
			typeA, typeB, typeC := MakeVarType("A"), MakeVarType("B"), MakeVarType("C")

			// The pairs this member speaks about are the VALUES of its
			// functions, so they live at (B, C) — one slot over from where
			// the chapter's alphabet and PairEta state themselves. Two
			// different moves get us there.
			//
			// PairEta is a proved fact, so it is taken at the instance:
			// Inst is the kernel type-instantiation of the dep.
			pairEta := PairEta.Inst(TypeBinder.BindA[B](), TypeBinder.BindB[C]())

			// fst and snd are names, so they come from the chapter's
			// type-parameterized declaration surface at the instance this
			// member works at. Re-declaring a name does not displace the
			// alphabet's binding, which is what keeps the statement texts
			// parsing.
			fst, snd := ProjectionsAt(ctx, typeB, typeC)

			pointwise := ctx.Lemma("∀f:(A → prod(B, C)). (λa:A. (fst(f(a)), snd(f(a)))) = f",
				func(arg *Argument, f Term) {
					arg.Show(
						"two functions agreeing at every point are equal, and at "+
							"each point PairEta rebuilds f(a) out of its components",
						By(pairEta))
				})

			return ctx.Theorem(headline, func(arg *Argument, P Term) {
				arg.Iff()
				arg.Forward(
					"a property of every function holds in particular of the componentwise ones",
					func(b *Argument, everyFn Fact) {
						b.Show(
							"the hypothesis, read at that function",
							By(everyFn))
					})
				arg.Backward(
					"an arbitrary f already IS componentwise, its components being λa. fst(f(a)) and λa. snd(f(a))",
					func(b *Argument, componentwise Fact) {
						f := b.Fix()
						a := ctx.Var("a", typeA)
						firstOf := a.To(fst.Apply(f.Apply(a)))
						secondOf := a.To(snd.Apply(f.Apply(a)))

						// Normalized: the instance arrives with its two
						// component functions still applied point by point,
						// and has to be β-reduced before it is the λ that
						// `pointwise` speaks about.
						b.Show(
							"the hypothesis at those two gives P of λa. (fst(f(a)), "+
								"snd(f(a))), which pointwise says is f itself",
							By(componentwise.At(firstOf, secondOf), pointwise))
					})
			})
		}),
})}

// existsPairFun — ForallPairFun with the quantifier dualized.
//
// A function into the product witnessing P is a pair of functions
// witnessing it componentwise, and back.
var existsPairFun = existsPairFunThm{family.Add(registry.ProofEntry{
	Name: "existsPairFun",
	Key:  "prop_92d8b3b78e4edc26",
	Build: family.Theorem("∀P:((A → prod(B, C)) → bool). "+
		"    (∃f:(A → prod(B, C)). P(f)) ⇔ ∃g:(A → B). ∃h:(A → C). P(λa:A. (g(a), h(a)))",
		func(a *Argument, P Term) {
			a.Show(
				"ForallPairFun at the complement of P, where having no counterexample is having a witness",
				By(ForallPairFun))
		}),
})}

// ---------------------------------------------------------------------------
// The paired abstraction
// ---------------------------------------------------------------------------
//
// `λ(x, y). body` is not a primitive: it abbreviates a CHOICE. The
// abbreviation names some function on the product whose value at every
// literal pairing (x, y) is body — if there is such a function at all.
// This part says what that choice comes to, and it is the only place in
// the chapter that descends below the abbreviation.
//
// One observation carries the whole part, and `agreesAtPairings` below
// makes it once: the specification a paired abstraction is chosen to
// meet is met by a function one can write down, so the chosen one meets
// it too — and where the specification pins a value, which is at every
// literal pairing, the choice is pinned.
//
// Above that observation the part is the chapter's usual one fact:
// PairEta, which says an arbitrary p is the pairing of its own
// components. So "pinned at every literal pairing" is "pinned
// everywhere", and that is what turns the pointwise agreement into the
// equation between FUNCTIONS both members state. `PairedLambdaEta` is
// that equation for an arbitrary function on the product; `PairedLambda`
// reads it at one particular function and identifies the paired
// abstraction of a two-argument g.

// PairedLambdaEta — every function on a product already IS a paired
// abstraction, namely its own.
//
// PairEta one level up: there a VALUE of the product turned out to be
// the pairing of its own parts, here a FUNCTION on the product turns
// out to be the abstraction over them.
var PairedLambdaEta = pairedLambdaEtaThm{family.Add(registry.ProofEntry{
	Name: "PairedLambdaEta",
	Key:  "prop_77ca291c2f71574a",
	Build: family.Sections("∀t:(prod(A, B) → C). t = λ(x, y). t((x, y))",
		func(ctx *Script, headline string) *GoalStackNode {
			op := ops(ctx)

			agreesAtPairings := ctx.Lemma("∀t:(prod(A, B) → C). ∀x:A. ∀y:B. "+
				"    (λ(u, v). t((u, v)))((x, y)) = t((x, y))",
				func(a *Argument, t, x, y Term) {
					// Here and nowhere else the abbreviation is opened.
					// `pattern_abstraction(P)` is `εf. P(f)`, so past this step the goal
					// speaks about the function CHOSEN out of those meeting
					// P — and P written out is the ∃-body just below.
					a.Do(Unfold(PatternAbstractionDef))

					// A statement text names a bound variable by the mint the
					// binder produced, so the closure's `t` is `t₀` here and
					// `x`, `y` are `x₀`, `y₀` in the label below.
					//
					// Stated and closed in the open rather than through
					// a.ObtainChosen: that verb eliminates an ∃ so the
					// argument can go on to name the chosen witness, and it
					// closes the inhabitation from a By premise list. Neither
					// half fits — t inhabits its own choice set as a Witness
					// step, which a premise list cannot carry, and the goal
					// already IS the chosen instance, so there is nothing
					// left to name afterwards.
					inhabited := a.Have(
						"t agrees with itself at every pairing, so there is something to choose",
						"∃f:(prod(A, B) → C). ∀u:A. ∀v:B. f((u, v)) = t((u, v))",
						Witness(t),
						TrivialNormalized())

					a.Show(
						"a choice out of an inhabited set meets the specification, and at (x₀, y₀) that is the claim",
						By(HilbertDenoted, inhabited))
				})

			return ctx.Theorem(headline, func(a *Argument, t Term) {
				// Two functions are equal when they agree at every point, so
				// the argument descends to an arbitrary point p of the product.
				a.Do(Funext())
				p := a.Fix()

				a.Show(
					"p is the pairing of its components, and at a pairing the abstraction already takes t's value",
					By(At(PairEta, p), At(agreesAtPairings, t, op.Fst.Apply(p), op.Snd.Apply(p))))
			})
		}),
})}

// PairedLambda — what a paired abstraction of a two-argument function
// DOES: project, then apply.
//
// PairedLambdaEta identifies every function on the product with its own
// paired abstraction; read at the projecting function λp. g(fst p, snd p)
// it says that function is the abstraction over `g(fst((x, y)),
// snd((x, y)))`, and Fst/Snd collapse that body to `g(x, y)`.
var PairedLambda = pairedLambdaThm{family.Add(registry.ProofEntry{
	Name: "PairedLambda",
	Key:  "prop_da23cf6e54b12812",
	Build: family.Theorem("∀g:(A → B → C). (λ(x, y). g(x, y)) = λp:prod(A, B). g(fst(p), snd(p))",
		func(a *Argument, g Term) {
			// The chain's middle term: the abstraction that pairs its two
			// arguments up and immediately takes them apart again. Built as
			// text because a pair-pattern lambda has no Go builder — the
			// pattern_abstraction encoding it stands for is reachable only through the DSL
			// surface, so the chapter's alphabet cannot hand it over.
			viaProjections := a.Ctx().TermText("λ(x:A, y:B). g₀(fst((x, y)), snd((x, y)))")

			// PairedLambdaEta taken as the RAW proved headline, which is the
			// plan's marked escape from the canonical install form. Naming
			// the ENTRY would resolve it through `NormalizedThm ∘ Dep`, and
			// Normalize extensionalizes an equation between functions into a
			// pointwise one — landing a ∀ over points beside a leg that has
			// none. The headline as proved is already an equation between
			// functions, which is what this leg is.

			a.Do(CalcEq(
				Leg(
					viaProjections,
					"a component put into a pairing comes straight back out of it",
					Collapse(a.Ctx()),
				),
				FinalLeg(
					"and an abstraction that projects its pairing is the projecting "+
						"function itself, by PairedLambdaEta read at that function",
					Cite(PairedLambdaEta)),
			))
		}),
})}

// ---------------------------------------------------------------------------
// Currying, and the quantifiers that cannot see it
// ---------------------------------------------------------------------------
//
// A function of two arguments and a function on the product carry the
// same data written two ways. This part says the quantifiers cannot
// tell the two ways apart: what holds of every two-argument function
// holds of every function on the product read through currying, and
// dually for a witness.
//
// These are the uncurry theorems, and the direction that names them is
// the one they license: a claim about every two-argument function may
// be discharged by proving it of the curries alone, so a proof gets to
// assume its two-argument function arrived from the product. Read the other way round they say the two quantifiers see
// the same things.
//
// One fact carries both members, and it is the recursion
// principle. PairRecursion factors an arbitrary two-argument g through
// the product — which is to say g is SOMEBODY'S curry — so a hypothesis
// about every curry already reaches g. That is the whole of the
// direction with anything to do; the other direction reads a hypothesis
// about every two-argument function at one particular curry.
//
// The part costs nothing below that. `λ(x, y). body` never has to be
// opened here, so neither PairedLambda nor the projections appear. Nor
// is there a sub-lemma: reading the recursion principle as an equation
// between functions rather than a pointwise agreement gives back the
// same proposition — same normalized key — so a section claiming it
// would be a second spelling, not a step.
//
// Naming note: both statements bind `a` and `b` as the λ-binders of a
// curry, so the outer deduction context is `arg` and nested ones
// continue at `b`, as in ForallPairFun above.

// forallUncurry — a universal statement about two-argument functions
// may be read as one about functions on the product.
//
// The transport of ForallPair one type-level up: there the
// pairs were the VALUES quantified over, here they are the ARGUMENTS.
var forallUncurry = forallUncurryThm{family.Add(registry.ProofEntry{
	Name: "forallUncurry",
	Key:  "prop_5f1ed8fc29d0e635",
	Build: family.Theorem("∀P:((A → B → C) → bool). "+
		"    (∀g:(A → B → C). P(g)) ⇔ ∀f:(prod(A, B) → C). P(λa:A. λb:B. f((a, b)))",
		func(arg *Argument, P Term) {
			arg.Iff()
			arg.Forward(
				"a property of every two-argument function holds of the curries in particular",
				func(b *Argument, ofEveryTwoArgFn Fact) {
					b.Show(
						"the hypothesis, read at the curry of f",
						By(ofEveryTwoArgFn))
				})
			arg.Backward(
				"an arbitrary g is itself a curry, so the hypothesis about every curry reaches it",
				func(b *Argument, ofEveryCurry Fact) {
					g := b.Fix()

					// PairRecursion at g: fn is a function on pairs with
					// fn((x, y)) = g(x, y).
					fn, factorsG := b.Unpack(At(PairRecursion, g))

					// Normalized: fn's agreement with g is pointwise, and
					// the closer needs the two functions identified before
					// it meets them.
					b.Show(
						"the hypothesis at fn is P of a curry taking g's value at "+
							"every pair of arguments, and a function that does that is g",
						By(Normalized, ofEveryCurry.At(fn), factorsG))
				})
		}),
})}

// existsUncurry — forallUncurry with the quantifier dualized.
//
// A two-argument function witnessing P is a function on the product
// whose curry witnesses it, and back.
var existsUncurry = existsUncurryThm{family.Add(registry.ProofEntry{
	Name: "existsUncurry",
	Key:  "prop_b55dc158e36b0d61",
	Build: family.Theorem("∀P:((A → B → C) → bool). "+
		"    (∃g:(A → B → C). P(g)) ⇔ ∃f:(prod(A, B) → C). P(λa:A. λb:B. f((a, b)))",
		func(arg *Argument, P *TermWrapper) {
			// λg. ¬P(g) — being a counterexample to P.
			g := arg.Ctx().Var("g", MakeFun(MakeVarType("A"), MakeVarType("B"), MakeVarType("C")))
			isCounterexample := g.To(Not(P.Apply(g)))

			arg.Show(
				"forallUncurry at that property: counterexamples run out on one side "+
					"exactly when on the other, which is the claim negated both sides",
				By(At(forallUncurry, isCounterexample)))
		}),
})}
