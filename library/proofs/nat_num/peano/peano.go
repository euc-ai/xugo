// peano.go — the chapter: the construction of ℕ.
//
// Eight parts, marked by banners:
//
// - The axiom of infinity
// - Naming the pair the axiom of infinity produced
// - The predicate that carves ℕ out of `ind`
// - `num` as a type, and the two constants transported into it
// - The first two Peano axioms
// - Induction on `num`
// - Primitive recursion
// - Case analysis on `num`

package peano

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The axiom of infinity
// ---------------------------------------------------------------------------

// Infinity — the axiom of infinity, and the one statement the corpus
// assumes outright: there is a type `ind`, and some map of it into
// itself separates points and misses a point. The construction of `num`
// needs nothing else; the map is the successor-to-be and the point it
// misses the zero-to-be.
//
// The type is introduced here and nowhere else. No rule of the logic
// mentions it, so declaring it adds nothing; this axiom is all the
// content `ind` has.
//
// It is stated in the form the construction consumes. "Injective and
// not onto" is the same content up to classical logic, and the point a
// map that is not onto misses is what the zero has to be; stated so,
// the axiom names it. Separation is stated as the implication alone:
// its converse is congruence, a theorem of the logic, and an axiom
// asserts nothing a proof could supply.
//
// The term the kernel is handed is built here in Go, from the logic's
// constructors; the statement text is its surface, and the registry
// checks that the two agree.
var Infinity = infinityThm{family.Add(registry.ProofEntry{
	Name: "Infinity",
	Key:  "prop_9b6596e3743238fc",
	Build: family.Postulate("ind",
		"∃f:(ind → ind). ∃z:ind. (∀x₁ x₂:ind. f(x₁) = f(x₂) ⇒ x₁ = x₂) ∧ (∀x:ind. f(x) ≠ z)",
		func() Term {
			ind := Ind{}.Reify()
			f := Var("f", MakeFun(ind, ind))
			z, x, y := Var("z", ind), Var("x", ind), Var("y", ind)
			separates := ForAll(x, y)(f.Apply(x).Eq(f.Apply(y)).Imply(x.Eq(y)))
			missesZ := ForAll(x)(Not(f.Apply(x).Eq(z)))
			return Exists(f)(Exists(z)(separates.And(missesZ)))
		}),
})}

// ---------------------------------------------------------------------------
// Naming the pair the axiom of infinity produced
// ---------------------------------------------------------------------------
//
// Naming the pair the axiom of infinity produced, and the two facts about `ind`
// that the rest of the chapter transports up to `num`.

// indSucDef — ind_suc is SOME injection of `ind` into itself that
// misses a point: the successor-to-be, chosen among the maps the axiom
// of infinity asserts.
var indSucDef = indSucDefThm{family.Define(registry.DefEntry{
	Name:  "indSucDef",
	Key:   "prop_d282919581723118",
	Const: "ind_suc",
	Type:  "ind → ind",
	Equations: []string{
		"ind_suc = εf:(ind → ind). ∃z:ind. (∀x₁ x₂:ind. f(x₁) = f(x₂) ⇒ x₁ = x₂) ∧ ∀x:ind. f(x) ≠ z",
	},
	// The postulate introduces `ind`; naming it orders the two.
	Deps: []registry.EntryLike{Infinity},
})}

// indZeroDef — ind_zero is SOME point ind_suc misses: the zero-to-be.
var indZeroDef = indZeroDefThm{family.Define(registry.DefEntry{
	Name:  "indZeroDef",
	Key:   "prop_d69e5cb62731165e",
	Const: "ind_zero",
	Type:  "ind",
	Equations: []string{
		"ind_zero = εz:ind. (∀x₁ x₂:ind. ind_suc(x₁) = ind_suc(x₂) ⇒ x₁ = x₂) ∧ ∀x:ind. ind_suc(x) ≠ z",
	},
	Deps: []registry.EntryLike{indSucDef},
})}

// indSucSpec — the specification of the chosen pair (ind_suc, ind_zero).
//
// Both constants are Hilbert choices: ind_suc is SOME f as the axiom of
// infinity describes it, and ind_zero is SOME point that f misses. Choosing them is
// what removes the existential quantifiers, and this statement is what
// the choice buys — the entire harvest of the ind layer, before anything
// is transported to num.
//
// So the proof is two nested ε-introductions and no mathematics; the
// four Case labels below name the obligations each one carries.
var indSucSpec = indSucSpecThm{family.Add(registry.ProofEntry{
	Name: "indSucSpec",
	Key:  "prop_791291dbca63a11c",
	Build: family.Theorem(
		"(∀x₁ x₂:ind. ind_suc(x₁) = ind_suc(x₂) ⇒ x₁ = x₂) ∧ (∀x:ind. ind_suc(x) ≠ ind_zero)",
		func(a *Argument) {
			v := ops(a.Ctx())
			a.Do(ExistentialConstDefStep(v.IndSuc,
				Case(
					"ind_suc chooses from the injections that miss a point — the axiom of infinity says there is one",
					Cite(Infinity)),
				Case(
					"naming that injection ind_suc leaves the residual: ∃z. ind_suc is injective and misses z",
					ExistentialConstDefStep(v.IndZero,
						Case(
							"ind_zero chooses from the points ind_suc misses — the ∃z just named is exactly that set",
							TrivialNormalized()),
						Case(
							"naming one of them ind_zero discharges the ∃z, which is the claim",
							TrivialNormalized()),
					)),
			))
		}),
})}

// Both projections cite indSucSpec alone: one step installs the pack's
// clauses and finishes the leaf, and the statement, not the body, is
// what selects the conjunct. The injective one also needs the converse
// of the separation the pack states, which is congruence and which the
// Normalized shaping supplies.

// indSucNotZero — ind_zero is not a successor. The half of indSucSpec that
// ind_zero's choice is FOR; upstairs it becomes suc n ≠ 0.
var indSucNotZero = indSucNotZeroThm{family.Add(registry.ProofEntry{
	Name: "indSucNotZero",
	Key:  "prop_7698aa732d642479",
	Build: family.Theorem("∀x:ind. ind_suc(x) ≠ ind_zero",
		By(indSucSpec)),
})}

// indSucInjective — ind_suc is injective. The half of indSucSpec that
// ind_suc's choice is FOR, read as an equivalence: the converse of the
// separation indSucSpec states is congruence. Upstairs it becomes
// suc m = suc n ⇔ m = n.
var indSucInjective = indSucInjectiveThm{family.Add(registry.ProofEntry{
	Name: "indSucInjective",
	Key:  "prop_64079b33652e7f37",
	Build: family.Theorem("∀x₁ x₂:ind. ind_suc(x₁) = ind_suc(x₂) ⇔ x₁ = x₂",
		By(Normalized, indSucSpec)),
})}

// ---------------------------------------------------------------------------
// The predicate that carves ℕ out of `ind`
// ---------------------------------------------------------------------------
//
// is_num is the SMALLEST subset of `ind` that contains ind_zero and is
// closed under ind_suc — the two rules below, and the theorems they
// come with. Nothing here unfolds it.

// isNum — the two rules that define is_num.
var isNum = family.DefineInductive(registry.InductiveEntry{
	Name: "isNum",
	Keys: registry.InductiveKeys{
		Rules:        "prop_b9c5203a514489aa",
		Induct:       "prop_fa79dd0bfe42a0ba",
		Cases:        "prop_92149d9a376e20b4",
		InductStrong: "prop_2944c20b7f13b77",
	},
	Const: "is_num",
	Type:  "ind → bool",
	Rules: []string{
		"is_num(ind_zero)",
		"∀i:ind. is_num(i) ⇒ is_num(ind_suc(i))",
	},
	Deps: []registry.EntryLike{indSucDef, indZeroDef},
})

// isNumRules — is_num contains ind_zero and is closed under ind_suc:
// the definition's rule set, registered verbatim as its Rules theorem.
var isNumRules = isNumRulesThm{isNum.Rules}

// isNumInductStrong — the same induction with the step told that the
// point it climbs from is itself a representative. That is what the
// transport into `num` needs: mk_num undoes dest_num only on
// representatives.
var isNumInductStrong = isNumInductStrongThm{isNum.InductStrong}

// ---------------------------------------------------------------------------
// `num` as a type, and the two constants transported into it
// ---------------------------------------------------------------------------
//
// `ind` is far too big — it holds the numerals and whatever else. Tier
// 2's is_num cuts them out, and `num` is declared to be a type in
// bijection with that subset via the pair mk_num / dest_num. A type
// definition may only be stamped against a NON-EMPTY subset, and
// isNumZero is the inhabitant this one was stamped with;
// ctx.TypeDefExpand takes that witness back and returns the bijection.
// So isNumZero comes first, and nothing after it needs any input
// beyond the bijection and the two defining equations.
//
// The classical proofs each re-derive whichever of these six facts they
// need. Stating each once is what this file is for; the tiers above then
// read as transport rather than as construction.

// isNumZero — ind_zero is a representative.
//
// The left conjunct of isNumRules, and the fact the type definition
// needs before it may be stamped at all: the subset being carved out
// has to be inhabited, and this is the inhabitant. One cite closes it,
// with no trailing refute — unlike the projections of indSucSpec above.
var isNumZero = isNumZeroThm{family.Add(registry.ProofEntry{
	Name: "isNumZero",
	Key:  "prop_3382580e638ad86c",
	Build: family.Theorem("is_num(ind_zero)",
		Cite(isNumRules)),
})}

// NumDef — `num` is the type in bijection with the representatives:
// is_num carved out of `ind`, the bijection the pair mk_num / dest_num,
// stamped against isNumZero — the inhabitant a type definition must be
// shown before it may be made. The two facts it comes with:
//
//   - NumDef.Retraction: `mk_num(dest_num(a)) = a` — going down to `ind`
//     and coming straight back is the identity on `num`, so dest_num is
//     injective and no two numbers share a representative. This is what
//     lets an argument that dropped to `ind` return with its conclusion.
//   - NumDef.Membership: `is_num(r) ⇔ dest_num(mk_num(r)) = r` — an
//     element of `ind` is a representative exactly when the round trip
//     up to `num` and back returns it unchanged. Forwards, a
//     representative survives the round trip; backwards, surviving is
//     enough to BE one, which is the direction isNumDest uses. With
//     the retraction it makes mk_num and dest_num mutually inverse
//     between `num` and the representatives, so `num` is that subset
//     and not a quotient of it.
//
// The inhabitation is the PROVED isNumZero, in the applied form the
// basic type definition takes (`is_num(ind_zero)`); the type is minted on
// its promise and the two facts are derived from its certificate at
// replay. Nothing kernel-external enters: the chapter's whole claim is
// that it needs exactly one such input, the axiom of infinity.
var NumDef = family.DefineType(registry.TypeEntry{
	Name:      "Num",
	Type:      "num",
	Abs:       "mk_num",
	Rep:       "dest_num",
	Pred:      "is_num",
	Existence: isNumZero,
	Witness:   "ind_zero",
	Deps:      []registry.EntryLike{isNumRules},
})

// isNumDest — everything in the image of dest_num is a representative.
//
// The bijection in the direction the transports actually use: tiers
// 4–6 start from a number, drop to its representative and work there,
// so they need to know that where they landed is a legal place to
// work. It is the one fact here that needs both halves.
var isNumDest = isNumDestThm{family.Add(registry.ProofEntry{
	Name: "isNumDest",
	Key:  "prop_972cab5af7e455a0",
	Build: family.Theorem("∀n:num. is_num(dest_num(n))",
		func(a *Argument, n Term) {
			v := ops(a.Ctx())
			r := v.DestNum.Apply(n) // r := dest_num(n₀), the candidate representative
			a.Show(
				"membership at r is the round-trip equation, and the retraction at n₀ collapses it to reflexivity",
				By(At(NumDef.Membership, r), NumDef.Retraction))
		}),
})}

// ZeroDef — zero is the representative ind_zero, brought up.
//
// One of the two definitional equations `num` carries; the constant is
// `_0` (printed `0`), spelled `zero` in the equation because the DSL
// keeps `_0` for its own numeral surface. A definition's Deps are the
// definitions it mentions — here the type, through its retraction —
// which is also what orders the mints at package init.
var ZeroDef = zeroDefThm{family.Define(registry.DefEntry{
	Name:      "ZeroDef",
	Key:       "prop_8731cb44a0351bf7",
	Const:     "_0",
	Spelled:   "zero",
	Type:      "num",
	Equations: []string{"zero = mk_num(ind_zero)"},
	Deps:      []registry.EntryLike{NumDef.Retraction},
})}

// SucDef — successor is ind_suc conjugated by the bijection: go down,
// step, come back.
//
// The other definitional equation. These two are what a `num`-level
// statement is rewritten with to become an `ind`-level one, which is
// why each Peano axiom upstairs opens with them and then argues
// downstairs. Spelled `successor` in the equation, as `_0` is spelled
// `zero`: the DSL keeps both names for its numeral surface.
var SucDef = sucDefThm{family.Define(registry.DefEntry{
	Name:      "SucDef",
	Key:       "prop_85a201a6f26a9848",
	Const:     "suc",
	Spelled:   "successor",
	Type:      "num → num",
	Equations: []string{"∀n:num. successor(n) = mk_num(ind_suc(dest_num(n)))"},
	Deps:      []registry.EntryLike{NumDef.Retraction},
})}

// destSuc — dest_num turns a successor upstairs into an ind_suc
// downstairs.
//
// SucDef says the same thing the other way round, as a recipe for
// building suc out of mk_num; reading it as a fact about dest_num means
// cancelling the mk_num, and that costs the whole bijection: ind_suc of
// a representative is a representative (isNumRules on top of
// isNumDest), so the round trip fixes it (NumDef.Membership). It is
// the last of the six transport facts, and the only one assembled from
// several of the others rather than read off the type definition —
// SucDef, isNumDest and NumDef.Membership, plus isNumRules above.
// Which is why it is stated here rather than left to the axioms that
// use it.
var destSuc = destSucThm{family.Add(registry.ProofEntry{
	Name: "destSuc",
	Key:  "prop_ba33e33b1abf6596",
	Build: family.Theorem("∀n:num. dest_num(suc(n)) = ind_suc(dest_num(n))",
		func(a *Argument, n Term) {
			v := ops(a.Ctx())
			r := v.DestNum.Apply(n) // r — n₀'s representative
			a.Show(
				"r is a representative, so ind_suc(r) is one too and the round "+
					"trip fixes it; SucDef identifies the result with dest_num(suc(n₀))",
				By(
					Normalized,
					At(SucDef, n),
					At(NumDef.Membership, v.IndSuc.Apply(r)),
					At(isNumDest, n),
					isNumRules))
		}),
})}

// ---------------------------------------------------------------------------
// The first two Peano axioms
// ---------------------------------------------------------------------------
//
// The first two Peano axioms, and the chapter's first exported
// names.
//
// Both are the same move. `dest_num` is not merely a bijection onto the
// representatives: it carries the (0, suc) structure on `num` onto the
// (ind_zero, ind_suc) structure on `ind`, sending 0 to ind_zero and suc(n) to
// ind_suc(dest_num n). So each axiom is its `ind`-level counterpart read
// through that correspondence — apply dest_num to both sides of the
// equation being refuted or cancelled, argue downstairs where the naming part put
// the facts, and come back with mk_num.
//
// The successor half of that correspondence is destSuc above; the
// zero half is one line and only the first member below wants it, so it
// is a Have there.

// SucNotZero — zero is not a successor.
//
// ind_suc misses ind_zero downstairs, and dest_num sends 0 to ind_zero and
// each successor into ind_suc's image, so a number equal to both would
// put ind_zero in that image.
var SucNotZero = sucNotZeroThm{family.Add(registry.ProofEntry{
	Name:     "SucNotZero",
	Key:      "prop_7ab59ff0cc33e880",
	ServesAs: "suc_not_zero",
	Build: family.Theorem("∀n:num. suc(n) ≠ 0",
		func(a *Argument, n Term) {
			v := ops(a.Ctx())

			// The zero half of the correspondence, needed only here.
			destZero := a.Have(
				"ind_zero is a representative by isNumRules, so the round "+
					"trip fixes it; ZeroDef identifies the result with dest_num(0)",
				"dest_num(0) = ind_zero",
				By(ZeroDef, At(NumDef.Membership, v.IndZero), isNumRules))

			a.Show(
				"suc(n₀) = 0 would read downstairs as ind_suc(dest_num(n₀)) "+
					"= ind_zero, which indSucNotZero forbids",
				By(destZero, At(destSuc, n), indSucNotZero))
		}),
})}

// SucInjective — distinct numbers have distinct successors.
//
// dest_num turns both successors into ind_suc values, where the naming part's
// injectivity cancels the ind_suc and leaves the two representatives
// equal; mk_num carries those back, since it undoes dest_num.
var SucInjective = sucInjectiveThm{family.Add(registry.ProofEntry{
	Name:     "SucInjective",
	Key:      "prop_f52d775da2bbf5b5",
	ServesAs: "suc_injective",
	Build: family.Theorem("∀m n:num. suc(m) = suc(n) ⇔ m = n",
		func(a *Argument, m, n Term) {
			v := ops(a.Ctx())
			rm, rn := v.DestNum.Apply(m), v.DestNum.Apply(n) // the two representatives

			a.Iff()
			a.Forward(
				"the equation descends to the representatives, where ind_suc cancels",
				func(b *Argument, sucEq Fact) {
					b.Show(
						"downstairs the equation reads ind_suc(rm) = ind_suc(rn); indSucInjective "+
							"cancels, and NumDef.Retraction carries rm, rn back to m₀, n₀",
						By(
							sucEq,
							At(destSuc, m),
							At(destSuc, n),
							At(indSucInjective, rm, rn),
							At(NumDef.Retraction, m),
							At(NumDef.Retraction, n)))
				})
			a.Backward(
				"suc(m₀) = suc(n₀) is a congruence of m₀ = n₀",
				Basic())
		}),
})}

// ---------------------------------------------------------------------------
// Induction on `num`
// ---------------------------------------------------------------------------
//
// Induction is not proved here so much as imported: the carving predicate's
// isNumInduct already IS the induction principle, stated one type down
// over is_num. What induction does is carry a predicate on `num` across
// the bridge and carry the conclusion back — the same transport the type
// and its axioms do, applied to a predicate instead of to an element.
//
// The one fact the transport needs and the type part does not state — the
// mirror of destSuc, going up — is weaker than its siblings there: it
// holds only at representatives. So it stays a section here rather than
// joining them.

// Induction — a predicate holding at 0 and inherited by successors
// holds everywhere.
//
// The proof hands isNumInductStrong the property P read at the point's
// tree, P(mk_num i), and reads its cover at dest_num n. The base case
// is P(0) at ind_zero (ZeroDef). The step needs mk_num(ind_suc i) to
// be suc(mk_num i), which holds only where the round trip closes, at a
// representative (mkSuc), and the strong form hands the step exactly
// that hypothesis. dest_num n is a representative (isNumDest) that
// mk_num carries back to n (NumDef.Retraction).
//
// Citing this entry: witnesses run (point, predicate), NOT the
// (predicate, point) the statement's own binder shows. This is the
// prefix-merge class, a property of the statement's shape: the ∀n
// lives inside the CONCLUSION, normalization hoists it into the
// install prefix beside P, and a stated prefix that does not cover the
// install prefix makes ground tuples read positionally against the
// install order, which runs (n, P). The witness-order census reports
// exactly this ([prefix-merged], 3 positional cites). Both consumers
// (Cases, Recursion) rely on this note; it lives here rather than at
// each cite site because the shape is a property of THIS entry.
var Induction = inductionThm{family.Add(registry.ProofEntry{
	Name:     "Induction",
	Key:      "prop_18ef44f766e2de1f",
	ServesAs: "num_induction",
	Build: family.Sections(
		Statement{
			Binders: "∀P:(num → bool). ∀n:num.",
			Hypotheses: []string{
				"P(0)",
				"∀n:num. P(n) ⇒ P(suc(n))",
			},
			Conclusion: "P(n)",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// mkSuc — destSuc read upwards. It carries the hypothesis destSuc
			// does not, because mk_num undoes dest_num only on representatives:
			// off is_num the round trip need not return i, and the identity
			// goes with it.
			mkSuc := ctx.Lemma(Statement{
				Binders: "∀i:ind.",
				Hypotheses: []string{
					"is_num(i)",
				},
				Conclusion: "suc(mk_num(i)) = mk_num(ind_suc(i))",
			},
				func(a *Argument, i Term, rep Fact) {
					v := ops(a.Ctx())
					a.Show(
						"SucDef routes suc(mk_num(i₀)) through dest_num(mk_num(i₀)); "+
							"i₀ being a representative collapses that round trip back to i₀",
						By(Normalized, rep, At(SucDef, v.MkNum.Apply(i)), At(NumDef.Membership, i)))
				})

			return ctx.Theorem(headline,
				func(a *Argument, P *TermWrapper, n Term, closure Fact) {
					v := ops(a.Ctx())

					// The property carried down to `ind`: P read at the point's
					// tree. It is spelled programmatically because it is an
					// argument, not a statement — nothing downstream refers to
					// the binder by name.
					i := Var("i", Ind{}.Reify())
					atTree := i.To(P.Apply(v.MkNum.Apply(i)))

					// The strengthened induction covers is_num with it, telling
					// the step that the point it climbs from is a representative.
					// Only one point of that cover is wanted — n₀'s own.
					r := v.DestNum.Apply(n)
					atRep := a.Have(
						"the strengthened induction at that property, read at dest_num(n)",
						"is_num(dest_num(n)) ⇒ P(mk_num(dest_num(n)))",
						ByInduction(At(isNumInductStrong, atTree, r),
							Case(
								"at ind_zero — ZeroDef says mk_num(ind_zero) is the 0 the base hypothesis is about",
								By(closure, ZeroDef)),
							Case(
								"across ind_suc — the step's own hypothesis says i is a "+
									"representative, so mkSuc turns mk_num(ind_suc(i)) into suc(mk_num(i))",
								By(closure, mkSuc))))

					a.Show(
						"dest_num(n₀) is a representative, so P holds at "+
							"mk_num(dest_num(n₀)), which the retraction makes n₀",
						By(atRep, At(isNumDest, n), NumDef.Retraction))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Primitive recursion
// ---------------------------------------------------------------------------
//
// Primitive recursion, the theorem the rest of `nat_num` is built
// with.
//
// A base value e and a step function f determine one function on ℕ. The
// difficulty is that `fn` cannot be written down — it is defined by what
// it does, not by a formula — so the proof builds its GRAPH first: the
// smallest relation G containing (0, e) and closed under
// (m, b) ↦ (suc m, f(b, m)). "Smallest" is built the way the carving predicate was built
// is_num, as the intersection of every relation with those two
// properties, and it is again the load-bearing half: closure alone makes
// G total, minimality makes it single-valued. A total single-valued
// relation is the graph of a function — reading it as one is pure
// logic, below the chapter — and the recursion equations then read
// straight off G's two rules.
//
// Uniqueness is a separate and much easier induction: two solutions
// agree at 0 because both are e, and inherit agreement because both take
// the same step.

// Recursion — a base value and a step function determine exactly one
// function on ℕ.
//
// Polymorphic in the result type — the only member here that is —
// because the values being recursed into have nothing to do with `num`.
//
// The file header has the argument. What each section contributes:
// `graph` builds the smallest closed relation, `functional` shows a
// smallest closed relation is a function, `existence` reads the
// recursion equations off it, `uniqueness` is the second induction, and
// the headline is their conjunction under ∃!.
var Recursion = recursionThm{family.Add(registry.ProofEntry{
	Name:     "Recursion",
	Key:      "prop_e0bc1adc29338ffc",
	ServesAs: "num_recursion",
	Build: family.Sections(
		"∀f:(A → num → A). ∀e:A. ∃!fn:(num → A). fn(0) = e ∧ (∀n:num. fn(suc(n)) = f(fn(n), n))",
		func(ctx *Script, headline string) *GoalStackNode {
			A := MakeVarType("A")

			// ---------------------------------------------------------------
			// graph — the smallest relation generated by the two rules
			// ---------------------------------------------------------------
			//
			// The intersection inherits both properties, and sits inside each
			// of them by construction — which is the second conjunct.
			graph := ctx.Lemma(
				"∀f:(A → num → A). ∀e:A. ∃G:(num → A → bool). "+
					"    (G(0, e) ∧ (∀m:num. ∀b:A. G(m, b) ⇒ G(suc(m), f(b, m)))) ∧ "+
					"    (∀R:(num → A → bool). "+
					"        (R(0, e) ∧ (∀m:num. ∀b:A. R(m, b) ⇒ R(suc(m), f(b, m)))) ⇒ "+
					"        (∀n:num. ∀a:A. G(n, a) ⇒ R(n, a)))",
				func(a *Argument, f *TermWrapper, e Term) {
					v := ops(a.Ctx())
					n, x := Var("n", NumType), Var("x", A)
					m, b := Var("m", NumType), Var("b", A)
					R := Var("R", MakeFun(NumType, MakeFun(A, TypeBool))) // num → A → bool

					// closedR — R contains (0, e) and is closed under the step rule.
					closedR := R.Apply(v.Zero, e).And(
						ForAll(m, b)(R.Apply(m, b).Imply(R.Apply(v.Suc.Apply(m), f.Apply(b, m)))))
					// isClosed — the same two rules as a property OF R. That is
					// how the last two leaves below use them: quoted whole, never
					// looked inside.
					isClosed := R.To(closedR)
					// The intersection: (n, x) is in it when every closed R holds there.
					a.Take(n.To(x.To(ForAll(R)(closedR.Imply(R.Apply(n, x))))))

					// Nothing to cite — each conjunct is a quantifier argument
					// about the intersection, so unfolding it leaves three
					// independent leaves. The last two name the property
					// `closed`, so they argue about "R is closed" as one atom
					// rather than as its two rules spelled out.
					a.Do(Expect(Basic(),
						Case(
							"(0, e) is in every closed R, hence in the intersection",
							CnfRefute()),
						Case(
							"the intersection is closed: if every closed R holds at "+
								"(m, b) then each holds at the step, by its own closure",
							DenoteTerm("closed", isClosed),
							Basic(),
							CnfRefute()),
						Case(
							"the intersection sits inside each closed R — that is what membership in it says",
							DenoteTerm("closed", isClosed),
							Basic(),
							CnfRefute()),
					))
				})

			// ---------------------------------------------------------------
			// functional — a smallest closed relation is single-valued
			// ---------------------------------------------------------------
			//
			// Closure alone gives a value at every n; minimality is what makes it
			// the ONLY one. Both halves come out of one induction, and each
			// uniqueness step is the same move: cut G down to the pairs that
			// already agree with the intended value, check that the smaller
			// relation is still closed, and let minimality say G was inside it
			// all along. The two Peano axioms are what make the cut-down
			// relation closed — SucNotZero because a successor is never the
			// index 0 being pinned, SucInjective because pinning suc(k) forces
			// the predecessor to be k.
			functional := ctx.Lemma(
				Statement{
					Binders: "∀f:(A → num → A). ∀e:A. ∀G:(num → A → bool).",
					// Minimality first: the closure rules, one hypothesis, are a
					// conjunction, which the first hypothesis of a statement
					// cannot be — a conjunction there reads as two.
					Hypotheses: []string{
						"∀R:(num → A → bool). " +
							"    (R(0, e) ∧ (∀m:num. ∀b:A. R(m, b) ⇒ R(suc(m), f(b, m)))) ⇒ (∀n:num. ∀a:A. G(n, a) ⇒ R(n, a))",
						"G(0, e) ∧ (∀m:num. ∀b:A. G(m, b) ⇒ G(suc(m), f(b, m)))",
					},
					Conclusion: "∀n:num. ∃y:A. G(n, y) ∧ (∀z:A. G(n, z) ⇒ z = y)",
				},
				func(a *Argument, f *TermWrapper, e Term, G *TermWrapper, minimal, closed Fact, n Term) {
					v := ops(a.Ctx())
					j, c := Var("j", NumType), Var("c", A)
					// pinAt(t, w) — G cut down to the pairs that already send the
					// index t to the value w. This is the relation minimality is
					// handed; everywhere else it is just G.
					pinAt := func(t, w Term) Term {
						return j.To(c.To(G.Apply(j, c).And(j.Eq(t).Imply(c.Eq(w)))))
					}
					// isValueAt — the predicate the induction runs on.
					y, z := Var("y", A), Var("z", A)
					isValueAt := j.To(Exists(y)(G.Apply(j, y).And(ForAll(z)(G.Apply(j, z).Imply(z.Eq(y))))))

					a.Show(
						"induction at «G has exactly one value at n», read at n₀",
						ByInduction(At(Induction, n, isValueAt),
							Case(
								"at 0 the value is e: G contains (0, e), and pinning index "+
									"0 to e leaves a closed relation because suc is never 0",
								Derive(func(b *Argument) {
									b.Take(e)
									b.Show(
										"minimality at G pinned to (0, e) puts every G-pair over index 0 at e",
										By(closed, minimal.At(pinAt(v.Zero, e)), SucNotZero))
								})),
							Case(
								"at suc(k) the value is f(w, k) for w the value at k: pinning suc(k) "+
									"to it stays closed — SucInjective sends the pinned successor to k",
								Derive(func(b *Argument) {
									k := b.Fix()
									w, atK := b.Unpack(b.Assume())
									b.Take(f.Apply(w, k))
									b.Show(
										"minimality at G pinned to (suc(k), f(w, k))",
										By(atK, closed, minimal.At(pinAt(v.Suc.Apply(k), f.Apply(w, k))), SucNotZero, SucInjective))
								}))))
				})

			// ---------------------------------------------------------------
			// existence — the recursion equations hold of some function
			// ---------------------------------------------------------------
			existence := ctx.Lemma(
				"∀f:(A → num → A). ∀e:A. ∃fn:(num → A). fn(0) = e ∧ (∀n:num. fn(suc(n)) = f(fn(n), n))",
				func(a *Argument, f, e Term) {
					// graph is already proved, so its ∃ is eliminated rather than
					// re-established — no restatement of its statement here.
					G, rules := a.Unpack(At(graph, f, e))

					single := a.Have(
						"G is single-valued, so it is the graph of a function",
						"∀n:num. ∃y:A. G₀(n, y) ∧ (∀z:A. G₀(n, z) ⇒ z = y)",
						By(rules, At(functional, f, e, G)))

					// A relation with exactly one value per argument IS a
					// function's graph — Skolemizing the value at each index
					// into one function is pure logic, so `single` is the only
					// premise the step needs.
					fn, isGraphOf := a.Obtain(
						"so name the function whose graph G is",
						"∃fn:(num → A). ∀x:num. ∀y:A. G₀(x, y) ⇔ y = fn(x)",
						By(single))

					a.Take(fn)
					a.Show(
						"G's two rules, read through that correspondence, ARE the recursion equations",
						By(isGraphOf, rules))
				})

			// ---------------------------------------------------------------
			// uniqueness — two solutions agree everywhere
			// ---------------------------------------------------------------
			uniqueness := ctx.Lemma(
				Statement{
					Binders: "∀f:(A → num → A). ∀e:A. ∀g h:(num → A).",
					Hypotheses: []string{
						"g(0) = e",
						"∀n:num. g(suc(n)) = f(g(n), n)",
						"h(0) = e",
						"∀n:num. h(suc(n)) = f(h(n), n)",
					},
					Conclusion: "∀k:num. g(k) = h(k)",
				},
				// Each solution's two equations, bound where the solution is.
				func(a *Argument, f, e Term, g *TermWrapper, gRec Fact, h *TermWrapper, hRec Fact, k Term) {
					j := Var("j", NumType)
					agree := j.To(g.Apply(j).Eq(h.Apply(j))) // the predicate induction runs on

					a.Show(
						"induction at «g and h agree at j», read at k₀",
						ByInduction(At(Induction, k, agree),
							Case(
								"both are e at 0",
								By(Normalized, gRec, hRec)),
							Case(
								"agreement is inherited: the same step function is applied to the same value",
								By(gRec, hRec))))
				})

			// ---------------------------------------------------------------
			// the theorem
			// ---------------------------------------------------------------
			return ctx.Theorem(headline,
				func(a *Argument, f, e Term) {
					// ∃! splits into the two sections' statements — a solution,
					// and no second one. `uniqueness` stays ungrounded in g and h:
					// the split's second leaf supplies both of them.
					a.Do(
						Cite(existence, f, e),
						Cite(uniqueness, f, e),
						StripQuant(), // name the solution existence promised
						Expect(Basic(),
							Case(
								"a solution exists — the one just named",
								CnfRefute()),
							Case(
								"and only one: two solutions agree at every point, so they are the same function",
								CnfRefute()),
						))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Case analysis on `num`
// ---------------------------------------------------------------------------
//
// Everything above builds `num` and hands back induction; from here on the
// chapter stops constructing and starts using.

// Cases — every number is zero or the successor of one.
//
// A consequence of induction, not a further construction: run Induction
// at the predicate the theorem itself states. Both of its branches are
// then reflexivity, so induction contributes no argument here — only its
// conclusion's reach, that these two shapes exhaust `num`.
var Cases = casesThm{family.Add(registry.ProofEntry{
	Name: "Cases",
	Key:  "prop_a34b5abab7f917cd",
	Build: family.Theorem("∀m:num. m = 0 ∨ (∃n:num. m = suc(n))",
		func(a *Argument, m Term) {
			v := ops(a.Ctx())
			x, n := Var("x", NumType), Var("n", NumType)
			// The predicate induction is run at — the theorem's own body.
			isZeroOrSuc := x.To(x.Eq(v.Zero).Or(Exists(n)(x.Eq(v.Suc.Apply(n)))))

			// Witness order is (point, predicate) — see Induction's entry.
			a.Show(
				"induction at «zero or a successor», read at m₀: 0 = 0 settles the "+
					"base and suc(k) = suc(k) the step, so neither consults the hypothesis",
				By(At(Induction, m, isZeroOrSuc)))
		}),
})}
