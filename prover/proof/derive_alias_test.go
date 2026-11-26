// derive_alias_test.go — the surface-name alias environment (derive.go
// §"Surface names"): claim texts spell readable names, and the block
// resolves them to the engine's minted variables under ONE NAME, ONE
// MEANING — a live spelling is never silently re-pointed. Automatic
// spellings (the goal's binder name, its α-rename base) are OFFERS,
// skipped when taken; an explicit Fix("u") name is strict — loud when
// taken; the minted spelling stays valid within the block that minted
// it (a sibling block may mint the same spelling afresh); and the
// section boundary alone binds statement names authoritatively.
//
// Every collision test plants a DECOY: a hypothesis in which the
// surface name is free, so the strip is forced to mint a renamed
// variable and the test distinguishes "resolved to the mint" from
// "resolved to the decoy" directly on the terms.
//
// The section shape is `∀n. R(n) ∧ Q(n) ⇒ Q(n)` rather than the
// tempting `∀n. R(n) ⇒ R(n)`: ConclImplyTactic deliberately refuses
// the degenerate A ⇒ A, so the antecedent must differ from the
// conclusion for a.Assume to strip.

package proof

import (
	"fmt"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/require"
)

// TestSurfaceAlias_FixOfferSkipsLiveName: after Fix on `∀n. …` with a
// free decoy `n` resident, the automatic spelling is NOT offered — the
// decoy keeps the name, the mint stays reachable by its minted
// spelling, and Fix("u") is the named road to a readable one.
//
//	R(n) ⊢ ∀n. R(n) ∧ Q(n) ⇒ Q(n)
func TestSurfaceAlias_FixOfferSkipsLiveName(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	R := ctx.Var("R", MakeFun(numType, TypeBool))
	Q := ctx.Var("Q", MakeFun(numType, TypeBool))
	n := ctx.Var("n", numType)

	sec := ctx.Section(MakeProp(
		ForAll(n)(R.Apply(n).And(Q.Apply(n)).Imply(Q.Apply(n))), R.Apply(n)))
	sec.Do(Derive(func(a *Argument) {
		fixed := a.Fix()
		v, ok := fixed.Core().AsVar()
		require.True(t, ok)
		require.NotEqual(t, "n", string(v.Name()), "the mint must rename away from the free decoy n")
		require.True(t, a.Term("n").Core().Equals(n.Core()),
			"the live decoy must keep its spelling — the automatic alias is an offer, not a rebind")
		require.True(t, a.Term(string(v.Name())).Core().Equals(fixed.Core()),
			"the minted spelling must resolve to the mint")
		h := a.Assume()
		a.Have("restate through the minted spelling", "R("+string(v.Name())+")", By(h))
		a.Show("the other conjunct closes the goal", By(h))
	}))
	require.True(t, sec.Proved(), "the block did not close")
}

// TestSurfaceAlias_AutoBindWhenFree: with no collision, bare Fix
// offers the goal's own binder name — the everyday case.
//
//	⊢ ∀n. R(n) ∧ Q(n) ⇒ Q(n)
func TestSurfaceAlias_AutoBindWhenFree(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	R := ctx.Var("R", MakeFun(numType, TypeBool))
	Q := ctx.Var("Q", MakeFun(numType, TypeBool))
	n := Var("n", numType)

	sec := ctx.Section(MakeProp(
		ForAll(n)(R.Apply(n).And(Q.Apply(n)).Imply(Q.Apply(n)))))
	sec.Do(Derive(func(a *Argument) {
		fixed := a.Fix()
		require.True(t, a.Term("n").Core().Equals(fixed.Core()),
			"an uncontested binder name must resolve to the mint")
		h := a.Assume()
		a.Have("restate through the surface name", "R(n)", By(h))
		a.Show("the other conjunct closes the goal", By(h))
	}))
	require.True(t, sec.Proved(), "surface-name claim did not resolve to the minted variable")
}

// TestSurfaceAlias_MintedSpellingStaysValid: within its block, the
// minted spelling is a legal claim spelling regardless of aliases (the
// escape hatch, and the whole existing corpus).
func TestSurfaceAlias_MintedSpellingStaysValid(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	R := ctx.Var("R", MakeFun(numType, TypeBool))
	Q := ctx.Var("Q", MakeFun(numType, TypeBool))
	n := ctx.Var("n", numType)

	sec := ctx.Section(MakeProp(
		ForAll(n)(R.Apply(n).And(Q.Apply(n)).Imply(Q.Apply(n))), R.Apply(n)))
	sec.Do(Derive(func(a *Argument) {
		fixed := a.Fix()
		v, ok := fixed.Core().AsVar()
		require.True(t, ok)
		h := a.Assume()
		a.Have("restate through the minted spelling", "R("+string(v.Name())+")", By(h))
		a.Show("the other conjunct closes the goal", By(h))
	}))
	require.True(t, sec.Proved(), "minted spelling stopped resolving")
}

// TestSurfaceAlias_NamedFixAndInheritance: Fix("p") makes the chosen
// name the one spelling; a nested block inherits it; and naming a
// LIVE spelling — here the inherited "p" — panics instead of
// re-pointing it.
func TestSurfaceAlias_NamedFixAndInheritance(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	R := ctx.Var("R", MakeFun(numType, TypeBool))
	Q := ctx.Var("Q", MakeFun(numType, TypeBool))
	n := ctx.Var("n", numType)

	sec := ctx.Section(MakeProp(
		ForAll(n)(R.Apply(n).And(Q.Apply(n)).Imply(Q.Apply(n))), R.Apply(n)))
	sec.Do(Derive(func(a *Argument) {
		outer := a.Fix("p")
		require.True(t, a.Term("p").Core().Equals(outer.Core()),
			"the chosen name must resolve to the mint")
		h := a.Assume()
		a.Have("an inner ∀ whose binder reuses the taken base name",
			"∀n:num. R(n) ∧ Q(n) ⇒ Q(n)",
			Derive(func(b *Argument) {
				b.Have("the outer name is inherited", "R(p)", By(h))
				require.Panics(t, func() { b.Fix("p") },
					"naming a live inherited spelling must panic")
				inner := b.Fix("q")
				require.False(t, inner.Core().Equals(outer.Core()),
					"the inner mint must be a fresh variable")
				h2 := b.Assume()
				b.Have("the inner name resolves to the inner mint", "R(q)", By(h2))
				b.Show("close the inner claim", By(h2))
			}))
		a.Have("outer p is still valid after the inner block", "R(p)", By(h))
		a.Show("close", By(h))
	}))
	require.True(t, sec.Proved(), "named spelling / inheritance broke the block")
}

// TestSurfaceAlias_NamedFixCollisionPanics: an explicit surface name
// that is already a declared variable panics — before any goal move,
// so the block continues undamaged.
func TestSurfaceAlias_NamedFixCollisionPanics(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	R := ctx.Var("R", MakeFun(numType, TypeBool))
	Q := ctx.Var("Q", MakeFun(numType, TypeBool))
	n := ctx.Var("n", numType)

	sec := ctx.Section(MakeProp(
		ForAll(n)(R.Apply(n).And(Q.Apply(n)).Imply(Q.Apply(n))), R.Apply(n)))
	sec.Do(Derive(func(a *Argument) {
		require.PanicsWithValue(t,
			`Argument.Fix("n"): that name is already a declared variable — pick a fresh one (the minted name always resolves)`,
			func() { a.Fix("n") },
			"a declared variable's name must be refused")
		fixed := a.Fix("m")
		require.True(t, a.Term("m").Core().Equals(fixed.Core()))
		h := a.Assume()
		a.Show("close", By(h))
	}))
	require.True(t, sec.Proved(), "the block did not survive the refused name")
}

// TestSurfaceAlias_ObtainWitnessKeepsLiveName: an Obtain'd witness
// whose ∃-binder collides with a live name does NOT re-point it — the
// ∃-binder's spelling is the author's own claim text, so a fresh
// binder name there is always available.
//
//	Q(m), R(k) ⊢ ∃j. R(j) ∨ Q(j)   — witnessed by the obtained mint
func TestSurfaceAlias_ObtainWitnessKeepsLiveName(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	R := ctx.Var("R", MakeFun(numType, TypeBool))
	Q := ctx.Var("Q", MakeFun(numType, TypeBool))
	m := ctx.Var("m", numType)
	k := ctx.Var("k", numType)
	j := Var("j", numType)

	sec := ctx.Section(MakeProp(
		Exists(j)(R.Apply(j).Or(Q.Apply(j))), Q.Apply(m), R.Apply(k)))
	sec.Do(Derive(func(a *Argument) {
		rk := a.Hyp(R.Apply(k).Core())
		w, got := a.Obtain("R is inhabited (at k)", "∃m:num. R(m)", By(rk))
		v, ok := w.Core().AsVar()
		require.True(t, ok)
		require.NotEqual(t, "m", string(v.Name()), "the witness mint must dodge the free decoy m")
		require.True(t, a.Term("m").Core().Equals(m.Core()),
			"the live decoy must keep its spelling — the ∃-binder's name is not re-pointed")
		require.True(t, a.Term(string(v.Name())).Core().Equals(w.Core()),
			"the minted spelling must resolve")
		a.Take(w)
		a.Show("the obtained fact settles the left disjunct", By(got))
	}))
	require.True(t, sec.Proved(), "the Obtain witness did not carry the goal")
}

// TestSurfaceAlias_ObtainFreshBinderAliased: an uncontested ∃-binder
// name aliases to the witness mint — the everyday Obtain.
//
//	R(k) ⊢ ∃j. R(j) ∨ Q(j)   — witnessed through the surface name
func TestSurfaceAlias_ObtainFreshBinderAliased(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	R := ctx.Var("R", MakeFun(numType, TypeBool))
	Q := ctx.Var("Q", MakeFun(numType, TypeBool))
	k := ctx.Var("k", numType)
	j := Var("j", numType)

	sec := ctx.Section(MakeProp(Exists(j)(R.Apply(j).Or(Q.Apply(j))), R.Apply(k)))
	sec.Do(Derive(func(a *Argument) {
		rk := a.Hyp(R.Apply(k).Core())
		w, got := a.Obtain("R is inhabited (at k)", "∃w:num. R(w)", By(rk))
		require.True(t, a.Term("w").Core().Equals(w.Core()),
			"the fresh ∃-binder name must alias to the witness mint")
		a.Take(a.Term("w"))
		a.Show("the obtained fact closes the goal", By(got))
	}))
	require.True(t, sec.Proved(), "the fresh ∃-binder's surface name did not resolve")
}

// TestSurfaceAlias_ObtainNamed: Named(…) in the proof list gives the
// witness its surface spelling, as Unpack's trailing names do — the
// claim's own binder name is then not offered, and a name already in
// use is refused.
func TestSurfaceAlias_ObtainNamed(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	R := ctx.Var("R", MakeFun(numType, TypeBool))
	Q := ctx.Var("Q", MakeFun(numType, TypeBool))
	k := ctx.Var("k", numType)
	j := Var("j", numType)

	sec := ctx.Section(MakeProp(Exists(j)(R.Apply(j).Or(Q.Apply(j))), R.Apply(k)))
	sec.Do(Derive(func(a *Argument) {
		rk := a.Hyp(R.Apply(k).Core())
		w, got := a.Obtain("R is inhabited (at k)", "∃w:num. R(w)", By(rk), Named("m"))
		require.True(t, a.Term("m").Core().Equals(w.Core()), "the named spelling must alias to the witness")
		require.Panics(t, func() { a.Term("w") }, "the claim's own binder name is not offered once the witness is named")
		require.Panics(t, func() { a.Obtain("again", "∃w:num. R(w)", By(rk), Named("k")) }, "a name in use is refused")
		require.Panics(t, func() { a.Obtain("again", "∃w:num. R(w)", By(rk), Named("p", "q")) }, "one name per witness")
		a.Take(a.Term("m"))
		a.Show("the obtained fact closes the goal", By(got))
	}))
	require.True(t, sec.Proved())
}

// TestSurfaceAlias_TheoremClosureParams: the section-boundary closure
// (Script.Theorem) binds statement binders through bindSlot, which is
// AUTHORITATIVE — the statement's names take the text namespace over
// anything resident (here a decoy free n), because the statement is
// the frame the body's claims are read in.
func TestSurfaceAlias_TheoremClosureParams(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	ctx.Var("R", MakeFun(numType, TypeBool))
	ctx.Var("Q", MakeFun(numType, TypeBool))
	ctx.Var("n", numType)

	sec := ctx.Theorem("Q(n) ⇒ (∀k:num. R(k)) ⇒ ∀n:num. R(n) ∨ Q(n)",
		func(a *Argument, decoy, law Fact, nn Term) {
			step := a.Have("R at n through the surface name", "R(n)", By(law.At(a.Term("n"))))
			a.Show("left disjunct", By(step))
		})
	require.True(t, sec.Proved(), "closure-bound statement binder did not resolve in a claim")
}

// TestTheorem_SequentStatementPanics: a section states a closed
// theorem — a statement text with hypotheses left of ⊢ panics at the
// section door, naming the closed spelling, before the body runs.
func TestTheorem_SequentStatementPanics(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	ctx.Var("R", MakeFun(numType, TypeBool))
	ctx.Var("Q", MakeFun(numType, TypeBool))
	ctx.Var("n", numType)

	var refusal string
	func() {
		defer func() { refusal = fmt.Sprint(recover()) }()
		ctx.Theorem("Q(n), ∀k:num. R(k) ⊢ ∀n:num. R(n) ∨ Q(n)",
			func(a *Argument) { t.Fatal("the body of a sequent section ran") })
	}()
	require.Contains(t, refusal, "has hypotheses left of ⊢, and a section states a closed theorem")
	closed := refusal[strings.LastIndex(refusal, ": ")+2:]
	require.NotContains(t, closed, "⊢", "the named spelling is closed")
	require.Contains(t, closed, "∀n:num.", "the free n is bound")
}

// TestSurfaceAlias_ClaimUndeclaredFreePanics: the TermText contract on
// the claim path — a free name the scope never declared is a typo, not
// a fresh variable, and the panic names it and the verb.
func TestSurfaceAlias_ClaimUndeclaredFreePanics(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	R := ctx.Var("R", MakeFun(numType, TypeBool))
	Q := ctx.Var("Q", MakeFun(numType, TypeBool))
	n := ctx.Var("n", numType)

	defer func() {
		r := recover()
		require.NotNil(t, r, "the typo'd claim must panic")
		require.Contains(t, fmt.Sprint(r), "Argument.Have", "the panic must name the verb")
		require.Contains(t, fmt.Sprint(r), "undeclared free [zzz:num]", "the panic must name the typo")
	}()
	sec := ctx.Section(MakeProp(
		ForAll(n)(R.Apply(n).And(Q.Apply(n)).Imply(Q.Apply(n)))))
	sec.Do(Derive(func(a *Argument) {
		a.Fix()
		h := a.Assume()
		a.Have("typo in the claim", "R(zzz)", By(h))
	}))
}

// TestSurfaceAlias_ClaimTextBoundNameOK: a name the claim text itself
// binds (∀/λ) is not an undeclared free.
func TestSurfaceAlias_ClaimTextBoundNameOK(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	ctx.Var("R", MakeFun(numType, TypeBool))
	ctx.Var("Q", MakeFun(numType, TypeBool))
	ctx.Var("n", numType)

	sec := ctx.Theorem("Q(n) ⇒ (∀k:num. R(k)) ⇒ ∀n:num. R(n) ∨ Q(n)",
		func(a *Argument, decoy, law Fact, nn Term) {
			restated := a.Have("the law weakened under a text-bound binder", "∀j:num. R(j) ∨ Q(j)", By(law))
			a.Show("the goal is its instance", By(restated.At(a.Term("n"))))
		})
	require.True(t, sec.Proved(), "a text-bound claim binder was mistaken for an undeclared free")
}

// TestSurfaceAlias_PanicLegend: when a verb fails with aliases active,
// the panic message carries the surface-name legend.
func TestSurfaceAlias_PanicLegend(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	R := ctx.Var("R", MakeFun(numType, TypeBool))
	Q := ctx.Var("Q", MakeFun(numType, TypeBool))
	n := ctx.Var("n", numType)

	defer func() {
		r := recover()
		require.NotNil(t, r, "the bad claim must panic")
		require.Contains(t, fmt.Sprint(r), "surface names: p ≔ ",
			"the panic message must carry the alias legend")
	}()
	sec := ctx.Section(MakeProp(
		ForAll(n)(R.Apply(n).And(Q.Apply(n)).Imply(Q.Apply(n))), R.Apply(n)))
	sec.Do(Derive(func(a *Argument) {
		a.Fix("p")
		a.Assume()
		a.Hyp("R(zzz)") // no such name — the failure must print the legend
	}))
}

// TestSurfaceAlias_SiblingMintsAreBranchLocal: a variable a block mints
// belongs to that block's goal. Two sibling branches each Fix a binder
// spelled c, at different types; the strip names both mints c₀ (each
// picks from its own goal), and the second registration is not a
// re-declaration of the first — the first branch's exit withdrew it.
//
//	⊢ (∀c:num. P(c) ⇒ P(c) ∨ Q(T)) ∧ (∀c:bool. Q(c) ⇒ Q(c) ∨ Q(F))
func TestSurfaceAlias_SiblingMintsAreBranchLocal(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	P := ctx.Var("P", MakeFun(numType, TypeBool))
	Q := ctx.Var("Q", MakeFun(TypeBool, TypeBool))
	cn, cb := Var("c", numType), Var("c", TypeBool)
	left := ForAll(cn)(P.Apply(cn).Imply(P.Apply(cn).Or(Q.Apply(T))))
	right := ForAll(cb)(Q.Apply(cb).Imply(Q.Apply(cb).Or(Q.Apply(F))))

	var mints []string
	branch := func(surface string) Action {
		return Derive(func(b *Argument) {
			fixed := b.Fix(surface)
			v, _ := fixed.Core().AsVar()
			mints = append(mints, string(v.Name()))
			h := b.Assume()
			b.Show("the left disjunct", By(h))
		})
	}
	sec := ctx.Section(MakeProp(left.And(right)))
	sec.Do(Derive(func(a *Argument) {
		a.Do(SplitConjAll(MakeCase("left", branch("u")), MakeCase("right", branch("v"))))
		_, stillDeclared := ctx.ParseScope.Vars[mints[1]]
		require.False(t, stillDeclared, "a closed branch's mint must leave the parse scope")
	}))
	require.True(t, sec.Proved())
	require.Equal(t, mints[0], mints[1], "the fixture must make both branches mint one name")
}

// TestSurfaceAlias_AliasedScopeKeepsAConstantsLettersItsOwn: a term or
// claim parsed after a block has minted a name reads a polymorphic
// constant's type letters as the constant's own, as the same text
// reads before any mint — the aliased scope is the script's scope with
// names added, and drops none of its switches. The composite below
// needs the constant at A := num, B := A, C := B: with the constant's
// `A` taken for the block's own it does not type.
func TestSurfaceAlias_AliasedScopeKeepsAConstantsLettersItsOwn(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	// What a member's script sets (NewScriptForEntry).
	ctx.ParseScope.FreshenMetaLetters = true

	tA, tB, tC := core.MakeVarType("A"), core.MakeVarType("B"), core.MakeVarType("C")
	// zz_comp : (B → C) → (A → B) → (A → C).
	ctx.ParseScope.ConstMetas["zz_comp"] = core.MakeConstMeta("zz_comp",
		MakeFun(MakeFun(tB, tC), MakeFun(MakeFun(tA, tB), MakeFun(tA, tC))))
	ctx.Var("f", MakeFun(tA, tB))
	ctx.Var("e", MakeFun(numType, tA))
	want := MakeFun(numType, tB)

	R := ctx.Var("R", MakeFun(numType, TypeBool))
	Q := ctx.Var("Q", MakeFun(numType, TypeBool))
	n := Var("n", numType) // the binder's name is free, so the Fix below aliases it
	sec := ctx.Section(MakeProp(ForAll(n)(R.Apply(n).And(Q.Apply(n)).Imply(Q.Apply(n)))))
	sec.Do(Derive(func(a *Argument) {
		before := a.Term("zz_comp(f, e)")
		require.True(t, before.Core().Type().Equals(want), "before any mint: %s", before.Core().Type())

		a.Fix()
		require.NotEmpty(t, a.surfaceAliases(), "fixture: the scope below must be the aliased one")
		after := a.Term("zz_comp(f, e)")
		require.True(t, after.Core().Type().Equals(want), "under an alias: %s", after.Core().Type())
		require.True(t, after.Core().AlphaEquals(before.Core()), "one text, one term")

		h := a.Assume()
		a.Show("the other conjunct closes the goal", By(h))
	}))
	require.True(t, sec.Proved())
}

// TestClaim_UnpinnedTypeLetterIsRefused: a claim that names a
// polymorphic constant and no term of its letter's type is refused at
// the claim door, as a statement is at the statement door — the letter
// would stay the parser's stand-in and the claim would be about a type
// its author never wrote. Pinned where the constant is written, it reads.
func TestClaim_UnpinnedTypeLetterIsRefused(t *testing.T) {
	setup := func() (*Script, *GoalStackNode) {
		ctx := NewScript(makeStepTestEnv())
		ctx.ParseScope.FreshenMetaLetters = true // as a member's script has it
		// zz_point : A, a constant whose instance nothing around it fixes.
		ctx.ParseScope.ConstMetas["zz_point"] = core.MakeConstMeta("zz_point", core.MakeVarType("A"))
		R := ctx.Var("R", MakeFun(numType, TypeBool))
		Q := ctx.Var("Q", MakeFun(numType, TypeBool))
		n := Var("n", numType)
		return ctx, ctx.Section(MakeProp(ForAll(n)(R.Apply(n).And(Q.Apply(n)).Imply(Q.Apply(n)))))
	}

	_, sec := setup()
	requirePanicContains(t, "zz_point⟨A:A⟩", func() {
		sec.Do(Derive(func(a *Argument) {
			a.Have("a point is itself, at no type in particular", "zz_point = zz_point", Basic())
		}))
	})

	_, sec = setup()
	sec.Do(Derive(func(a *Argument) {
		a.Fix()
		h := a.Assume()
		a.Have("a point is itself, at the naturals", "zz_point⟨A:num⟩ = zz_point", Basic())
		a.Show("the other conjunct closes the goal", By(h))
	}))
	require.True(t, sec.Proved())
}
