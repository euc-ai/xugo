package emit

import (
	"os/exec"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"go.uber.org/goleak"
)

// TestEmit_PrefixFreeClaimText covers the claim-text rendering: a text
// payload carrying free variables renders as BARE mathematical
// content, with the types declared in Go through `ctx.Var(name, τ)`.
//
// The charter bans decl pieces left of ⊢ in blessed text
// (lint-enforced), so a prefixed form would cost every landing a
// hand-strip.
func TestEmit_PrefixFreeClaimText(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	m := ext.Var("m_0", core.TypeA())
	R := ext.WrapTerm(ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool())))
	G := ext.Var("G", core.TypeBool())

	// The claim's conclusion has two free vars (m_0 and R) whose types
	// the parser cannot infer — exactly the shape that forced the decl
	// prelude.
	claim := prop.MakeProp(R.Apply(m).Core())
	goal := prop.MakeProp(G.Core())
	residual := prop.MakeProp(G.Core(), claim.Conclusion())

	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(claim), pb.PropRef(residual)},
			Step:     &proof.StepProto_Assert{Assert: pb.PropRef(claim)},
		},
		{
			Goal: pb.PropRef(claim),
			Step: &proof.StepProto_TrivialSimplify{},
		},
		{
			Goal: pb.PropRef(residual),
			Step: &proof.StepProto_TrivialSimplify{},
		},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildClaimText"}, detailed(pb, steps...)).Source
	// The claim is stated as mathematics; the types are declared in Go.
	if !strings.Contains(src, `AssertStep(ctx.MakePropText("R(m₀)")`) {
		t.Errorf("claim did not render prefix-free\n--- source: ---\n%s", src)
	}
	for _, decl := range []string{`ctx.Var("m_0", `, `ctx.Var("R", `} {
		if !strings.Contains(src, decl) {
			t.Errorf("missing scope registration %q\n--- source: ---\n%s", decl, src)
		}
	}
	// No parsed text payload spells a turnstile — the predicate the gate
	// suite's lint enforces.
	assertNoTurnstile(t, src)
}

// assertNoTurnstile mirrors the gate suite's
// TestLintNoTurnstileInStatementText on emit output: no PARSED text
// payload — a MakePropText argument, a headline, a lemma statement —
// spells ⊢. Case / Have / Show labels are documentation, not parsed
// text, and are exempt there as here.
func assertNoTurnstile(t *testing.T, src string) {
	t.Helper()
	for _, line := range strings.Split(src, "\n") {
		for _, verb := range []string{"MakePropText(\"", "family.Theorem(\"", "ctx.Lemma(\""} {
			_, rest, found := strings.Cut(line, verb)
			if !found {
				continue
			}
			if text, _, closed := strings.Cut(rest, "\""); closed && strings.Contains(text, "⊢") {
				t.Errorf("a parsed text spells ⊢ in: %s", line)
			}
		}
	}
}

// TestEmit_ClaimTextPinsANameHeldAtTwoTypes covers a member whose
// steps mint one free name at two types (kernel-distinct variables,
// as disjoint branches mint them): `Script.Var` refuses the second
// type, so neither is registered. Each is declared as a plain Go value,
// and each claim that spells the name passes the variable it means as
// a scope override — the text stays bare, with no declaration prelude.
func TestEmit_ClaimTextPinsANameHeldAtTwoTypes(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	mA := ext.Var("m_0", core.TypeA())
	mBool := ext.Var("m_0", core.TypeBool())
	R := ext.WrapTerm(ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool())))
	Q := ext.WrapTerm(ext.Var("Q", core.MakeFun(core.TypeBool(), core.TypeBool())))
	G := ext.Var("G", core.TypeBool())

	first := prop.MakeProp(R.Apply(mA).Core())
	second := prop.MakeProp(Q.Apply(mBool).Core())
	goal := prop.MakeProp(G.Core())
	afterFirst := prop.MakeProp(G.Core(), first.Conclusion())
	afterSecond := prop.MakeProp(G.Core(), first.Conclusion(), second.Conclusion())

	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(first), pb.PropRef(afterFirst)},
			Step:     &proof.StepProto_Assert{Assert: pb.PropRef(first)},
		},
		{
			Goal: pb.PropRef(first),
			Step: &proof.StepProto_TrivialSimplify{},
		},
		{
			Goal:     pb.PropRef(afterFirst),
			SubGoals: []*ext.HolPropProto{pb.PropRef(second), pb.PropRef(afterSecond)},
			Step:     &proof.StepProto_Assert{Assert: pb.PropRef(second)},
		},
		{
			Goal: pb.PropRef(second),
			Step: &proof.StepProto_TrivialSimplify{},
		},
		{
			Goal: pb.PropRef(afterSecond),
			Step: &proof.StepProto_TrivialSimplify{},
		},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildTwoTypes"}, detailed(pb, steps...)).Source
	for _, claim := range []string{`ctx.MakePropText("R(m₀)", m_0`, `ctx.MakePropText("Q(m₀)", m_0`} {
		_, argument, found := strings.Cut(src, claim)
		if !found || !strings.Contains(strings.SplitN(argument, "\n", 2)[0], ".Core()") {
			t.Errorf("claim did not pin its variable by the core term after %q\n--- source: ---\n%s", claim, src)
		}
	}
	if got := strings.Count(src, `:= Var("m_0", `); got != 2 {
		t.Errorf("want both m_0 instances declared unregistered, got %d\n--- source: ---\n%s", got, src)
	}
	if strings.Contains(unspaced(src), `ctx.Var("m_0"`) {
		t.Errorf("a name held at two types was registered\n--- source: ---\n%s", src)
	}
	assertNoTurnstile(t, src)

	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skip("go binary not on PATH")
	}
	const pkg = "twotypesemit"
	member := emitMember(t, env, EmitOptions{Family: "tmp/" + pkg, FuncName: "Build_TwoTypes"}, detailed(pb, steps...)).Source
	assertNoTurnstile(t, member)
	vetMember(t, goBin, pkg, member)
}
