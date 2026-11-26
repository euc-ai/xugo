package proof

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// The WF analyzer works over the REAL num type (the measure lands in
// ext.NumType and the obligation spells dsl's `<`), so the test
// vocabulary uses it too; the mod/zero stand-ins are test-local consts
// that never register globally.
func wfTestConst2(name string) ConstTerm {
	t := MakeFun(NumType, MakeFun(NumType, NumType))
	return MakeConstTerm(MakeConstMeta(TermName(name), t), t)
}

func wfTestConst0(name string) ConstTerm {
	return MakeConstTerm(MakeConstMeta(TermName(name), NumType), NumType)
}

// wfGcdEquation builds transcript D's shape at a fresh name:
// ∀m n. g(m, n) = COND(n = zero, m, g(n, mod(m, n)))
func wfGcdEquation(name string) (Prop, VarTerm) {
	mod, zero := wfTestConst2("zz_wf_mod"), wfTestConst0("zz_wf_zero")
	m, n := Var("m", NumType), Var("n", NumType)
	g := Var(TermName(name), MakeFun(NumType, MakeFun(NumType, NumType)))
	eq := g.Apply(m, n).Eq(Cond(
		n.Eq(WrapTerm(zero)).Core(),
		m.Core(),
		g.Apply(n, Apply(mod, m, n)).Core()))
	return prop.MakeProp(ForAll(m)(ForAll(n)(eq))), g.Core().(VarTerm)
}

func wfTestMeasure() Term {
	n := Var("n", NumType)
	return n.To(n).Core()
}

func TestAnalyzeWFDefinition(t *testing.T) {
	equation, defVar := wfGcdEquation("zz_gcd_wf")
	wfd, err := AnalyzeWFDefinition(equation, defVar, wfTestMeasure())
	if err != nil {
		t.Fatal(err)
	}
	if wfd.RecArgPos != 1 {
		t.Fatalf("RecArgPos = %d, want 1 (the measure binder names n)", wfd.RecArgPos)
	}
	if len(wfd.CallSites) != 1 {
		t.Fatalf("call sites = %d, want 1", len(wfd.CallSites))
	}
	site := wfd.CallSites[0]
	if len(site.Guards) != 1 {
		t.Fatalf("site guards = %d, want 1 (the else-branch negation)", len(site.Guards))
	}
	mod, zero := wfTestConst2("zz_wf_mod"), wfTestConst0("zz_wf_zero")
	m, n := Var("m", NumType), Var("n", NumType)
	wantGuard := Not(n.Eq(WrapTerm(zero))).Core()
	if !site.Guards[0].AlphaEquals(wantGuard) {
		t.Errorf("guard = %s, want %s", PrintTerm(site.Guards[0]), PrintTerm(wantGuard))
	}
	if !site.RecArg(wfd.RecArgPos).AlphaEquals(Apply(mod, m, n).Core()) {
		t.Errorf("call rec-arg = %s, want mod(m, n)", PrintTerm(site.RecArg(wfd.RecArgPos)))
	}
	// The obligation, β-normalized: ∀m n. ¬(n = zero) ⇒ mod(m, n) < n.
	decrease := Apply(dsl.NatLtMeta.Term(), Apply(mod, m, n).Core(), n.Core())
	want := ForAll(m)(ForAll(n)(
		Not(n.Eq(WrapTerm(zero))).Imply(decrease))).Core()
	if !wfd.Obligation.Conclusion().AlphaEquals(want) {
		t.Errorf("obligation = %s\nwant %s",
			PrintTerm(wfd.Obligation.Conclusion()), PrintTerm(want))
	}
	// The existence statement quantifies the author equation whole.
	if !wfd.ExistsStmt.Conclusion().HasFree(defVar) == false {
		// ∃f closes the definiendum.
		t.Errorf("ExistsStmt leaves the definiendum free: %s",
			PrintTerm(wfd.ExistsStmt.Conclusion()))
	}
}

func TestAnalyzeWFDefinitionRejects(t *testing.T) {
	zero := wfTestConst0("zz_wf_zero")
	m, n := Var("m", NumType), Var("n", NumType)
	g := Var("zz_gcd_rej", MakeFun(NumType, MakeFun(NumType, NumType)))
	gVar := g.Core().(VarTerm)
	nn := func(w *ext.TermWrapper) Term { return w.Core() }

	base, baseVar := wfGcdEquation("zz_gcd_rej2")
	kMeasure := func(name string) Term {
		v := Var(TermName(name), NumType)
		return v.To(v).Core()
	}

	for _, tc := range []struct {
		name    string
		p       Prop
		v       VarTerm
		measure Term
		want    string
	}{
		{
			"measure names no LHS argument",
			base, baseVar, kMeasure("k"),
			"names no LHS argument",
		},
		{
			"recursion in the guard",
			prop.MakeProp(ForAll(m)(ForAll(n)(g.Apply(m, n).Eq(
				Cond(nn(g.Apply(m, n).Eq(WrapTerm(zero))), m.Core(), n.Core()))))),
			gVar, wfTestMeasure(),
			"COND guard",
		},
		{
			"bare occurrence",
			// h consumes the function itself: h(g) — g reaches the RHS
			// unapplied.
			prop.MakeProp(ForAll(m)(ForAll(n)(g.Apply(m, n).Eq(
				Apply(MakeConstTerm(MakeConstMeta("zz_wf_h",
					MakeFun(MakeFun(NumType, MakeFun(NumType, NumType)), NumType)),
					MakeFun(MakeFun(NumType, MakeFun(NumType, NumType)), NumType)),
					g.Core()))))),
			gVar, wfTestMeasure(),
			"unapplied",
		},
		{
			"partial application",
			// h2 consumes a 1-argument section: h2(g(n)).
			prop.MakeProp(ForAll(m)(ForAll(n)(g.Apply(m, n).Eq(
				Apply(MakeConstTerm(MakeConstMeta("zz_wf_h2",
					MakeFun(MakeFun(NumType, NumType), NumType)),
					MakeFun(MakeFun(NumType, NumType), NumType)),
					nn(g.Apply(n))))))),
			gVar, wfTestMeasure(),
			"full argument list",
		},
		{
			"no recursion at all",
			prop.MakeProp(ForAll(m)(ForAll(n)(g.Apply(m, n).Eq(m)))),
			gVar, wfTestMeasure(),
			"direct shape",
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			_, err := AnalyzeWFDefinition(tc.p, tc.v, tc.measure)
			if err == nil {
				t.Fatal("analysis accepted a v1-excluded shape")
			}
			if tc.want != "" && !strings.Contains(err.Error(), tc.want) {
				t.Errorf("error %q does not mention %q", err, tc.want)
			}
		})
	}
}

func TestDeriveWFReadings(t *testing.T) {
	equation, _ := wfGcdEquation("zz_gcd_read")
	// The readings derivation is head-agnostic (const or still-var
	// definiendum); a test axiom stands in for the characterizing
	// theorem.
	characterizing := core.NewAxiom(equation.Conclusion())
	readings, err := DeriveWFReadings(characterizing)
	if err != nil {
		t.Fatal(err)
	}
	if len(readings) != 2 {
		t.Fatalf("readings = %d, want 2 (base + step)", len(readings))
	}

	mod, zero := wfTestConst2("zz_wf_mod"), wfTestConst0("zz_wf_zero")
	m, n := Var("m", NumType), Var("n", NumType)
	g := Var("zz_gcd_read", MakeFun(NumType, MakeFun(NumType, NumType)))

	// Base: the guard n = zero substitutes — ∀m. g(m, zero) = m.
	wantBase := ForAll(m)(g.Apply(m, WrapTerm(zero)).Eq(m)).Core()
	if !readings[0].Conclusion().AlphaEquals(wantBase) {
		t.Errorf("base reading = %s\nwant %s",
			PrintTerm(readings[0].Conclusion()), PrintTerm(wantBase))
	}
	// Step: guarded — ∀m n. ¬(n = zero) ⇒ g(m, n) = g(n, mod(m, n)).
	wantStep := ForAll(m)(ForAll(n)(
		Not(n.Eq(WrapTerm(zero))).Imply(
			g.Apply(m, n).Eq(g.Apply(n, Apply(mod, m, n)))))).Core()
	if !readings[1].Conclusion().AlphaEquals(wantStep) {
		t.Errorf("step reading = %s\nwant %s",
			PrintTerm(readings[1].Conclusion()), PrintTerm(wantStep))
	}
	for i, r := range readings {
		if r.NumHyps() != 0 {
			t.Errorf("reading %d carries %d hyps", i, r.NumHyps())
		}
	}
}
