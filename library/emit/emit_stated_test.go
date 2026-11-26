// emit_stated_test.go — the renderings that read ExternalLeaf.Stated:
// a payload that is a type instance of the statement a dep serves
// renders as ctx.AtTypes(ctx.Dep(name), τ…) (By premise, Simp rule,
// Cite), and a Simp rule's marker is computed against the served
// statement rather than copied from the record. Plus the AtTypes
// fusion's Thm-slot spelling on a normalize-STABLE source — the branch
// the older fixture never reached.

package emit

import (
	"os/exec"
	"strings"
	"testing"

	"go.uber.org/goleak"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

// statedFixture is a polymorphic equation ∀x:A. f(x) = g(x) with f, g
// free at A → A, its instance at bool, and the same instance FLIPPED —
// enough to exercise every arm of the marker computation.
type statedFixture struct {
	stated, flipped, other core.Prop // the served statement, its equation turned around, a different shape
	instance               core.Prop // stated at A := bool
	instanceFlipped        core.Prop
}

func newStatedFixture() statedFixture {
	x := ext.Var("x", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	g := ext.Var("g", core.MakeFun(core.TypeA(), core.TypeA()))
	h := ext.Var("h", core.MakeFun(core.TypeA(), core.TypeA()))
	stated := prop.MakeProp(ext.ForAll(x)(f.Apply(x).Eq(g.Apply(x))).Core())
	flipped := prop.MakeProp(ext.ForAll(x)(g.Apply(x).Eq(f.Apply(x))).Core())
	other := prop.MakeProp(ext.ForAll(x)(f.Apply(x).Eq(h.Apply(x))).Core())
	toBool := core.MakeTypeSubst(core.TypeA(), core.TypeBool())
	return statedFixture{
		stated:          stated,
		flipped:         flipped,
		other:           other,
		instance:        core.PropTypeInst(stated, toBool),
		instanceFlipped: core.PropTypeInst(flipped, toBool),
	}
}

// simpSection records one simp_with over the given rule with the given
// flip bit, its rule child closed and a residual left: the shape
// SimpWithExpandFlipped produces.
func simpSection(rule core.Prop, flip bool) *proof.DetailedProofProto {
	C := ext.Var("C", core.TypeBool())
	goal := prop.MakeProp(C.Core())
	residual := prop.MakeProp(C.Core(), rule.Conclusion())
	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(rule), pb.PropRef(residual)},
			Step: &proof.StepProto_SimpWith{SimpWith: &proof.SimpWithProto{
				Rules:    []*ext.HolPropProto{pb.PropRef(rule)},
				RuleFlip: []bool{flip},
			}},
		},
		{Goal: pb.PropRef(rule), Step: &proof.StepProto_TrivialSimplify{}},
		{Goal: pb.PropRef(residual), Step: &proof.StepProto_TrivialSimplify{}},
	}
	return detailed(pb, steps...)
}

// statedResolver answers every key with one library theorem serving
// `stated` — the engine's registry tier, which hands emit the entry's
// own statement alongside its registered name.
func statedResolver(name string, stated core.Prop) func(core.PropKey) (ExternalLeaf, bool) {
	return func(key core.PropKey) (ExternalLeaf, bool) {
		return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: name, Stated: stated}, true
	}
}

func emitStated(t *testing.T, section *proof.DetailedProofProto, resolver func(core.PropKey) (ExternalLeaf, bool)) EmitResult {
	t.Helper()
	return emitMember(t, makeTestEnv(t), EmitOptions{
		FuncName:            "BuildStated",
		ResolveExternalLeaf: resolver,
	}, section)
}

// TestEmit_SimpMarkerReadsServedForm: the recorded bit reads against
// the rule the SESSION fired; the marker reads against the rule the
// target SERVES. Same statement → the bit as recorded; the equation
// turned around → toggled; another shape → the fusion declines to the
// pinned SimpWith, which replays the recorded rule verbatim.
func TestEmit_SimpMarkerReadsServedForm(t *testing.T) {
	defer goleak.VerifyNone(t)
	fx := newStatedFixture()

	// Session fired the stated form unflipped; the target serves it.
	res := emitStated(t, simpSection(fx.stated, false), statedResolver("LAW", fx.stated))
	if !strings.Contains(res.Source, `Simp(Fwd("LAW"))`) {
		t.Errorf("same statement: want the bit as recorded\n--- source: ---\n%s", res.Source)
	}

	// Session fired the clause `g = f`; the member's headline reads
	// `f = g` — the restated-headline class. Fwd as recorded would fold
	// where the session unfolded.
	res = emitStated(t, simpSection(fx.flipped, false), statedResolver("LAW", fx.stated))
	if !strings.Contains(res.Source, `Simp(Rev("LAW"))`) {
		t.Errorf("turned-around statement: want the bit toggled\n--- source: ---\n%s", res.Source)
	}
	// …and a recorded flip toggles back to Fwd.
	res = emitStated(t, simpSection(fx.flipped, true), statedResolver("LAW", fx.stated))
	if !strings.Contains(res.Source, `Simp(Fwd("LAW"))`) {
		t.Errorf("turned-around statement, recorded flipped: want Fwd\n--- source: ---\n%s", res.Source)
	}

	// The target serves a rule of another shape: no Simp can re-fire the
	// recorded rewrite, so the pinned rendering stands.
	res = emitStated(t, simpSection(fx.stated, false), statedResolver("LAW", fx.other))
	if strings.Contains(res.Source, "Simp(") {
		t.Errorf("another shape: the fusion must decline\n--- source: ---\n%s", res.Source)
	}
	if !strings.Contains(res.Source, "SimpWith(") {
		t.Errorf("another shape: want the pinned SimpWith rendering\n--- source: ---\n%s", res.Source)
	}

	// Unknown served form (the resolver cannot say what the name serves):
	// the bit as recorded — emit has nothing to read it against.
	res = emitStated(t, simpSection(fx.flipped, true), statedResolver("ROW", nil))
	if !strings.Contains(res.Source, `Simp(Rev("ROW"))`) {
		t.Errorf("unknown served form: want the bit as recorded\n--- source: ---\n%s", res.Source)
	}
}

// TestEmit_SimpRuleAtTypeInstance: a rule recorded as a type instance
// of the served statement renders as the instance — the dep's identity
// and the σ both kept — and its marker reads against the instance of
// the served form.
func TestEmit_SimpRuleAtTypeInstance(t *testing.T) {
	defer goleak.VerifyNone(t)
	fx := newStatedFixture()

	res := emitStated(t, simpSection(fx.instance, false), statedResolver("LAW", fx.stated))
	want := `Simp(Fwd(ctx.AtTypes(ctx.Dep("LAW"), TypeBool)))`
	if !strings.Contains(res.Source, want) {
		t.Errorf("type instance: want %s\n--- source: ---\n%s", want, res.Source)
	}
	if len(res.DepNames) != 1 || res.DepNames[0] != "LAW" {
		t.Errorf("DepNames = %v, want [LAW]", res.DepNames)
	}

	res = emitStated(t, simpSection(fx.instanceFlipped, false), statedResolver("LAW", fx.stated))
	want = `Simp(Rev(ctx.AtTypes(ctx.Dep("LAW"), TypeBool)))`
	if !strings.Contains(res.Source, want) {
		t.Errorf("turned-around type instance: want %s\n--- source: ---\n%s", want, res.Source)
	}
}

// TestEmit_ByPremiseAtTypeInstance: a named By premise whose install is
// a type instance of the served statement renders as the instance, so
// the replayed composite installs it EXACTLY (a *TypedThm premise) —
// the σ a bare name would hand back to replay's speculative
// re-adaptation.
func TestEmit_ByPremiseAtTypeInstance(t *testing.T) {
	defer goleak.VerifyNone(t)
	fx := newStatedFixture()

	// f(a) = g(a) ⇒ q ⊢ q — not propositionally trivial, so the body
	// renders (a ⊤-normalizing goal takes the trivial-true path).
	q := ext.Var("q", core.TypeBool())
	a := ext.Var("a", core.TypeBool())
	f := ext.WrapTerm(ext.Var("f", core.MakeFun(core.TypeBool(), core.TypeBool())))
	g := ext.WrapTerm(ext.Var("g", core.MakeFun(core.TypeBool(), core.TypeBool())))
	hyp := ext.WrapTerm(f.Apply(a).Eq(g.Apply(a)).Core()).Imply(q).Core()
	pb := ext.NewPoolBuilder()
	goal := prop.MakeProp(q.Core(), hyp)
	install := pb.PropRef(fx.instance)
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{install},
			Step: &proof.StepProto_By{By: &proof.ByProto{
				Premises: []*proof.ByPremiseProto{
					{Install: pb.PropRef(prop.MakeProp(hyp)), Resident: true},
					{Install: install, Witnesses: []uint32{pb.TermRef(a)}, Exact: true},
				},
				Shape: &proof.ByShapeProto{},
			}},
		},
		{Goal: install, Step: &proof.StepProto_TypeInst{TypeInst: pb.PropRef(fx.stated)}},
	}
	res := emitStated(t, detailed(pb, steps...), statedResolver("LAW", fx.stated))
	want := `At(ctx.AtTypes(ctx.Dep("LAW"), TypeBool), `
	if !strings.Contains(res.Source, want) {
		t.Errorf("By premise at a type instance: want %s\n--- source: ---\n%s", want, res.Source)
	}
	if len(res.DepNames) != 1 || res.DepNames[0] != "LAW" {
		t.Errorf("DepNames = %v, want [LAW]", res.DepNames)
	}
}

// TestEmit_AtTypesFusionThmSlotCompiles: the fused cross-type cite on a
// normalize-STABLE source, at a type the family has no phantom for (so
// no Inst[τ] spelling exists), renders ctx.Dep(entry) in the Thm slot,
// and the package type-checks.
func TestEmit_AtTypesFusionThmSlotCompiles(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}
	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	raw := prop.MakeProp(ext.ForAll(f, x, y)(x.Eq(y).Imply(f.Apply(x).Eq(f.Apply(y)).Core()).Core()).Core())
	source, _ := proof.Normalize(raw) // the session served the normalized form: normalize-stable
	if payloadIsClosedNormalizeUnstable(source) {
		t.Fatal("fixture defeated: the source must be normalize-stable to reach the bare-name branch")
	}
	vars := proof.OrderedPropTypeVars(source)
	if len(vars) != 1 {
		t.Fatalf("fixture defeated: want one type var, got %d", len(vars))
	}
	payload := core.PropTypeInst(source, core.MakeTypeSubst(vars[0], ext.MakeType("complex")))
	C := ext.Var("C", core.TypeBool())
	goal := prop.MakeProp(C.Core())
	residual := prop.MakeProp(C.Core(), payload.Conclusion())

	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(payload), pb.PropRef(residual)},
			Step:     &proof.StepProto_LemmaPreserve{LemmaPreserve: pb.PropRef(payload)},
		},
		{Goal: pb.PropRef(payload), Step: &proof.StepProto_TypeInst{TypeInst: pb.PropRef(source)}},
		{Goal: pb.PropRef(residual), Step: &proof.StepProto_TrivialSimplify{}},
	}
	resolver := func(key core.PropKey) (ExternalLeaf, bool) {
		if key == source.AlphaKey() {
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "POLY_ROW"}, true
		}
		return ExternalLeaf{}, false
	}
	const pkg = "attypesslotemit"
	src := emitMember(t, env, EmitOptions{
		Family:              "tmp/" + pkg,
		FuncName:            "Build_AtTypesSlot",
		ResolveExternalLeaf: resolver,
		// The dep is a landed sibling: ctx.Dep takes the entry var, so
		// the member vets only with one to spell.
		FamilyDepEntry: func(name string, _ core.PropKey) (FamilyDepRef, bool) {
			if name == "POLY_ROW" {
				return FamilyDepRef{Expr: "PolyRow"}, true
			}
			return FamilyDepRef{}, false
		},
	}, detailed(pb, steps...)).Source
	want := `Cite(ctx.AtTypes(ctx.Dep(PolyRow), MakeType("complex")))`
	if !strings.Contains(src, want) {
		t.Fatalf("want %s\n--- source: ---\n%s", want, src)
	}
	if strings.Contains(unspaced(src), `AtTypes("POLY_ROW"`) {
		t.Fatalf("the Thm slot rendered a bare name\n--- source: ---\n%s", src)
	}

	vetMemberWith(t, goBin, pkg, src, map[string]string{
		"polyrow.go": "package " + pkg + "\n\nimport \"github.com/euc-ai/xugo/library/registry\"\n\nvar PolyRow = &registry.ProofEntry{Name: \"POLY_ROW\"}\n",
	})
}

// TestEmit_DatatypeFieldTypeInstanceCompiles exercises a sole-letter
// instance whose dependency is a bare datatype theorem field.
func TestEmit_DatatypeFieldTypeInstanceCompiles(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}
	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	raw := prop.MakeProp(ext.ForAll(f, x, y)(x.Eq(y).Imply(f.Apply(x).Eq(f.Apply(y)).Core()).Core()).Core())
	source, _ := proof.Normalize(raw) // the session served the normalized form: normalize-stable
	if payloadIsClosedNormalizeUnstable(source) {
		t.Fatal("fixture defeated: the source must be normalize-stable to reach the bare-name branch")
	}
	vars := proof.OrderedPropTypeVars(source)
	if len(vars) != 1 {
		t.Fatalf("fixture defeated: want one type var, got %d", len(vars))
	}
	payload := core.PropTypeInst(source, core.MakeTypeSubst(vars[0], core.TypeBool()))
	C := ext.Var("C", core.TypeBool())
	goal := prop.MakeProp(C.Core())
	residual := prop.MakeProp(C.Core(), payload.Conclusion())

	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(payload), pb.PropRef(residual)},
			Step:     &proof.StepProto_LemmaPreserve{LemmaPreserve: pb.PropRef(payload)},
		},
		{Goal: pb.PropRef(payload), Step: &proof.StepProto_TypeInst{TypeInst: pb.PropRef(source)}},
		{Goal: pb.PropRef(residual), Step: &proof.StepProto_TrivialSimplify{}},
	}
	resolver := func(key core.PropKey) (ExternalLeaf, bool) {
		if key == source.AlphaKey() {
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "POLY_ROW"}, true
		}
		return ExternalLeaf{}, false
	}
	const pkg = "datatypefieldinstemit"
	src := emitMember(t, env, EmitOptions{
		Family:              "tmp/" + pkg,
		FuncName:            "Build_AtTypesSlot",
		ResolveExternalLeaf: resolver,
		// The dep is a landed sibling: ctx.Dep takes the entry var, so
		// the member vets only with one to spell.
		FamilyDepEntry: func(name string, _ core.PropKey) (FamilyDepRef, bool) {
			if name == "POLY_ROW" {
				return FamilyDepRef{Expr: "RecordData.Fields[0]", BareEntry: true}, true
			}
			return FamilyDepRef{}, false
		},
	}, detailed(pb, steps...)).Source
	want := `Cite(ctx.AtTypes(ctx.Dep(RecordData.Fields[0]), TypeBool))`
	if !strings.Contains(src, want) {
		t.Errorf("want %s\n--- source: ---\n%s", want, src)
	}
	if strings.Contains(unspaced(src), `AtTypes("POLY_ROW"`) {
		t.Fatalf("the Thm slot rendered a bare name\n--- source: ---\n%s", src)
	}

	vetMemberWith(t, goBin, pkg, src, map[string]string{
		"polyrow.go": "package " + pkg + "\n\nimport \"github.com/euc-ai/xugo/library/registry\"\n\nvar RecordData = struct { Fields []*registry.ProofEntry }{Fields: []*registry.ProofEntry{{Name: \"POLY_ROW\"}}}\n",
	})
}

// leanRwSection records one LeanRw over rule with the obligation child
// and the residual — the shape rewriteOnlyTacticCore produces.
func leanRwSection(rule core.Prop) *proof.DetailedProofProto {
	C := ext.Var("C", core.TypeBool())
	goal := prop.MakeProp(C.Core())
	residual := prop.MakeProp(C.Core(), rule.Conclusion())
	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(rule), pb.PropRef(residual)},
			Step:     &proof.StepProto_LeanRw{LeanRw: pb.PropRef(rule)},
		},
		{Goal: pb.PropRef(rule), Step: &proof.StepProto_TrivialSimplify{}},
		{Goal: pb.PropRef(residual), Step: &proof.StepProto_TrivialSimplify{}},
	}
	return detailed(pb, steps...)
}

// TestEmit_LeanRwRuleResolvesThroughStated: a rewrite rule that IS the
// statement a dep serves renders as the dep; one that is a type
// instance of it renders as the instance's stated form; one the dep
// does not serve exactly (turned around, a term pin) stays verbatim —
// the rule's instantiation is load-bearing.
func TestEmit_LeanRwRuleResolvesThroughStated(t *testing.T) {
	defer goleak.VerifyNone(t)
	fx := newStatedFixture()

	res := emitStated(t, leanRwSection(fx.stated), statedResolver("LAW", fx.stated))
	if !strings.Contains(res.Source, `LeanRw(ctx.Dep("LAW"))`) {
		t.Errorf("the served statement: want the dep reference\n--- source: ---\n%s", res.Source)
	}
	if len(res.DepNames) != 1 || res.DepNames[0] != "LAW" {
		t.Errorf("DepNames = %v, want [LAW]", res.DepNames)
	}

	res = emitStated(t, leanRwSection(fx.instance), statedResolver("LAW", fx.stated))
	if !strings.Contains(res.Source, `LeanRw(ctx.AtTypes(ctx.Dep("LAW"), TypeBool).Reference())`) {
		t.Errorf("a type instance: want the stated form at the instance\n--- source: ---\n%s", res.Source)
	}

	res = emitStated(t, leanRwSection(fx.flipped), statedResolver("LAW", fx.stated))
	if strings.Contains(unspaced(res.Source), `LeanRw(ctx.Dep(`) || strings.Contains(res.Source, "AtTypes(") {
		t.Errorf("a rule the dep does not serve exactly must stay verbatim\n--- source: ---\n%s", res.Source)
	}
	if !strings.Contains(res.Source, "LeanRw(ctx.MakePropText(") {
		t.Errorf("want the verbatim rule\n--- source: ---\n%s", res.Source)
	}
}

// TestEmit_PinnedSimpRuleNote: a simp rule that is a TERM instance of
// the dep's statement (a session term_specialize pin) declines the
// Simp fusion and is spelled out, with a note naming the pin.
func TestEmit_PinnedSimpRuleNote(t *testing.T) {
	defer goleak.VerifyNone(t)
	fx := newStatedFixture()
	a := ext.Var("a", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	g := ext.Var("g", core.MakeFun(core.TypeA(), core.TypeA()))
	pinned := prop.MakeProp(f.Apply(a).Eq(g.Apply(a)).Core()) // the stated rule at x := a

	res := emitStated(t, simpSection(pinned, false), statedResolver("LAW", fx.stated))
	if strings.Contains(unspaced(res.Source), "Simp(Fwd(") {
		t.Errorf("a pinned rule must not fuse into Simp over the ∀-form\n--- source: ---\n%s", res.Source)
	}
	if !strings.Contains(res.Source, "LAW pinned at a —") {
		t.Errorf("want the pin named\n--- source: ---\n%s", res.Source)
	}
	if !strings.Contains(res.Source, "SimpWith(") {
		t.Errorf("want the pinned SimpWith rendering\n--- source: ---\n%s", res.Source)
	}
}

// TestEmit_ACRegroupRenders: the AC composite renders as the kit's goal
// face over the certificate pair as cite targets, both declared.
func TestEmit_ACRegroupRenders(t *testing.T) {
	defer goleak.VerifyNone(t)
	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	z := ext.Var("z", core.TypeA())
	op := ext.Var("op", core.MakeFun(core.TypeA(), core.MakeFun(core.TypeA(), core.TypeA())))
	assoc := prop.MakeProp(ext.ForAll(x, y, z)(
		op.Apply(op.Apply(x).Apply(y)).Apply(z).Eq(op.Apply(x).Apply(op.Apply(y).Apply(z)))).Core())
	sym := prop.MakeProp(ext.ForAll(x, y)(op.Apply(x).Apply(y).Eq(op.Apply(y).Apply(x))).Core())
	C := ext.Var("C", core.TypeBool())
	goal := prop.MakeProp(C.Core())
	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{{
		Goal: pb.PropRef(goal),
		Step: &proof.StepProto_AcRegroup{AcRegroup: &proof.AcRegroupProto{
			Assoc: pb.PropRef(assoc), Sym: pb.PropRef(sym),
		}},
	}}
	resolver := func(key core.PropKey) (ExternalLeaf, bool) {
		switch key {
		case assoc.AlphaKey():
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "OP_ASSOC", Stated: assoc}, true
		case sym.AlphaKey():
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "OP_SYM", Stated: sym}, true
		}
		return ExternalLeaf{}, false
	}
	res := emitStated(t, detailed(pb, steps...), resolver)
	if !strings.Contains(res.Source, `ACRegroup(ctx.Dep("OP_ASSOC"), ctx.Dep("OP_SYM"))`) {
		t.Errorf("want the kit's goal face over the pair\n--- source: ---\n%s", res.Source)
	}
	if strings.Contains(res.Source, "ThmCert{}") {
		t.Errorf("no certificate placeholder may remain\n--- source: ---\n%s", res.Source)
	}
	if len(res.DepNames) != 2 {
		t.Errorf("DepNames = %v, want both certificates", res.DepNames)
	}
}
