package emit

import (
	"fmt"
	"go/parser"
	"go/token"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/utils"
	"go.uber.org/goleak"
	"google.golang.org/protobuf/types/known/emptypb"
)

// makeTestEnv builds a ProverEnv with mock const-meta service and a
// generous CNF refuter timeout. The replay cache (see cnf_replay_test.go)
// is wired in so any AutoExpand calls a test makes never invoke the live
// CNF refuter once testdata/cnf_replay.gob has been recorded.
func makeTestEnv(t *testing.T) *proof.ProverEnv {
	var cnfNormalizationCache utils.Map[core.TermKey, proof.Prop]
	env := &proof.ProverEnv{
		ProofService:          proof.MockConstMetaService(),
		CnfRefuterTimeout:     30 * time.Second,
		CnfNormalizationCache: &cnfNormalizationCache,
		CnfNormalizeCache:     proof.NewCNFNormalizeCache(),
	}
	installCNFReplay(t, env)
	return env
}

// emitTestFamily is the family a fixture member renders into unless the
// test names its own.
const emitTestFamily = "sets/set_order"

// detailed binds one section's recorded ministep tree to its pool. Call
// it after every ref the steps use has been added to pb.
func detailed(pb *ext.PoolBuilder, steps ...*proof.StepProto) *proof.DetailedProofProto {
	return &proof.DetailedProofProto{Steps: steps, Pool: pb.Pool()}
}

// unspaced is s with its blanks and line breaks removed: a test that
// asks whether the emitted source holds a piece of code reads both
// sides so, since the formatter lays a call past the width out over
// lines.
func unspaced(s string) string { return strings.Join(strings.Fields(s), "") }

// emitMember renders sections as one member (Family defaults to
// emitTestFamily), failing the test on an emit error (fatally) or on
// output that does not parse. A record whose steps were written against
// a goal with hypotheses is opened on its closed statement first
// (closedRecord): a section states a closed theorem, and emit refuses
// one whose goal carries hypotheses.
func emitMember(t *testing.T, env *proof.ProverEnv, opts EmitOptions, sections ...*proof.DetailedProofProto) EmitResult {
	t.Helper()
	if opts.Family == "" {
		opts.Family = emitTestFamily
	}
	for i, d := range sections {
		sections[i] = closedRecord(env, d)
	}
	res, err := EmitMember(sections, env.ProofService.LoadConstMeta, opts)
	if err != nil {
		t.Fatalf("EmitMember: %v", err)
	}
	if _, err := parser.ParseFile(token.NewFileSet(), "member.go", res.Source, parser.AllErrors); err != nil {
		t.Errorf("emitted source does not parse: %v\n--- source: ---\n%s", err, res.Source)
	}
	return res
}

// closedRecord is d opened on its closed statement: when the first
// step's goal holds hypotheses, the record starts at the goal with them
// curried onto the conclusion as leading premises and strips them, one
// StripImp each, down to the goal the steps were written against — the
// session that proved a closed statement records the same strips. A
// record whose goal holds none is d itself.
func closedRecord(env *proof.ProverEnv, d *proof.DetailedProofProto) *proof.DetailedProofProto {
	if len(d.Steps) == 0 || len(d.Steps[0].Goal.Hyps) == 0 {
		return d
	}
	goal, _ := ext.NewPoolReader(d.Pool, env.ProofService.LoadConstMeta).Prop(d.Steps[0].Goal)
	pb := ext.NewPoolBuilderExtending(d.Pool)
	hyps := goal.Hyps()
	stated := func(k int) core.Prop { // the first k hypotheses assumed, the rest premises
		t := goal.Conclusion()
		for i := len(hyps) - 1; i >= k; i-- {
			t = ext.WrapTerm(hyps[i]).Imply(t).Core()
		}
		return core.MakeProp(t, hyps[:k]...)
	}
	strips := make([]*proof.StepProto, 0, len(hyps)+len(d.Steps))
	for k := range hyps {
		next := d.Steps[0].Goal
		if k+1 < len(hyps) {
			next = pb.PropRef(stated(k + 1))
		}
		strips = append(strips, &proof.StepProto{
			Goal:     pb.PropRef(stated(k)),
			SubGoals: []*ext.HolPropProto{next},
			Step:     &proof.StepProto_StripImp{StripImp: &emptypb.Empty{}},
		})
	}
	return &proof.DetailedProofProto{Steps: append(strips, d.Steps...), Pool: pb.Pool()}
}

// TestEmit_RefusesASequentSection: a section states a closed theorem,
// so a record whose goal carries hypotheses is refused, naming the
// closed spelling the session's goal should have stated.
func TestEmit_RefusesASequentSection(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := makeTestEnv(t)
	P := ext.WrapTerm(ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool())))
	Q := ext.WrapTerm(ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool())))
	a := ext.Var("a", core.TypeA())
	pb := ext.NewPoolBuilder()
	goal := pb.PropRef(prop.MakeProp(Q.Apply(a).Core(), P.Apply(a).Core()))
	record := detailed(pb, &proof.StepProto{Goal: goal, Step: &proof.StepProto_CnfRefute{}})
	_, err := EmitMember([]*proof.DetailedProofProto{record}, env.ProofService.LoadConstMeta,
		EmitOptions{Family: emitTestFamily, FuncName: "Build_Sequent"})
	if err == nil {
		t.Fatal("a record whose goal carries hypotheses emitted")
	}
	for _, want := range []string{"a section states a closed theorem", "(P(a) ⇒ Q(a))"} {
		if !strings.Contains(err.Error(), want) {
			t.Errorf("the refusal does not say %q: %v", want, err)
		}
	}
}

// vetMember type-checks an emitted member of family "tmp/<pkg>" in a
// scratch package directory beside this package: the member file and a
// family handle. The bare proof names the member spells are in scope
// by the dot import of library/authoring the emitter wrote into it, or
// not at all — so this is also the check that the emitter writes the
// import exactly where a file needs one: a missing one is "undefined",
// a needless one "imported and not used". The directory is removed
// when the test ends.
func vetMember(t *testing.T, goBin, pkg, src string) {
	t.Helper()
	vetMemberWith(t, goBin, pkg, src, nil)
}

// landedEntry gives a fixture's dep an entry var, as a landed dep has
// one: the FamilyDepEntry option naming the var for the dep's
// registered name, and the scratch package's file declaring it — a bare
// registry entry, the cite target the emitted member compiles against.
// A dep with no entry renders as its quoted name, which no cite verb
// takes.
func landedEntry(pkg, depName, ident string) (func(string, core.PropKey) (FamilyDepRef, bool), map[string]string) {
	resolve := func(name string, _ core.PropKey) (FamilyDepRef, bool) {
		if name != depName {
			return FamilyDepRef{}, false
		}
		return FamilyDepRef{Expr: ident, BareEntry: true}, true
	}
	declared := fmt.Sprintf("package %s\n\nimport \"github.com/euc-ai/xugo/library/registry\"\n\nvar %s = &registry.ProofEntry{Name: %q}\n",
		pkg, ident, depName)
	return resolve, map[string]string{"entries.go": declared}
}

// vetMemberWith is vetMember with further files of the scratch package
// (name → content) — the declarations a member reads from its family.
func vetMemberWith(t *testing.T, goBin, pkg, src string, further map[string]string) {
	t.Helper()
	pkgDir := "testdata_" + pkg + "_tmp"
	if err := os.MkdirAll(pkgDir, 0o755); err != nil {
		t.Fatalf("mkdir scratch package: %v", err)
	}
	t.Cleanup(func() { _ = os.RemoveAll(pkgDir) })
	familyFile := fmt.Sprintf("package %s\n\nimport \"github.com/euc-ai/xugo/library/registry\"\n\nvar family = registry.NewFamily(\"tmp/%s\", nil)\n", pkg, pkg)
	files := map[string]string{
		"member.go": src,
		"family.go": familyFile,
	}
	for name, content := range further {
		files[name] = content
	}
	for name, content := range files {
		if err := os.WriteFile(filepath.Join(pkgDir, name), []byte(content), 0o644); err != nil {
			t.Fatalf("write %s: %v", name, err)
		}
	}
	out, err := exec.Command(goBin, "vet", "./"+pkgDir).CombinedOutput()
	if err != nil {
		t.Fatalf("go vet on the emitted member failed:\n%s\n\n--- member.go: ---\n%s", out, src)
	}
}

// TestEmit_AssertStep guards against a regression where the
// _AssertStep ministep type fell through emit.emitMiniStep's switch
// to the "unhandled ministep" placeholder (rendering `nil`, which
// would runtime-panic when ctx.Do dereferences it).
//
// We construct a synthetic single-step DetailedProofProto whose only
// ministep is Assert (the test does not require a replay-valid proof —
// emit just renders, it doesn't replay), then assert the source
// contains a real `AssertStep(ctx.MakePropText(...))` call site and no
// "unhandled" placeholders.
func TestEmit_AssertStep(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	P := ext.Var("P", core.TypeBool())
	Q := ext.Var("Q", core.TypeBool())
	goal := prop.MakeProp(P.Imply(Q))
	claim := prop.MakeProp(P.Imply(Q)) // hyp-free; emit doesn't validate replay

	pb := ext.NewPoolBuilder()
	step := &proof.StepProto{
		Goal: pb.PropRef(goal),
		Step: &proof.StepProto_Assert{
			Assert: pb.PropRef(claim),
		},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildAssert"}, detailed(pb, step)).Source

	if !strings.Contains(src, "AssertStep(ctx.MakePropText(") {
		t.Errorf("Assert ministep did not render as AssertStep(ctx.MakePropText(...))\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "unhandled ministep") {
		t.Errorf("ministep fell through to unhandled placeholder\n--- source: ---\n%s", src)
	}
}

// TestEmit_StmtTextForm_PolyMultiInstance verifies the member statement
// of a polymorphic const at multiple type instantiations round-trips as
// TEXT — the admission gate refuses a statement that does not. The prop
// is the exact top statement shape of cardinality.HasSizeFunspace: has_size at three
// instances (A, B, A→B) with a Skolem-named meta type-var (?83621), set_member
// at two instances, set_comprehension/comprehension_spec/nat_pow, a λ∃ set-comprehension body, and
// free vars of polymorphic types.
func TestEmit_StmtTextForm_PolyMultiInstance(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)
	reg := func(m core.ConstTermMeta) core.ConstTermMeta {
		got, _ := env.ProofService.LoadOrStoreConstMeta(m)
		return got
	}

	A := core.MakeVarType("A")
	B := core.MakeVarType("B")
	num := ext.NumType
	setA := core.MakeFun(A, core.TypeBool())
	setB := core.MakeFun(B, core.TypeBool())
	funAB := core.MakeFun(A, B)
	setAB := core.MakeFun(funAB, core.TypeBool())

	// Metas with production-faithful abstract type-var names: has_size's
	// meta var is the Normalize-fresh `?83621`, comprehension_spec's is `?66608` —
	// the printer surfaces these verbatim in ⟨…⟩ annotations, and the
	// parser must resolve them.
	skolHS := core.MakeVarType("?83621")
	skolSS := core.MakeVarType("?66608")
	hasSizeMeta := reg(core.MakeConstMeta("has_size",
		core.MakeFun(core.MakeFun(skolHS, core.TypeBool()), num, core.TypeBool())))
	inMeta := reg(core.MakeConstMeta("set_member",
		core.MakeFun(A, core.MakeFun(A, core.TypeBool()), core.TypeBool())))
	setComprehensionMeta := reg(core.MakeConstMeta("set_comprehension",
		core.MakeFun(core.MakeFun(A, core.TypeBool()), core.MakeFun(A, core.TypeBool()))))
	comprehensionSpecMeta := reg(core.MakeConstMeta("comprehension_spec",
		core.MakeFun(skolSS, core.TypeBool(), skolSS, core.TypeBool())))
	expMeta := reg(core.MakeConstMeta("nat_pow", core.MakeFun(num, num, num)))

	hsA := ext.Const(hasSizeMeta, core.MakeFun(setA, num, core.TypeBool()))
	hsB := ext.Const(hasSizeMeta, core.MakeFun(setB, num, core.TypeBool()))
	hsAB := ext.Const(hasSizeMeta, core.MakeFun(setAB, num, core.TypeBool()))
	inA := ext.Const(inMeta, core.MakeFun(A, setA, core.TypeBool()))
	inB := ext.Const(inMeta, core.MakeFun(B, setB, core.TypeBool()))
	setComprehensionAB := ext.Const(setComprehensionMeta, core.MakeFun(setAB, setAB))
	comprehensionSpecAB := ext.Const(comprehensionSpecMeta, core.MakeFun(funAB, core.TypeBool(), funAB, core.TypeBool()))
	expC := ext.Const(expMeta, expMeta.AbsType())

	s := ext.Var("s", setA)
	tv := ext.Var("t", setB)
	m := ext.Var("m", num)
	n := ext.Var("n", num)
	d := ext.Var("d", B)
	f := ext.Var("f", funAB)
	x := ext.Var("x", A)
	g := ext.Var("GEN%PVAR%148", funAB)

	member := comprehensionSpecAB.Apply(g,
		ext.ForAll(x)(inA.Apply(x, s).Imply(inB.Apply(f.Apply(x), tv))).
			And(ext.ForAll(x)(ext.Not(inA.Apply(x, s)).Imply(f.Apply(x).Eq(d)))),
		f)
	comprehension := setComprehensionAB.Apply(g.To(ext.Exists(f)(member)))
	concl := hsA.Apply(s, m).And(hsB.Apply(tv, n)).
		Imply(hsAB.Apply(comprehension, expC.Apply(n, m)))
	goal := prop.MakeProp(concl)

	pb := ext.NewPoolBuilder()
	step := &proof.StepProto{
		Goal: pb.PropRef(goal),
		Step: &proof.StepProto_Assert{
			Assert: pb.PropRef(goal),
		},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildHasSizeFunspaceShape"}, detailed(pb, step)).Source

	// The statement is the Theorem call's first argument, inline — in
	// parts, since it has a premise (a Statement literal up to the body).
	_, after, ok := strings.Cut(src, "family.Theorem(")
	if !ok {
		t.Fatalf("no family.Theorem call emitted\n--- source: ---\n%s", src)
	}
	goalText, _, _ := strings.Cut(after, "func(")
	// The annotated multi-instance const must appear with its Skolem-named
	// type-var — the exact syntax the parser round-trips.
	if !strings.Contains(goalText, "has_size⟨?83621:") {
		t.Errorf("expected Skolem-annotated has_size in the statement text\n--- goal text: ---\n%s", goalText)
	}
}

// TestEmit_Arith guards the emit branch for the unified arithmetic-automation
// ministep: an Arith StepProto must render as the bare `Arith()` Step
// (resolving to the proof.Arith alias), not fall through emitMiniStep's
// switch to the "unhandled ministep" panic. emit only renders; it does
// not replay, so the synthetic goal need not be Arith-provable.
func TestEmit_Arith(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	// emit deserializes each section goal up front and the mock const-meta
	// service has no arithmetic consts, so we use a bool goal (only special
	// consts, like TestEmit_AssertStep). Faithful to the rendering under test:
	// emit only renders the ministep variant, it does not replay, so the goal
	// shape is irrelevant to whether the dispatch renders.
	P := ext.Var("P", core.TypeBool())
	Q := ext.Var("Q", core.TypeBool())
	pb := ext.NewPoolBuilder()
	goal := pb.PropRef(prop.MakeProp(P.Imply(Q)))

	step := &proof.StepProto{
		Goal: goal,
		Step: &proof.StepProto_Arith{Arith: &emptypb.Empty{}},
	}
	src := emitMember(t, env, EmitOptions{FuncName: "BuildArith"}, detailed(pb, step)).Source
	if !strings.Contains(src, "Arith()") {
		t.Errorf("Arith ministep did not render as Arith()\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "Capabilit") {
		t.Errorf("the member declares a capability — none is declared, the use is observed\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "unhandled ministep") {
		t.Errorf("ministep fell through to unhandled placeholder\n--- source: ---\n%s", src)
	}
}

// TestPhaseC_SectionTextRoundTrip exercises ParsePropTextInScope and
// Script.MakePropText on a synthetic subset-style prop.
// Verifies:
// - emit's FormatPropForParser output parses back to an alpha-equal
// prop when scope carries the non-well-known consts;
// - Script.MakePropText respects the script's accumulated scope.
func TestPhaseC_SectionTextRoundTrip(t *testing.T) {
	A := core.MakeVarType("A")
	setT := core.MakeFun(A, core.TypeBool())
	subsetMeta := core.MakeConstMeta("subset", core.MakeFun(setT, setT, core.TypeBool()))
	subsetTerm := core.MakeConstTerm(subsetMeta, core.MakeFun(setT, setT, core.TypeBool()))

	// subset reflexivity: ∀s. subset(s, s) — closed, polymorphic in A.
	s := ext.Var("s", setT)
	original := prop.MakeProp(ext.ForAll(s)(ext.WrapTerm(subsetTerm).Apply(s, s)))

	// Bare ext-level round-trip with explicit scope.
	text := prop.FormatPropForParser(original)
	scope := &dsl.ParseScope{
		Consts: map[string]core.ConstTerm{"subset": subsetTerm},
	}
	res := dsl.ParsePropTextInScope(text, scope)
	if len(res.Errors) > 0 {
		t.Fatalf("ParsePropTextInScope: %+v\n--- text: %s", res.Errors, text)
	}
	if res.Prop.AlphaKey() != original.AlphaKey() {
		t.Errorf("alpha-key mismatch:\n  text: %s\n  parsed: %s\n  expected: %s",
			text, prop.PrintProp(res.Prop), prop.PrintProp(original))
	}

	// Script-level: registering via ctx.Const-equivalent populates scope
	// such that ctx.MakePropText resolves the name. We construct a
	// Script manually since ctx.Const requires a wired ProofService.
	script := &proof.Script{
		ParseScope: dsl.ParseScope{
			Consts: map[string]core.ConstTerm{"subset": subsetTerm},
		},
	}
	got := script.MakePropText(text)
	if got.AlphaKey() != original.AlphaKey() {
		t.Errorf("Script.MakePropText alpha-key mismatch:\n  got: %s\n  want: %s",
			prop.PrintProp(got), prop.PrintProp(original))
	}
}

// TestPhaseC_NatRoundTrip checks that a bare _0 survives the parser-mode
// round-trip: formatConstBase prints it as "0", and the numeral-literal
// path re-lowers "0" to `_0`, so the parsed statement α-equals the
// original.
func TestPhaseC_NatRoundTrip(t *testing.T) {
	cases := []struct {
		name  string
		build func() core.Prop
	}{
		{"P_app_0", func() core.Prop {
			_0 := dsl.ZeroMeta.Term()
			SUC := dsl.SUCMeta.Term()
			P := ext.Var("P", core.MakeFun(dsl.NumType, core.TypeBool()))
			n := ext.Var("n", dsl.NumType)
			body := P.Apply(_0).
				And(ext.ForAll(n)(P.Apply(n).Imply(P.Apply(ext.WrapTerm(SUC).Apply(n))))).
				Imply(ext.ForAll(n)(P.Apply(n)))
			return prop.MakeProp(ext.ForAll(P)(body))
		}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			p := tc.build()
			text := prop.FormatPropForParser(p)
			res := dsl.ParsePropTextInScope(text, nil)
			if len(res.Errors) > 0 {
				t.Fatalf("parse failed: %+v\n  text: %s", res.Errors, text)
			}
			if res.Prop.AlphaKey() != p.AlphaKey() {
				t.Errorf("alpha-key mismatch\n  text:     %s\n  parsed:   %s\n  expected: %s",
					text, prop.PrintProp(res.Prop), prop.PrintProp(p))
			}
		})
	}
}

// TestSanitizeIdent guards the per-symbol readable-ident table
// (`+ → plus`, `<< → ll`, `== → eqEq`, …) and the unicode-decompose
// path (`ẋ → x` via NFD + drop combining marks). Both routes exist
// to eliminate the pre-Phase-A `_x` cross-file ambiguity where the
// same Go ident meant different consts in different proofs.
//
// Regression scope: every entry in symbolicIdent + the unicode
// pre-composed cases observed in the current corpus (`ẋ`, `kʹ`) plus
// the absolute fallbacks (empty input, all-punctuation, leading
// digit).
func TestSanitizeIdent(t *testing.T) {
	cases := []struct {
		in, want string
		why      string
	}{
		// Plain alphanumeric — pass through unchanged.
		{"x", "x", "plain ASCII letter"},
		{"foo_bar", "foo_bar", "alnum + underscore"},
		{"P", "P", "uppercase letter"},
		{"x_2", "x_2", "trailing digit"},

		// symbolicIdent table — every entry. Drift in the table
		// without a matching test update will trip these.
		{"+", "plus", "symbolicIdent: +"},
		{"-", "minus", "symbolicIdent: -"},
		{"*", "times", "symbolicIdent: *"},
		{"/", "div", "symbolicIdent: /"},
		{"<", "lt", "symbolicIdent: <"},
		{"<=", "le", "symbolicIdent: <="},
		{"<<", "ll", "symbolicIdent: << (well-founded relation)"},
		{">", "gt", "symbolicIdent: >"},
		{">=", "ge", "symbolicIdent: >="},
		{"==", "eqEq", "symbolicIdent: == (mod-eq)"},
		{",", "pair", "symbolicIdent: , (pair ctor)"},

		// Unicode letters (L*) are legal in Go identifiers — kept
		// as-is by the unicode.IsLetter arm. NFC-composed input keeps
		// precomposed accented letters as a single codepoint.
		{"ẋ", "ẋ", "U+1E8B 'x with dot above' (Ll) — kept as-is"},
		{"kʹ", "kʹ", "k + U+02B9 modifier prime (Lm) — kept as-is"},
		{"δ", "δ", "Greek small delta (Ll) — kept as-is"},
		{"αβ", "αβ", "multi-rune Greek — all kept"},
		{"finiteᴬ", "finiteᴬ", "ASCII + superscript letter modifier (Lm) suffix"},
		// NFD-encoded input composes to NFC and then passes IsLetter.
		{"ẋ", "ẋ", "x + combining-dot-above (NFD) → NFC ẋ → kept"},

		// Symbols / punctuation Go's spec doesn't allow in identifiers
		// still collapse to `_`.
		{"x'", "x_", "ASCII apostrophe (Po) → underscore"},
		{"x₀", "x_", "subscript digit (No, NOT Nd) → underscore"},
		{"x²", "x_", "superscript digit (No, NOT Nd) → underscore"},
		{"x⟨A⟩", "x_A_", "math angle brackets (Ps/Pe) → underscore"},
		{"f∘g", "f_g", "ring operator (Sm) → underscore"},
		{"@", "_x", "single punctuation → _ → _x"},
		{"", "_x", "empty input"},

		// cleanupSanitizedIdent post-process:
		//
		// Rule 1 — strip `_` adjacent to Lm (modifier letters). A HOL
		// name mixing ASCII apostrophe (Po → `_`) with modifier prime
		// `ʹ` (Lm → kept) would otherwise emit `y_ʹ_` — the `_`s next to
		// the modifier are noise; the letter+modifier reads naturally
		// as `yʹ`.
		{"y'ʹ", "yʹ", "apo+prime: strip _ next to Lm"},
		{"y'ʹ'", "yʹ", "apo+prime+apo: strip both _ next to Lm"},
		{"y_ʹ_", "yʹ", "underscore-decorated prime → strip _"},

		// Rule 2 — collapse `_+` runs to a single `_`. Multi-char
		// input mapping to consecutive `_`s (e.g. Normalize appending
		// `''` then `_` suffix) shouldn't produce visual clutter.
		{"y__", "y_", "double underscore → single"},
		{"y___2", "y_2", "triple underscore + 2 → y_2"},
		{"y'', ", "y_", "two apo + comma → y___ → y_"},

		// Rules 1+2 together:
		{"y_ʹ_ʹ_", "yʹʹ", "underscores between/around primes all stripped"},

		// HOL `Normalize` produces `GEN%PVAR%N` for freshly-generated
		// var slots. The `%` chars sanitize to `_`, yielding a legal
		// Go ident — no `_x` fallback needed.
		{"GEN%PVAR%26", "GEN_PVAR_26", "GEN%PVAR%N pattern"},

		// Leading-digit names get a `_` prefix to make them valid
		// Go identifiers.
		{"42x", "_42x", "leading digit"},
	}
	for _, tc := range cases {
		t.Run(tc.why, func(t *testing.T) {
			got := sanitizeIdent(tc.in)
			if got != tc.want {
				t.Errorf("sanitizeIdent(%q) = %q, want %q", tc.in, got, tc.want)
			}
		})
	}
}

// TestSanitizeIdent_NoUxLeak is a corpus-level guard: a healthy
// emit output has zero `_x` Go idents anywhere. If a new symbolic
// const name appears in the corpus that isn't in symbolicIdent, or a
// new unicode shape that NFD can't recover, this test surfaces it
// before a release.
//
// The check is conservative: we look for the substring `_x` in
// declared form (` _x ` or `_x := `) rather than in arbitrary
// positions, so legitimate names like `_x_2` (escaped collision) or
// `__x_priv` aren't false positives.
func TestSanitizeIdent_NoUxLeak(t *testing.T) {
	// Spot-check by running every symbolicIdent value back through
	// sanitizeIdent and confirming idempotence — a readable ident
	// shouldn't itself sanitize away.
	for sym, ident := range symbolicIdent {
		got := sanitizeIdent(ident)
		if got != ident {
			t.Errorf("symbolicIdent[%q]=%q not idempotent under sanitizeIdent: got %q",
				sym, ident, got)
		}
		if ident == "_x" {
			t.Errorf("symbolicIdent[%q] = %q — table entry must not be the fallback marker",
				sym, ident)
		}
	}
}

// TestEmit_LemmaPreserveStep guards the emit arms for the
// hypothesis-preserving `lemma_preserve` ministep (the agent-session
// `lemma` dispatch): (a) the bare form renders as
// LemmaPreserve(ctx.MakePropText(<prop text>)) — not the "unhandled
// ministep" fallthrough; (b) the external-citation idiom (lemma_preserve
// immediately closed by an α-equal KnownThm) fuses into one Cite of the
// payload — never the legacy UseLemma / UseLemmaExact install verbs.
func TestEmit_LemmaPreserveStep(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))
	C := ext.Var("C", core.TypeBool())
	lemma := prop.MakeProp(ext.ForAll(x)(R.Apply(x)).Core())
	goal := prop.MakeProp(C.Core())
	residual := prop.MakeProp(C.Core(), lemma.Conclusion())

	// (a) bare form: lemma child closed by TrivialSimplify (NOT KnownThm),
	// so the Cite fusion must not fire and the bare arm renders.
	{
		pb := ext.NewPoolBuilder()
		steps := []*proof.StepProto{
			{
				Goal:     pb.PropRef(goal),
				SubGoals: []*ext.HolPropProto{pb.PropRef(lemma), pb.PropRef(residual)},
				Step:     &proof.StepProto_LemmaPreserve{LemmaPreserve: pb.PropRef(lemma)},
			},
			{
				Goal: pb.PropRef(lemma),
				Step: &proof.StepProto_TrivialSimplify{},
			},
			{
				Goal: pb.PropRef(residual),
				Step: &proof.StepProto_TrivialSimplify{},
			},
		}
		src := emitMember(t, env, EmitOptions{FuncName: "BuildLemmaPreserve"}, detailed(pb, steps...)).Source
		if !strings.Contains(src, "LemmaPreserve(ctx.MakePropText(") {
			t.Errorf("bare lemma_preserve did not render as LemmaPreserve(ctx.MakePropText(...))\n--- source: ---\n%s", src)
		}
		if strings.Contains(src, "unhandled ministep") {
			t.Errorf("ministep fell through to unhandled placeholder\n--- source: ---\n%s", src)
		}
	}

	// (b) citation idiom: lemma child closed by an α-equal KnownThm →
	// one Cite of the payload.
	{
		pb := ext.NewPoolBuilder()
		steps := []*proof.StepProto{
			{
				Goal:     pb.PropRef(goal),
				SubGoals: []*ext.HolPropProto{pb.PropRef(lemma), pb.PropRef(residual)},
				Step:     &proof.StepProto_LemmaPreserve{LemmaPreserve: pb.PropRef(lemma)},
			},
			{
				Goal: pb.PropRef(lemma),
				Step: &proof.StepProto_KnownThm{
					KnownThm: &proof.KnownThmProto{StrongerGoal: pb.PropRef(lemma)},
				},
			},
			{
				Goal: pb.PropRef(residual),
				Step: &proof.StepProto_TrivialSimplify{},
			},
		}
		src := emitMember(t, env, EmitOptions{FuncName: "BuildLemmaPreserveCite"}, detailed(pb, steps...)).Source
		if !strings.Contains(src, "Cite(") {
			t.Errorf("lemma_preserve + KnownThm did not fuse into Cite(...)\n--- source: ---\n%s", src)
		}
		for _, legacy := range []string{"UseLemma(", "UseLemmaExact(", "LemmaPreserve(", "CiteKnown("} {
			if strings.Contains(src, legacy) {
				t.Errorf("lemma_preserve + KnownThm still renders %q\n--- source: ---\n%s", legacy, src)
			}
		}
	}
}

// TestEmit_ResolveExternalLeafTier: an external lemma reference consults
// the EmitOptions.ResolveExternalLeaf hook (the emit-section RPC wiring)
// and renders the classified form — here the dep name
// `Cite("IN_DELETE_LIKE")` — instead of the TODO placeholder. Without
// the hook the same proto renders the placeholder, which the second
// half asserts stays intact.
func TestEmit_ResolveExternalLeafTier(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))
	C := ext.Var("C", core.TypeBool())
	lemma := prop.MakeProp(ext.ForAll(x)(R.Apply(x)).Core())
	goal := prop.MakeProp(C.Core())
	residual := prop.MakeProp(C.Core(), lemma.Conclusion())

	// The Lemma step's lemma child closes via an α-equal KnownThm — the
	// Cite-fusion shape (mirrors TestEmit_LemmaPreserveStep (b)); the
	// fusion resolves the lemma reference through externalLeafExpr,
	// which is where the resolver tier lives.
	mkSection := func() *proof.DetailedProofProto {
		pb := ext.NewPoolBuilder()
		steps := []*proof.StepProto{
			{
				Goal:     pb.PropRef(goal),
				SubGoals: []*ext.HolPropProto{pb.PropRef(lemma), pb.PropRef(residual)},
				Step:     &proof.StepProto_Lemma{Lemma: pb.PropRef(lemma)},
			},
			{
				Goal: pb.PropRef(lemma),
				Step: &proof.StepProto_KnownThm{
					KnownThm: &proof.KnownThmProto{StrongerGoal: pb.PropRef(lemma)},
				},
			},
			{
				Goal: pb.PropRef(residual),
				Step: &proof.StepProto_TrivialSimplify{},
			},
		}
		return detailed(pb, steps...)
	}

	// (a) resolver wired → the dep-name rendering, no TODO.
	{
		lemmaKey := lemma.AlphaKey()
		normalized, _ := proof.Normalize(lemma)
		normalizedKey := normalized.AlphaKey()
		src := emitMember(t, env, EmitOptions{
			FuncName: "BuildResolveLeaf",
			ResolveExternalLeaf: func(key core.PropKey) (ExternalLeaf, bool) {
				if key == lemmaKey || key == normalizedKey {
					return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "IN_DELETE_LIKE"}, true
				}
				return ExternalLeaf{}, false
			},
		}, mkSection()).Source
		if !strings.Contains(src, `Cite("IN_DELETE_LIKE")`) {
			t.Errorf("resolver-classified leaf did not render as Cite(\"IN_DELETE_LIKE\")\n--- source: ---\n%s", src)
		}
		if strings.Contains(src, "TODO: external lemma") || strings.Contains(src, "TODO: unresolved lemma") {
			t.Errorf("resolver wired but TODO placeholder still rendered\n--- source: ---\n%s", src)
		}
	}

	// (b) no resolver → the TODO placeholder fallback intact.
	{
		src := emitMember(t, env, EmitOptions{FuncName: "BuildResolveLeafNoHook"}, mkSection()).Source
		if !strings.Contains(src, "TODO: unresolved lemma") {
			t.Errorf("no-resolver emit lost the TODO placeholder fallback\n--- source: ---\n%s", src)
		}
	}
}

// TestEmit_Cites covers the citation renderings
// (chapter_constitution.md §"Citation forms: compute, don't pin"):
//
//	(a) a LibraryThm leaf consumed as a lemma payload renders as
//	 `Cite("N")` — the consolidated cite verb, whose dep-NAME target
//	 resolves the statement the dep serves itself;
//	(b) a cite of an earlier section renders as the bare node
//	 reference (`Cite(lemma1)` — Cite reads the promise itself), not
//	 as `ExactFrom(<ref>, MakePropText("<statement re-quote>"))`.
func TestEmit_Cites(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))
	C := ext.Var("C", core.TypeBool())
	lemma := prop.MakeProp(ext.ForAll(x)(R.Apply(x)).Core())
	goal := prop.MakeProp(C.Core())
	residual := prop.MakeProp(C.Core(), lemma.Conclusion())

	// Two sections: section 1 proves `lemma`; section 2 cites it via
	// the Lemma + KnownThm fusion (the Cite shape) and closes the
	// residual. The fusion's payload resolution is where both the
	// external-leaf tier (a) and the earlier-section tier (b) live.
	mkSections := func() []*proof.DetailedProofProto {
		pb := ext.NewPoolBuilder()
		lemmaSteps := []*proof.StepProto{
			{
				Goal: pb.PropRef(lemma),
				Step: &proof.StepProto_TrivialSimplify{},
			},
		}
		goalSteps := []*proof.StepProto{
			{
				Goal:     pb.PropRef(goal),
				SubGoals: []*ext.HolPropProto{pb.PropRef(lemma), pb.PropRef(residual)},
				Step:     &proof.StepProto_Lemma{Lemma: pb.PropRef(lemma)},
			},
			{
				Goal: pb.PropRef(lemma),
				Step: &proof.StepProto_KnownThm{
					KnownThm: &proof.KnownThmProto{StrongerGoal: pb.PropRef(lemma)},
				},
			},
			{
				Goal: pb.PropRef(residual),
				Step: &proof.StepProto_TrivialSimplify{},
			},
		}
		return []*proof.DetailedProofProto{detailed(pb, lemmaSteps...), detailed(pb, goalSteps...)}
	}

	// (b) earlier-section cite → node reference, no ExactFrom re-quote.
	{
		src := emitMember(t, env, EmitOptions{FuncName: "BuildCites"}, mkSections()...).Source
		if !strings.Contains(src, "Cite(lemma1)") {
			t.Errorf("section cite did not render as Cite(<node>)\n--- source: ---\n%s", src)
		}
		if strings.Contains(src, "ExactFrom") {
			t.Errorf("emit still reifies ExactFrom for a section cite\n--- source: ---\n%s", src)
		}
		for _, legacy := range []string{"UseLemma(", "UseLemmaExact(", "CiteSpecialize("} {
			if strings.Contains(src, legacy) {
				t.Errorf("emit still renders the legacy %q spelling\n--- source: ---\n%s", legacy, src)
			}
		}
	}

	// (a) external LibraryThm leaf: drop section 1 so the payload
	// resolves through the external-leaf resolver.
	{
		lemmaKey := lemma.AlphaKey()
		normalized, _ := proof.Normalize(lemma)
		normalizedKey := normalized.AlphaKey()
		res := emitMember(t, env, EmitOptions{
			FuncName: "BuildCitesLeaf",
			ResolveExternalLeaf: func(key core.PropKey) (ExternalLeaf, bool) {
				if key == lemmaKey || key == normalizedKey {
					return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "IN_DELETE_LIKE"}, true
				}
				return ExternalLeaf{}, false
			},
		}, mkSections()[1])
		src := res.Source
		// The consolidated verb with the dep NAME: Cite resolves a named
		// target itself, so neither a normalize wrap nor a per-dep claim
		// ladder appears.
		if !strings.Contains(src, `Cite("IN_DELETE_LIKE"),`) {
			t.Errorf("LibraryThm lemma payload did not render Cite(\"N\")\n--- source: ---\n%s", src)
		}
		if strings.Contains(src, "NormalizedThm(") {
			t.Errorf("emit still hand-spells the NormalizedThm wrap\n--- source: ---\n%s", src)
		}
		// The rendered dep is surfaced on the result.
		if len(res.DepNames) != 1 || res.DepNames[0] != "IN_DELETE_LIKE" {
			t.Errorf("DepNames = %v, want [IN_DELETE_LIKE]", res.DepNames)
		}
		for _, banned := range []string{"env.LazyAuto", "TrustedReplay", "MemoizedBuild"} {
			if strings.Contains(src, banned) {
				t.Errorf("member output still renders %q\n--- source: ---\n%s", banned, src)
			}
		}
	}
}

// TestEmit_CitesConjunctionPayload covers the payload-faithful arm of
// the lemma-cite dispatch: a LibraryThm leaf whose recorded payload is
// NOT normalize-stable (a multi-clause conjunction with per-conjunct
// binders — the MULT shape) must never be wrapped in NormalizedThm.
// Normalize re-binds such conjunctions under one shared ∀-prefix;
// installing that packed form diverges from the session's split clause
// facts (leaves that closed at the cite in-session fail replay).
func TestEmit_CitesConjunctionPayload(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))
	S := ext.Var("S", core.MakeFun(core.TypeA(), core.MakeFun(core.TypeA(), core.TypeBool())))
	C := ext.Var("C", core.TypeBool())
	// ∀R S. (∀x. R(x)) ∧ (∀x y. S(x, y)) — CLOSED, per-conjunct inner
	// binders: the MULT shape (closedness matters — the dispatch's
	// guard keeps free-var payloads on the wrap arm).
	lemma := prop.MakeProp(ext.ForAll(R, S)(ext.And(
		ext.ForAll(x)(R.Apply(x)).Core(),
		ext.ForAll(x, y)(S.Apply(x).Apply(y)).Core(),
	).Core()).Core())
	goal := prop.MakeProp(C.Core())
	residual := prop.MakeProp(C.Core(), lemma.Conclusion())

	// Fixture guards: the payload must be CLOSED and NOT normalize-
	// stable, or this test silently degrades to re-testing the wrap
	// branch.
	if lemma.NumHyps() != 0 || len(lemma.Conclusion().Frees(func(core.VarTerm) bool { return true })) != 0 {
		t.Fatalf("fixture defeated: conjunction payload is not closed")
	}
	normalized, _ := proof.Normalize(lemma)
	if normalized.AlphaKey() == lemma.AlphaKey() {
		t.Fatalf("fixture defeated: Normalize is identity on the conjunction payload — pick a shape Normalize re-binds")
	}

	pb := ext.NewPoolBuilder()
	goalSteps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(lemma), pb.PropRef(residual)},
			Step:     &proof.StepProto_Lemma{Lemma: pb.PropRef(lemma)},
		},
		{
			Goal: pb.PropRef(lemma),
			Step: &proof.StepProto_KnownThm{
				KnownThm: &proof.KnownThmProto{StrongerGoal: pb.PropRef(lemma)},
			},
		},
		{
			Goal: pb.PropRef(residual),
			Step: &proof.StepProto_TrivialSimplify{},
		},
	}

	lemmaKey := lemma.AlphaKey()
	normalizedKey := normalized.AlphaKey()
	res := emitMember(t, env, EmitOptions{
		FuncName: "BuildConjPayload",
		ResolveExternalLeaf: func(key core.PropKey) (ExternalLeaf, bool) {
			if key == lemmaKey || key == normalizedKey {
				return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "MULT_LIKE"}, true
			}
			return ExternalLeaf{}, false
		},
	}, detailed(pb, goalSteps...))
	src := res.Source
	if strings.Contains(src, "NormalizedThm(") {
		t.Errorf("non-normalize-stable conjunction payload still rendered NormalizedThm-wrapped\n--- source: ---\n%s", src)
	}
	if !strings.Contains(src, `ctx.Dep("MULT_LIKE")`) {
		t.Errorf("conjunction payload did not render the bare claiming-dep cite\n--- source: ---\n%s", src)
	}
	if len(res.DepNames) != 1 || res.DepNames[0] != "MULT_LIKE" {
		t.Errorf("DepNames = %v, want [MULT_LIKE]", res.DepNames)
	}
}

// TestEmit_SimpCiteTargets covers the simp rendering: a recorded
// `simp_with` whose rules all resolve to named deps renders as the
// `Simp` verb over CITE TARGETS, and the per-rule obligation Cases
// disappear because Simp discharges them from those same certificates.
// TestEmit_SimpFusionRendersFiredRulesOnly: a recorded simp_with whose
// rule list is wider than what fired — the bound family's bare `simp`
// hands the driver its whole installed set — renders only the rules the
// step carries a child for, and an unfired rule's target never enters
// the source (so it is no Dep either).
func TestEmit_SimpFusionRendersFiredRulesOnly(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))
	S := ext.Var("S", core.MakeFun(core.TypeA(), core.TypeBool()))
	U := ext.Var("U", core.MakeFun(core.TypeA(), core.TypeBool()))
	C := ext.Var("C", core.TypeBool())
	ruleFwd := prop.MakeProp(ext.ForAll(x)(R.Apply(x)).Core())
	ruleFlipped := prop.MakeProp(ext.ForAll(x)(S.Apply(x)).Core())
	ruleUnused := prop.MakeProp(ext.ForAll(x)(U.Apply(x)).Core())
	goal := prop.MakeProp(C.Core())
	residual := prop.MakeProp(C.Core(), ruleFwd.Conclusion())

	// Three rules handed to the driver; children for the two that fired.
	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal: pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{
				pb.PropRef(ruleFwd), pb.PropRef(ruleFlipped), pb.PropRef(residual),
			},
			Step: &proof.StepProto_SimpWith{SimpWith: &proof.SimpWithProto{
				Rules:    []*ext.HolPropProto{pb.PropRef(ruleUnused), pb.PropRef(ruleFwd), pb.PropRef(ruleFlipped)},
				RuleFlip: []bool{false, false, true},
			}},
		},
		{Goal: pb.PropRef(ruleFwd), Step: &proof.StepProto_TrivialSimplify{}},
		{Goal: pb.PropRef(ruleFlipped), Step: &proof.StepProto_TrivialSimplify{}},
		{Goal: pb.PropRef(residual), Step: &proof.StepProto_TrivialSimplify{}},
	}
	resolver := func(key core.PropKey) (ExternalLeaf, bool) {
		switch key {
		case ruleFwd.AlphaKey():
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "RULE_FWD"}, true
		case ruleFlipped.AlphaKey():
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "RULE_FLIPPED"}, true
		case ruleUnused.AlphaKey():
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "RULE_UNUSED"}, true
		}
		return ExternalLeaf{}, false
	}

	res := emitMember(t, env, EmitOptions{
		FuncName:            "BuildSimpFired",
		ResolveExternalLeaf: resolver,
	}, detailed(pb, steps...))
	src := res.Source
	if !strings.Contains(src, `Simp(Fwd("RULE_FWD"), Rev("RULE_FLIPPED"))`) {
		t.Errorf("Simp must name the two rules that fired, in recorded order\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "RULE_UNUSED") {
		t.Errorf("an unfired rule must not enter the source as a rule or a dep\n--- source: ---\n%s", src)
	}
}

func TestEmit_SimpCiteTargets(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))
	S := ext.Var("S", core.MakeFun(core.TypeA(), core.TypeBool()))
	C := ext.Var("C", core.TypeBool())
	ruleFwd := prop.MakeProp(ext.ForAll(x)(R.Apply(x)).Core())
	ruleFlipped := prop.MakeProp(ext.ForAll(x)(S.Apply(x)).Core())
	goal := prop.MakeProp(C.Core())
	residual := prop.MakeProp(C.Core(), ruleFwd.Conclusion())

	// The recorded fan-out SimpWithExpandFlipped produces: one child per
	// FIRED rule (the rule prop verbatim), residual last.
	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal: pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{
				pb.PropRef(ruleFwd), pb.PropRef(ruleFlipped), pb.PropRef(residual),
			},
			Step: &proof.StepProto_SimpWith{SimpWith: &proof.SimpWithProto{
				Rules:    []*ext.HolPropProto{pb.PropRef(ruleFwd), pb.PropRef(ruleFlipped)},
				RuleFlip: []bool{false, true},
			}},
		},
		{Goal: pb.PropRef(ruleFwd), Step: &proof.StepProto_TrivialSimplify{}},
		{Goal: pb.PropRef(ruleFlipped), Step: &proof.StepProto_TrivialSimplify{}},
		{Goal: pb.PropRef(residual), Step: &proof.StepProto_TrivialSimplify{}},
	}
	resolver := func(key core.PropKey) (ExternalLeaf, bool) {
		switch key {
		case ruleFwd.AlphaKey():
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "RULE_FWD"}, true
		case ruleFlipped.AlphaKey():
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "RULE_FLIPPED"}, true
		}
		return ExternalLeaf{}, false
	}

	res := emitMember(t, env, EmitOptions{
		FuncName:            "BuildSimp",
		ResolveExternalLeaf: resolver,
	}, detailed(pb, steps...))
	src := res.Source
	if !strings.Contains(src, `Simp(Fwd("RULE_FWD"), Rev("RULE_FLIPPED"))`) {
		t.Errorf("simp_with did not render the Simp verb over cite targets\n--- source: ---\n%s", src)
	}
	// The prop-taking Step spellings and their pinned rule literals
	// are what Simp exists to remove.
	for _, banned := range []string{"SimpWith(", "SimpWithFlipped(", "SimpWithOriented("} {
		if strings.Contains(src, banned) {
			t.Errorf("emit still renders %q\n--- source: ---\n%s", banned, src)
		}
	}
	// Rule obligations are Simp's job — no Case/CiteKnown pair per rule
	// should survive.
	if strings.Contains(src, "CiteKnown(") {
		t.Errorf("emit still discharges rule obligations by hand\n--- source: ---\n%s", src)
	}
	if got := len(res.DepNames); got != 2 {
		t.Errorf("DepNames = %v, want both rule deps", res.DepNames)
	}
}

// deriveStaircaseSection is a right-nested run of two `assert` steps —
// two facts established in order — closed by a refute.
func deriveStaircaseSection() *proof.DetailedProofProto {
	P := ext.Var("P", core.TypeBool())
	Q := ext.Var("Q", core.TypeBool())
	C := ext.Var("C", core.TypeBool())
	claim1 := prop.MakeProp(P.Core())
	claim2 := prop.MakeProp(Q.Core())
	goal := prop.MakeProp(C.Core())
	after1 := prop.MakeProp(C.Core(), P.Core())
	after2 := prop.MakeProp(C.Core(), P.Core(), Q.Core())

	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(claim1), pb.PropRef(after1)},
			Step:     &proof.StepProto_Assert{Assert: pb.PropRef(claim1)},
		},
		{Goal: pb.PropRef(claim1), Step: &proof.StepProto_TrivialSimplify{}},
		{
			Goal:     pb.PropRef(after1),
			SubGoals: []*ext.HolPropProto{pb.PropRef(claim2), pb.PropRef(after2)},
			Step:     &proof.StepProto_Assert{Assert: pb.PropRef(claim2)},
		},
		{Goal: pb.PropRef(claim2), Step: &proof.StepProto_TrivialSimplify{}},
		{Goal: pb.PropRef(after2), Step: &proof.StepProto_CnfRefute{}},
	}
	return detailed(pb, steps...)
}

// TestEmit_DeriveStaircase covers the staircase rendering: a
// right-nested run of `assert` steps — k facts established in order —
// renders as a chain of k `a.Have`s plus an `a.Show`, instead of the
// k-deep AssertStep(claim, Case, Case) nesting whose "after" labels are
// control-flow filler. A body that is one whole staircase renders the
// chain directly on the closure's own Argument.
func TestEmit_DeriveStaircase(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)
	src := emitMember(t, env, EmitOptions{FuncName: "BuildDerive"}, deriveStaircaseSection()).Source
	if got := strings.Count(src, "a.Have("); got != 2 {
		t.Errorf("Have count = %d, want 2 (one per established fact)\n--- source: ---\n%s", got, src)
	}
	if !strings.Contains(src, "a.Show(") {
		t.Errorf("the staircase has no terminal Show\n--- source: ---\n%s", src)
	}
	// The closure IS an Argument context: no driver around the driver.
	if strings.Contains(src, "Derive(func") {
		t.Errorf("a whole-body staircase rendered a nested Derive block\n--- source: ---\n%s", src)
	}
	// The staircase itself must be gone.
	if strings.Contains(src, "AssertStep(") {
		t.Errorf("emit still renders the AssertStep staircase\n--- source: ---\n%s", src)
	}
}

// TestEmit_DeriveCompiles type-checks the staircase rendering. The
// Have/Show chain is statement-position calls on the closure's
// Argument rather than a comma-separated step list, so parsing it is
// not enough — the receiver, the alias set and the argument shapes have
// to hold up under the type checker.
func TestEmit_DeriveCompiles(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}

	env := makeTestEnv(t)
	const pkg = "derivecompilesemit"
	src := emitMember(t, env, EmitOptions{
		Family:   "tmp/" + pkg,
		FuncName: "Build_DeriveCompiles",
	}, deriveStaircaseSection()).Source
	if !strings.Contains(src, "a.Have(") {
		t.Fatalf("fixture defeated: no Have chain emitted\n--- source: ---\n%s", src)
	}
	vetMember(t, goBin, pkg, src)
}

// TestEmit_DeriveStaircaseMinimum pins the threshold: ONE assert is a
// genuine binary branch (claim + a residual that immediately branches)
// and keeps AssertStep; the Have chain starts at two consecutive
// claim/continue nestings, which is the staircase flag rule.
func TestEmit_DeriveStaircaseMinimum(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	P := ext.Var("P", core.TypeBool())
	C := ext.Var("C", core.TypeBool())
	claim := prop.MakeProp(P.Core())
	goal := prop.MakeProp(C.Core())
	after := prop.MakeProp(C.Core(), P.Core())

	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(claim), pb.PropRef(after)},
			Step:     &proof.StepProto_Assert{Assert: pb.PropRef(claim)},
		},
		{Goal: pb.PropRef(claim), Step: &proof.StepProto_TrivialSimplify{}},
		{Goal: pb.PropRef(after), Step: &proof.StepProto_CnfRefute{}},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildOneAssert"}, detailed(pb, steps...)).Source
	if strings.Contains(src, "Derive(func") || strings.Contains(src, ".Have(") {
		t.Errorf("a single assert rendered as a Have chain\n--- source: ---\n%s", src)
	}
	if !strings.Contains(src, "AssertStep(") {
		t.Errorf("a single assert lost its AssertStep rendering\n--- source: ---\n%s", src)
	}
}

// TestEmit_AtTypesFusion covers the cross-type install pair's fusion:
// `lemma_preserve(<row at the target type>)` whose obligation child is
// `type_inst(<polymorphic row>)` renders as one
// `Cite(ctx.AtTypes(ctx.Dep("N"), τ))`, replacing two hand-copied
// statement texts (one of them carrying the row's machine type-var
// spelling).
func TestEmit_AtTypesFusion(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	// Polymorphic congruence row ∀f x y:A. x = y ⇒ f(x) = f(y), cited at
	// A := bool. (A row whose Normalize stays non-trivial and keeps its
	// type variable — a tautology normalizes to ⊤ and has none.)
	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	source := prop.MakeProp(ext.ForAll(f, x, y)(x.Eq(y).Imply(f.Apply(x).Eq(f.Apply(y)).Core()).Core()).Core())
	srcNorm, _ := proof.Normalize(source)
	vars := proof.OrderedPropTypeVars(srcNorm)
	if len(vars) != 1 {
		t.Fatalf("fixture defeated: want exactly one type var, got %d in %s",
			len(vars), prop.PrintProp(srcNorm))
	}
	payload := core.PropTypeInst(srcNorm, core.MakeTypeSubst(vars[0], core.TypeBool()))
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
		if key == source.AlphaKey() || key == srcNorm.AlphaKey() {
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "POLY_ROW"}, true
		}
		return ExternalLeaf{}, false
	}

	src := emitMember(t, env, EmitOptions{
		FuncName:            "BuildAtTypes",
		ResolveExternalLeaf: resolver,
	}, detailed(pb, steps...)).Source
	if !strings.Contains(src, `Cite(ctx.AtTypes(ctx.Dep("POLY_ROW"), TypeBool))`) {
		t.Errorf("cross-type install pair did not fuse into AtTypes\n--- source: ---\n%s", src)
	}
	// The two hand-copied texts the fusion exists to delete.
	for _, banned := range []string{"TypeInstSourceExact", "LemmaPreserve("} {
		if strings.Contains(src, banned) {
			t.Errorf("emit still renders %q\n--- source: ---\n%s", banned, src)
		}
	}
}

// TestEmit_AtTypesArgsRejectsWrongInstance is the safety control for
// the AtTypes derivation: the fusion reproduces what Script.AtTypes
// will build and requires it to α-equal the recorded payload, so a
// payload that is NOT the row's type instance must decline rather than
// emit a confidently wrong cite.
func TestEmit_AtTypesArgsRejectsWrongInstance(t *testing.T) {
	defer goleak.VerifyNone(t)

	// Only PrintType is exercised here, which needs no const/var
	// resolution callbacks.
	e := &_Emitter{}
	e.printer = &ext.GoTermPrinter{BareNames: true}

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	source := prop.MakeProp(ext.ForAll(f, x, y)(x.Eq(y).Imply(f.Apply(x).Eq(f.Apply(y)).Core()).Core()).Core())
	srcNorm, _ := proof.Normalize(source)

	// A genuine instance derives and verifies.
	vars := proof.OrderedPropTypeVars(srcNorm)
	good := core.PropTypeInst(srcNorm, core.MakeTypeSubst(vars[0], core.TypeBool()))
	if _, ok := e.atTypesArgs(source, good); !ok {
		t.Errorf("atTypesArgs declined a genuine type instance")
	}
	// A DIFFERENT theorem over the same type vars is not an instance of
	// the row, however well its types line up.
	bad := prop.MakeProp(ext.ForAll(f, x, y)(x.Eq(y).Imply(f.Apply(x).Eq(y).Core()).Core()).Core())
	if args, ok := e.atTypesArgs(source, bad); ok {
		t.Errorf("atTypesArgs accepted a non-instance payload, args = %q", args)
	}
}

// TestEmit_PayloadTextFormNoDeadVars verifies the text-form-aware
// payload marking (markGoUsedFromPropPayload): a Lemma payload that
// round-trips as text must NOT force declarations for its bound/free
// vars (declared, never referenced by any rendered Go expression).
// Section 1 proves `∀x. R(x)`, section 2 cites it as a Lemma payload;
// neither x nor R is referenced by any Go expression, so the emitted
// file must carry no Variables block at all.
func TestEmit_PayloadTextFormNoDeadVars(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))
	C := ext.Var("C", core.TypeBool())
	lemma := prop.MakeProp(ext.ForAll(x)(R.Apply(x)).Core())
	goal := prop.MakeProp(C.Core())
	residual := prop.MakeProp(C.Core(), lemma.Conclusion())

	pb := ext.NewPoolBuilder()
	lemmaSteps := []*proof.StepProto{
		{
			Goal: pb.PropRef(lemma),
			Step: &proof.StepProto_TrivialSimplify{},
		},
	}
	goalSteps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(lemma), pb.PropRef(residual)},
			Step:     &proof.StepProto_Lemma{Lemma: pb.PropRef(lemma)},
		},
		{
			Goal: pb.PropRef(lemma),
			Step: &proof.StepProto_KnownThm{
				KnownThm: &proof.KnownThmProto{StrongerGoal: pb.PropRef(lemma)},
			},
		},
		{
			Goal: pb.PropRef(residual),
			Step: &proof.StepProto_TrivialSimplify{},
		},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildDeadVar"},
		detailed(pb, lemmaSteps...), detailed(pb, goalSteps...)).Source
	if strings.Contains(src, "=== Variables ===") || strings.Contains(unspaced(src), `Var("`) {
		t.Errorf("text-form Lemma payload still forces var declarations\n--- source: ---\n%s", src)
	}
}

// TestEmit_SetTacStep guards the emit branch for the set_tac ministep: a
// SetTac StepProto in the legacy mode must render as
// `SetTacLegacy("<const>", …)` — the exact-mode constructor whose apply
// is the SAME driver the recording ran (record/emit/replay-reuse), never
// the door `SetTac()` that tries membership first — with the recorded
// const list verbatim, and must not fall through to the "unhandled
// ministep" placeholder. emit only renders; it does not replay, so the
// synthetic goal need not be set_tac-provable.
func TestEmit_SetTacStep(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	P := ext.Var("P", core.TypeBool())
	Q := ext.Var("Q", core.TypeBool())
	pb := ext.NewPoolBuilder()
	goal := pb.PropRef(prop.MakeProp(P.Imply(Q)))

	step := &proof.StepProto{
		Goal: goal,
		Step: &proof.StepProto_SetTac{
			SetTac: &proof.SetTacProto{Consts: []string{"empty_set", "set_member"}},
		},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildSetTac"}, detailed(pb, step)).Source
	if !strings.Contains(src, `SetTacLegacy("empty_set", "set_member")`) {
		t.Errorf("SetTac ministep did not render as the exact legacy form with the recorded const list\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "unhandled ministep") {
		t.Errorf("ministep fell through to unhandled placeholder\n--- source: ---\n%s", src)
	}
}

// --- Expect / Finally render forms (structured fan-out) ---------------------
//
// Shared shape notes for the tests below: emit renders, it does not
// replay, so the synthetic protos need only structural validity
// (preorder + per-step SubGoals counts). `basic` is the canonical
// NON-case-eligible ministep; a `basic` with N subgoals models an
// auto-splitting step (iff split, ε split) that has no native Case
// form.

// TestEmit_FinallyTailFold: a non-case-eligible ministep whose children
// are ALL CnfRefute leaves folds the run into one broadcast terminator:
// Basic() + Finally(CnfRefute()).
func TestEmit_FinallyTailFold(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	P := ext.Var("P", core.TypeBool())
	Q := ext.Var("Q", core.TypeBool())
	R := ext.Var("R", core.TypeBool())
	goal := prop.MakeProp(P.Or(Q).Or(R))

	pb := ext.NewPoolBuilder()
	g1 := pb.PropRef(prop.MakeProp(P.Core()))
	g2 := pb.PropRef(prop.MakeProp(Q.Core()))
	g3 := pb.PropRef(prop.MakeProp(R.Core()))
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{g1, g2, g3},
			Step:     &proof.StepProto_Basic{Basic: &emptypb.Empty{}},
		},
		{Goal: g1, Step: &proof.StepProto_CnfRefute{CnfRefute: &emptypb.Empty{}}},
		{Goal: g2, Step: &proof.StepProto_CnfRefute{CnfRefute: &emptypb.Empty{}}},
		{Goal: g3, Step: &proof.StepProto_CnfRefute{CnfRefute: &emptypb.Empty{}}},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildFinallyFold"}, detailed(pb, steps...)).Source
	if !strings.Contains(src, "Finally(CnfRefute())") {
		t.Errorf("uniform refute tail did not fold to Finally(CnfRefute())\n--- source: ---\n%s", src)
	}
	if n := strings.Count(src, "CnfRefute()"); n != 1 {
		t.Errorf("expected exactly 1 CnfRefute() occurrence (inside Finally), got %d\n--- source: ---\n%s", n, src)
	}
	if strings.Contains(src, "Expect(") {
		t.Errorf("uniform tail should fold to Finally, not wrap in Expect\n--- source: ---\n%s", src)
	}
}

// TestEmit_FinallyMixedTail: one substantive child + a trailing ≥2
// refute run still folds (remaining substantive ≤ 1): the node renders
// as a flat cascade — Basic(), Assumption(), Finally(...) — not as a
// Case block.
func TestEmit_FinallyMixedTail(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	P := ext.Var("P", core.TypeBool())
	Q := ext.Var("Q", core.TypeBool())
	R := ext.Var("R", core.TypeBool())
	goal := prop.MakeProp(P.Or(Q).Or(R))

	pb := ext.NewPoolBuilder()
	g1 := pb.PropRef(prop.MakeProp(P.Core(), P.Core())) // P ⊢ P — assumption-closable
	g2 := pb.PropRef(prop.MakeProp(Q.Core()))
	g3 := pb.PropRef(prop.MakeProp(R.Core()))
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{g1, g2, g3},
			Step:     &proof.StepProto_Basic{Basic: &emptypb.Empty{}},
		},
		{Goal: g1, Step: &proof.StepProto_Assumption{Assumption: &emptypb.Empty{}}},
		{Goal: g2, Step: &proof.StepProto_CnfRefute{CnfRefute: &emptypb.Empty{}}},
		{Goal: g3, Step: &proof.StepProto_CnfRefute{CnfRefute: &emptypb.Empty{}}},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildFinallyMixed"}, detailed(pb, steps...)).Source
	if !strings.Contains(src, "Finally(CnfRefute())") {
		t.Errorf("mixed tail did not fold trailing refutes into Finally\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "Expect(") {
		t.Errorf("≤1 substantive child must render flat cascade + Finally, not Expect\n--- source: ---\n%s", src)
	}
	if !strings.Contains(src, "Assumption()") {
		t.Errorf("substantive child lost in fold\n--- source: ---\n%s", src)
	}
}

// TestEmit_ExpectAutoSplit: a non-case-eligible ministep with ≥2
// substantive children wraps in Expect with positional Case labels —
// the structured form of what would otherwise render as a flat DFS
// cascade the reader had to simulate.
func TestEmit_ExpectAutoSplit(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	P := ext.Var("P", core.TypeBool())
	Q := ext.Var("Q", core.TypeBool())
	goal := prop.MakeProp(P.Or(Q))

	pb := ext.NewPoolBuilder()
	g1 := pb.PropRef(prop.MakeProp(P.Core(), P.Core()))
	g2 := pb.PropRef(prop.MakeProp(Q.Core(), Q.Core()))
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{g1, g2},
			Step:     &proof.StepProto_Basic{Basic: &emptypb.Empty{}},
		},
		{Goal: g1, Step: &proof.StepProto_Assumption{Assumption: &emptypb.Empty{}}},
		{Goal: g2, Step: &proof.StepProto_Assumption{Assumption: &emptypb.Empty{}}},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildExpect"}, detailed(pb, steps...)).Source
	if !strings.Contains(src, "Expect(Basic(),") {
		t.Errorf("auto-split fan-out did not wrap in Expect\n--- source: ---\n%s", src)
	}
	if len(caseLabeled(src, "case_0:")) != 1 || len(caseLabeled(src, "case_1:")) != 1 {
		t.Errorf("expected positional case_0/case_1 labels on the Expect branches\n--- source: ---\n%s", src)
	}
	// A branch label is its role tag and the CONCLUSION the branch
	// proves; the branch's hypotheses are the context comment's.
	for _, label := range []string{"case_0: P\"", "case_1: Q\""} {
		if len(caseLabeled(src, label)) != 1 {
			t.Errorf("missing the branch labeled %q\n--- source: ---\n%s", label, src)
		}
	}
	for _, want := range []string{"//   h0: P\n", "//   h0: Q\n"} {
		if !strings.Contains(src, want) {
			t.Errorf("missing %q\n--- source: ---\n%s", want, src)
		}
	}
	if strings.Contains(src, "⊢") {
		t.Errorf("a branch label prints its conclusion, never the sequent\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "Finally(") {
		t.Errorf("no foldable tail here — Finally must not appear\n--- source: ---\n%s", src)
	}
}

// TestEmit_FinallyNoFoldSingleRefute: a single trailing refute (run
// length 1) never folds; with 2 substantive children the node takes
// the Expect form and the lone refute renders as a labeled Case body.
func TestEmit_FinallyNoFoldSingleRefute(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	P := ext.Var("P", core.TypeBool())
	Q := ext.Var("Q", core.TypeBool())
	goal := prop.MakeProp(P.Or(Q))

	pb := ext.NewPoolBuilder()
	g1 := pb.PropRef(prop.MakeProp(P.Core(), P.Core()))
	g2 := pb.PropRef(prop.MakeProp(Q.Core()))
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{g1, g2},
			Step:     &proof.StepProto_Basic{Basic: &emptypb.Empty{}},
		},
		{Goal: g1, Step: &proof.StepProto_Assumption{Assumption: &emptypb.Empty{}}},
		{Goal: g2, Step: &proof.StepProto_CnfRefute{CnfRefute: &emptypb.Empty{}}},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildNoFold"}, detailed(pb, steps...)).Source
	if strings.Contains(src, "Finally(") {
		t.Errorf("run of length 1 must not fold to Finally\n--- source: ---\n%s", src)
	}
	if !strings.Contains(src, "Expect(Basic(),") {
		t.Errorf("2 substantive children should take the Expect form\n--- source: ---\n%s", src)
	}
	if !strings.Contains(src, "CnfRefute()") {
		t.Errorf("the lone refute must survive as a Case body\n--- source: ---\n%s", src)
	}
}

// TestEmit_ExpectFinallyCompiles: end-to-end compile check of the two
// render forms against the bare-name surface (library/authoring). The proto nests a
// uniform refute tail INSIDE an Expect Case body:
//
//	basic ──┬── assumption (case_0)
//	        └── basic ──┬── refute (case_1: folds to Basic() +
//	                    ├── refute  Finally(CnfRefute()))
//	                    └── refute
//
// exercising the Expect head, renderStepExpr's marker branch, and the
// Expect/Finally aliases in one compiled member.
func TestEmit_ExpectFinallyCompiles(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}

	env := makeTestEnv(t)

	P := ext.Var("P", core.TypeBool())
	Q := ext.Var("Q", core.TypeBool())
	R := ext.Var("R", core.TypeBool())
	S := ext.Var("S", core.TypeBool())
	goal := prop.MakeProp(P.Or(Q))

	pb := ext.NewPoolBuilder()
	g1 := pb.PropRef(prop.MakeProp(P.Core(), P.Core()))
	g2 := pb.PropRef(prop.MakeProp(Q.Core()))
	h1 := pb.PropRef(prop.MakeProp(Q.Core(), R.Core()))
	h2 := pb.PropRef(prop.MakeProp(R.Core()))
	h3 := pb.PropRef(prop.MakeProp(S.Core()))
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{g1, g2},
			Step:     &proof.StepProto_Basic{Basic: &emptypb.Empty{}},
		},
		{Goal: g1, Step: &proof.StepProto_Assumption{Assumption: &emptypb.Empty{}}},
		{
			Goal:     g2,
			SubGoals: []*ext.HolPropProto{h1, h2, h3},
			Step:     &proof.StepProto_Basic{Basic: &emptypb.Empty{}},
		},
		{Goal: h1, Step: &proof.StepProto_CnfRefute{CnfRefute: &emptypb.Empty{}}},
		{Goal: h2, Step: &proof.StepProto_CnfRefute{CnfRefute: &emptypb.Empty{}}},
		{Goal: h3, Step: &proof.StepProto_CnfRefute{CnfRefute: &emptypb.Empty{}}},
	}

	const pkg = "expectfinallyemit"
	src := emitMember(t, env, EmitOptions{
		Family:   "tmp/" + pkg,
		FuncName: "Build_ExpectFinally",
	}, detailed(pb, steps...)).Source

	if !strings.Contains(src, "Expect(Basic(),") {
		t.Errorf("outer 2-way fan-out did not take the Expect form\n--- source: ---\n%s", src)
	}
	if !strings.Contains(src, "Finally(CnfRefute()),") {
		t.Errorf("nested uniform tail did not fold to a Case-body Finally\n--- source: ---\n%s", src)
	}
	vetMember(t, goBin, pkg, src)
}

// TestEmit_SetTacStandardVocabulary: a set_tac record carrying exactly
// the driver's own vocabulary — what the session's `set_tac` always
// records (proof.DefaultSetTacConsts) — renders as the bare
// zero-argument call the chapter set families spell, not the 18-name
// list. A narrowed list stays spelled out (TestEmit_SetTacStep).
func TestEmit_SetTacStandardVocabulary(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	P := ext.Var("P", core.TypeBool())
	Q := ext.Var("Q", core.TypeBool())
	pb := ext.NewPoolBuilder()
	goal := pb.PropRef(prop.MakeProp(P.Imply(Q)))

	recorded := make([]string, 0, 18)
	for _, c := range proof.DefaultSetTacConsts() {
		recorded = append(recorded, string(c))
	}
	step := &proof.StepProto{
		Goal: goal,
		Step: &proof.StepProto_SetTac{
			SetTac: &proof.SetTacProto{Consts: recorded, Mode: proof.SetTacMode_SET_TAC_MEMBERSHIP},
		},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildSetTacStandard"}, detailed(pb, step)).Source
	if !strings.Contains(src, "SetTacMembership()") {
		t.Errorf("the standard vocabulary did not render as the bare call\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, `"delete"`) {
		t.Errorf("the standard vocabulary was spelled out\n--- source: ---\n%s", src)
	}
}

// TestEmit_StripQuant1Step: the bounded single-binder strip (proto tag
// 54) has an emit arm — a Go-recorded tree carrying a.Fix's ministep
// renders `StripQuant1()` instead of hitting the unhandled-ministep
// panic.
func TestEmit_StripQuant1Step(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))
	goal := prop.MakeProp(ext.ForAll(x)(R.Apply(x)).Core())
	body := prop.MakeProp(R.Apply(x).Core())

	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(body)},
			Step:     &proof.StepProto_StripQuant1{},
		},
		{Goal: pb.PropRef(body), Step: &proof.StepProto_TrivialSimplify{}},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildStripQuant1"}, detailed(pb, steps...)).Source
	if !strings.Contains(src, "StripQuant1()") {
		t.Errorf("strip_quant1 did not render\n--- source: ---\n%s", src)
	}
}

// TestEmit_DeriveHaveHandleRw: a Have chain whose later step rewrites
// with a fact a Have introduced binds that Have to a Go ident and
// addresses the rewrite through it — `fact1 := a.Have(…)` …
// `fact1.Rw()` — the handle form of the SAME ministep, instead of
// the positional `Rw(i, false)` the chapter lint bans. The rendering is
// type-checked: the binding statement and the method call are a new
// Go shape for the chain.
func TestEmit_DeriveHaveHandleRw(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}

	env := makeTestEnv(t)

	P := ext.Var("P", core.TypeBool())
	Q := ext.Var("Q", core.TypeBool())
	C := ext.Var("C", core.TypeBool())
	R := ext.Var("R", core.TypeBool())
	eq := P.Eq(Q).Core()
	claim1 := prop.MakeProp(eq)
	claim2 := prop.MakeProp(R.Core())
	goal := prop.MakeProp(C.Core())
	after1 := prop.MakeProp(C.Core(), eq)
	after2 := prop.MakeProp(C.Core(), eq, R.Core())
	rewritten := prop.MakeProp(Q.Core(), eq, R.Core())
	eqIdx := -1
	for i := range after2.NumHyps() {
		if after2.Hyp(i).AlphaEquals(eq) {
			eqIdx = i
		}
	}
	if eqIdx < 0 {
		t.Fatal("fixture defeated: the equation is not among the goal's hyps")
	}

	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(claim1), pb.PropRef(after1)},
			Step:     &proof.StepProto_Assert{Assert: pb.PropRef(claim1)},
		},
		{Goal: pb.PropRef(claim1), Step: &proof.StepProto_TrivialSimplify{}},
		{
			Goal:     pb.PropRef(after1),
			SubGoals: []*ext.HolPropProto{pb.PropRef(claim2), pb.PropRef(after2)},
			Step:     &proof.StepProto_Assert{Assert: pb.PropRef(claim2)},
		},
		{Goal: pb.PropRef(claim2), Step: &proof.StepProto_TrivialSimplify{}},
		{
			Goal:     pb.PropRef(after2),
			SubGoals: []*ext.HolPropProto{pb.PropRef(rewritten)},
			Step:     &proof.StepProto_Rw{Rw: &proof.RwProto{HypIndex: int32(eqIdx)}},
		},
		{Goal: pb.PropRef(rewritten), Step: &proof.StepProto_CnfRefute{}},
	}

	const pkg = "derivehandleemit"
	src := emitMember(t, env, EmitOptions{
		Family:   "tmp/" + pkg,
		FuncName: "Build_DeriveHandle",
	}, detailed(pb, steps...)).Source
	if !strings.Contains(src, "fact1 := a.Have(") {
		t.Errorf("the rewritten-with fact is not bound\n--- source: ---\n%s", src)
	}
	if !strings.Contains(src, "fact1.Rw()") {
		t.Errorf("the rewrite did not render in the handle form\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, fmt.Sprintf("Rw(%d, false)", eqIdx)) {
		t.Errorf("the rewrite still renders a positional hyp index\n--- source: ---\n%s", src)
	}
	// The second Have is addressed by nothing: no binding, no unused local.
	if strings.Contains(src, "fact2") {
		t.Errorf("a Have nothing addresses was bound\n--- source: ---\n%s", src)
	}
	vetMember(t, goBin, pkg, src)
}

// TestEmit_IffSplitsRenderNamedHalves: an ⇔ split renders its two
// branches through the NAMED slot constructors, each child in its own
// slot and in the order the constructor takes them — Forward (L ⊢ R)
// before Backward (R ⊢ L) for a goal ⇔, although the tactic produces
// the ⇐ child first; BothHold before NeitherHolds for a hypothesis one.
// Nothing observed this before: emit's role tags read "fwd" at child 0
// and "bwd" at child 1 — the reverse of ConclIffTactic — and tagged the
// hyp split, which has no directions at all, the same way. Both defects
// were invisible because a Case label is narrative and no gate read
// one; the emitted family member is type-checked, which is what reads
// the order.
func TestEmit_IffSplitsRenderNamedHalves(t *testing.T) {
	env := makeTestEnv(t)
	L := ext.Var("L", core.TypeBool())
	R := ext.Var("R", core.TypeBool())
	C := ext.Var("C", core.TypeBool())

	pb := ext.NewPoolBuilder()

	// ⊢ L ⇔ R  →  child 0 is R ⊢ L, child 1 is L ⊢ R.
	iffGoal := prop.MakeProp(L.Eq(R).Core())
	backChild := prop.MakeProp(L.Core(), R.Core())
	fwdChild := prop.MakeProp(R.Core(), L.Core())
	// L ⇔ R ⊢ C  →  child 0 has both, child 1 has both negations.
	hypGoal := prop.MakeProp(C.Core(), L.Eq(R).Core())
	bothChild := prop.MakeProp(C.Core(), L.Core(), R.Core())
	neitherChild := prop.MakeProp(C.Core(), ext.Not(L.Core()), ext.Not(R.Core()))

	for _, tc := range []struct {
		name  string
		steps []*proof.StepProto
		want  []string
		bad   []string
		// order is the whole point: the constructor's first slot first.
		// An emitter that names both halves but places them the other
		// way round is exactly the defect this test exists for.
		order [2]string
	}{
		{
			name: "goal",
			steps: []*proof.StepProto{
				{
					Goal:     pb.PropRef(iffGoal),
					SubGoals: []*ext.HolPropProto{pb.PropRef(backChild), pb.PropRef(fwdChild)},
					Step:     &proof.StepProto_SplitIff{SplitIff: &emptypb.Empty{}},
				},
				{Goal: pb.PropRef(backChild), Step: &proof.StepProto_CnfRefute{}},
				{Goal: pb.PropRef(fwdChild), Step: &proof.StepProto_CnfRefute{}},
			},
			want:  []string{"SplitIff(", "Forward(", "Backward("},
			bad:   []string{"Case(\"fwd", "Case(\"bwd", "SplitIffCases("},
			order: [2]string{"Forward(", "Backward("},
		},
		{
			name: "hyp",
			steps: []*proof.StepProto{
				{
					Goal:     pb.PropRef(hypGoal),
					SubGoals: []*ext.HolPropProto{pb.PropRef(bothChild), pb.PropRef(neitherChild)},
					Step:     &proof.StepProto_SplitHypIff{SplitHypIff: &proof.HypIndexProto{}},
				},
				{Goal: pb.PropRef(bothChild), Step: &proof.StepProto_CnfRefute{}},
				{Goal: pb.PropRef(neitherChild), Step: &proof.StepProto_CnfRefute{}},
			},
			want:  []string{"SplitHypIff(", "BothHold(", "NeitherHolds("},
			bad:   []string{"Case(\"fwd", "Case(\"bwd", "SplitHypIffCases("},
			order: [2]string{"BothHold(", "NeitherHolds("},
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			src := emitMember(t, env, EmitOptions{FuncName: "BuildIffSplit"}, detailed(pb, tc.steps...)).Source
			for _, w := range tc.want {
				if !strings.Contains(src, w) {
					t.Errorf("missing %q\n--- source: ---\n%s", w, src)
				}
			}
			for _, b := range tc.bad {
				if strings.Contains(src, b) {
					t.Errorf("still renders %q\n--- source: ---\n%s", b, src)
				}
			}
			// The slot IS the role, so the label states the branch goal
			// and nothing else — a role tag in the text would be a second,
			// unchecked copy of what the constructor already says.
			if strings.Contains(unspaced(src), "Backward(\"bwd") || strings.Contains(unspaced(src), "BothHold(\"both") {
				t.Errorf("the label repeats the slot\n--- source: ---\n%s", src)
			}
			if i, j := strings.Index(src, tc.order[0]), strings.Index(src, tc.order[1]); i < 0 || j < 0 || i > j {
				t.Errorf("the halves must render as %s, then %s\n--- source: ---\n%s",
					tc.order[0], tc.order[1], src)
			}
			goBin, err := exec.LookPath("go")
			if err != nil {
				t.Skip("go binary not on PATH")
			}
			const pkg = "iffsplitemit"
			member := emitMember(t, env, EmitOptions{Family: "tmp/" + pkg, FuncName: "Build_IffSplit"}, detailed(pb, tc.steps...)).Source
			vetMember(t, goBin, pkg, member)
		})
	}
}

// TestEmit_SoleLetterInstSpelling: the cross-type install pair of a
// LANDED sole-letter entry renders in the bound family's own spelling —
// the typed wrapper's explicit instance, `PolyRow.Inst[Bool]()` — and
// not through the `ctx.AtTypes(ctx.Dep(…), τ)` string channel.
// Without a landed entry (no wrapper to call)
// the AtTypes form stays: TestEmit_AtTypesFusion is that control.
func TestEmit_SoleLetterInstSpelling(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	source := prop.MakeProp(ext.ForAll(f, x, y)(x.Eq(y).Imply(f.Apply(x).Eq(f.Apply(y)).Core()).Core()).Core())
	srcNorm, _ := proof.Normalize(source)
	vars := proof.OrderedPropTypeVars(srcNorm)
	if len(vars) != 1 {
		t.Fatalf("fixture defeated: want exactly one type var, got %d", len(vars))
	}
	payload := core.PropTypeInst(srcNorm, core.MakeTypeSubst(vars[0], core.TypeBool()))
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
		if key == source.AlphaKey() || key == srcNorm.AlphaKey() {
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "POLY_ROW", Stated: source}, true
		}
		return ExternalLeaf{}, false
	}
	src := emitMember(t, env, EmitOptions{
		FuncName:            "BuildSoleInst",
		Family:              "real/real_field",
		EntryKey:            "prop_sole_inst_row",
		ResolveExternalLeaf: resolver,
		FamilyDepEntry: func(name string, key core.PropKey) (FamilyDepRef, bool) {
			if name == "POLY_ROW" {
				return FamilyDepRef{Expr: "PolyRow"}, true
			}
			return FamilyDepRef{}, false
		},
	}, detailed(pb, steps...)).Source
	if !strings.Contains(src, "Cite(PolyRow.Inst[Bool]())") {
		t.Errorf("the landed sole-letter entry's instance is not the wrapper's Inst\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "AtTypes(") {
		t.Errorf("the string channel is still rendered for a landed sole-letter entry\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "Deps:") {
		t.Errorf("a proved member renders no Deps — its recording observes what it reads\n--- source: ---\n%s", src)
	}
}

// TestEmit_SeveralLettersInstSpelling: a landed entry whose statement
// has several type variables is cited at a type instance through its
// typed wrapper too — `PolyRow.Inst(TypeBinder.BindA[Bool](),
// TypeBinder.BindB[Nat]())`, each letter of the stated form bound by
// name — and not through `ctx.AtTypes(ctx.Dep(PolyRow), TypeBool,
// NumType)`, whose positions are the normalized form's first
// occurrences. An entry with no wrapper to call (BareEntry) keeps the
// AtTypes form.
func TestEmit_SeveralLettersInstSpelling(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.MakeVarType("B")))
	source := prop.MakeProp(ext.ForAll(f, x, y)(x.Eq(y).Imply(f.Apply(x).Eq(f.Apply(y)).Core()).Core()).Core())
	srcNorm, _ := proof.Normalize(source)
	vars := proof.OrderedPropTypeVars(srcNorm)
	if len(vars) != 2 {
		t.Fatalf("fixture defeated: want two type vars, got %d", len(vars))
	}
	at := map[core.TypeName]core.HolType{"A": core.TypeBool(), "B": dsl.NumType}
	payload := core.PropTypeInst(srcNorm,
		core.MakeTypeSubst(vars[0], at[vars[0].Name()]), core.MakeTypeSubst(vars[1], at[vars[1].Name()]))
	C := ext.Var("C", core.TypeBool())
	goal := prop.MakeProp(C.Core())
	residual := prop.MakeProp(C.Core(), payload.Conclusion())

	resolver := func(key core.PropKey) (ExternalLeaf, bool) {
		if key == source.AlphaKey() || key == srcNorm.AlphaKey() {
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "POLY_ROW", Stated: source}, true
		}
		return ExternalLeaf{}, false
	}
	emitWith := func(ref FamilyDepRef) string {
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
		return emitMember(t, env, EmitOptions{
			FuncName:            "BuildSeveralInst",
			Family:              "real/real_field",
			EntryKey:            "prop_several_inst_row",
			ResolveExternalLeaf: resolver,
			FamilyDepEntry: func(name string, key core.PropKey) (FamilyDepRef, bool) {
				return ref, name == "POLY_ROW"
			},
		}, detailed(pb, steps...)).Source
	}

	src := emitWith(FamilyDepRef{Expr: "PolyRow"})
	if !strings.Contains(src, "Cite(PolyRow.Inst(TypeBinder.BindA[Bool](), TypeBinder.BindB[Nat]()))") {
		t.Errorf("the landed entry's instance is not the wrapper's Inst at its letters\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "AtTypes(") {
		t.Errorf("the positional string channel is still rendered for a landed entry\n--- source: ---\n%s", src)
	}

	bare := emitWith(FamilyDepRef{Expr: "PolyData.Row", BareEntry: true})
	if !strings.Contains(bare, "Cite(ctx.AtTypes(ctx.Dep(PolyData.Row), ") {
		t.Errorf("an entry with no wrapper does not keep the AtTypes form\n--- source: ---\n%s", bare)
	}
}

// TestEmit_GivenBranchHandleRw: a Case branch that rewrites with the
// ONE hypothesis its step introduced renders as the Given closure and
// addresses the rewrite through the hypothesis's handle (`h.Rw()`),
// never the positional `Rw(0, false)` the chapter lint refuses. The
// rendering is type-checked: the closure and the
// method call are a new Go shape for a branch body.
func TestEmit_GivenBranchHandleRw(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}
	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	eq := x.Eq(f.Apply(y)).Core()
	goal := prop.MakeProp(P.Apply(x).Core())
	yes := prop.MakeProp(P.Apply(x).Core(), eq)
	no := prop.MakeProp(P.Apply(x).Core(), ext.Not(eq))
	rewritten := prop.MakeProp(P.Apply(f.Apply(y).Core()).Core(), eq)

	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(yes), pb.PropRef(no)},
			Step:     &proof.StepProto_ByCase{ByCase: pb.TermRef(eq)},
		},
		{
			Goal:     pb.PropRef(yes),
			SubGoals: []*ext.HolPropProto{pb.PropRef(rewritten)},
			Step:     &proof.StepProto_Rw{Rw: &proof.RwProto{HypIndex: 0}},
		},
		{Goal: pb.PropRef(rewritten), Step: &proof.StepProto_CnfRefute{}},
		{Goal: pb.PropRef(no), Step: &proof.StepProto_CnfRefute{}},
	}
	const pkg = "givenbranchemit"
	src := emitMember(t, env, EmitOptions{
		Family:   "tmp/" + pkg,
		FuncName: "Build_GivenBranch",
	}, detailed(pb, steps...)).Source
	for _, want := range []string{"Given(func(b *Argument, h Fact) {", "b.Show(", "h.Rw()"} {
		if !strings.Contains(src, want) {
			t.Errorf("missing %q\n--- source: ---\n%s", want, src)
		}
	}
	if strings.Contains(unspaced(src), "Rw(0,false)") {
		t.Errorf("the branch still addresses its hypothesis by position\n--- source: ---\n%s", src)
	}
	vetMember(t, goBin, pkg, src)
}

// TestEmit_GivenReceiverAndHandleAreTwoNames: the Given closure's
// receiver and its Fact parameter are named from pools that keep clear
// of each other. Here the goal's own variables take b … g, so the
// branch's receiver is `h` — the name the hypothesis handle is also
// drawn under — and the two must come out distinct for the closure to
// compile.
func TestEmit_GivenReceiverAndHandleAreTwoNames(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}
	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	b, c, d, e, g := ext.Var("b", core.TypeA()), ext.Var("c", core.TypeA()), ext.Var("d", core.TypeA()), ext.Var("e", core.TypeA()), ext.Var("g", core.TypeA())
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.MakeFun(core.TypeA(), core.MakeFun(core.TypeA(), core.MakeFun(core.TypeA(), core.MakeFun(core.TypeA(), core.TypeBool()))))))
	letters := R.Apply(b, c, d, e, g).Core()
	eq := x.Eq(f.Apply(y)).Core()
	goal := prop.MakeProp(P.Apply(x).Core(), letters)
	yes := prop.MakeProp(P.Apply(x).Core(), letters, eq)
	no := prop.MakeProp(P.Apply(x).Core(), letters, ext.Not(eq))
	rewritten := prop.MakeProp(P.Apply(f.Apply(y).Core()).Core(), letters, eq)
	eqIdx := -1
	for i := range yes.NumHyps() {
		if yes.Hyp(i).AlphaEquals(eq) {
			eqIdx = i
		}
	}
	if eqIdx < 0 {
		t.Fatal("fixture defeated: the case hypothesis is not among the branch's hyps")
	}

	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(yes), pb.PropRef(no)},
			Step:     &proof.StepProto_ByCase{ByCase: pb.TermRef(eq)},
		},
		{
			Goal:     pb.PropRef(yes),
			SubGoals: []*ext.HolPropProto{pb.PropRef(rewritten)},
			Step:     &proof.StepProto_Rw{Rw: &proof.RwProto{HypIndex: int32(eqIdx)}},
		},
		{Goal: pb.PropRef(rewritten), Step: &proof.StepProto_CnfRefute{}},
		{Goal: pb.PropRef(no), Step: &proof.StepProto_CnfRefute{}},
	}
	const pkg = "givenreceiveremit"
	src := emitMember(t, env, EmitOptions{
		Family:   "tmp/" + pkg,
		FuncName: "Build_GivenReceiver",
	}, detailed(pb, steps...)).Source
	m := regexp.MustCompile(`Given\(func\((\w+) \*Argument, (\w+) Fact\)`).FindStringSubmatch(src)
	if m == nil {
		t.Fatalf("no Given closure\n--- source: ---\n%s", src)
	}
	if m[1] == m[2] {
		t.Errorf("the receiver and the hypothesis handle are both %q\n--- source: ---\n%s", m[1], src)
	}
	vetMember(t, goBin, pkg, src)
}

// TestEmit_SeveralHypothesesBranchSaysSo: a branch granted SEVERAL
// hypotheses that rewrites with one of them stays positional — the
// closure form's argument order is the induction template's, which the
// record does not carry — and the output SAYS SO, naming the lint that
// will refuse it and the GivenEach closure to rewrite it into, instead
// of failing a gate without a word.
func TestEmit_SeveralHypothesesBranchSaysSo(t *testing.T) {
	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	u := ext.Var("u", core.TypeA())
	v := ext.Var("v", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	L := x.Eq(f.Apply(y)).Core()
	R := u.Eq(f.Apply(v)).Core()
	// L ⇔ R ⊢ P(x): the hypothesis split grants L and R to one branch.
	hypGoal := prop.MakeProp(P.Apply(x).Core(), ext.Eq(L, R))
	both := prop.MakeProp(P.Apply(x).Core(), L, R)
	neither := prop.MakeProp(P.Apply(x).Core(), ext.Not(L), ext.Not(R))
	lIdx := -1
	for i := range both.NumHyps() {
		if both.Hyp(i).AlphaEquals(L) {
			lIdx = i
		}
	}
	if lIdx < 0 {
		t.Fatal("fixture defeated: L is not among the branch's hyps")
	}
	rewritten := prop.MakeProp(P.Apply(f.Apply(y).Core()).Core(), L, R)

	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(hypGoal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(both), pb.PropRef(neither)},
			Step:     &proof.StepProto_SplitHypIff{SplitHypIff: &proof.HypIndexProto{}},
		},
		{
			Goal:     pb.PropRef(both),
			SubGoals: []*ext.HolPropProto{pb.PropRef(rewritten)},
			Step:     &proof.StepProto_Rw{Rw: &proof.RwProto{HypIndex: int32(lIdx)}},
		},
		{Goal: pb.PropRef(rewritten), Step: &proof.StepProto_CnfRefute{}},
		{Goal: pb.PropRef(neither), Step: &proof.StepProto_CnfRefute{}},
	}
	src := emitMember(t, env, EmitOptions{FuncName: "Build_TwoHyps"}, detailed(pb, steps...)).Source
	if !strings.Contains(src, fmt.Sprintf("Rw(%d, false)", lIdx)) {
		t.Errorf("a two-hypothesis branch is expected to stay positional\n--- source: ---\n%s", src)
	}
	for _, want := range []string{"TestLintNoPositionalHypIndices", "GivenEach(func(b *Argument, ihs []Fact)"} {
		if !strings.Contains(src, want) {
			t.Errorf("the output does not say so: missing %q\n--- source: ---\n%s", want, src)
		}
	}
	if strings.Contains(unspaced(src), unspaced("Given(func(b *Argument, h Fact")) {
		t.Errorf("a two-hypothesis branch must not take the one-hypothesis closure\n--- source: ---\n%s", src)
	}
}

// TestEmit_StripQuantHypIndexRoundTrips pins the flat renderer for
// strip_quant's optional hyp_index: a record naming a hyp renders as
// StripQuantAt(i) and a record without one as StripQuant() — the same
// split emit makes for SplitDisj / SplitDisjAt, so a session's named
// ∃-elimination is not silently widened to the pick-first form.
func TestEmit_StripQuantHypIndexRoundTrips(t *testing.T) {
	env := makeTestEnv(t)
	x := ext.Var("x", core.TypeA())
	x0 := ext.Var("x_0", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	g := ext.Var("g", core.TypeBool())
	goal := prop.MakeProp(g.Core(), ext.Exists(x)(P.Apply(x)))
	child := prop.MakeProp(g.Core(), P.Apply(x0).Core())
	zero := int32(0)

	for _, tc := range []struct {
		name    string
		payload *proof.HypIndexProto
		want    string
		bad     string
	}{
		{"indexed", &proof.HypIndexProto{HypIndex: &zero}, "StripQuantAt(0)", "StripQuant()"},
		{"pick-first", &proof.HypIndexProto{}, "StripQuant()", "StripQuantAt("},
		{"legacy-empty-payload", nil, "StripQuant()", "StripQuantAt("},
	} {
		t.Run(tc.name, func(t *testing.T) {
			pb := ext.NewPoolBuilder()
			steps := []*proof.StepProto{
				{
					Goal:     pb.PropRef(goal),
					SubGoals: []*ext.HolPropProto{pb.PropRef(child)},
					Step:     &proof.StepProto_StripQuant{StripQuant: tc.payload},
				},
				{Goal: pb.PropRef(child), Step: &proof.StepProto_CnfRefute{}},
			}
			src := emitMember(t, env, EmitOptions{FuncName: "BuildStripQuantAt"}, detailed(pb, steps...)).Source
			if !strings.Contains(src, tc.want) {
				t.Errorf("missing %q\n--- source: ---\n%s", tc.want, src)
			}
			if strings.Contains(src, tc.bad) {
				t.Errorf("still renders %q\n--- source: ---\n%s", tc.bad, src)
			}
		})
	}
}

func TestEmitInductionUsesCoreTermOfBinder(t *testing.T) {
	env := makeTestEnv(t)
	pool := ext.NewPoolBuilder()
	n := ext.Var("n", dsl.NumType)
	step := &proof.StepProto{Step: &proof.StepProto_Induction{
		Induction: pool.TermRef(n.Core()),
	}}
	emitter := &_Emitter{
		reader: ext.NewPoolReader(pool.Pool(), env.ProofService.LoadConstMeta),
		printer: &ext.GoTermPrinter{
			VarIdent: func(core.VarTerm) (string, bool) { return "n", true },
		},
	}
	if got := emitter.emitMiniStep(step); got != "ctx.InductStep(n.Core())" {
		t.Errorf("induction over a typed binder rendered as %q", got)
	}
	if got, hasArg := emitter.emitMiniStepCaseHead(step); got != "ctx.InductStep(n.Core()" || !hasArg {
		t.Errorf("induction with cases over a typed binder rendered as %q (has argument %t)", got, hasArg)
	}
}

// TestCaseTag_ReturnsOnlyListedRoleTags: whatever ministep fans a
// branch, its tag is one of caseRoleTags or the numbered `case_<idx>`.
// The chapter lint refuses exactly those (the gate suite's
// TestLintRefusesEveryEmittedRoleTag), so a tag added to caseTag and
// not to the list would be a rendered label the lint lets through.
// The step types are read off StepProto's oneof, so a new ministep is
// covered without being named here.
func TestCaseTag_ReturnsOnlyListedRoleTags(t *testing.T) {
	listed := map[string]bool{}
	for _, tag := range caseRoleTags {
		listed[tag] = true
	}
	numbered := regexp.MustCompile(`^case_[0-9]+$`)
	returned := map[string]bool{}
	members := (&proof.StepProto{}).ProtoReflect().Descriptor().Oneofs().ByName("step").Fields()
	if members.Len() == 0 {
		t.Fatal("StepProto has no `step` oneof members to read")
	}
	for i := 0; i < members.Len(); i++ {
		fd := members.Get(i)
		step := &proof.StepProto{}
		m := step.ProtoReflect()
		if fd.Message() != nil {
			m.Set(fd, m.NewField(fd))
		} else {
			m.Set(fd, fd.Default())
		}
		for idx := 0; idx < 3; idx++ {
			tag := caseTag(step, idx)
			returned[tag] = true
			if !listed[tag] && !numbered.MatchString(tag) {
				t.Errorf("caseTag(%s, %d) = %q, which caseRoleTags does not list", fd.Name(), idx, tag)
			}
		}
	}
	for _, tag := range caseRoleTags {
		if !returned[tag] {
			t.Errorf("caseRoleTags lists %q, which no ministep's caseTag returns", tag)
		}
	}
}

// TestEmit_BranchLabelIsTheConclusion: a conjunction split under a
// hypothesis labels each arm with its role tag and the CONJUNCT the arm
// proves. The hypothesis is the context comment's — a label that
// printed the sequent spent its width on the hypothesis list, and under
// a long one never reached the conclusion.
func TestEmit_BranchLabelIsTheConclusion(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	H := ext.Var("H", core.TypeBool())
	P := ext.Var("P", core.TypeBool())
	Q := ext.Var("Q", core.TypeBool())
	goal := prop.MakeProp(P.And(Q).Core(), H.Core())

	pb := ext.NewPoolBuilder()
	left := pb.PropRef(prop.MakeProp(P.Core(), H.Core()))
	right := pb.PropRef(prop.MakeProp(Q.Core(), H.Core()))
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{left, right},
			Step:     &proof.StepProto_SplitConj{SplitConj: &emptypb.Empty{}},
		},
		{Goal: left, Step: &proof.StepProto_Assumption{Assumption: &emptypb.Empty{}}},
		{Goal: right, Step: &proof.StepProto_Assumption{Assumption: &emptypb.Empty{}}},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildSplitUnderHyp"}, detailed(pb, steps...)).Source
	for _, label := range []string{"left: P\"", "right: Q\""} {
		if len(caseLabeled(src, label)) != 1 {
			t.Errorf("missing the branch labeled %q\n--- source: ---\n%s", label, src)
		}
	}
	for _, want := range []string{"//   h0: H\n", "//   concl: P\n", "//   concl: Q\n"} {
		if !strings.Contains(src, want) {
			t.Errorf("missing %q\n--- source: ---\n%s", want, src)
		}
	}
	for _, label := range caseLabeled(src, "") {
		if strings.Contains(label, "H") {
			t.Errorf("a branch label names the hypothesis: %s", label)
		}
	}
}

// caseLabeled returns the label of each Case in src whose label opens
// with prefix, from the prefix to the end of its line.
func caseLabeled(src, prefix string) []string {
	var labels []string
	for _, m := range regexp.MustCompile(`Case\(\s*"(.*)`).FindAllStringSubmatch(src, -1) {
		if strings.HasPrefix(m[1], prefix) {
			labels = append(labels, m[1])
		}
	}
	return labels
}
