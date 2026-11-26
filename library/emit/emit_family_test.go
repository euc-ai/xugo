package emit

// Tests for the member scaffold: the family.Add entry, family.Theorem
// and family.Sections, and the declarations a member body carries.

import (
	"os/exec"
	"strings"
	"testing"

	"go.uber.org/goleak"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/xugofmt"
	"github.com/euc-ai/xugo/prover/proof"
)

// familyFixtureSection builds the one-section Lemma+KnownThm+residual
// fixture (the Cite fusion shape TestEmit_Cites uses) with a ∀-headed
// section goal, so the member has a binder slot to suggest. Returns the
// section plus the lemma payload's lookup keys for the external-leaf
// resolver.
func familyFixtureSection() (*proof.DetailedProofProto, core.PropKey, core.PropKey) {
	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))
	S := ext.Var("S", core.MakeFun(core.TypeA(), core.TypeBool()))
	goal := prop.MakeProp(ext.ForAll(x)(R.Apply(x)).Core())
	lemma := prop.MakeProp(ext.ForAll(y)(S.Apply(y)).Core())
	residual := prop.MakeProp(goal.Conclusion(), lemma.Conclusion())

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
	normalized, _ := proof.Normalize(lemma)
	return detailed(pb, steps...), lemma.AlphaKey(), normalized.AlphaKey()
}

// assertFormatted pins paste-readiness: a member lands as rendered, so
// it is already in a chapter file's layout (xugofmt).
func assertFormatted(t *testing.T, src string) {
	t.Helper()
	if formatted, err := xugofmt.Source([]byte(src)); err != nil {
		t.Fatalf("member output does not format: %v\n--- source: ---\n%s", err, src)
	} else if string(formatted) != src {
		t.Errorf("member output is not in xugo_fmt's layout\n--- emitted: ---\n%s\n--- xugo_fmt: ---\n%s", src, formatted)
	}
}

// TestEmit_FamilyProfile: a single-section member renders the families
// framework's shape — family.Add entry var (typed Deps through the
// resolver hook, Key from EntryKey) + a zero-parameter family.Theorem
// binder closure with the liftable signature as a comment.
func TestEmit_FamilyProfile(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := makeTestEnv(t)
	section, lemmaKey, normalizedKey := familyFixtureSection()

	resolveLeaf := func(key core.PropKey) (ExternalLeaf, bool) {
		if key == lemmaKey || key == normalizedKey {
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "IN_DELETE_LIKE"}, true
		}
		return ExternalLeaf{}, false
	}

	// (a) typed-dep arm: the resolver lands the dep as a cross-family
	// entry var, whose package import the file must carry.
	res := emitMember(t, env, EmitOptions{
		FuncName:            "Build_FamMember",
		Family:              "real/real_field",
		EntryKey:            "prop_fam_member_row",
		ResolveExternalLeaf: resolveLeaf,
		FamilyDepEntry: func(name string, key core.PropKey) (FamilyDepRef, bool) {
			if name != "IN_DELETE_LIKE" {
				t.Errorf("FamilyDepEntry called with unexpected name %q", name)
			}
			if key == "" {
				t.Errorf("FamilyDepEntry called with empty key for %q", name)
			}
			return FamilyDepRef{
				Expr:       "real_ring.NegNeg",
				ImportPath: "github.com/euc-ai/xugo/library/proofs/real/real_ring",
			}, true
		},
	}, section)
	src := res.Source
	assertFormatted(t, src)

	for _, want := range []string{
		"package real_field",
		`"github.com/euc-ai/xugo/library/registry"`,
		`"github.com/euc-ai/xugo/library/proofs/real/real_ring"`,
		"var FamMember = family.Add(registry.ProofEntry{",
		`Key:  "prop_fam_member_row",`,
		// The Build constructor is the literal's last field, inline — one
		// declaration per entry (the entry lint's E1) — and the statement
		// is its first argument inline: a hoisted GoalText const is for a
		// text several sites share, and the statement has one.
		"\tBuild: family.Theorem(\"",
		"a.Do(",
		// The cite target is the entry var the registry resolves the
		// name to — never the raw registered name.
		`Cite(real_ring.NegNeg),`,
		// The liftable binder signature, read off the ∀x headline.
		"//\tfunc(a *Argument, x Term)",
	} {
		if !strings.Contains(src, want) {
			t.Errorf("member output missing %q\n--- source: ---\n%s", want, src)
		}
	}
	// The typed dep leaves no DepNames string behind, and a proved
	// member renders no Deps: its recording observes what it reads.
	if strings.Contains(src, "DepNames:") || strings.Contains(src, "Deps:") {
		t.Errorf("a proved member rendered a dep list\n--- source: ---\n%s", src)
	}
	// A member is hand-maintained chapter source: no generated-file
	// header, no separate Build func, no self-installed CNF blob.
	for _, banned := range []string{
		"Code generated",
		"func Build_FamMember",
		"var Build_FamMember",
		"go:embed",
		"InstallCNFCache",
	} {
		if strings.Contains(src, banned) {
			t.Errorf("member output renders %q\n--- source: ---\n%s", banned, src)
		}
	}
	if len(res.DepNames) != 1 || res.DepNames[0] != "IN_DELETE_LIKE" {
		t.Errorf("DepNames = %v, want [IN_DELETE_LIKE]", res.DepNames)
	}

	// (b) no dep resolver → the dep renders as a TODO inside Deps (a dep
	// is an entry; the name has none yet), and no cross-family import
	// appears.
	src2 := emitMember(t, env, EmitOptions{
		FuncName:            "Build_FamMember",
		Family:              "real/real_field",
		ResolveExternalLeaf: resolveLeaf,
	}, section).Source
	if !strings.Contains(src2, "// TODO: the proof cites IN_DELETE_LIKE, which no entry proves") {
		t.Errorf("unresolved dep did not render as a TODO in the entry\n--- source: ---\n%s", src2)
	}
	if strings.Contains(src2, "real_ring") {
		t.Errorf("no resolver, yet a cross-family import rendered\n--- source: ---\n%s", src2)
	}
	if strings.Contains(src2, "Key:") {
		t.Errorf("no EntryKey, yet a Key line rendered\n--- source: ---\n%s", src2)
	}
}

// TestEmit_FamilySections: a member proved through a lemma of its own
// renders as family.Sections — the earlier section a `ctx.Lemma` local,
// the member's own section `return ctx.Theorem(headline, …)` citing the
// local by closure capture.
func TestEmit_FamilySections(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))
	S := ext.Var("S", core.MakeFun(core.TypeA(), core.TypeBool()))
	goal := prop.MakeProp(ext.ForAll(x)(R.Apply(x)).Core())
	lemma := prop.MakeProp(ext.ForAll(y)(S.Apply(y)).Core())
	residual := prop.MakeProp(goal.Conclusion(), lemma.Conclusion())

	pb := ext.NewPoolBuilder()
	lemmaSteps := []*proof.StepProto{{
		Goal: pb.PropRef(lemma),
		Step: &proof.StepProto_CnfRefute{},
	}}
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

	res := emitMember(t, env, EmitOptions{
		FuncName: "Build_TwoSections",
		Family:   "real/real_field",
		EntryKey: "prop_two_sections",
	}, detailed(pb, lemmaSteps...), detailed(pb, goalSteps...))
	src := res.Source
	assertFormatted(t, src)

	for _, want := range []string{
		"package real_field",
		"var TwoSections = family.Add(registry.ProofEntry{",
		`Key:  "prop_two_sections",`,
		"\tBuild: family.Sections(\"",
		"func(ctx *Script, headline string) *GoalStackNode {",
		"lemma1 := ctx.Lemma(",
		"return ctx.Theorem(headline,",
		"Cite(lemma1),",
	} {
		if !strings.Contains(src, want) {
			t.Errorf("sections output missing %q\n--- source: ---\n%s", want, src)
		}
	}
	// The lemma is declared before the theorem that cites it.
	if strings.Index(src, "lemma1 := ctx.Lemma(") > strings.Index(src, "Cite(lemma1)") {
		t.Errorf("the lemma local is cited before it is declared\n--- source: ---\n%s", src)
	}
	// A section of the member is no dep.
	if strings.Contains(src, "Deps:") || len(res.DepNames) != 0 {
		t.Errorf("a cite of the member's own lemma rendered a dep (DepNames = %v)\n--- source: ---\n%s", res.DepNames, src)
	}
}

// TestEmit_FamilySectionsRefuseDefinition: a definition is a member of
// its own — a `define` section among several is refused, loudly, rather
// than rendered as one lemma of a Sections member.
func TestEmit_FamilySectionsRefuseDefinition(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := makeTestEnv(t)

	defMeta, _ := env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("MY_DEF", core.TypeBool()))
	def := ext.Const(defMeta, core.TypeBool())
	P := ext.Var("P", core.TypeBool())
	definition := prop.MakeProp(def.Eq(P).Core())
	goal := prop.MakeProp(P.Imply(def).Core())

	pb := ext.NewPoolBuilder()
	defineSteps := []*proof.StepProto{{
		Goal: pb.PropRef(definition),
		Step: &proof.StepProto_Define{Define: &proof.DefineProto{Const: pb.TermRef(def)}},
	}}
	goalSteps := []*proof.StepProto{{
		Goal: pb.PropRef(goal),
		Step: &proof.StepProto_CnfRefute{},
	}}

	_, err := EmitMember(
		[]*proof.DetailedProofProto{detailed(pb, defineSteps...), detailed(pb, goalSteps...)},
		env.ProofService.LoadConstMeta,
		EmitOptions{Family: "real/real_field", FuncName: "Build_DefineAmongSections"},
	)
	if err == nil {
		t.Fatal("a define section among several was not refused")
	}
	if !strings.Contains(err.Error(), "records a definition door") {
		t.Errorf("the refusal does not name the definition: %v", err)
	}
}

// TestEmit_FamilyVocabPrunesDeclarations: a constant the family's
// vocabulary declares is not re-registered by the member body
// (EmitOptions.FamilyVocab — the family installs it before the headline
// parses), a def_expand renders as `Unfold("<name>")` (the name-taking
// spelling of the same ministep, declaring nothing), and a Skolem no
// rendered text mentions gets no `ctx.Var` line — no const/var wall, a
// defined constant declared a second time beside the vocabulary. The
// negative control (no vocabulary handed in) keeps the
// registration-only const line.
func TestEmit_FamilyVocabPrunesDeclarations(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := makeTestEnv(t)
	reg := func(m core.ConstTermMeta) core.ConstTermMeta {
		got, _ := env.ProofService.LoadOrStoreConstMeta(m)
		return got
	}
	A := core.MakeVarType("A")
	setA := core.MakeFun(A, core.TypeBool())
	setNum := core.MakeFun(ext.NumType, core.TypeBool())
	subsetMeta := reg(core.MakeConstMeta("subset", core.MakeFun(setA, setA, core.TypeBool())))
	subsetNum := ext.Const(subsetMeta, core.MakeFun(setNum, setNum, core.TypeBool()))

	s := ext.Var("s", setNum)
	tv := ext.Var("t", setNum)
	body := subsetNum.Apply(s, tv).Imply(subsetNum.Apply(tv, s))
	goal := prop.MakeProp(ext.ForAll(s, tv)(body).Core())
	stripped := prop.MakeProp(body.Core())
	unfolded := prop.MakeProp(s.Eq(tv).Core())

	mkSection := func() *proof.DetailedProofProto {
		pb := ext.NewPoolBuilder()
		steps := []*proof.StepProto{
			{
				Goal:     pb.PropRef(goal),
				SubGoals: []*ext.HolPropProto{pb.PropRef(stripped)},
				Step:     &proof.StepProto_StripQuant{},
			},
			{
				Goal:     pb.PropRef(stripped),
				SubGoals: []*ext.HolPropProto{pb.PropRef(unfolded)},
				Step:     &proof.StepProto_DefExpand{DefExpand: pb.TermRef(subsetNum)},
			},
			{Goal: pb.PropRef(unfolded), Step: &proof.StepProto_TrivialSimplify{}},
		}
		return detailed(pb, steps...)
	}

	{
		src := emitMember(t, env, EmitOptions{
			FuncName:    "Build_VocabMember",
			EntryKey:    "prop_vocab_member",
			FamilyVocab: &FamilyVocab{Consts: map[string]bool{"subset": true}},
		}, mkSection()).Source
		if strings.Contains(unspaced(src), `Const("subset"`) {
			t.Errorf("a vocabulary const was re-registered by the body\n--- source: ---\n%s", src)
		}
		if !strings.Contains(src, `Unfold("subset")`) {
			t.Errorf("def_expand did not render as Unfold\n--- source: ---\n%s", src)
		}
		if strings.Contains(src, "DefExpandStep(") {
			t.Errorf("def_expand still renders the const-term form\n--- source: ---\n%s", src)
		}
		if strings.Contains(src, "ctx.Var(") {
			t.Errorf("a Skolem no text mentions was declared\n--- source: ---\n%s", src)
		}
	}
	{
		// Negative control: without the vocabulary the registration-only
		// const line is kept (the family may not declare it).
		src := emitMember(t, env, EmitOptions{
			FuncName: "Build_VocabMemberControl",
			EntryKey: "prop_vocab_member_control",
		}, mkSection()).Source
		if !strings.Contains(unspaced(src), `ctx.Const("subset"`) {
			t.Errorf("control lost the registration-only const line\n--- source: ---\n%s", src)
		}
	}
}

func TestEmit_DependencyPackageNameDoesNotShadow(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skip(err)
	}
	env := makeTestEnv(t)
	x := ext.Var("x", core.TypeA())
	w := ext.Var("functions", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	law := prop.MakeProp(ext.ForAll(x)(P.Apply(x)).Core())
	goal := prop.MakeProp(P.Apply(w).Core())
	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{Goal: pb.PropRef(goal), SubGoals: []*ext.HolPropProto{pb.PropRef(law)}, Step: &proof.StepProto_By{By: &proof.ByProto{Premises: []*proof.ByPremiseProto{{Install: pb.PropRef(law), Witnesses: []uint32{pb.TermRef(w)}}}}}},
		{Goal: pb.PropRef(law), Step: &proof.StepProto_KnownThm{KnownThm: &proof.KnownThmProto{StrongerGoal: pb.PropRef(law)}}},
	}
	const pkg = "packagenameemit"
	src := emitMember(t, env, EmitOptions{Family: "tmp/" + pkg, FuncName: "Build_PackageName",
		ResolveExternalLeaf: func(key core.PropKey) (ExternalLeaf, bool) {
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "LAW", Stated: law}, key == law.AlphaKey()
		},
		FamilyDepEntry: func(name string, _ core.PropKey) (FamilyDepRef, bool) {
			return FamilyDepRef{Expr: "functions.InjectiveOnDef", ImportPath: "github.com/euc-ai/xugo/library/proofs/sets/functions"}, name == "LAW"
		},
	}, detailed(pb, steps...)).Source
	vetMember(t, goBin, pkg, src)
}

func TestEmit_NormalizedSectionTypeInstanceCompiles(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skip(err)
	}
	env := makeTestEnv(t)
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool()))
	lemma := prop.MakeProp(ext.ForAll(x)(P.Apply(x).Imply(Q.Apply(x).Core())).Core())
	normalized, _ := proof.Normalize(lemma)
	if normalized.AlphaKey() == lemma.AlphaKey() {
		t.Fatal("fixture must normalize the source")
	}
	instance := core.PropTypeInst(normalized, core.MakeTypeSubst(core.TypeA(), core.TypeBool()))
	pb := ext.NewPoolBuilder()
	lemmaRef, instanceRef, normalizedRef := pb.PropRef(lemma), pb.PropRef(instance), pb.PropRef(normalized)
	first := detailed(pb, &proof.StepProto{Goal: lemmaRef, Step: &proof.StepProto_TrivialSimplify{}})
	second := detailed(pb, &proof.StepProto{Goal: instanceRef, Step: &proof.StepProto_TypeInst{TypeInst: normalizedRef}})
	const pkg = "normalizedsectioninstemit"
	src := emitMember(t, env, EmitOptions{Family: "tmp/" + pkg, FuncName: "Build_NormalizedSection"}, first, second).Source
	vetMember(t, goBin, pkg, src)
}
