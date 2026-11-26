package emit

import (
	"math/big"
	"os/exec"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// complexPhantom is the alias a family's generated wrapper preamble
// declares for another chapter's phantom its statements name, as the
// scratch package of a member over the complex numbers needs it. The
// phantoms of the types minted below the chapters (Real, Nat, the
// letters) need no such file: the member's own dot import of
// library/authoring brings them.
const complexPhantom = `import "github.com/euc-ai/xugo/library/proofs/complex/complex_field"

type Complex = complex_field.Complex
`

// realNumeralEnv is makeTestEnv with the constants of a real numeral
// loadable, so a recorded `&n` decodes.
func realNumeralEnv(t *testing.T) *proof.ProverEnv {
	env := makeTestEnv(t)
	for _, meta := range []core.ConstTermMeta{ext.ZeroMeta, ext.Bit0Meta, ext.Bit1Meta, dsl.RealOfNumMeta} {
		env.ProofService.LoadOrStoreConstMeta(meta)
	}
	return env
}

// byAtRealTwoSection is a `by` that closes the member's statement from
// the named premise `∀x:real. f(x)` grounded at the witness `&2`, with
// the dep resolver that names the premise. The statement is
// `∀y:real. f(y) ⇒ f(&2)` when it binds a real and `f(&2)` when it
// binds nothing.
func byAtRealTwoSection(bindsAReal bool) (*proof.DetailedProofProto, func(core.PropKey) (ExternalLeaf, bool)) {
	x := ext.Var("x", dsl.RealType)
	y := ext.Var("y", dsl.RealType)
	f := ext.WrapTerm(ext.Var("f", core.MakeFun(dsl.RealType, core.TypeBool())))
	two := ext.WrapTerm(dsl.RealOfNumMeta.Term()).Apply(ext.MakeNumeral(big.NewInt(2)))
	lemma := prop.MakeProp(ext.ForAll(x)(f.Apply(x)).Core())
	statement := f.Apply(two)
	if bindsAReal {
		statement = ext.ForAll(y)(f.Apply(y).Imply(f.Apply(two)))
	}

	pb := ext.NewPoolBuilder()
	claimRef := pb.PropRef(lemma)
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(prop.MakeProp(statement.Core())),
			SubGoals: []*ext.HolPropProto{claimRef},
			Step: &proof.StepProto_By{By: &proof.ByProto{
				Premises: []*proof.ByPremiseProto{{Install: claimRef, Witnesses: []uint32{pb.TermRef(two.Core())}}},
			}},
		},
		{Goal: claimRef, Step: &proof.StepProto_KnownThm{KnownThm: &proof.KnownThmProto{StrongerGoal: claimRef}}},
	}
	normalized, _ := proof.Normalize(lemma)
	resolve := func(key core.PropKey) (ExternalLeaf, bool) {
		if key == lemma.AlphaKey() || key == normalized.AlphaKey() {
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "HOLDS_EVERYWHERE"}, true
		}
		return ExternalLeaf{}, false
	}
	return detailed(pb, steps...), resolve
}

// TestEmit_ByWitnessIsItsText: a `by` premise's witness that is no
// variable renders as the text a chapter writes, parsed by the
// Argument the step runs under and typed by its phantom —
// `a.TermAs[Real]("&2")` — and not as the Go tower of the numeral's
// constructors. The member binds no local for the tower's constants,
// and it type-checks.
//
// The text is read at the phantom's type, so `TermAs[Real]("&2")`
// remains a real numeral even in a family whose ambient domain is ℤ. The
// phantom `Real` is in every proof file's scope — the type is minted
// below the chapters, and library/authoring declares its phantom — so
// a member whose statement binds no real writes the text all the same.
func TestEmit_ByWitnessIsItsText(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}
	env := realNumeralEnv(t)
	section, resolve := byAtRealTwoSection(true)

	const pkg = "bywitnesstextemit"
	entry, entries := landedEntry(pkg, "HOLDS_EVERYWHERE", "HoldsEverywhere")
	src := emitMember(t, env, EmitOptions{
		Family:              "tmp/" + pkg,
		FuncName:            "Build_ByWitnessText",
		ResolveExternalLeaf: resolve,
		FamilyDepEntry:      entry,
	}, section).Source
	if !strings.Contains(src, `By(At(HoldsEverywhere, a.TermAs[Real]("&2")))`) {
		t.Errorf("the witness &2 is not rendered as its typed text\n--- source: ---\n%s", src)
	}
	if strings.Contains(strings.ToUpper(src), "BIT0.APPLY") || strings.Contains(strings.ToUpper(src), "BIT1.APPLY") ||
		strings.Contains(src, "real_of_num.Apply") {
		t.Errorf("the witness still renders the numeral's constructor tower\n--- source: ---\n%s", src)
	}
	for _, local := range []string{"bit0 :=", "bit1 :=", "_0 :=", "real_of_num :="} {
		if strings.Contains(src, local) {
			t.Errorf("a constant the witness text spells is bound to a local nothing reads (%s)\n--- source: ---\n%s", local, src)
		}
	}
	vetMemberWith(t, goBin, pkg, src, entries)

	section, resolve = byAtRealTwoSection(true)
	src = emitMember(t, env, EmitOptions{
		FuncName: "BuildByWitnessTyped", CoerceDomain: dsl.IntType, ResolveExternalLeaf: resolve,
	}, section).Source
	if !strings.Contains(src, `By(At("HOLDS_EVERYWHERE", a.TermAs[Real]("&2")))`) {
		t.Errorf("the witness's expected type does not override the ambient domain\n%s", src)
	}

	section, resolve = byAtRealTwoSection(false)
	src = emitMember(t, env, EmitOptions{FuncName: "BuildByWitnessUnbound", ResolveExternalLeaf: resolve}, section).Source
	if !strings.Contains(src, `By(At("HOLDS_EVERYWHERE", a.TermAs[Real]("&2")))`) {
		t.Errorf("a member whose statement binds no real does not write the witness &2 as its typed text\n--- source: ---\n%s", src)
	}
}

// byAtComplexSection is a `by` whose one premise is the named
// `∀x:complex. f(x)` grounded at the witness `g(c)`, with the dep
// resolver that names the premise. The statement is
// `∀y:complex. f(y) ⇒ f(g(c))` when it binds a complex — the signature
// that puts the phantom `Complex` in the family's scope — and `f(g(c))`
// when it binds nothing.
func byAtComplexSection(bindsAComplex bool) (*proof.DetailedProofProto, func(core.PropKey) (ExternalLeaf, bool)) {
	complexType := ext.MakeType("complex")
	x := ext.Var("x", complexType)
	y := ext.Var("y", complexType)
	c := ext.Var("c", complexType)
	g := ext.WrapTerm(ext.Var("g", core.MakeFun(complexType, complexType)))
	f := ext.WrapTerm(ext.Var("f", core.MakeFun(complexType, core.TypeBool())))
	witness := g.Apply(c)
	lemma := prop.MakeProp(ext.ForAll(x)(f.Apply(x)).Core())
	statement := f.Apply(witness)
	if bindsAComplex {
		statement = ext.ForAll(y)(f.Apply(y).Imply(f.Apply(witness)))
	}

	pb := ext.NewPoolBuilder()
	claimRef := pb.PropRef(lemma)
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(prop.MakeProp(statement.Core())),
			SubGoals: []*ext.HolPropProto{claimRef},
			Step: &proof.StepProto_By{By: &proof.ByProto{
				Premises: []*proof.ByPremiseProto{{Install: claimRef, Witnesses: []uint32{pb.TermRef(witness.Core())}}},
			}},
		},
		{Goal: claimRef, Step: &proof.StepProto_KnownThm{KnownThm: &proof.KnownThmProto{StrongerGoal: claimRef}}},
	}
	normalized, _ := proof.Normalize(lemma)
	resolve := func(key core.PropKey) (ExternalLeaf, bool) {
		if key == lemma.AlphaKey() || key == normalized.AlphaKey() {
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "HOLDS_EVERYWHERE"}, true
		}
		return ExternalLeaf{}, false
	}
	return detailed(pb, steps...), resolve
}

// TestEmit_WitnessTextNeedsItsPhantomInScope: the phantom of a type a
// CHAPTER mints is in a family's scope only where the family declares
// it or one of its wrappers' signatures names the type. A member whose
// statement binds a complex has `Complex` to name — its own wrapper is
// generated when it lands, and the preamble aliases the phantom — and
// writes the witness as a typed text; one whose statement binds nothing
// has no `Complex`, and writes the witness as the text `Term` reads,
// which names no phantom — not as a Go expression over bound locals.
func TestEmit_WitnessTextNeedsItsPhantomInScope(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}
	env := makeTestEnv(t)

	const pkg = "witnessphantomscopeemit"
	entry, further := landedEntry(pkg, "HOLDS_EVERYWHERE", "HoldsEverywhere")
	section, resolve := byAtComplexSection(true)
	src := emitMember(t, env, EmitOptions{
		Family:              "tmp/" + pkg,
		FuncName:            "Build_ByWitnessInScope",
		ResolveExternalLeaf: resolve,
		FamilyDepEntry:      entry,
	}, section).Source
	if !strings.Contains(src, `By(At(HoldsEverywhere, a.TermAs[Complex]("g(c)")))`) {
		t.Errorf("the witness g(c) is not rendered as its typed text\n--- source: ---\n%s", src)
	}
	further["phantoms.go"] = "package " + pkg + "\n\n" + complexPhantom
	vetMemberWith(t, goBin, pkg, src, further)

	section, resolve = byAtComplexSection(false)
	src = emitMember(t, env, EmitOptions{FuncName: "BuildByWitnessOutOfScope", ResolveExternalLeaf: resolve}, section).Source
	if strings.Contains(src, "TermAs[") {
		t.Errorf("a witness text was emitted at a phantom the family does not have in scope\n--- source: ---\n%s", src)
	}
	if !strings.Contains(src, `At("HOLDS_EVERYWHERE", a.Term("g(c)"))`) {
		t.Errorf("the witness is not rendered as its untyped text\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, ".Apply(") {
		t.Errorf("the witness is a Go expression where its text reads back\n--- source: ---\n%s", src)
	}
}

// citeAtSection is a cite of the named `∀x. R(x)` grounded at witness:
// the `lemma_preserve + known_thm + specialize` triple one fused
// `Cite(dep, w)` renders.
func citeAtSection(witnessType core.HolType) (*proof.DetailedProofProto, func(core.PropKey) (ExternalLeaf, bool)) {
	x := ext.Var("x", witnessType)
	c := ext.Var("c", witnessType)
	g := ext.WrapTerm(ext.Var("g", core.MakeFun(witnessType, witnessType)))
	R := ext.WrapTerm(ext.Var("R", core.MakeFun(witnessType, core.TypeBool())))
	G := ext.Var("G", core.TypeBool())
	witness := g.Apply(c)

	all := ext.ForAll(x)(R.Apply(x)).Core()
	lemma := prop.MakeProp(all)
	goal := prop.MakeProp(G.Core())
	installed := prop.MakeProp(G.Core(), all)
	ground := prop.MakeProp(G.Core(), R.Apply(witness).Core())

	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(lemma), pb.PropRef(installed)},
			Step:     &proof.StepProto_LemmaPreserve{LemmaPreserve: pb.PropRef(lemma)},
		},
		{Goal: pb.PropRef(lemma), Step: &proof.StepProto_KnownThm{KnownThm: &proof.KnownThmProto{StrongerGoal: pb.PropRef(lemma)}}},
		{
			Goal:     pb.PropRef(installed),
			SubGoals: []*ext.HolPropProto{pb.PropRef(ground)},
			Step: &proof.StepProto_Specialize{Specialize: &proof.SpecializeProto{
				Hyps: []*proof.SpecializeProto_Hyp{{HypIndex: 0, Witnesses: []uint32{pb.TermRef(witness.Core())}}},
			}},
		},
		{Goal: pb.PropRef(ground), Step: &proof.StepProto_TrivialSimplify{}},
	}
	normalized, _ := proof.Normalize(lemma)
	resolve := func(key core.PropKey) (ExternalLeaf, bool) {
		if key == lemma.AlphaKey() || key == normalized.AlphaKey() {
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "HOLDS_EVERYWHERE"}, true
		}
		return ExternalLeaf{}, false
	}
	return detailed(pb, steps...), resolve
}

// TestEmit_FusedCiteWitnessIsItsText: the witness of a fused
// `Cite(dep, w)` is written as its text too. The variables the text
// mentions are registered for the parse and bound to no local — the
// grounding's witnesses are marked where they are printed, so a member
// whose witness is a text compiles.
//
// A type letter beyond E is spelled where the member's family declares
// its phantom, a letter some registered statement of the family binds
// (typedgen.LettersInScope). A witness whose type no phantom of its
// family spells — a letter the family declares none for — has no
// `TermAs` to be typed by, and is the text `Term` reads, its variables
// registered and bound to no local as a typed text's are.
func TestEmit_FusedCiteWitnessIsItsText(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}
	env := makeTestEnv(t)
	section, resolve := citeAtSection(core.TypeA())

	const pkg = "citewitnesstextemit"
	entry, entries := landedEntry(pkg, "HOLDS_EVERYWHERE", "HoldsEverywhere")
	src := emitMember(t, env, EmitOptions{
		Family:              "tmp/" + pkg,
		FuncName:            "Build_CiteWitnessText",
		ResolveExternalLeaf: resolve,
		FamilyDepEntry:      entry,
	}, section).Source
	if !strings.Contains(src, `Cite(HoldsEverywhere, a.TermAs[A]("g(c)")),`) {
		t.Errorf("the fused cite's witness is not rendered as its typed text\n--- source: ---\n%s", src)
	}
	for _, name := range []string{"c", "g"} {
		if !strings.Contains(src, `ctx.Var("`+name+`", `) {
			t.Errorf("the variable %s the text mentions is not registered\n--- source: ---\n%s", name, src)
		}
		if strings.Contains(src, name+` := ctx.Var(`) {
			t.Errorf("the variable %s is bound to a local nothing reads\n--- source: ---\n%s", name, src)
		}
	}
	vetMemberWith(t, goBin, pkg, src, entries)

	// A family one of whose statements binds the letter I: its
	// generated file declares the phantom.
	letters := registry.NewFamily("zz_emit_family_letter", nil)
	letters.Add(registry.ProofEntry{
		Name:  "Indexed",
		Build: registry.BuildSpec{Headline: "∀x:I. x = x", Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
	})
	section, resolve = citeAtSection(core.MakeVarType("I"))
	src = emitMember(t, env, EmitOptions{
		Family:              letters.Name,
		FuncName:            "BuildCiteWitnessFamilyLetter",
		ResolveExternalLeaf: resolve,
	}, section).Source
	if !strings.Contains(src, `Cite("HOLDS_EVERYWHERE", a.TermAs[I]("g(c)")),`) {
		t.Errorf("the witness at the family's letter I is not rendered as its typed text\n--- source: ---\n%s", src)
	}

	for _, unspelled := range []struct{ letter, family string }{
		{"F", ""},           // library/authoring's F is the false term
		{"G", letters.Name}, // no statement of the family binds G
	} {
		section, resolve = citeAtSection(core.MakeVarType(unspelled.letter))
		src = emitMember(t, env, EmitOptions{
			Family:              unspelled.family,
			FuncName:            "BuildCiteWitnessGo",
			ResolveExternalLeaf: resolve,
		}, section).Source
		if !strings.Contains(src, `Cite("HOLDS_EVERYWHERE", a.Term("g(c)")),`) {
			t.Errorf("%s in %q: the witness is not rendered as its untyped text\n--- source: ---\n%s", unspelled.letter, unspelled.family, src)
		}
		if strings.Contains(src, "TermAs[") {
			t.Errorf("%s in %q: a witness of a type no phantom spells was emitted as a typed text\n--- source: ---\n%s", unspelled.letter, unspelled.family, src)
		}
		for _, name := range []string{"c", "g"} {
			if !strings.Contains(src, `ctx.Var("`+name+`", `) || strings.Contains(src, name+` := ctx.Var(`) {
				t.Errorf("%s in %q: the variable %s the text mentions is not registered and unbound\n--- source: ---\n%s", unspelled.letter, unspelled.family, name, src)
			}
		}
	}
}

// TestEmit_InstanceCaseWithAWitnessTextTakesItsClosure: a Case of the
// Instance door is an argument of the entry literal, with no Argument
// in scope. A branch whose step writes a witness as a text — parsed by
// an Argument — and needs neither the Script nor a declaration still
// takes the closure that binds one, and the member type-checks. The
// witness is a num: an instance statement binds nothing, so the only
// phantoms its family is sure to have are the ones every proof file
// has, library/authoring's.
func TestEmit_InstanceCaseWithAWitnessTextTakesItsClosure(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}
	f := newInstanceFixture(t)
	countMeta, _ := f.env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("zz_count", core.MakeFun(TypeInd, dsl.NumType)))
	counted := ext.Const(countMeta, core.MakeFun(TypeInd, dsl.NumType)).Apply(f.point)
	vocabulary := f.vocabulary()
	vocabulary.Consts["zz_count"] = true

	atMeta, _ := f.env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("zz_at", core.MakeFun(dsl.NumType, core.TypeBool())))
	n := ext.Var("n", dsl.NumType)
	everywhere := prop.MakeProp(ext.ForAll(n)(ext.Const(atMeta, core.MakeFun(dsl.NumType, core.TypeBool())).Apply(n)).Core())
	first, second, _ := f.conjuncts()
	statement := prop.MakeProp(f.triple.Apply(f.point).Core())
	unfolded := prop.MakeProp(ext.WrapTerm(first.Conclusion()).And(second.Conclusion()).Core())

	pb := ext.NewPoolBuilder()
	claimRef := pb.PropRef(everywhere)
	section := detailed(pb,
		&proof.StepProto{
			Goal:     pb.PropRef(statement),
			SubGoals: []*ext.HolPropProto{pb.PropRef(unfolded)},
			Step:     &proof.StepProto_DefExpand{DefExpand: pb.TermRef(f.triple)},
		},
		&proof.StepProto{
			Goal:     pb.PropRef(unfolded),
			SubGoals: []*ext.HolPropProto{pb.PropRef(first), pb.PropRef(second)},
			Step:     &proof.StepProto_SplitConj{},
		},
		&proof.StepProto{
			Goal:     pb.PropRef(first),
			SubGoals: []*ext.HolPropProto{claimRef},
			Step: &proof.StepProto_By{By: &proof.ByProto{
				Premises: []*proof.ByPremiseProto{{Install: claimRef, Witnesses: []uint32{pb.TermRef(counted.Core())}}},
			}},
		},
		&proof.StepProto{Goal: claimRef, Step: &proof.StepProto_KnownThm{KnownThm: &proof.KnownThmProto{StrongerGoal: claimRef}}},
		&proof.StepProto{Goal: pb.PropRef(second), Step: &proof.StepProto_TrivialSimplify{}},
	)
	normalized, _ := proof.Normalize(everywhere)
	resolve := func(key core.PropKey) (ExternalLeaf, bool) {
		if key == everywhere.AlphaKey() || key == normalized.AlphaKey() {
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "HOLDS_EVERYWHERE"}, true
		}
		return ExternalLeaf{}, false
	}

	const pkg = "instancewitnesstextemit"
	entry, entries := landedEntry(pkg, "HOLDS_EVERYWHERE", "HoldsEverywhere")
	src := emitMember(t, f.env, EmitOptions{
		Family:              "tmp/" + pkg,
		FuncName:            "Build_PairAtThePoint",
		EntryKey:            "prop_pair_at_the_point",
		Structure:           equivalenceStructure,
		FamilyVocab:         vocabulary,
		ResolveExternalLeaf: resolve,
		FamilyDepEntry:      entry,
	}, section).Source
	want := "\t\t\tDerive(func(a *Argument) {\n" +
		"\t\t\t\ta.Do(\n" +
		"\t\t\t\t\tBy(At(HoldsEverywhere, a.TermAs[Nat](\"zz_count(zz_point)\"))),\n" +
		"\t\t\t\t)\n" +
		"\t\t\t}),\n"
	if !strings.Contains(src, want) {
		t.Errorf("the Case whose witness is a text lacks the closure that binds its Argument:\n%s\n--- source: ---\n%s", want, src)
	}
	if !strings.Contains(src, "family.Instance(") {
		t.Fatalf("fixture defeated: the member is not rendered through the Instance door\n--- source: ---\n%s", src)
	}
	vetMemberWith(t, goBin, pkg, src, entries)
}
