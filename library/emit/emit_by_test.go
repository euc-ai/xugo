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

// TestEmit_ByStep guards the emit branch for the `by` composite
// ministep: a ByProto must render as the math layer's By(...) call —
// shaping values first, then the premises (named → cite-target expr,
// wrapped in At(...) when witnessed; resident → the Fact parameter that
// binds it, here the statement's premise the record strips) —
// and the node's CLAIM CHILDREN must not render at all (they are
// implied by the premise list; the replayed By certifies them itself).
// emit only renders; it does not replay, so the synthetic goal need not
// be By-provable.
func TestEmit_ByStep(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	f := ext.WrapTerm(ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA())))
	g := ext.WrapTerm(ext.Var("g", core.MakeFun(core.TypeA(), core.TypeA())))
	P := ext.WrapTerm(ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool())))
	a := ext.Var("a", core.TypeA())

	lemma := prop.MakeProp(ext.ForAll(x)(f.Apply(x).Eq(g.Apply(x))).Core())
	hyp := P.Apply(g.Apply(a)).Core()

	pb := ext.NewPoolBuilder()
	goalProp := prop.MakeProp(P.Apply(f.Apply(a)).Core(), hyp)
	goal := pb.PropRef(goalProp)
	claimRef := pb.PropRef(lemma)

	byStep := &proof.StepProto{
		Goal:     goal,
		SubGoals: []*ext.HolPropProto{claimRef},
		Step: &proof.StepProto_By{
			By: &proof.ByProto{
				Premises: []*proof.ByPremiseProto{
					{Install: pb.PropRef(prop.MakeProp(hyp)), Resident: true},
					{Install: claimRef, Witnesses: []uint32{pb.TermRef(a)}},
				},
				Shape: &proof.ByShapeProto{},
			},
		},
	}
	// The claim child (⊢ lemma), closed by known_thm at record time —
	// must be swallowed by the By rendering, not rendered as a Cite.
	claimStep := &proof.StepProto{
		Goal: claimRef,
		Step: &proof.StepProto_KnownThm{
			KnownThm: &proof.KnownThmProto{StrongerGoal: claimRef},
		},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildBy"}, detailed(pb, byStep, claimStep)).Source
	if !strings.Contains(src, "By(\n\t\t\t\t\tNormalized,\n\t\t\t\t\th,\n") {
		t.Errorf("By ministep did not render shape+resident premise\n--- source: ---\n%s", src)
	}
	if !strings.Contains(src, "At(") {
		t.Errorf("witnessed named premise did not render as At(...)\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "unhandled ministep") {
		t.Errorf("ministep fell through to unhandled placeholder\n--- source: ---\n%s", src)
	}
	// The claim child must be swallowed: no separate Cite/UseLemma line
	// for the premise statement beyond the By expression itself.
	if strings.Contains(src, "CiteKnown(") || strings.Contains(src, "UseThm(") {
		t.Errorf("claim child rendered separately — it must be implied by the premise list\n--- source: ---\n%s", src)
	}
}

// TestEmit_ByCompiles is the go-vet gate for the By rendering: the
// emitted member must TYPE-CHECK against the bare-name surface
// (library/authoring), not merely parse — this is what catches a
// By-family name missing from the surface
// (By/ByArith/At/ResidentHyp/Where/Broadcast + the shaping values),
// which a parse-only test cannot see.
func TestEmit_ByCompiles(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	f := ext.WrapTerm(ext.Var("f", core.MakeFun(core.TypeA(), core.TypeBool())))
	P := ext.WrapTerm(ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool())))
	a := ext.Var("a", core.TypeA())

	lemma := prop.MakeProp(ext.ForAll(x)(f.Apply(x)).Core())
	hyp := P.Apply(a).Core()

	pb := ext.NewPoolBuilder()
	goalProp := prop.MakeProp(f.Apply(a).Core(), hyp)
	claimRef := pb.PropRef(lemma)
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goalProp),
			SubGoals: []*ext.HolPropProto{claimRef},
			Step: &proof.StepProto_By{By: &proof.ByProto{
				Premises: []*proof.ByPremiseProto{
					{Install: pb.PropRef(prop.MakeProp(hyp)), Resident: true},
					{Install: claimRef, Witnesses: []uint32{pb.TermRef(a)}},
					// A premise pinned by name renders as Where(…) — the
					// bare-name surface must carry the name for the member
					// to type-check (the gate this test exists for).
					{Install: claimRef, Named: []*proof.NamedWitnessProto{{Binder: "x", Term: pb.TermRef(a)}}},
				},
				Shape: &proof.ByShapeProto{},
			}},
		},
		{
			Goal: claimRef,
			Step: &proof.StepProto_KnownThm{
				KnownThm: &proof.KnownThmProto{StrongerGoal: claimRef},
			},
		},
	}

	const pkg = "bycompilesemit"
	src := emitMember(t, env, EmitOptions{
		Family:   "tmp/" + pkg,
		FuncName: "Build_ByCompiles",
	}, detailed(pb, steps...)).Source
	if !strings.Contains(src, "By(") {
		t.Fatalf("fixture defeated: no By call emitted\n--- source: ---\n%s", src)
	}
	vetMember(t, goBin, pkg, src)
}

// TestEmit_ByStepArith: the arith closer renders ByArith(...), not
// By(...) — the closer choice is the record, never re-decided.
func TestEmit_ByStepArith(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	P := ext.WrapTerm(ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool())))
	Q := ext.WrapTerm(ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool())))
	a := ext.Var("a", core.TypeA())
	hyp := P.Apply(a).Core()

	pb := ext.NewPoolBuilder()
	goal := pb.PropRef(prop.MakeProp(Q.Apply(a).Core(), hyp))

	byStep := &proof.StepProto{
		Goal: goal,
		Step: &proof.StepProto_By{
			By: &proof.ByProto{
				Premises: []*proof.ByPremiseProto{
					{Install: pb.PropRef(prop.MakeProp(hyp)), Resident: true},
				},
				Arith: true,
			},
		},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildByArith"}, detailed(pb, byStep)).Source
	if !strings.Contains(src, "ByArith(h)") {
		t.Errorf("arith closer did not render as ByArith\n--- source: ---\n%s", src)
	}
}

// TestEmit_ByStepSettac: the settac closer renders BySets(...), not
// By(...) — the closer choice is the record, never re-decided. Bare
// form: a premise-free BySets is legal for this closer (the driver's
// vocabulary unfolding is its content), so the render has no arguments.
func TestEmit_ByStepSettac(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	P := ext.WrapTerm(ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool())))
	a := ext.Var("a", core.TypeA())

	pb := ext.NewPoolBuilder()
	goal := pb.PropRef(prop.MakeProp(P.Apply(a).Core()))

	byStep := &proof.StepProto{
		Goal: goal,
		Step: &proof.StepProto_By{
			By: &proof.ByProto{
				Settac: true,
			},
		},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildBySets"}, detailed(pb, byStep)).Source
	if !strings.Contains(src, "BySets()") {
		t.Errorf("settac closer did not render as BySets\n--- source: ---\n%s", src)
	}
}

// TestEmit_ByStepChase: the chase closer renders ByChase(Depth(k), …),
// the depth first — the closer and its parameter are the record, never
// re-decided.
func TestEmit_ByStepChase(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	P := ext.WrapTerm(ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool())))
	a := ext.Var("a", core.TypeA())

	pb := ext.NewPoolBuilder()
	goal := pb.PropRef(prop.MakeProp(P.Apply(a).Core()))

	byStep := &proof.StepProto{
		Goal: goal,
		Step: &proof.StepProto_By{
			By: &proof.ByProto{
				Chase:      true,
				ChaseDepth: 3,
			},
		},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildByChase"}, detailed(pb, byStep)).Source
	if !strings.Contains(src, "ByChase(Depth(3))") {
		t.Errorf("chase closer did not render as ByChase(Depth(3))\n--- source: ---\n%s", src)
	}
}

// TestEmit_ByWhereRenders — a premise pinned by name (ByPremiseProto.
// named, the session's sparse term_specialize / the macro's Where)
// renders as the Where chain, one link per binder in recorded order,
// and never as a positional At.
func TestEmit_ByWhereRenders(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	f := ext.WrapTerm(ext.Var("f", core.MakeFun(core.TypeA(), core.MakeFun(core.TypeA(), core.TypeBool()))))
	P := ext.WrapTerm(ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool())))
	a := ext.Var("a", core.TypeA())
	b := ext.Var("b", core.TypeA())

	lemma := prop.MakeProp(ext.ForAll(x)(ext.ForAll(y)(f.Apply(x, y))).Core())
	hyp := P.Apply(a).Core()
	pb := ext.NewPoolBuilder()
	goalProp := prop.MakeProp(f.Apply(a, b).Core(), hyp)
	claimRef := pb.PropRef(lemma)
	byStep := &proof.StepProto{
		Goal:     pb.PropRef(goalProp),
		SubGoals: []*ext.HolPropProto{claimRef},
		Step: &proof.StepProto_By{By: &proof.ByProto{
			Premises: []*proof.ByPremiseProto{
				{Install: pb.PropRef(prop.MakeProp(hyp)), Resident: true},
				{Install: claimRef, Named: []*proof.NamedWitnessProto{
					{Binder: "y", Term: pb.TermRef(b)},
					{Binder: "x", Term: pb.TermRef(a)},
				}},
			},
		}},
	}
	claimStep := &proof.StepProto{
		Goal: claimRef,
		Step: &proof.StepProto_KnownThm{KnownThm: &proof.KnownThmProto{StrongerGoal: claimRef}},
	}
	src := emitMember(t, env, EmitOptions{FuncName: "BuildByWhere"}, detailed(pb, byStep, claimStep)).Source
	// The chain's line runs past the width with its unresolved-lemma
	// comment, so the formatter lays the two calls out an argument to a
	// line.
	if !strings.Contains(unspaced(src), `"y",b).Where("x",a_2)`) {
		t.Errorf("named premise did not render as the Where chain in recorded order\n--- source: ---\n%s", src)
	}
	if !strings.Contains(src, "Where(") {
		t.Errorf("named premise did not render as Where(...)\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "At(") {
		t.Errorf("a named premise must not render a positional At\n--- source: ---\n%s", src)
	}
}

// A reading owns only its bare resident hypothesis. Authored premises
// beside it must survive the recorded-call reconstruction and its audit.
func TestAuthoredByPremisesKeepsOtherPremises(t *testing.T) {
	env := makeTestEnv(t)
	f := newHavePremiseFixture()
	pb := ext.NewPoolBuilder()
	under := f.resident(pb, f.q)
	other := f.resident(pb, f.everywhere)
	grounded := f.resident(pb, f.q, f.c)
	scaled := f.resident(pb, f.q)
	scaled.Scaled = true
	// The law `Q ⇒ C` read under the resident Q installs C.
	law := pb.PropRef(prop.MakeProp(ext.WrapTerm(f.q).Imply(f.goal).Core()))
	reading := &proof.ByPremiseProto{
		Install: pb.PropRef(prop.MakeProp(f.goal)),
		Reading: &proof.ReadingProto{Law: law, Under: under.Install},
	}
	r := ext.NewPoolReader(pb.Pool(), env.ProofService.LoadConstMeta)
	got := authoredByPremises(r, &proof.ByProto{Premises: []*proof.ByPremiseProto{reading, under, other, grounded, scaled}})
	want := []*proof.ByPremiseProto{reading, other, grounded, scaled}
	if len(got) != len(want) {
		t.Fatalf("got %d premises, want %d", len(got), len(want))
	}
	for i := range want {
		if got[i] != want[i] {
			t.Errorf("premise %d was replaced or dropped", i)
		}
	}
}

// TestAuthoredByPremisesKeepsALooseCitesHypothesis: a law cited as
// itself beside the hypothesis it was read under — its install the
// law's own statement, the reading on it the record of that reading —
// keeps the resident premise for the hypothesis: the executor keeps
// nothing beside a law cited as itself.
func TestAuthoredByPremisesKeepsALooseCitesHypothesis(t *testing.T) {
	env := makeTestEnv(t)
	f := newHavePremiseFixture()
	pb := ext.NewPoolBuilder()
	under := f.resident(pb, f.q)
	other := f.resident(pb, f.everywhere)
	law := pb.PropRef(prop.MakeProp(ext.WrapTerm(f.q).Imply(f.goal).Core()))
	cited := &proof.ByPremiseProto{
		Install: law,
		Reading: &proof.ReadingProto{Law: law, Under: under.Install},
	}
	r := ext.NewPoolReader(pb.Pool(), env.ProofService.LoadConstMeta)
	if !readingCitedLoose(r, cited) {
		t.Fatal("a law installed as itself under a hypothesis is a loose cite")
	}
	got := authoredByPremises(r, &proof.ByProto{Premises: []*proof.ByPremiseProto{cited, under, other}})
	want := []*proof.ByPremiseProto{cited, under, other}
	if len(got) != len(want) {
		t.Fatalf("got %d premises, want %d", len(got), len(want))
	}
	for i := range want {
		if got[i] != want[i] {
			t.Errorf("premise %d was replaced or dropped", i)
		}
	}
}

// Scaled coefficients are Go expressions even when their symbols occur
// elsewhere only inside mathematical text, or only in the coefficient.
// A symbol of the goal is a variable of the proof, declared `ctx.Var`;
// one that occurs in the coefficient alone is built by `Var`, which
// registers no name in the script's scope.
func TestEmit_ScaledCoefficientSymbols(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}
	for _, only := range []bool{false, true} {
		name := "scaledregistered"
		if only {
			name = "scaledonly"
		}
		t.Run(name, func(t *testing.T) {
			env := makeTestEnv(t)
			coefficient := ext.Var("coefficient", core.TypeA())
			point := coefficient
			term := coefficient.Core()
			names := []string{"coefficient"}
			if only {
				point = ext.Var("point", core.TypeA())
				scale := ext.WrapTerm(ext.Var("scale", core.MakeFun(core.TypeA(), core.TypeA())))
				term = scale.Apply(coefficient).Core()
				names = append(names, "scale")
			}
			P := ext.WrapTerm(ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool())))
			Q := ext.WrapTerm(ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool())))
			hyp := P.Apply(point).Core()
			pb := ext.NewPoolBuilder()
			step := &proof.StepProto{
				Goal: pb.PropRef(prop.MakeProp(Q.Apply(point).Core(), hyp)),
				Step: &proof.StepProto_By{By: &proof.ByProto{
					Arith: true,
					Premises: []*proof.ByPremiseProto{{
						Install: pb.PropRef(prop.MakeProp(hyp)), Resident: true,
						Scaled: true, Coefficient: pb.TermRef(term),
					}},
				}},
			}
			src := emitMember(t, env, EmitOptions{
				Family: "tmp/" + name, FuncName: "Build_ScaledSymbols",
			}, detailed(pb, step)).Source
			declare := "ctx.Var"
			if only {
				declare = "Var"
			}
			for _, symbol := range names {
				if !strings.Contains(src, symbol+` := `+declare+`("`+symbol+`"`) {
					t.Errorf("coefficient symbol %s has no Go binding by %s\n%s", symbol, declare, src)
				}
			}
			vetMember(t, goBin, name, src)
		})
	}
}
