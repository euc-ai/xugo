package emit

// Tests for the Instance door's rendering (emitter.instanceDoor): a
// single-section member stating a structure's predicate, proved by the
// predicate unfolded and one branch per conjunct of its definition,
// renders as family.Instance with one Case per conjunct.

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

// instanceFixture is a predicate `zz_triple` over a point, the
// conjunction it unfolds to — `(zz_first(c) ∧ zz_second(c)) ∧
// zz_third(c)` — and the constants they are stated in.
type instanceFixture struct {
	env                          *proof.ProverEnv
	triple, first, second, third *ext.TermWrapper
	point                        *ext.TermWrapper
}

func newInstanceFixture(t *testing.T) instanceFixture {
	env := makeTestEnv(t)
	constant := func(name string, ty core.HolType) *ext.TermWrapper {
		meta, _ := env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta(core.TermName(name), ty))
		return ext.Const(meta, ty)
	}
	predicate := core.MakeFun(TypeInd, core.TypeBool())
	return instanceFixture{
		env:    env,
		triple: constant("zz_triple", predicate),
		first:  constant("zz_first", predicate),
		second: constant("zz_second", predicate),
		third:  constant("zz_third", predicate),
		point:  constant("zz_point", TypeInd),
	}
}

// vocabulary declares the fixture's constants as the family's, so that
// a body registers none of them and binds one only where a step names
// it as a Go value.
func (f instanceFixture) vocabulary() *FamilyVocab {
	return &FamilyVocab{Consts: map[string]bool{
		"zz_triple": true, "zz_first": true, "zz_second": true, "zz_third": true, "zz_point": true,
	}}
}

// conjuncts are the three goals the definition's conjunction splits to.
func (f instanceFixture) conjuncts() (first, second, third core.Prop) {
	return prop.MakeProp(f.first.Apply(f.point).Core()),
		prop.MakeProp(f.second.Apply(f.point).Core()),
		prop.MakeProp(f.third.Apply(f.point).Core())
}

// section is the instance `zz_triple(zz_point)` proved as the door
// proves it: the predicate unfolded, the conjunction split by two
// binary steps, and the three branches closed —
//
//   - the first by one step that needs nothing;
//   - the second by a witness, a Go value the body must bind;
//   - the third by two asserted facts and a close, a deduction.
func (f instanceFixture) section() *proof.DetailedProofProto {
	first, second, third := f.conjuncts()
	statement := prop.MakeProp(f.triple.Apply(f.point).Core())
	firstTwo := prop.MakeProp(ext.WrapTerm(first.Conclusion()).And(second.Conclusion()).Core())
	unfolded := prop.MakeProp(ext.WrapTerm(firstTwo.Conclusion()).And(third.Conclusion()).Core())
	afterFirst := prop.MakeProp(third.Conclusion(), first.Conclusion())
	afterSecond := prop.MakeProp(third.Conclusion(), first.Conclusion(), second.Conclusion())
	secondAfterFirst := prop.MakeProp(second.Conclusion(), first.Conclusion())

	pb := ext.NewPoolBuilder()
	return detailed(pb,
		&proof.StepProto{
			Goal:     pb.PropRef(statement),
			SubGoals: []*ext.HolPropProto{pb.PropRef(unfolded)},
			Step:     &proof.StepProto_DefExpand{DefExpand: pb.TermRef(f.triple)},
		},
		&proof.StepProto{
			Goal:     pb.PropRef(unfolded),
			SubGoals: []*ext.HolPropProto{pb.PropRef(firstTwo), pb.PropRef(third)},
			Step:     &proof.StepProto_SplitConj{},
		},
		&proof.StepProto{
			Goal:     pb.PropRef(firstTwo),
			SubGoals: []*ext.HolPropProto{pb.PropRef(first), pb.PropRef(second)},
			Step:     &proof.StepProto_SplitConj{},
		},
		&proof.StepProto{Goal: pb.PropRef(first), Step: &proof.StepProto_TrivialSimplify{}},
		&proof.StepProto{
			Goal:     pb.PropRef(second),
			SubGoals: []*ext.HolPropProto{pb.PropRef(second)},
			Step:     &proof.StepProto_Witness{Witness: pb.TermRef(f.point)},
		},
		&proof.StepProto{Goal: pb.PropRef(second), Step: &proof.StepProto_TrivialSimplify{}},
		&proof.StepProto{
			Goal:     pb.PropRef(third),
			SubGoals: []*ext.HolPropProto{pb.PropRef(first), pb.PropRef(afterFirst)},
			Step:     &proof.StepProto_Assert{Assert: pb.PropRef(first)},
		},
		&proof.StepProto{Goal: pb.PropRef(first), Step: &proof.StepProto_TrivialSimplify{}},
		&proof.StepProto{
			Goal:     pb.PropRef(afterFirst),
			SubGoals: []*ext.HolPropProto{pb.PropRef(secondAfterFirst), pb.PropRef(afterSecond)},
			Step:     &proof.StepProto_Assert{Assert: pb.PropRef(second)},
		},
		&proof.StepProto{Goal: pb.PropRef(secondAfterFirst), Step: &proof.StepProto_TrivialSimplify{}},
		&proof.StepProto{Goal: pb.PropRef(afterSecond), Step: &proof.StepProto_CnfRefute{}},
	)
}

// equivalenceStructure resolves the fixture's predicate to a structure
// var the corpus declares, so the rendered member type-checks.
func equivalenceStructure(predicate string) (FamilyDepRef, bool) {
	if predicate != "zz_triple" {
		return FamilyDepRef{}, false
	}
	return FamilyDepRef{
		Expr:       "equivalence.Equivalence",
		ImportPath: "github.com/euc-ai/xugo/library/proofs/relations/equivalence",
	}, true
}

// TestEmit_InstanceDoor: the instance renders as one family.Instance
// call — the structure, the statement, one Case per conjunct in the
// definition's order, the two binary splits flattened — and a Case
// carries a closure of its own exactly where its steps need the Script
// or an Argument.
func TestEmit_InstanceDoor(t *testing.T) {
	defer goleak.VerifyNone(t)
	f := newInstanceFixture(t)

	const pkg = "instancedooremit"
	res := emitMember(t, f.env, EmitOptions{
		Family:      "tmp/" + pkg,
		FuncName:    "Build_TripleAtThePoint",
		EntryKey:    "prop_triple_at_the_point",
		Structure:   equivalenceStructure,
		FamilyVocab: f.vocabulary(),
	}, f.section())
	src := res.Source
	assertFormatted(t, src)

	for _, want := range []string{
		`"github.com/euc-ai/xugo/library/proofs/relations/equivalence"`,
		"\tBuild: family.Instance(equivalence.Equivalence, \"zz_triple(zz_point)\",\n",
		// A branch that needs nothing renders its steps bare.
		"\t\tCase(\n" +
			"\t\t\t\"case_0: zz_first(zz_point)\",\n" +
			"\t\t\t// context:\n" +
			"\t\t\t//   concl: zz_first(zz_point)\n" +
			"\t\t\tTrivialSimplify(),\n" +
			"\t\t),\n",
		// A branch naming a Go value binds it in its own closure.
		"\t\tCase(\n" +
			"\t\t\t\"case_1: zz_second(zz_point)\",\n" +
			"\t\t\t// context:\n" +
			"\t\t\t//   concl: zz_second(zz_point)\n" +
			"\t\t\tDerive(func(a *Argument) {\n" +
			"\t\t\t\tctx := a.Ctx()\n" +
			"\t\t\t\t// === Constants ===\n" +
			"\t\t\t\tzz_point := ctx.Const(\"zz_point\", MakeType(\"ind\"))\n" +
			"\n" +
			"\t\t\t\ta.Do(\n" +
			"\t\t\t\t\tWitness(zz_point),\n" +
			"\t\t\t\t\tTrivialSimplify(),\n" +
			"\t\t\t\t)\n" +
			"\t\t\t}),\n" +
			"\t\t),\n",
		// A deduction states its facts on the closure's own Argument.
		"\t\tCase(\n" +
			"\t\t\t\"case_2: zz_third(zz_point)\",\n" +
			"\t\t\t// context:\n" +
			"\t\t\t//   concl: zz_third(zz_point)\n" +
			"\t\t\tDerive(func(a *Argument) {\n" +
			"\t\t\t\ta.Have(\n" +
			"\t\t\t\t\t\"zz_first(zz_point)\",\n" +
			"\t\t\t\t\t\"zz_first(zz_point)\",\n",
		"\t\t\t\ta.Show(\n" +
			"\t\t\t\t\t\"zz_third(zz_point)\",\n" +
			"\t\t\t\t\tCnfRefute(),\n" +
			"\t\t\t\t)\n" +
			"\t\t\t}),\n" +
			"\t\t),\n" +
			"\t),\n" +
			"})\n",
	} {
		if !strings.Contains(src, want) {
			t.Errorf("instance output lacks\n%s\n--- source: ---\n%s", want, src)
		}
	}
	// The door unfolds the predicate and splits the conjunction itself;
	// the value one Case binds is bound in no other.
	for _, banned := range []string{"family.Theorem(", "SplitConj", `Unfold("zz_triple")`} {
		if strings.Contains(src, banned) {
			t.Errorf("instance output still renders %q\n--- source: ---\n%s", banned, src)
		}
	}
	if got := strings.Count(src, `ctx.Const("zz_point"`); got != 1 {
		t.Errorf("zz_point is bound in %d Cases, want the one that names it\n--- source: ---\n%s", got, src)
	}

	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}
	vetMember(t, goBin, pkg, src)
}

// TestEmit_InstanceDoorIsForTheDoorsOwnProof: a member the door cannot
// state, or whose recorded proof is not the door's own, stays a
// family.Theorem.
func TestEmit_InstanceDoorIsForTheDoorsOwnProof(t *testing.T) {
	defer goleak.VerifyNone(t)
	f := newInstanceFixture(t)
	first, second, third := f.conjuncts()
	statement := prop.MakeProp(f.triple.Apply(f.point).Core())
	firstTwo := prop.MakeProp(ext.WrapTerm(first.Conclusion()).And(second.Conclusion()).Core())
	unfolded := prop.MakeProp(ext.WrapTerm(firstTwo.Conclusion()).And(third.Conclusion()).Core())
	x := ext.Var("x", TypeInd)
	H := ext.Var("H", core.TypeBool())

	// split closes the definition's conjunction over hyps, two
	// conjuncts in one branch when pairClosed.
	split := func(pb *ext.PoolBuilder, hyps []core.Term, pairClosed bool) []*proof.StepProto {
		over := func(p core.Prop) *ext.HolPropProto { return pb.PropRef(prop.MakeProp(p.Conclusion(), hyps...)) }
		steps := []*proof.StepProto{{
			Goal:     over(unfolded),
			SubGoals: []*ext.HolPropProto{over(firstTwo), over(third)},
			Step:     &proof.StepProto_SplitConj{},
		}}
		if pairClosed {
			steps = append(steps, &proof.StepProto{Goal: over(firstTwo), Step: &proof.StepProto_TrivialSimplify{}})
		} else {
			steps = append(steps,
				&proof.StepProto{
					Goal:     over(firstTwo),
					SubGoals: []*ext.HolPropProto{over(first), over(second)},
					Step:     &proof.StepProto_SplitConj{},
				},
				&proof.StepProto{Goal: over(first), Step: &proof.StepProto_TrivialSimplify{}},
				&proof.StepProto{Goal: over(second), Step: &proof.StepProto_TrivialSimplify{}})
		}
		return append(steps, &proof.StepProto{Goal: over(third), Step: &proof.StepProto_TrivialSimplify{}})
	}
	unfoldThenSplit := func(pb *ext.PoolBuilder, hyps []core.Term, pairClosed bool) []*proof.StepProto {
		return append([]*proof.StepProto{{
			Goal:     pb.PropRef(prop.MakeProp(statement.Conclusion(), hyps...)),
			SubGoals: []*ext.HolPropProto{pb.PropRef(prop.MakeProp(unfolded.Conclusion(), hyps...))},
			Step:     &proof.StepProto_DefExpand{DefExpand: pb.TermRef(f.triple)},
		}}, split(pb, hyps, pairClosed)...)
	}

	for _, tc := range []struct {
		name      string
		structure func(string) (FamilyDepRef, bool)
		steps     func(pb *ext.PoolBuilder) []*proof.StepProto
	}{
		{"the door's own proof (control)", equivalenceStructure,
			func(pb *ext.PoolBuilder) []*proof.StepProto { return unfoldThenSplit(pb, nil, false) }},
		{"a predicate no chapter made a structure", func(string) (FamilyDepRef, bool) { return FamilyDepRef{}, false },
			func(pb *ext.PoolBuilder) []*proof.StepProto { return unfoldThenSplit(pb, nil, false) }},
		{"no structure resolver", nil,
			func(pb *ext.PoolBuilder) []*proof.StepProto { return unfoldThenSplit(pb, nil, false) }},
		{"an instance under a hypothesis", equivalenceStructure,
			func(pb *ext.PoolBuilder) []*proof.StepProto { return unfoldThenSplit(pb, []core.Term{H.Core()}, false) }},
		{"two conjuncts closed in one branch", equivalenceStructure,
			func(pb *ext.PoolBuilder) []*proof.StepProto { return unfoldThenSplit(pb, nil, true) }},
		{"an instance under a ∀-prefix", equivalenceStructure,
			func(pb *ext.PoolBuilder) []*proof.StepProto {
				parametric := prop.MakeProp(ext.ForAll(x)(f.triple.Apply(x)).Core())
				at := prop.MakeProp(f.triple.Apply(x).Core())
				return []*proof.StepProto{
					{Goal: pb.PropRef(parametric), SubGoals: []*ext.HolPropProto{pb.PropRef(at)}, Step: &proof.StepProto_StripQuant{}},
					{Goal: pb.PropRef(at), Step: &proof.StepProto_TrivialSimplify{}},
				}
			}},
		{"a step before the unfold", equivalenceStructure,
			func(pb *ext.PoolBuilder) []*proof.StepProto {
				return append([]*proof.StepProto{{
					Goal:     pb.PropRef(statement),
					SubGoals: []*ext.HolPropProto{pb.PropRef(statement)},
					Step:     &proof.StepProto_ByContra{},
				}}, unfoldThenSplit(pb, nil, false)...)
			}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			pb := ext.NewPoolBuilder()
			src := emitMember(t, f.env, EmitOptions{
				FuncName:    "Build_TripleAtThePoint",
				Structure:   tc.structure,
				FamilyVocab: f.vocabulary(),
			}, detailed(pb, tc.steps(pb)...)).Source
			door := strings.Contains(src, "family.Instance(")
			if control := tc.name == "the door's own proof (control)"; door != control {
				t.Errorf("rendered through the Instance door: %v, want %v\n--- source: ---\n%s", door, control, src)
			}
			if !door && !strings.Contains(src, "family.Theorem(") {
				t.Errorf("neither door rendered the member\n--- source: ---\n%s", src)
			}
		})
	}
}
