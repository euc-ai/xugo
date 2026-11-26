package emit

import (
	"os/exec"
	"regexp"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"google.golang.org/protobuf/types/known/emptypb"
)

// havePremiseFixture is the vocabulary of the Have-premise fixtures:
// the first Have states `∀x. F(x)`, the second `Q`, and the goal is
// `C`. A later `by` cites the first at the witness `c` and the second
// as it stands.
type havePremiseFixture struct {
	everywhere, q, c core.Term
	goal             core.Term
}

func newHavePremiseFixture() havePremiseFixture {
	x := ext.Var("x", core.TypeA())
	F := ext.WrapTerm(ext.Var("F", core.MakeFun(core.TypeA(), core.TypeBool())))
	return havePremiseFixture{
		everywhere: ext.ForAll(x)(F.Apply(x)).Core(),
		q:          ext.Var("Q", core.TypeBool()).Core(),
		c:          ext.Var("c", core.TypeA()).Core(),
		goal:       ext.Var("C", core.TypeBool()).Core(),
	}
}

// resident is a `by` premise naming the resident hypothesis h, grounded
// at the witnesses.
func (f havePremiseFixture) resident(pb *ext.PoolBuilder, h core.Term, witnesses ...core.Term) *proof.ByPremiseProto {
	p := &proof.ByPremiseProto{Install: pb.PropRef(prop.MakeProp(h)), Resident: true}
	for _, w := range witnesses {
		p.Witnesses = append(p.Witnesses, pb.TermRef(w))
	}
	return p
}

func byStep(goal *ext.HolPropProto, premises ...*proof.ByPremiseProto) *proof.StepProto {
	return &proof.StepProto{Goal: goal, Step: &proof.StepProto_By{By: &proof.ByProto{Premises: premises}}}
}

// staircase is the two-Have chain over goal — each claim branch
// carrying the hypotheses resident at its Have — whose second Have is
// proved by secondProof and whose continuation is closed by the tail
// steps. underBoth is the continuation's goal, both facts resident.
func (f havePremiseFixture) staircase(pb *ext.PoolBuilder, goal core.Term, hyps []core.Term,
	secondProof func(claimGoal *ext.HolPropProto) *proof.StepProto,
	tail func(underBoth *ext.HolPropProto) []*proof.StepProto) []*proof.StepProto {
	with := func(concl core.Term, more ...core.Term) *ext.HolPropProto {
		return pb.PropRef(prop.MakeProp(concl, append(append([]core.Term{}, hyps...), more...)...))
	}
	firstClaim := pb.PropRef(prop.MakeProp(f.everywhere))
	secondClaim := pb.PropRef(prop.MakeProp(f.q))
	steps := []*proof.StepProto{
		{
			Goal:     with(goal),
			SubGoals: []*ext.HolPropProto{with(f.everywhere), with(goal, f.everywhere)},
			Step:     &proof.StepProto_Assert{Assert: firstClaim},
		},
		{Goal: with(f.everywhere), Step: &proof.StepProto_TrivialSimplify{}},
		{
			Goal:     with(goal, f.everywhere),
			SubGoals: []*ext.HolPropProto{with(f.q, f.everywhere), with(goal, f.everywhere, f.q)},
			Step:     &proof.StepProto_Assert{Assert: secondClaim},
		},
		secondProof(with(f.q, f.everywhere)),
	}
	return append(steps, tail(with(goal, f.everywhere, f.q))...)
}

// TestEmit_DeriveHavePremiseIsItsHandle: in a Have chain, a later `by`
// whose resident premise is the hypothesis an earlier Have stated
// renders the premise as that Have's Go name — `fact1`, `At(fact1, c)`
// where it is grounded — and not as the hypothesis's statement in a
// `ResidentHyp` text. The rendering is type-checked: a Have's Fact in
// a premise list, bare and under At, has to hold up under the type
// checker as it does under the parser.
func TestEmit_DeriveHavePremiseIsItsHandle(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}
	env := makeTestEnv(t)
	f := newHavePremiseFixture()

	pb := ext.NewPoolBuilder()
	steps := f.staircase(pb, f.goal, nil,
		func(claimGoal *ext.HolPropProto) *proof.StepProto {
			return byStep(claimGoal, f.resident(pb, f.everywhere, f.c))
		},
		func(underBoth *ext.HolPropProto) []*proof.StepProto {
			return []*proof.StepProto{byStep(underBoth, f.resident(pb, f.everywhere, f.c), f.resident(pb, f.q))}
		})

	const pkg = "havepremiseemit"
	src := emitMember(t, env, EmitOptions{Family: "tmp/" + pkg, FuncName: "Build_HavePremise"}, detailed(pb, steps...)).Source
	if !strings.Contains(src, "fact1 := a.Have(") || !strings.Contains(src, "fact2 := a.Have(") {
		t.Errorf("a Have a later premise cites is not bound\n--- source: ---\n%s", src)
	}
	if !strings.Contains(src, "By(At(fact1, c)),") {
		t.Errorf("the second Have's proof does not cite the first at its witness by its handle\n--- source: ---\n%s", src)
	}
	if !strings.Contains(src, "By(At(fact1, c), fact2),") {
		t.Errorf("the Show does not cite the two Haves by their handles\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "ResidentHyp(") {
		t.Errorf("a premise a Have states still renders as the hypothesis's text\n--- source: ---\n%s", src)
	}
	vetMember(t, goBin, pkg, src)
}

// TestEmit_HaveStatedSimpClaimIsItsHandle: a later simp rule recorded
// as the claim a Have stated, with no hypotheses (a session's text rule
// spelling the Have), is a use of the Have — the driver discharges it
// against the hypothesis with no obligation child — and renders as the
// Have's handle beside a named rule that has one.
func TestEmit_HaveStatedSimpClaimIsItsHandle(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}
	env := makeTestEnv(t)
	f := newHavePremiseFixture()
	r := ext.Var("R", core.TypeBool()).Core()
	named := prop.MakeProp(ext.WrapTerm(f.goal).Eq(ext.WrapTerm(r)).Core())

	pb := ext.NewPoolBuilder()
	steps := f.staircase(pb, f.goal, nil,
		func(claimGoal *ext.HolPropProto) *proof.StepProto {
			return byStep(claimGoal, f.resident(pb, f.everywhere, f.c))
		},
		func(underBoth *ext.HolPropProto) []*proof.StepProto {
			residual := pb.PropRef(prop.MakeProp(r, f.everywhere, f.q))
			return []*proof.StepProto{
				{
					Goal:     underBoth,
					SubGoals: []*ext.HolPropProto{pb.PropRef(named), residual},
					Step: &proof.StepProto_SimpWith{SimpWith: &proof.SimpWithProto{
						Rules: []*ext.HolPropProto{pb.PropRef(prop.MakeProp(f.q)), pb.PropRef(named)},
					}},
				},
				{Goal: pb.PropRef(named), Step: &proof.StepProto_TrivialSimplify{}},
				byStep(residual, f.resident(pb, f.q)),
			}
		})
	resolver := func(key core.PropKey) (ExternalLeaf, bool) {
		if key == named.AlphaKey() {
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "RULE_NAMED"}, true
		}
		return ExternalLeaf{}, false
	}

	const pkg = "havesimpclaimemit"
	entry, entries := landedEntry(pkg, "RULE_NAMED", "RuleNamed")
	src := emitMember(t, env, EmitOptions{
		Family: "tmp/" + pkg, FuncName: "Build_HaveSimpClaim", ResolveExternalLeaf: resolver, FamilyDepEntry: entry,
	}, detailed(pb, steps...)).Source
	if !strings.Contains(src, "fact2 := a.Have(") || !strings.Contains(src, `Simp(Fwd(fact2), Fwd(RuleNamed))`) {
		t.Errorf("the simp rule the second Have states is not its handle\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "ResidentHyp(") {
		t.Errorf("a rule a Have states still renders as the hypothesis's text\n--- source: ---\n%s", src)
	}
	vetMemberWith(t, goBin, pkg, src, entries)
}

// TestEmit_HavePremiseOutOfScopeKeepsItsStatement: the handle is the
// Have's Go local, in scope from the Have to the end of its block. A
// `by` in another branch that cites the same statement as a resident
// hypothesis keeps `ResidentHyp(…)`: no Have of its own block states
// it.
func TestEmit_HavePremiseOutOfScopeKeepsItsStatement(t *testing.T) {
	env := makeTestEnv(t)
	f := newHavePremiseFixture()
	other := ext.Var("D", core.TypeBool()).Core()

	pb := ext.NewPoolBuilder()
	left := pb.PropRef(prop.MakeProp(f.goal))
	right := pb.PropRef(prop.MakeProp(other, f.everywhere))
	steps := []*proof.StepProto{{
		Goal:     pb.PropRef(prop.MakeProp(ext.WrapTerm(f.goal).And(other).Core())),
		SubGoals: []*ext.HolPropProto{left, right},
		Step:     &proof.StepProto_SplitConj{SplitConj: &emptypb.Empty{}},
	}}
	steps = append(steps, f.staircase(pb, f.goal, nil,
		func(claimGoal *ext.HolPropProto) *proof.StepProto {
			return &proof.StepProto{Goal: claimGoal, Step: &proof.StepProto_TrivialSimplify{}}
		},
		func(underBoth *ext.HolPropProto) []*proof.StepProto {
			return []*proof.StepProto{byStep(underBoth, f.resident(pb, f.everywhere, f.c))}
		})...)
	steps = append(steps, byStep(right, f.resident(pb, f.everywhere, f.c)))

	src := emitMember(t, env, EmitOptions{FuncName: "BuildHavePremiseBranches"}, detailed(pb, steps...)).Source
	if got := strings.Count(src, "By(At(fact1, c))"); got != 1 {
		t.Errorf("the Have's own block cites it by handle %d times, want 1\n--- source: ---\n%s", got, src)
	}
	if got := strings.Count(src, "By(At(ResidentHyp("); got != 1 {
		t.Errorf("the other branch's premise renders as a statement %d times, want 1\n--- source: ---\n%s", got, src)
	}
}

// TestEmit_HavePremiseNeedsTheHypothesisAllTheWay: a Have's Fact names
// the hypothesis its claim states only while no step between them
// moves it. Where a goal on the way from the Have to the `by` does not
// carry the claim, the premise keeps its statement.
func TestEmit_HavePremiseNeedsTheHypothesisAllTheWay(t *testing.T) {
	env := makeTestEnv(t)
	f := newHavePremiseFixture()

	pb := ext.NewPoolBuilder()
	steps := f.staircase(pb, f.goal, nil,
		func(claimGoal *ext.HolPropProto) *proof.StepProto {
			return &proof.StepProto{Goal: claimGoal, Step: &proof.StepProto_TrivialSimplify{}}
		},
		func(underBoth *ext.HolPropProto) []*proof.StepProto {
			// The continuation's first step is recorded on a goal that
			// carries only the second fact; the `by` under it has both.
			moved := pb.PropRef(prop.MakeProp(f.goal, f.q))
			return []*proof.StepProto{
				{Goal: moved, SubGoals: []*ext.HolPropProto{underBoth}, Step: &proof.StepProto_Basic{Basic: &emptypb.Empty{}}},
				byStep(underBoth, f.resident(pb, f.everywhere, f.c), f.resident(pb, f.q)),
			}
		})

	src := emitMember(t, env, EmitOptions{FuncName: "BuildHavePremiseMoved"}, detailed(pb, steps...)).Source
	// The second Have is the one bound, so it takes the first ident.
	if !strings.Contains(src, `By(At(ResidentHyp(ctx.MakePropText("∀x:A. F(x)")), c), fact1),`) {
		t.Errorf("want the moved hypothesis cited by its statement and the one that stayed by its handle\n--- source: ---\n%s", src)
	}
	if !regexp.MustCompile(`fact1 := a\.Have\(\s*"Q",`).MatchString(src) {
		t.Errorf("the Have whose hypothesis stayed is not bound\n--- source: ---\n%s", src)
	}
	if got := strings.Count(src, ":= a.Have("); got != 1 {
		t.Errorf("%d Haves are bound, want only the one whose hypothesis stayed\n--- source: ---\n%s", got, src)
	}
}
