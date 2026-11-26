package emit

import (
	"fmt"
	"go/token"
	"os/exec"
	"regexp"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

func TestDeriveReceiverBeyondLetters(t *testing.T) {
	e := &_Emitter{}
	seen := map[string]bool{}
	for depth := 0; depth < 80; depth++ {
		name := e.deriveReceiver(depth)
		if !token.IsIdentifier(name) || seen[name] || name == "h" {
			t.Fatalf("depth %d gave invalid or reused receiver %q", depth, name)
		}
		seen[name] = true
	}
	for depth, want := range map[int]string{0: "a", 1: "b", 6: "g", 7: "i", 24: "z", 25: "arg1"} {
		if got := e.deriveReceiver(depth); got != want {
			t.Fatalf("depth %d: got %q, want %q", depth, got, want)
		}
	}
}

// TestEmit_DeriveReceiversPastTheLetters: a member whose statement
// names every letter from `b` to `z`, and `arg1`, leaves no letter free
// for a Derive receiver, so its two nested blocks take arg2 and arg3 —
// distinct from one another and from every name the statement holds —
// and the member still type-checks.
func TestEmit_DeriveReceiversPastTheLetters(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}
	env := makeTestEnv(t)

	var letters []ext.TermLike
	relation := core.TypeBool()
	for _, name := range append(strings.Split("bcdefghijklmnopqrstuvwxyz", ""), "arg1") {
		letters = append(letters, ext.Var(ext.TermName(name), core.TypeA()))
		relation = core.MakeFun(core.TypeA(), relation)
	}
	held := ext.Var("R", relation).Apply(letters...).Core()

	// staircase proves goal by two asserts, the first claim proved by a
	// staircase of its own while depth lasts: each level below the
	// body's renders as one more nested Derive block.
	pb := ext.NewPoolBuilder()
	var steps []*proof.StepProto
	claims := 0
	claim := func() core.Term {
		claims++
		return ext.Var(ext.TermName(fmt.Sprintf("P%d", claims)), core.TypeBool()).Core()
	}
	var staircase func(conclusion core.Term, hyps []core.Term, depth int)
	staircase = func(conclusion core.Term, hyps []core.Term, depth int) {
		first, second := claim(), claim()
		withFirst := append(append([]core.Term{}, hyps...), first)
		withBoth := append(append([]core.Term{}, withFirst...), second)
		goal := prop.MakeProp(conclusion, hyps...)
		firstGoal := prop.MakeProp(first, hyps...)
		after := prop.MakeProp(conclusion, withFirst...)
		secondGoal := prop.MakeProp(second, withFirst...)
		last := prop.MakeProp(conclusion, withBoth...)
		steps = append(steps, &proof.StepProto{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(firstGoal), pb.PropRef(after)},
			Step:     &proof.StepProto_Assert{Assert: pb.PropRef(prop.MakeProp(first))},
		})
		if depth > 0 {
			staircase(first, hyps, depth-1)
		} else {
			steps = append(steps, &proof.StepProto{Goal: pb.PropRef(firstGoal), Step: &proof.StepProto_TrivialSimplify{}})
		}
		steps = append(steps,
			&proof.StepProto{
				Goal:     pb.PropRef(after),
				SubGoals: []*ext.HolPropProto{pb.PropRef(secondGoal), pb.PropRef(last)},
				Step:     &proof.StepProto_Assert{Assert: pb.PropRef(prop.MakeProp(second))},
			},
			&proof.StepProto{Goal: pb.PropRef(secondGoal), Step: &proof.StepProto_TrivialSimplify{}},
			&proof.StepProto{Goal: pb.PropRef(last), Step: &proof.StepProto_CnfRefute{}},
		)
	}
	staircase(ext.Var("C", core.TypeBool()).Core(), []core.Term{held}, 2)

	const pkg = "derivereceiversemit"
	src := emitMember(t, env, EmitOptions{
		Family:   "tmp/" + pkg,
		FuncName: "Build_DeriveReceivers",
	}, detailed(pb, steps...)).Source
	var receivers []string
	for _, m := range regexp.MustCompile(`Derive\(func\((\w+) \*Argument\)`).FindAllStringSubmatch(src, -1) {
		receivers = append(receivers, m[1])
	}
	if strings.Join(receivers, " ") != "arg2 arg3" {
		t.Errorf("nested receivers = %v, want [arg2 arg3]\n--- source: ---\n%s", receivers, src)
	}
	vetMember(t, goBin, pkg, src)
}
