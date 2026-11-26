package main

import (
	"os"
	"os/exec"
	"strings"
	"testing"
)

// decodeRPCInput is the one door every RPC body enters through: the
// envelope's `cmd` is dropped, and any member the handler's input does
// not declare is refused by name. The second half is the contract — a
// wrong field was once silently dropped and reported as whatever the
// handler missed next.
func TestDecodeRPCInput_DropsCmdAndRefusesUnknownMembers(t *testing.T) {
	var in QueryRPCInput
	if err := decodeRPCInput([]byte(`{"cmd":"query","what":"member","member":"dot.AddLeft"}`), &in); err != nil {
		t.Fatalf("a body with only cmd and declared members: %v", err)
	}
	if in.What != "member" || in.Member != "dot.AddLeft" {
		t.Fatalf("members not decoded: %+v", in)
	}

	var again QueryRPCInput
	err := decodeRPCInput([]byte(`{"cmd":"query","name":"dot.AddLeft"}`), &again)
	if err == nil {
		t.Fatal("an undeclared member decoded silently")
	}
	if !strings.Contains(err.Error(), "name") {
		t.Fatalf("the refusal does not name the member: %v", err)
	}
	if again.Member != "" {
		t.Fatalf("a refused body still populated the input: %+v", again)
	}
}

// The command line's stdin enters through the same door: a member the
// input does not declare ends the command with the member named. The
// command exits the process on a bad input, so the child is this test
// binary re-run with the input on its stdin.
func TestReadInput_RefusesAnUndeclaredMember(t *testing.T) {
	if os.Getenv("XUGO_TEST_READ_INPUT_CHILD") == "1" {
		var in CheckConsistencyInput
		readInput(&in)
		os.Exit(0)
	}
	run := func(stdin string) (string, error) {
		child := exec.Command(os.Args[0], "-test.run=^TestReadInput_RefusesAnUndeclaredMember$")
		child.Env = append(os.Environ(), "XUGO_TEST_READ_INPUT_CHILD=1")
		child.Stdin = strings.NewReader(stdin)
		out, err := child.CombinedOutput()
		return string(out), err
	}

	if out, err := run(`{"statements":[{"text":"p"}]}`); err != nil {
		t.Fatalf("an input of declared members was refused: %v\n%s", err, out)
	}
	out, err := run(`{"statements":[{"text":"p"}],"statments":[{"text":"q"}]}`)
	if err == nil {
		t.Fatalf("an undeclared member decoded silently:\n%s", out)
	}
	if !strings.Contains(out, "statments") {
		t.Fatalf("the refusal does not name the member:\n%s", out)
	}
}
