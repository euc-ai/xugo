package main

import (
	json "encoding/json/v2"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/engine"
	"github.com/euc-ai/xugo/library/registry"
)

// A command that drives no engine answers with none built: main runs it
// before initEngine. The child is this test binary running main on the
// command line the parent passes, and it fails when main left an engine
// behind. Each such command has one row in a child, which is where its
// exit code is read too; what the commands answer beyond that is asked
// in this process (engineFreeOutput), a child costing the corpus's
// load each time.
func TestEngineFreeCommandsBuildNoEngine(t *testing.T) {
	if line := os.Getenv("XUGO_TEST_ENGINE_FREE_LINE"); line != "" {
		os.Args = append([]string{"xugo"}, strings.Fields(line)...)
		main()
		if eng != nil || proverEnv != nil || constMetaMgr != nil {
			fmt.Fprintln(os.Stderr, "main built an engine for", line)
			os.Exit(1)
		}
		os.Exit(0)
	}
	// A fault store with one open fault, for the `faults` rows: the
	// listing fails while a fault is open, and passes once it is
	// acknowledged.
	dataDir := t.TempDir()
	open := engine.NewEngine(nil, engine.WithFaultStore(faultStoreUnder(dataDir))).
		RecordCommandFault("inspect", []byte(`{"cmd":"inspect"}`), "a panic that left a command")
	// The cards command reads an attacker's transcript even when the
	// data dir cannot host a CNF store. It needs no session engine.
	cardsDir := t.TempDir()
	if err := os.WriteFile(filepath.Join(cardsDir, "cnf_cache"), []byte("not a directory"), 0o644); err != nil {
		t.Fatal(err)
	}
	var card *registry.ProofEntry
	for _, entry := range registry.All() {
		if entry.IsCard() {
			card = entry
			break
		}
	}
	if card == nil {
		t.Fatal("the corpus has no card for the transcript fixture")
	}
	lineageDir := filepath.Join(cardsDir, "sessions", "cards-cli")
	if err := os.MkdirAll(lineageDir, 0o755); err != nil {
		t.Fatal(err)
	}
	transcript, err := json.Marshal(struct {
		ID     string                `json:"id"`
		Events []engine.LineageEvent `json:"events"`
	}{"cards-cli", []engine.LineageEvent{{Kind: "add_goal", Goal: &engine.LineageGoal{NormKey: card.Key, Section: 0}}}})
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(lineageDir, "lineage.json"), transcript, 0o644); err != nil {
		t.Fatal(err)
	}
	rows := []struct {
		command, line, answer string
		exit                  int
	}{
		{"registry-fingerprint", "registry-fingerprint", `"fingerprint"`, 0},
		{"query", "query overview", `"domains"`, 0},
		{"browse", "browse --port 0 --timeout 1ms", `"status":"listening","url":"http://127.0.0.1:`, 0},
		{"cards", "--data-dir " + cardsDir + " cards --key " + card.Key, `"attacked_by":[{"lineage":"cards-cli","section":0}]`, 0},
		{"faults", "--data-dir " + dataDir + " faults", `"id":"` + open.ID + `"`, 1},
	}
	run := map[string]bool{}
	for _, row := range rows {
		run[row.command] = true
		child := exec.Command(os.Args[0], "-test.run=^TestEngineFreeCommandsBuildNoEngine$")
		child.Env = append(os.Environ(), "XUGO_TEST_ENGINE_FREE_LINE="+row.line)
		out, err := child.CombinedOutput()
		if exit := child.ProcessState.ExitCode(); exit != row.exit {
			t.Fatalf("xugo %s exited %d, want %d (%v)\n%s", row.line, exit, row.exit, err, out)
		}
		if !strings.Contains(string(out), row.answer) {
			t.Fatalf("xugo %s answered without %s:\n%s", row.line, row.answer, out)
		}
	}
	for name := range engineFreeCommands {
		if !run[name] {
			t.Errorf("%s runs before initEngine and no row here runs it", name)
		}
	}

	for _, row := range []struct {
		command, dataDir string
		args             []string
		answer           string
	}{
		{"query", "", []string{"cards", path.Base(card.Family().Name)}, `"statement_typed"`},
		{"cards", "", nil, `{"cards":[]}`},
		{"cards", cardsDir, []string{"--lineage", "cards-cli"}, `"entry":"` + card.Name + `"`},
		{"faults", t.TempDir(), nil, `"open":0`},
		{"faults", dataDir, []string{"show", open.ID}, `"rpc_body":{"cmd":"inspect"}`},
		{"faults", dataDir, []string{"ack", open.ID, "--note=handled"}, `"note":"handled"`},
		{"faults", dataDir, nil, `"open":0,"acknowledged":1`},
		{"faults", dataDir, []string{"--all"}, `"id":"` + open.ID + `"`},
	} {
		if out := engineFreeOutput(t, row.dataDir, row.command, row.args...); !strings.Contains(out, row.answer) {
			t.Fatalf("xugo --data-dir %q %s %v answered without %s:\n%s", row.dataDir, row.command, row.args, row.answer, out)
		}
	}
}

// engineFreeOutput is what an engine-free command writes to stdout, run
// in this process under dataDir. A command that ends the process — a
// refused argument, a listing with an open fault — ends the test binary.
func engineFreeOutput(t *testing.T, dataDir, command string, args ...string) string {
	t.Helper()
	r, w, err := os.Pipe()
	if err != nil {
		t.Fatal(err)
	}
	stdout, flag := os.Stdout, dataDirFlag
	os.Stdout, dataDirFlag = w, dataDir
	defer func() {
		os.Stdout, dataDirFlag = stdout, flag
		resetTrace()
	}()
	written := make(chan []byte)
	go func() {
		out, _ := io.ReadAll(r)
		written <- out
	}()
	engineFreeCommands[command](args)
	w.Close()
	return string(<-written)
}
