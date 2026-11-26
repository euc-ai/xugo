package main

import (
	"bytes"
	"context"
	json "encoding/json/v2"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync/atomic"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/engine"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// startTestServer starts the serve HTTP handler on a random port and returns
// the base URL. RPC tests initialize their engine with initTestEngine first.
func startTestServer(t *testing.T) string {
	t.Helper()

	ln, err := net.Listen("tcp", "127.0.0.1:0")
	require.NoError(t, err)
	port := ln.Addr().(*net.TCPAddr).Port

	server := &http.Server{Handler: serveHandler(func() {})}
	go server.Serve(ln)
	t.Cleanup(func() { server.Close() })

	// Wait for server to be ready.
	baseURL := fmt.Sprintf("http://127.0.0.1:%d", port)
	for i := 0; i < 50; i++ {
		resp, err := http.Get(baseURL + "/health")
		if err == nil {
			resp.Body.Close()
			break
		}
		time.Sleep(10 * time.Millisecond)
	}

	return baseURL
}

func rpcCall(t *testing.T, baseURL string, body map[string]any) map[string]any {
	t.Helper()
	data, err := json.Marshal(body)
	require.NoError(t, err)
	return rpcCallRaw(t, baseURL, data)
}

func rpcCallRaw(t *testing.T, baseURL string, data []byte) map[string]any {
	t.Helper()
	resp, err := http.Post(baseURL+"/rpc", "application/json", bytes.NewReader(data))
	require.NoError(t, err)
	defer resp.Body.Close()

	respBody, err := io.ReadAll(resp.Body)
	require.NoError(t, err)

	var result map[string]any
	require.NoError(t, json.Unmarshal(respBody, &result), "response: %s", string(respBody))
	return result
}

func TestServe_Health(t *testing.T) {
	base := startTestServer(t)

	resp, err := http.Get(base + "/health")
	require.NoError(t, err)
	defer resp.Body.Close()

	assert.Equal(t, 200, resp.StatusCode)
	body, _ := io.ReadAll(resp.Body)
	assert.Contains(t, string(body), `"ok"`)
}

// TestServe_AddGoal_PropInputValidation pins the wire-level validation
// for the add-goal `goal` field: a goal is given as `text`; an empty
// goal and a `key` are refused.
func TestServe_AddGoal_PropInputValidation(t *testing.T) {
	initTestEngine()
	base := startTestServer(t)

	// Create session
	res := rpcCall(t, base, map[string]any{"cmd": "session-create"})
	sessionID, ok := res["id"].(string)
	require.True(t, ok, "session-create should return id, got: %v", res)

	// add-goal with no goal field → must fail with PropInput validation
	res = rpcCall(t, base, map[string]any{
		"cmd":        "add-goal",
		"session_id": sessionID,
	})
	errMsg, _ := res["error"].(string)
	assert.Contains(t, errMsg, "must set 'text'", "empty goal should be rejected")

	// add-goal with goal.key → refused: a goal is given as text
	res = rpcCall(t, base, map[string]any{
		"cmd":        "add-goal",
		"session_id": sessionID,
		"goal":       map[string]any{"key": "prop_nonexistent"},
	})
	errMsg, _ = res["error"].(string)
	assert.Contains(t, errMsg, "a goal is given as 'text'", "goal.key should be refused")

	// add-goal with goal.text → the door. It resolves strictly: the text
	// must quantify or declare its variables.
	res = rpcCall(t, base, map[string]any{
		"cmd":        "add-goal",
		"session_id": sessionID,
		"goal":       map[string]any{"text": "∀p:bool. p ⇒ p"},
	})
	if errMsg, _ := res["error"].(string); errMsg != "" {
		t.Fatalf("text-mode add-goal failed: %s", errMsg)
	}
	assert.NotEmpty(t, res["goal_id"], "text-mode add-goal should return a goal_id")

	// add-goal with both fields set → refused for the key
	res = rpcCall(t, base, map[string]any{
		"cmd":        "add-goal",
		"session_id": sessionID,
		"goal":       map[string]any{"text": "p", "key": "prop_x"},
	})
	errMsg, _ = res["error"].(string)
	assert.Contains(t, errMsg, "a goal is given as 'text'", "goal with a key should be rejected")
}

// TestServe_CheckDerivation_TextIngress is the end-to-end integration
// test for the text-DSL ingress through a JSON envelope: send modus
// ponens premises and conclusion as `{"text": "..."}` and verify the
// engine evaluates the derivation. Pins the contract that stateless
// verification works without --data-dir or proto_hex.
func TestServe_CheckDerivation_TextIngress(t *testing.T) {
	initTestEngine()
	base := startTestServer(t)

	res := rpcCall(t, base, map[string]any{
		"cmd": "check-derivation",
		"premises": []map[string]any{
			{"text": "p"},
			{"text": "p ⇒ q"},
		},
		"conclusion": map[string]any{"text": "q"},
	})
	if errMsg, _ := res["error"].(string); errMsg != "" {
		t.Fatalf("check-derivation failed: %s", errMsg)
	}
	assert.Equal(t, "valid", res["result"])
}

func TestServe_UnknownCommand(t *testing.T) {
	initTestEngine()
	base := startTestServer(t)

	data, _ := json.Marshal(map[string]any{"cmd": "nonexistent"})
	resp, err := http.Post(base+"/rpc", "application/json", bytes.NewReader(data))
	require.NoError(t, err)
	defer resp.Body.Close()

	assert.Equal(t, 400, resp.StatusCode)
	body, _ := io.ReadAll(resp.Body)
	assert.Contains(t, string(body), "unknown command")
}

func TestServe_MissingCmd(t *testing.T) {
	initTestEngine()
	base := startTestServer(t)

	data, _ := json.Marshal(map[string]any{"data": "hello"})
	resp, err := http.Post(base+"/rpc", "application/json", bytes.NewReader(data))
	require.NoError(t, err)
	defer resp.Body.Close()

	assert.Equal(t, 400, resp.StatusCode)
	body, _ := io.ReadAll(resp.Body)
	assert.Contains(t, string(body), "missing")
}

// TestParseServeArgs: serve reads its three flags in both spellings and
// refuses everything else. A global flag after the subcommand is the
// case that matters: accepted silently, `serve --data-dir D` would
// start a server with no session store.
func TestParseServeArgs(t *testing.T) {
	port, portFile, timeout, err := parseServeArgs([]string{"--port", "8080", "--port-file=/tmp/p", "--timeout", "12h"})
	require.NoError(t, err)
	assert.Equal(t, 8080, port)
	assert.Equal(t, "/tmp/p", portFile)
	assert.Equal(t, 12*time.Hour, timeout)

	_, _, timeout, err = parseServeArgs(nil)
	require.NoError(t, err)
	assert.Equal(t, 10*time.Minute, timeout, "the default inactivity timeout")

	for _, args := range [][]string{
		{"--data-dir", "data"},
		{"--data-dir=data"},
		{"--port"}, // a flag without its value
		{"extra"},
	} {
		_, _, _, err := parseServeArgs(args)
		require.Error(t, err, "serve must refuse %v", args)
		assert.Contains(t, err.Error(), args[0])
	}
	_, _, _, err = parseServeArgs([]string{"--data-dir", "data"})
	assert.Contains(t, err.Error(), "before the subcommand")

	_, _, _, err = parseServeArgs([]string{"--port=eighty"})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "bad --port")
}

// serveRequest sends one request through the server's handler, addressed
// to host. It returns the status, the JSON reply, and how often the
// handler touched the inactivity timer.
func serveRequest(t *testing.T, method, host, path, body string, header map[string]string) (int, map[string]any, int) {
	t.Helper()
	touched := 0
	req := httptest.NewRequest(method, "http://"+host+path, strings.NewReader(body))
	for name, value := range header {
		req.Header.Set(name, value)
	}
	rec := httptest.NewRecorder()
	serveHandler(func() { touched++ }).ServeHTTP(rec, req)
	var reply map[string]any
	require.NoError(t, json.Unmarshal(rec.Body.Bytes(), &reply), "reply: %s", rec.Body.String())
	return rec.Code, reply, touched
}

// TestServe_RefusesAWebPage pins who drives the server: a program on
// this machine, and no web page. A page of another site can have the
// browser POST to the loopback port without its user seeing it; the
// browser marks such a request, and it is refused before it is
// dispatched or counted as activity. A page whose own name has been
// pointed at 127.0.0.1 is same-origin to the browser, and is refused by
// the Host it sends.
func TestServe_RefusesAWebPage(t *testing.T) {
	initTestEngine()
	const local = "127.0.0.1:8080"
	const create = `{"cmd":"session-create"}`

	for _, c := range []struct {
		name, host string
		header     map[string]string
		says       string
	}{
		{"a fetch from another site", local,
			map[string]string{"Sec-Fetch-Site": "cross-site", "Origin": "https://example.com", "Content-Type": "text/plain"}, "another origin"},
		{"a form posted by a browser that sends no Sec-Fetch-Site", local,
			map[string]string{"Origin": "https://example.com", "Content-Type": "application/x-www-form-urlencoded"}, "another origin"},
		{"a sandboxed frame", local,
			map[string]string{"Origin": "null"}, "another origin"},
		{"a page served from another port of this machine", local,
			map[string]string{"Sec-Fetch-Site": "same-site", "Origin": "http://127.0.0.1:3000"}, "another origin"},
		{"the same page, by its Origin alone", local,
			map[string]string{"Origin": "http://127.0.0.1:3000"}, "another origin"},
		{"a page whose name was pointed at this machine", "example.com:8080",
			map[string]string{"Sec-Fetch-Site": "same-origin", "Origin": "http://example.com:8080"}, "Host"},
		{"a name that is not this machine's, from no browser", "example.com", nil, "Host"},
	} {
		t.Run(c.name, func(t *testing.T) {
			code, reply, touched := serveRequest(t, http.MethodPost, c.host, "/rpc", create, c.header)
			assert.Equal(t, http.StatusForbidden, code, "reply: %v", reply)
			assert.Contains(t, reply["error"], c.says)
			assert.NotContains(t, reply, "id", "the refused request created a session")
			assert.Zero(t, touched, "a refused request is not activity")
		})
	}

	for _, c := range []struct {
		name, host string
		header     map[string]string
	}{
		{"curl -d", local, map[string]string{"Content-Type": "application/x-www-form-urlencoded"}},
		{"addressed as localhost", "localhost:8080", nil},
		{"addressed with no port", "127.0.0.1", nil},
	} {
		t.Run(c.name, func(t *testing.T) {
			code, reply, touched := serveRequest(t, http.MethodPost, c.host, "/rpc", create, c.header)
			assert.Equal(t, http.StatusOK, code, "reply: %v", reply)
			assert.Contains(t, reply, "id")
			assert.Equal(t, 1, touched)
		})
	}

	t.Run("the health check under a name that is not this machine's", func(t *testing.T) {
		code, reply, touched := serveRequest(t, http.MethodGet, "example.com:8080", "/health", "", nil)
		assert.Equal(t, http.StatusForbidden, code, "reply: %v", reply)
		assert.Zero(t, touched)
	})
}

// TestServe_RefusesABodyOverItsLimit pins the cap on a request's body:
// a body of exactly the limit is read and dispatched, one byte more is
// refused with the limit named.
func TestServe_RefusesABodyOverItsLimit(t *testing.T) {
	const local = "127.0.0.1:8080"
	const cmd = `{"cmd":"registry-fingerprint"}`
	atLimit := cmd + strings.Repeat(" ", maxRPCBody-len(cmd))

	code, reply, _ := serveRequest(t, http.MethodPost, local, "/rpc", atLimit, nil)
	assert.Equal(t, http.StatusOK, code, "reply: %v", reply)
	assert.Contains(t, reply, "fingerprint")

	code, reply, _ = serveRequest(t, http.MethodPost, local, "/rpc", atLimit+" ", nil)
	assert.Equal(t, http.StatusRequestEntityTooLarge, code, "reply: %v", reply)
	assert.Contains(t, reply["error"], strconv.Itoa(maxRPCBody))
}

// TestServe_ErrorCarriesTheResultBesideIt pins the reply of a command
// that returned a result beside its error — emit-section's rendered
// member beside its CNF collection error: the result's fields and the
// error in one object under the error's status. A command that returned
// no result, a typed nil pointer included, replies with the error alone.
func TestServe_ErrorCarriesTheResultBesideIt(t *testing.T) {
	decode := func(t *testing.T, rec *httptest.ResponseRecorder) map[string]any {
		t.Helper()
		var reply map[string]any
		require.NoError(t, json.Unmarshal(rec.Body.Bytes(), &reply), "reply: %s", rec.Body.String())
		return reply
	}
	collection := fmt.Errorf("collect CNF cache: section 0: By: CNF cache MISS")

	rec := httptest.NewRecorder()
	writeHTTPErrorWith(rec, http.StatusBadRequest, &engine.EmitSectionResult{SectionID: 0, FuncName: "Build_Draft", Go: "package draft\n"}, collection)
	reply := decode(t, rec)
	assert.Equal(t, http.StatusBadRequest, rec.Code)
	assert.Equal(t, collection.Error(), reply["error"])
	assert.Equal(t, "package draft\n", reply["go"])
	assert.Equal(t, "Build_Draft", reply["func_name"])

	rec = httptest.NewRecorder()
	writeHTTPErrorWith(rec, http.StatusBadRequest, (*engine.EmitSectionResult)(nil), collection)
	reply = decode(t, rec)
	assert.Equal(t, http.StatusBadRequest, rec.Code)
	assert.Equal(t, map[string]any{"error": collection.Error()}, reply)
}

// TestServe_ProbeCarriesTheEngineReply: the probe RPC answers with the
// engine's probe result as it stands. A closing `by` probe names its
// closer and the rows a recording would write (by_closer, records), as
// the manual's probe row says, and the subgoals carry their changes;
// a reply reshaped in the handler would drop each of them.
func TestServe_ProbeCarriesTheEngineReply(t *testing.T) {
	initTestEngine()
	base := startTestServer(t)

	res := rpcCall(t, base, map[string]any{"cmd": "session-create", "family": "sets/set_image"})
	sessionID, ok := res["id"].(string)
	require.True(t, ok, "session-create: %v", res)
	res = rpcCall(t, base, map[string]any{"cmd": "add-goal", "session_id": sessionID,
		"goal": map[string]any{"text": "∀f:num → B → C. ∀n:num. ∀u:B. ∀S:set(B). u ∈ S ⇒ f(n)(u) ∈ image(f(n), S)"}})
	goalID, ok := res["goal_id"].(string)
	require.True(t, ok, "add-goal: %v", res)

	// A probe that leaves a subgoal reports what changed in it.
	res = rpcCall(t, base, map[string]any{"cmd": "probe", "session_id": sessionID, "goal_id": goalID,
		"tactic": map[string]any{"type": "strip_quant"}})
	require.Equal(t, "success", res["outcome"], "probe strip_quant: %v", res)
	subgoals, _ := res["subgoals"].([]any)
	require.Len(t, subgoals, 1, "probe strip_quant: %v", res)
	assert.Contains(t, subgoals[0], "changes", "a probe's subgoal carries its changes: %v", subgoals[0])

	for _, move := range []string{"strip_quant", "strip_imp"} {
		res = rpcCall(t, base, map[string]any{"cmd": "apply", "session_id": sessionID, "goal_id": goalID,
			"tactic": map[string]any{"type": move}})
		require.Equal(t, true, res["success"], "apply %s: %v", move, res)
		goals := res["state"].(map[string]any)["goals"].([]any)
		goalID = goals[0].(map[string]any)["id"].(string)
	}

	res = rpcCall(t, base, map[string]any{"cmd": "probe", "session_id": sessionID, "goal_id": goalID,
		"tactic": map[string]any{"type": "by",
			"by_hyps":     []any{map[string]any{"hyp_index": 0}},
			"with_lemmas": []any{map[string]any{"key": "set_image.FunInImage"}}}})
	require.Equal(t, "success", res["outcome"], "probe by: %v", res)
	require.Equal(t, "close", res["effect"], "probe by: %v", res)
	assert.Equal(t, "apply/conditioning", res["by_closer"], "a closing by probe names its closer: %v", res)
	assert.Contains(t, res["records"], "Records nothing", "a closing by probe says what a recording writes: %v", res)
}

// _BreakingCNFStore fails an assertion at its first read of a proof and
// holds nothing: the first tactic whose close reaches the store breaks
// an engine invariant.
type _BreakingCNFStore struct {
	proof.CNFStore
	reads *atomic.Int32
}

func (s _BreakingCNFStore) ReadProof(core.PropKey) *refuter.CNFRefuteProofProto {
	if s.reads.Add(1) == 1 {
		utils.Assert(false)
	}
	return nil
}

// TestServe_AnEngineFaultIsMarkedRecordedAndLocksTheSession: over /rpc,
// an apply whose tactic breaks an engine invariant answers 200 with
// success:false, an engine_fault diagnostic and the fault's mark; the
// record under <data-dir>/faults holds the request body as it came; the
// session still answers inspect and refuses apply and add-goal, naming
// the fault; and the fault store's listing shows it open until it is
// acknowledged, after which the session moves again.
func TestServe_AnEngineFaultIsMarkedRecordedAndLocksTheSession(t *testing.T) {
	dataDir := t.TempDir()
	opts := initSessionEnv(dataDir)
	testEngineBundles()
	proverEnv.ProofService.CNFStore = _BreakingCNFStore{proverEnv.ProofService.CNFStore, &atomic.Int32{}}
	eng = engine.NewEngine(proverEnv, opts...)
	base := startTestServer(t)

	res := rpcCall(t, base, map[string]any{"cmd": "session-create"})
	sessionID, ok := res["id"].(string)
	require.True(t, ok, "session-create: %v", res)
	res = rpcCall(t, base, map[string]any{"cmd": "add-goal", "session_id": sessionID, "goal": map[string]any{
		"text": "∀f:num → num. ∀g:num → num. ∀h:num → num. ∀k:num → num. ∀a:num. ∀b:num. ∀c:num. ∀d:num. " +
			"f(a) = g(b) ⇒ g(b) = h(c) ⇒ h(c) = k(d) ⇒ f(a) = k(d)"}})
	goalID, ok := res["goal_id"].(string)
	require.True(t, ok, "add-goal: %v", res)

	// Down to the leaf with the three equations as hypotheses.
	for _, move := range []string{"strip_quant", "strip_imp", "strip_imp", "strip_imp"} {
		res = rpcCall(t, base, map[string]any{"cmd": "apply", "session_id": sessionID, "goal_id": goalID,
			"tactic": map[string]any{"type": move}})
		if res["success"] != true {
			break
		}
		goalID = res["state"].(map[string]any)["goals"].([]any)[0].(map[string]any)["id"].(string)
	}

	apply := map[string]any{"cmd": "apply", "session_id": sessionID, "goal_id": goalID,
		"tactic": map[string]any{"type": "by", "by_hyps": []any{
			map[string]any{"hyp_index": 0}, map[string]any{"hyp_index": 1}, map[string]any{"hyp_index": 2}}}}
	res = rpcCall(t, base, apply)
	require.Equal(t, false, res["success"], "apply by: %v", res)
	mark, ok := res["engine_fault"].(map[string]any)
	require.True(t, ok, "the reply carries the fault's mark: %v", res)
	faultID := mark["id"].(string)
	assert.Contains(t, mark["panic"], utils.AssertionFailed)
	assert.Contains(t, mark["site"], "serve_test.go:")
	diagnostics := res["diagnostics"].([]any)
	require.Len(t, diagnostics, 1)
	assert.Equal(t, "engine_fault", diagnostics[0].(map[string]any)["type"])
	assert.NotContains(t, diagnostics[0], "repair_hints")

	record, err := engine.ReadFault(faultStoreUnder(dataDir), faultID)
	require.NoError(t, err)
	assert.Equal(t, mark["record"], filepath.Join(faultStoreUnder(dataDir), faultID+".json"))
	assert.Equal(t, "apply", record.Command)
	assert.Equal(t, sessionID, record.Session)
	sent, err := json.Marshal(apply)
	require.NoError(t, err)
	assert.JSONEq(t, string(sent), string(record.RPCBody), "the body as /rpc received it")
	require.NotNil(t, record.Goal)
	assert.Equal(t, goalID, record.Goal.GoalID)
	assert.NotEmpty(t, record.Goal.Blob)

	// The session: reads answer, moves are refused.
	res = rpcCall(t, base, map[string]any{"cmd": "inspect", "session_id": sessionID})
	assert.NotContains(t, res, "error", "inspect still answers: %v", res)
	res = rpcCall(t, base, map[string]any{"cmd": "session-lineage", "session_id": sessionID})
	events := res["events"].([]any)
	assert.Equal(t, "fault", events[len(events)-1].(map[string]any)["kind"], "the fault is in the lineage: %v", res)
	for _, move := range []map[string]any{
		apply,
		{"cmd": "probe", "session_id": sessionID, "goal_id": goalID, "tactic": map[string]any{"type": "strip_quant"}},
		{"cmd": "add-goal", "session_id": sessionID, "goal": map[string]any{"text": "∀x:num. x = x"}},
	} {
		res = rpcCall(t, base, move)
		require.Contains(t, res, "error", "%s is refused: %v", move["cmd"], res)
		assert.Contains(t, res["error"], faultID, "%s's refusal names the fault", move["cmd"])
	}

	// The observing step: open until acknowledged.
	view, err := engine.ViewFaults(faultStoreUnder(dataDir), false)
	require.NoError(t, err)
	require.Equal(t, 1, view.Open)
	assert.Equal(t, faultID, view.Faults[0].ID)
	assert.Equal(t, "by", view.Faults[0].Tactic)
	_, err = engine.AcknowledgeFault(faultStoreUnder(dataDir), faultID, "reproduced; fixed at its source")
	require.NoError(t, err)
	view, err = engine.ViewFaults(faultStoreUnder(dataDir), false)
	require.NoError(t, err)
	assert.Equal(t, 0, view.Open)
	assert.Equal(t, 1, view.Acknowledged)
	res = rpcCall(t, base, apply)
	assert.Equal(t, true, res["success"], "acknowledged, the session moves again: %v", res)
}

// TestServe_APanicThatLeavesACommandIsAnEngineFault: the handler's
// reading of a panic out of a command is HTTP 500 with the fault's mark
// beside the error, and the record holds the request.
func TestServe_APanicThatLeavesACommandIsAnEngineFault(t *testing.T) {
	dataDir := t.TempDir()
	opts := initSessionEnv(dataDir)
	testEngineBundles()
	eng = engine.NewEngine(proverEnv, opts...)

	body := []byte(`{"cmd":"emit-section","session_id":"none","section":0}`)
	rec := httptest.NewRecorder()
	func() {
		defer func() { answerPanic(rec, "emit-section", body, recover()) }()
		panic("a command broke")
	}()
	assert.Equal(t, http.StatusInternalServerError, rec.Code)
	var reply map[string]any
	require.NoError(t, json.Unmarshal(rec.Body.Bytes(), &reply), "reply: %s", rec.Body.String())
	assert.Equal(t, "panic: a command broke", reply["error"])
	mark, ok := reply["engine_fault"].(map[string]any)
	require.True(t, ok, "the reply carries the fault's mark: %v", reply)
	record, err := engine.ReadFault(faultStoreUnder(dataDir), mark["id"].(string))
	require.NoError(t, err)
	assert.Equal(t, "emit-section", record.Command)
	assert.Equal(t, "a command broke", record.Panic)
	assert.Contains(t, record.Site, "serve_test.go:")
	assert.JSONEq(t, string(body), string(record.RPCBody))
}

// TestServe_ACommandThatDoesNotAnswerIsInFlightInTheFaultStore: over
// /rpc, an inspect that has not answered is a file of the fault store
// once it has run engine.InFlightAfter, naming the command, the session
// and the goal, with the body as it came. A serve stopped then leaves
// the file, and the fault store's listing names the request by its
// command. When its client goes away the inspect is cut off, answers,
// and its file is gone.
//
// The inspect is of a goal one of whose rw probes does not end in any
// time the test waits (hypothesis f(m) = g((λn. f(n))(m)): its right
// side holds its left side once the redex is reduced, and the passes of
// rw run to the goal's size), under a budget of ten minutes.
func TestServe_ACommandThatDoesNotAnswerIsInFlightInTheFaultStore(t *testing.T) {
	dataDir := t.TempDir()
	opts := initSessionEnv(dataDir)
	testEngineBundles()
	eng = engine.NewEngine(proverEnv, opts...)
	kept := engine.InFlightAfter
	engine.InFlightAfter = 50 * time.Millisecond
	t.Cleanup(func() { engine.InFlightAfter = kept })
	base := startTestServer(t)
	store := faultStoreUnder(dataDir)

	res := rpcCall(t, base, map[string]any{"cmd": "session-create"})
	sessionID, ok := res["id"].(string)
	require.True(t, ok, "session-create: %v", res)
	wide := "m"
	for range 700 {
		wide = "g(" + wide + ")"
	}
	res = rpcCall(t, base, map[string]any{"cmd": "add-goal", "session_id": sessionID, "goal": map[string]any{
		"text": "∀f:A → A. ∀g:A → A. ∀m:A. ∀P:A → bool. ∀Q:A → bool. " +
			"f(m) = g((λn:A. f(n))(m)) ⇒ P(" + wide + ") ⇒ Q(f(m)) ∧ Q(m)"}})
	goalID, ok := res["goal_id"].(string)
	require.True(t, ok, "add-goal: %v", res)
	for _, move := range []string{"strip_quant", "strip_imp", "strip_imp"} {
		res = rpcCall(t, base, map[string]any{"cmd": "apply", "session_id": sessionID, "goal_id": goalID,
			"tactic": map[string]any{"type": move}})
		require.Equal(t, true, res["success"], "apply %s: %v", move, res)
		goalID = res["state"].(map[string]any)["goals"].([]any)[0].(map[string]any)["id"].(string)
	}

	inFlight := func() []engine.FaultInFlight {
		files, err := filepath.Glob(filepath.Join(store, fmt.Sprintf("serve-%d-*.inflight", os.Getpid())))
		require.NoError(t, err)
		var running []engine.FaultInFlight
		for _, file := range files {
			data, err := os.ReadFile(file)
			if err != nil {
				continue // answered between the listing and the read
			}
			var one engine.FaultInFlight
			require.NoError(t, json.Unmarshal(data, &one))
			running = append(running, one)
		}
		return running
	}
	require.Empty(t, inFlight(), "the commands so far answered and left nothing")

	inspect, err := json.Marshal(map[string]any{"cmd": "inspect", "session_id": sessionID, "goal_id": goalID, "budget_ms": 600_000})
	require.NoError(t, err)
	ctx, hangUp := context.WithCancel(t.Context())
	defer hangUp()
	answered := make(chan struct{})
	go func() {
		defer close(answered)
		req, err := http.NewRequestWithContext(ctx, http.MethodPost, base+"/rpc", bytes.NewReader(inspect))
		if err != nil {
			return
		}
		req.Header.Set("Content-Type", "application/json")
		if resp, err := http.DefaultClient.Do(req); err == nil {
			resp.Body.Close()
		}
	}()

	require.Eventually(t, func() bool { return len(inFlight()) == 1 }, 20*time.Second, 10*time.Millisecond,
		"the inspect is on disk once it has run InFlightAfter")
	running := inFlight()[0]
	assert.Equal(t, "inspect", running.Command)
	assert.Equal(t, sessionID, running.Session)
	assert.Equal(t, goalID, running.GoalID)
	assert.Positive(t, running.LineageSeq, "the session's position, read while the inspect holds its lock")
	assert.JSONEq(t, string(inspect), string(running.RPCBody), "the body as /rpc received it")
	assert.Nil(t, running.Tactic, "an inspect runs no tactic")

	// The serve is stopped here: what it left is a dead process's.
	files, err := filepath.Glob(filepath.Join(store, fmt.Sprintf("serve-%d-*.inflight", os.Getpid())))
	require.NoError(t, err)
	require.Len(t, files, 1)
	left, err := os.ReadFile(files[0])
	require.NoError(t, err)
	stopped := exec.Command("true")
	require.NoError(t, stopped.Run())
	require.NoError(t, os.WriteFile(
		filepath.Join(store, fmt.Sprintf("serve-%d-1.inflight", stopped.ProcessState.Pid())), left, 0o644))
	view, err := engine.ViewFaults(store, false)
	require.NoError(t, err)
	require.Equal(t, 1, view.Open, "the listing: %+v", view.Faults)
	assert.Equal(t, "serve", view.Faults[0].Command)
	require.Len(t, view.Faults[0].InFlight, 1)
	assert.Equal(t, engine.FaultRowInFlight{Command: "inspect", Session: sessionID, GoalID: goalID}, view.Faults[0].InFlight[0])

	// The client goes away: the probe is cut off and the inspect answers.
	hangUp()
	select {
	case <-answered:
	case <-time.After(20 * time.Second):
		t.Fatal("the client's request did not end")
	}
	require.Eventually(t, func() bool { return len(inFlight()) == 0 }, 20*time.Second, 10*time.Millisecond,
		"the inspect was cut off when its client went away, and is in flight no longer")
	res = rpcCall(t, base, map[string]any{"cmd": "inspect", "session_id": sessionID, "goal_id": goalID, "budget_ms": 100})
	assert.NotContains(t, res, "error", "the session takes its next command: %v", res)
}
