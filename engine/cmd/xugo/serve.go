package main

import (
	"context"
	json "encoding/json/v2"
	"errors"
	"fmt"
	"github.com/euc-ai/xugo/engine"
	"github.com/euc-ai/xugo/library/registry"
	"io"
	"net"
	"net/http"
	"os"
	"os/signal"
	"reflect"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
)

// parseServeArgs reads serve's own flags. Anything else is refused: a
// global flag is read only before the subcommand, so `serve --data-dir
// D` would otherwise start a server with no session store and say
// nothing.
func parseServeArgs(args []string) (port int, portFile string, timeout time.Duration, err error) {
	timeout = 10 * time.Minute
	value := func(i int, flag string) (string, int, bool) {
		switch {
		case args[i] == flag && i+1 < len(args):
			return args[i+1], i + 1, true
		case strings.HasPrefix(args[i], flag+"="):
			return strings.TrimPrefix(args[i], flag+"="), i, true
		}
		return "", i, false
	}
	for i := 0; i < len(args); i++ {
		if v, next, ok := value(i, "--port"); ok {
			if port, err = strconv.Atoi(v); err != nil {
				return 0, "", 0, fmt.Errorf("bad --port: %v", err)
			}
			i = next
		} else if v, next, ok := value(i, "--port-file"); ok {
			portFile, i = v, next
		} else if v, next, ok := value(i, "--timeout"); ok {
			if timeout, err = time.ParseDuration(v); err != nil {
				return 0, "", 0, fmt.Errorf("bad --timeout: %v", err)
			}
			i = next
		} else {
			return 0, "", 0, fmt.Errorf("serve: unknown argument %q — serve takes --port, --port-file and --timeout, each with a value; "+
				"a global flag goes before the subcommand (xugo --data-dir DIR serve …)", args[i])
		}
	}
	return port, portFile, timeout, nil
}

// cmdServe starts an HTTP server that exposes the engine via a single /rpc endpoint.
// Sessions persist in memory for the server's lifetime, enabling the multi-step
// session workflow (session-create → add-goal → inspect → explore → apply → ...)
// that is impossible with the one-command-per-process CLI model.
func cmdServe(args []string) {
	port, portFile, timeout, err := parseServeArgs(args)
	if err != nil {
		fatal("%v", err)
	}

	// Bind to the requested port (0 = auto-select).
	ln, err := net.Listen("tcp", fmt.Sprintf("127.0.0.1:%d", port))
	if err != nil {
		fatal("listen: %v", err)
	}
	actualPort := ln.Addr().(*net.TCPAddr).Port

	// The fault store keeps what this process would leave if it died
	// with no recover to write a record (engine/fault_crash.go): what an
	// earlier serve left that way becomes a record now.
	if dataDirFlag != "" {
		store := faultStoreUnder(dataDirFlag)
		if err := engine.CollectCrashes(store); err != nil {
			fmt.Fprintf(os.Stderr, "xugo serve: warning: reading what an earlier serve left in %s: %v\n", store, err)
		}
		endReport, err := engine.OpenCrashReport(store)
		if err != nil {
			fatal("open the crash report under %s: %v", store, err)
		}
		defer endReport()
	}

	// Inactivity timer — shuts down the server after `timeout` of no requests.
	var timerMu sync.Mutex
	timer := time.AfterFunc(timeout, func() {
		fmt.Fprintf(os.Stderr, "xugo serve: inactivity timeout (%s), shutting down\n", timeout)
		os.Exit(0)
	})
	resetTimer := func() {
		timerMu.Lock()
		timer.Reset(timeout)
		timerMu.Unlock()
	}

	server := &http.Server{Handler: serveHandler(resetTimer)}

	// Announce the port, and the registry this binary linked — the
	// `registry-fingerprint` RPC answers the same pair, so a log line
	// and a live serve can be compared against a fresh build.
	entries, digest := registry.Fingerprint()
	startupMsg, _ := json.Marshal(map[string]any{
		"status":               "listening",
		"port":                 actualPort,
		"registry_entries":     entries,
		"registry_fingerprint": digest,
	})
	fmt.Println(string(startupMsg))

	if portFile != "" {
		if err := os.WriteFile(portFile, []byte(strconv.Itoa(actualPort)), 0644); err != nil {
			fmt.Fprintf(os.Stderr, "xugo serve: warning: cannot write port file: %v\n", err)
		}
	}

	// Graceful shutdown on signal. The line names the signal, so a log
	// that ends here says the process was SIGNALLED — by whom is the
	// reader's next question — and is never mistaken for the inactivity
	// timeout, which reports itself above.
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)
	go func() {
		sig := <-sigCh
		fmt.Fprintf(os.Stderr, "xugo serve: %s received, shutting down\n", sig)
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()
		server.Shutdown(ctx)
	}()

	if err := server.Serve(ln); err != nil && err != http.ErrServerClosed {
		fatal("serve: %v", err)
	}
}

// maxRPCBody is the most a request's body may hold. A session's requests
// are a goal's text or a tactic with its premises, kilobytes at most;
// the cap is there so that no request makes the server hold more.
const maxRPCBody = 1 << 20

// serveHandler is the server's HTTP surface: GET /health, and POST /rpc
// through which every command goes. touch is called for each request it
// answers — the inactivity timer's reset.
func serveHandler(touch func()) http.Handler {
	mux := http.NewServeMux()

	// Health check.
	mux.HandleFunc("GET /health", func(w http.ResponseWriter, r *http.Request) {
		touch()
		w.Header().Set("Content-Type", "application/json")
		w.Write([]byte(`{"status":"ok"}` + "\n"))
	})

	// RPC endpoint — all commands go through here.
	mux.HandleFunc("POST /rpc", func(w http.ResponseWriter, r *http.Request) {
		touch()
		w.Header().Set("Content-Type", "application/json")

		// A panic that leaves a command is an engine fault: recorded with
		// the request and answered as HTTP 500 carrying the record's mark
		// (answerPanic). Without the recover net/http's own closes the
		// connection, and the client sees an empty reply.
		var cmd string
		var body []byte
		defer func() {
			if rec := recover(); rec != nil {
				answerPanic(w, cmd, body, rec)
			}
		}()

		body, err := io.ReadAll(http.MaxBytesReader(w, r.Body, maxRPCBody))
		if err != nil {
			var tooLarge *http.MaxBytesError
			if errors.As(err, &tooLarge) {
				writeHTTPError(w, http.StatusRequestEntityTooLarge,
					"the request body is over the %d bytes /rpc reads", tooLarge.Limit)
				return
			}
			writeHTTPError(w, http.StatusBadRequest, "read body: %v", err)
			return
		}

		var envelope struct {
			Cmd string `json:"cmd"`
		}
		if err := json.Unmarshal(body, &envelope); err != nil {
			writeHTTPError(w, http.StatusBadRequest, "parse cmd: %v", err)
			return
		}
		if envelope.Cmd == "" {
			writeHTTPError(w, http.StatusBadRequest, "missing 'cmd' field")
			return
		}
		cmd = envelope.Cmd

		// The request is kept in the fault store once its command has
		// run a while (engine.KeepInFlight), so a serve stopped during
		// a command that never answers leaves the request behind.
		ctx, answered := eng.KeepInFlight(engine.WithRPCRequest(r.Context(), body), cmd, body)
		defer answered()
		result, err := rpcDispatch(ctx, cmd, body)
		if err != nil {
			writeHTTPErrorWith(w, http.StatusBadRequest, result, err)
			return
		}

		data, err := json.Marshal(result)
		if err != nil {
			writeHTTPError(w, http.StatusInternalServerError, "marshal result: %v", err)
			return
		}
		w.Write(data)
		w.Write([]byte("\n"))
	})

	return localOnly(mux)
}

// answerPanic answers a request whose command panicked with rec: the
// panic is an engine fault, recorded with the request body
// (engine.RecordCommandFault), and the reply is HTTP 500 with the
// record's mark beside the error. It is called from the deferred
// function that recovered rec.
func answerPanic(w http.ResponseWriter, cmd string, body []byte, rec any) {
	fault := eng.RecordCommandFault(cmd, body, rec)
	writeHTTPErrorWith(w, http.StatusInternalServerError,
		map[string]any{"engine_fault": fault}, fmt.Errorf("panic: %v", rec))
}

// localOnly admits what a program on this machine sends and refuses
// what a web page can make a browser send. The server has no
// authentication: its guard is that it listens on the loopback
// interface, and a browser on this machine is inside that guard.
//
// A page of another origin can have the browser POST here, unseen by
// its user. The browser marks such a request — Sec-Fetch-Site, or an
// Origin that is not the Host — and http.CrossOriginProtection reads
// the mark. A page whose own name has been pointed at 127.0.0.1 is
// same-origin to the browser and carries no such mark; it is known by
// the Host it sends, which is that name. A request with neither sign
// is a program's: curl, an agent.
func localOnly(next http.Handler) http.Handler {
	crossOrigin := http.NewCrossOriginProtection()
	refuse := func(w http.ResponseWriter, format string, args ...any) {
		w.Header().Set("Content-Type", "application/json")
		writeHTTPError(w, http.StatusForbidden, format, args...)
	}
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if !isLoopbackHost(r.Host) {
			refuse(w, "Host %q is not this machine — the server answers only a request addressed to 127.0.0.1 or localhost", r.Host)
			return
		}
		if err := crossOrigin.Check(r); err != nil {
			refuse(w, "a request from a web page of another origin is refused (%v) — the server is driven by programs on this machine, never by a browser", err)
			return
		}
		next.ServeHTTP(w, r)
	})
}

// isLoopbackHost reports whether a Host header names the loopback
// interface: localhost or a loopback address, with a port or without.
func isLoopbackHost(hostport string) bool {
	host := hostport
	if h, _, err := net.SplitHostPort(hostport); err == nil {
		host = h
	}
	host = strings.TrimSuffix(strings.TrimPrefix(host, "["), "]")
	if strings.EqualFold(host, "localhost") {
		return true
	}
	ip := net.ParseIP(host)
	return ip != nil && ip.IsLoopback()
}

func writeHTTPError(w http.ResponseWriter, code int, format string, args ...any) {
	w.WriteHeader(code)
	msg := fmt.Sprintf(format, args...)
	data, _ := json.Marshal(map[string]string{"error": msg})
	w.Write(data)
	w.Write([]byte("\n"))
}

// writeHTTPErrorWith writes err as writeHTTPError does and, when the
// command returned a result beside it — emit-section's rendered member
// beside its CNF collection error — the result's fields in the same
// object, under the error's status.
func writeHTTPErrorWith(w http.ResponseWriter, code int, result any, err error) {
	if result == nil || (reflect.ValueOf(result).Kind() == reflect.Pointer && reflect.ValueOf(result).IsNil()) {
		writeHTTPError(w, code, "%v", err)
		return
	}
	encoded, mErr := json.Marshal(result)
	if mErr != nil {
		writeHTTPError(w, http.StatusInternalServerError, "marshal result: %v", mErr)
		return
	}
	var fields map[string]any
	if uErr := json.Unmarshal(encoded, &fields); uErr != nil {
		writeHTTPError(w, http.StatusInternalServerError, "the result is not an object: %v", uErr)
		return
	}
	fields["error"] = err.Error()
	data, mErr := json.Marshal(fields)
	if mErr != nil {
		writeHTTPError(w, http.StatusInternalServerError, "marshal result: %v", mErr)
		return
	}
	w.WriteHeader(code)
	w.Write(data)
	w.Write([]byte("\n"))
}
