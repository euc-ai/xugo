package main

import (
	"context"
	"fmt"
	"net"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/euc-ai/xugo/library/index"
	"github.com/euc-ai/xugo/library/visualize"
)

// browsePort is the port `xugo browse` serves on where none is asked
// for: one address to open and to keep.
const browsePort = 8717

// parseBrowseArgs reads browse's own flags: the port (0 has the system
// pick one), the time with no request after which the command ends (0
// for never), the library/proofs directory, and the directory to write
// the site into in place of serving it.
func parseBrowseArgs(args []string) (port int, timeout time.Duration, root, write string, err error) {
	port = browsePort
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
				return 0, 0, "", "", fmt.Errorf("bad --port: %v", err)
			}
			i = next
		} else if v, next, ok := value(i, "--timeout"); ok {
			if timeout, err = time.ParseDuration(v); err != nil {
				return 0, 0, "", "", fmt.Errorf("bad --timeout: %v", err)
			}
			i = next
		} else if v, next, ok := value(i, "--root"); ok {
			root, i = v, next
		} else if v, next, ok := value(i, "--write"); ok {
			write, i = v, next
		} else {
			return 0, 0, "", "", fmt.Errorf("browse: unknown argument %q — browse takes --port N, --timeout D, --root DIR and --write DIR", args[i])
		}
	}
	return port, timeout, root, write, nil
}

// BrowseOutput is the line `xugo browse` prints once it serves: the
// address to open, and the size of the corpus it serves.
type BrowseOutput struct {
	Status   string `json:"status"`
	URL      string `json:"url"`
	Families int    `json:"families"`
	Members  int    `json:"members"`
}

// BrowseWritten is the line `xugo browse --write` prints: the directory
// the site is written into, and the size of the site and of the corpus.
type BrowseWritten struct {
	Status   string `json:"status"`
	Dir      string `json:"dir"`
	Files    int    `json:"files"`
	Bytes    int64  `json:"bytes"`
	Families int    `json:"families"`
	Members  int    `json:"members"`
}

// cmdBrowse serves the corpus to browse (library/visualize.Site): the
// family graph, any member's graph drawn as it is asked for, and a
// search of the members, on this machine alone.
//
//	xugo browse [--port N] [--timeout D] [--root DIR]
//	xugo browse --write DIR [--root DIR]
//
// It reads the corpus, prints the address it serves at as a line of
// JSON, and serves until it is interrupted — or, with --timeout, until
// no page has been asked for that long. With --write it serves nothing:
// it writes the same site into DIR, every member's page with it, to be
// published as the files they are. --root DIR names the library/proofs
// directory when the working directory is not under the module.
func cmdBrowse(args []string) {
	port, timeout, root, write, err := parseBrowseArgs(args)
	if err != nil {
		fatal("%v", err)
	}
	if root == "" {
		mod, err := moduleRoot()
		if err != nil {
			fatal("browse: %v (pass --root, the library/proofs directory)", err)
		}
		root = filepath.Join(mod, "library", "proofs")
	}
	corpus, err := index.Load(root)
	if err != nil {
		fatal("browse: %v", err)
	}
	if write != "" {
		size, err := visualize.NewSite(corpus, "xugo browse --write").Write(write)
		if err != nil {
			fatal("browse: %v", err)
		}
		writeJSON(BrowseWritten{Status: "written", Dir: write, Files: size.Files, Bytes: size.Bytes,
			Families: len(corpus.Families), Members: len(corpus.Members)})
		return
	}
	ln, err := net.Listen("tcp", fmt.Sprintf("127.0.0.1:%d", port))
	if err != nil {
		fatal("browse: %v (another port: xugo browse --port N; 0 has the system pick one)", err)
	}

	server := &http.Server{}
	stop := func(why string) {
		fmt.Fprintf(os.Stderr, "xugo browse: %s, shutting down\n", why)
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()
		server.Shutdown(ctx)
	}
	site := visualize.NewSite(corpus, "xugo browse")
	server.Handler = site
	if timeout > 0 {
		var mu sync.Mutex
		idle := time.AfterFunc(timeout, func() { stop(fmt.Sprintf("no page asked for in %s", timeout)) })
		server.Handler = http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			mu.Lock()
			idle.Reset(timeout)
			mu.Unlock()
			site.ServeHTTP(w, r)
		})
	}

	writeJSON(BrowseOutput{
		Status:   "listening",
		URL:      fmt.Sprintf("http://127.0.0.1:%d/", ln.Addr().(*net.TCPAddr).Port),
		Families: len(corpus.Families),
		Members:  len(corpus.Members),
	})

	signals := make(chan os.Signal, 1)
	signal.Notify(signals, syscall.SIGINT, syscall.SIGTERM)
	go func() { stop(fmt.Sprintf("%s received", <-signals)) }()

	if err := server.Serve(ln); err != nil && err != http.ErrServerClosed {
		fatal("browse: %v", err)
	}
}
