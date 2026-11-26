package main

import (
	"os"
	"strings"

	"github.com/euc-ai/xugo/engine"
)

// cmdFaults is `xugo --data-dir DIR faults`: the engine faults on
// record under the data dir (engine/fault.go), read from the store with
// no engine and no serve.
//
//	faults [--all]         list the open faults; exit 1 while there is one
//	faults show ID         print one record whole
//	faults ack ID --note T acknowledge one, saying what was done
func cmdFaults(args []string) {
	if dataDirFlag == "" {
		fatal("faults reads the fault store of a data dir: xugo --data-dir DIR faults")
	}
	store := faultStoreUnder(dataDirFlag)
	if len(args) > 0 && args[0] == "show" {
		if len(args) != 2 {
			fatal("faults show takes the fault's id: xugo --data-dir DIR faults show ID")
		}
		record, err := engine.ReadFault(store, args[1])
		if err != nil {
			fatal("%v", err)
		}
		writeJSON(record)
		return
	}
	if len(args) > 0 && args[0] == "ack" {
		id, note := "", ""
		for i := 1; i < len(args); i++ {
			switch {
			case args[i] == "--note" && i+1 < len(args):
				note = args[i+1]
				i++
			case strings.HasPrefix(args[i], "--note="):
				note = strings.TrimPrefix(args[i], "--note=")
			case id == "" && !strings.HasPrefix(args[i], "--"):
				id = args[i]
			default:
				fatal("faults ack: unknown argument %s (xugo --data-dir DIR faults ack ID --note TEXT)", args[i])
			}
		}
		if id == "" {
			fatal("faults ack takes the fault's id: xugo --data-dir DIR faults ack ID --note TEXT")
		}
		record, err := engine.AcknowledgeFault(store, id, note)
		if err != nil {
			fatal("faults ack: %v", err)
		}
		writeJSON(map[string]any{"id": record.ID, "ack": record.Ack})
		return
	}

	all := false
	for _, arg := range args {
		if arg != "--all" {
			fatal("faults: unknown argument %s (faults [--all] | faults show ID | faults ack ID --note TEXT)", arg)
		}
		all = true
	}
	view, err := engine.ViewFaults(store, all)
	if err != nil {
		fatal("faults: %v", err)
	}
	writeJSON(view)
	if view.Open > 0 {
		// An open fault is the listing's failure: a shell step that runs
		// the listing stops on it.
		traceEntry.ExitCode = 1
		writeTrace()
		os.Exit(1)
	}
}
