// overrun.go — a run its context ended, and a run its budget did not
// hold.
//
// A tactic run its context ends inside a unit of work unwinds by a
// utils.Cut. That is no fault and no failure of the tactic: the run is
// answered as cut off (_CutOffError), and nothing is recorded.
//
// A run that ends well past its deadline, cut off or not, is another
// matter: some unit of its work read no clock for that long, which is a
// defect of the engine whatever the run was looking for. The engine
// writes it down in the fault store as an overrun. The record locks no
// session, since the run did answer; `xugo faults` lists it until it is
// acknowledged, like any other.

package engine

import (
	"errors"
	"fmt"
	"os"
	"time"
	"uuid"

	"github.com/euc-ai/xugo/utils"
)

// _CutOffError is the error of a tactic run its context ended inside a
// unit of work: the run did not reach an answer.
type _CutOffError struct {
	tactic string
	cut    utils.Cut
	// stack is the stack of the poll that raised the cut.
	stack string
}

// cutStackOf is the stack of the cut err reports, "" where err is no
// cut-off.
func cutStackOf(err error) string {
	var cutOff _CutOffError
	if errors.As(err, &cutOff) {
		return cutOff.stack
	}
	return ""
}

func (c _CutOffError) Error() string {
	return fmt.Sprintf("%s was cut off %s — its context is done (%v): the request's deadline or budget passed, "+
		"or its caller went away. The run did not reach its end, so this is no evidence that the tactic does "+
		"not apply.", c.tactic, c.cut.Where, c.cut.Cause)
}

// overrunRecordAfter is how far past its deadline a run ends before the
// engine records an overrun. A unit in flight at the deadline finishes,
// so every run ends a little late; seconds late on a loaded machine is
// still one slow unit. Past this, a unit read no clock. A variable so
// that a test can lower it.
var overrunRecordAfter = 5 * time.Second

// FaultOverrun is what an overrun record holds beside the request: the
// work that ran late, the budget it had, and how late it ended.
type FaultOverrun struct {
	// What names the work: the tactic run, or a probe of inspect.
	What     string `json:"what"`
	BudgetMs int    `json:"budget_ms,omitempty"`
	// LateMs is how long after its deadline the work ended.
	LateMs int `json:"late_ms"`
	// CutOff says the work was ended by a cut; false for work that
	// returned an answer late.
	CutOff bool `json:"cut_off,omitempty"`
}

// overrunObserver, when set, is handed every overrun record: a test
// reads the records its run made.
var overrunObserver func(*FaultRecord)

// noteOverrun records that the work of the scope's request named what
// ended past deadline, if it ended overrunRecordAfter past it. stack is
// the stack of the cut that ended the work, "" for work that returned.
// The session is not locked. The session lock is held by the caller.
func (e *Engine) noteOverrun(scope *_FaultScope, what string, deadline time.Time, stack string) {
	late := time.Since(deadline)
	if deadline.IsZero() || late <= overrunRecordAfter {
		return
	}
	now := time.Now().UTC()
	record := scope.record(nil, "")
	record.ID = now.Format("20060102T150405Z") + "-" + uuid.New().String()[:8]
	record.At = now
	record.Goroutine = "request"
	record.Site = ""
	record.Stack = stack
	record.Overrun = &FaultOverrun{
		What:     what,
		BudgetMs: scope.budgetMs,
		LateMs:   int(late.Milliseconds()),
		CutOff:   stack != "",
	}
	record.Panic = fmt.Sprintf("overrun: %s ended %d ms past its deadline: a unit of its work read no clock for that long",
		what, late.Milliseconds())
	if overrunObserver != nil {
		overrunObserver(&record)
	}
	where := "(no fault store)"
	if e.faultStore != "" {
		path := faultRecordPath(e.faultStore, record.ID)
		if err := writeFaultRecord(path, &record); err != nil {
			fmt.Fprintf(os.Stderr, "[fault] %s: the record was not written: %v\n", record.ID, err)
		} else {
			where = path
		}
	}
	fmt.Fprintf(os.Stderr, "[fault] %s in %s: %s\n  record: %s\n", record.ID, record.Command, record.Panic, where)
}
