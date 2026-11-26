// Package wallclock marks the tests whose verdict depends on the speed
// of the machine that runs them.
//
// A proof is found by a live search under a time ceiling: the refuter's
// budget for one call, the session's budget for one command. A test
// that asserts such a search closes, or that a read returns inside a
// latency bound, passes on the machine its ceilings were measured on
// and fails on a slower one, where the same search is cut off before it
// arrives. Nothing is wrong with the code under test there, and no
// member of the corpus rests on such a test: a proof replays from its
// recorded refutations and searches nothing.
//
// A test of the class opens with
//
//	wallclock.SkipOnSlowMachine(t)
//
// and is skipped where XUGO_SLOW_MACHINE=1, which CI sets for the
// runner of its tests. Everywhere else it runs. The calls are the list
// of the class: `git grep SkipOnSlowMachine`.
//
// A test joins the class when it fails on a slow machine and passes
// there with its ceilings raised and nothing else changed. A test that
// still fails then has found a defect.
package wallclock

import (
	"os"
	"testing"
)

// SkipOnSlowMachine skips t on a machine declared slow. It is the first
// statement of a test of the class, or of the one subtest that belongs
// to it.
func SkipOnSlowMachine(t testing.TB) {
	t.Helper()
	if os.Getenv("XUGO_SLOW_MACHINE") == "1" {
		t.Skip("the verdict depends on the machine's speed, and XUGO_SLOW_MACHINE=1 declares this machine slow")
	}
}
