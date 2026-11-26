package tactic

import (
	"os"
	"testing"
)

// TestMain holds every reconstruction the package's tests build to all
// of what a reconstruction is handed: a child closed at its conclusion
// from all its hypotheses, which every process checks at the step's
// creation, and a child closed by a stronger theorem, by contradiction
// or from no hypothesis (HoldStrongerCloses).
func TestMain(m *testing.M) {
	os.Exit(HoldStrongerCloses(m.Run))
}
