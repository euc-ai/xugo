package wallclock

import "testing"

// TestSkipOnSlowMachine: a marked test is skipped where the variable is
// exactly "1" and runs under every other value, unset among them.
func TestSkipOnSlowMachine(t *testing.T) {
	for _, tc := range []struct {
		value   string
		skipped bool
	}{
		{"", false},
		{"0", false},
		{"1", true},
	} {
		t.Setenv("XUGO_SLOW_MACHINE", tc.value)
		ran, skipped := false, false
		t.Run("value="+tc.value, func(t *testing.T) {
			defer func() { skipped = t.Skipped() }()
			SkipOnSlowMachine(t)
			ran = true
		})
		if skipped != tc.skipped || ran == tc.skipped {
			t.Errorf("XUGO_SLOW_MACHINE=%q: skipped=%v, ran=%v; want skipped=%v", tc.value, skipped, ran, tc.skipped)
		}
	}
}
