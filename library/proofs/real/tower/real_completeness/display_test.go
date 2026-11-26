package real_completeness

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
)

// TestDisplayAbbrevsFoldChapterStatements pins the display folds
// against the REAL statement texts: the same builder output that
// becomes section statements must render with its concepts folded.
// This is the family-side half of the guarantee — the ext-side tests
// pin the matcher's semantics; this pins that the registrations in
// display.go stay in sync with the builders they parse.
func TestDisplayAbbrevsFoldChapterStatements(t *testing.T) {
	nadd := dsl.NaddType
	num := dsl.NumType
	scope := &dsl.ParseScope{ConstMetas: map[string]core.ConstTermMeta{
		"nadd_le":     dsl.NaddLeMeta,
		"nadd_mul":    dsl.NaddStarMeta,
		"nadd_of_num": core.MakeConstMeta("nadd_of_num", core.MakeFun(num, nadd)),
		"suc":         core.MakeConstMeta("suc", core.MakeFun(num, num)),
	}}

	res := dsl.ParseTermTextInScope(tightBoundText, nil, scope, core.TypeBool())
	if res.Term == nil {
		t.Fatalf("tightBoundText no longer parses standalone: %v", res.Errors)
	}
	display := ext.PrintTerm(res.Term)
	for _, want := range []string{"⟦isNumericalMax(P, r_fn)⟧", "⟦isTightBound(P, r_fn)⟧"} {
		if !strings.Contains(display, want) {
			t.Errorf("tightBoundText display missing %s:\n%s", want, display)
		}
	}
	if len(display) > 120 {
		t.Errorf("tightBoundText display did not fold below 120 chars (%d):\n%s", len(display), display)
	}
}
