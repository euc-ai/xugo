// display.go — display abbreviations for the completeness chapter's
// recurring concepts (ext.RegisterDisplayAbbrev; mechanism doc in
// ext/render.go).
//
// NaddComplete's statements are composed from the named text builders
// in complete.go; goals DISPLAYED during its construction and
// replay (session inspect, panics, dump-section) carry the same
// formulas as 100–200-character walls. The registrations here fold
// them back to their names — `⟦isNumericalMax(P₀, r_fn₀)⟧` — in
// DISPLAY output only: the terms, keys and recorded CNF trajectories
// are untouched (the fold never fires in the parser round-trip
// profiles), and the ⟦⟧ marking says the name is a display macro, not
// parseable syntax.
//
// Each pattern is PARSED FROM THE SAME BUILDER that generates the
// statements, so pattern and statement cannot drift: an edit to a
// builder either keeps both in sync or panics here at init.

package real_completeness

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
)

func init() {
	nadd := dsl.NaddType
	num := dsl.NumType
	naddBool := core.MakeFun(nadd, core.TypeBool())
	numNum := core.MakeFun(num, num)

	// The parse scope: every const the builder texts mention, at its
	// own type (name+type is what the display matcher compares, so
	// fresh metas are fine).
	scope := &dsl.ParseScope{ConstMetas: map[string]core.ConstTermMeta{
		"nadd_le":     dsl.NaddLeMeta,
		"nadd_mul":    dsl.NaddStarMeta,
		"nadd_add":    dsl.NaddPlusMeta,
		"nadd_of_num": core.MakeConstMeta("nadd_of_num", core.MakeFun(num, nadd)),
		"dest_nadd":   core.MakeConstMeta("dest_nadd", core.MakeFun(nadd, num, num)),
		"mk_nadd":     core.MakeConstMeta("mk_nadd", core.MakeFun(numNum, nadd)),
		"suc":         core.MakeConstMeta("suc", numNum),
	}}

	// Param variables — the names the folds display their argument
	// slots under. Chosen to avoid the builders' internal binders
	// (x, s, n, i).
	pv := func(name string, ty core.HolType) ext.VarTerm {
		return ext.Var(ext.TermName(name), ty).Core().(ext.VarTerm)
	}
	P := pv("P", naddBool)
	v := pv("v", num)
	sc := pv("sc", num)
	fn := pv("fn", numNum)
	M := pv("M", nadd)

	register := func(name, text string, ctx map[string]core.HolType, params ...ext.VarTerm) {
		res := dsl.ParseTermTextInScope(text, ctx, scope, core.TypeBool())
		if res.Term == nil {
			panic(fmt.Sprintf("complete display abbrev %q: pattern parse failed: %v", name, res.Errors))
		}
		ext.RegisterDisplayAbbrev(name, params, res.Term)
	}

	pvs := map[string]core.HolType{"P": naddBool, "v": num, "sc": num}
	pfn := map[string]core.HolType{"P": naddBool, "fn": numNum}
	fnCtx := map[string]core.HolType{"fn": numNum}

	// Most specific first: the fold tries patterns in registration
	// order and the first match wins.
	register("isNumericalMax", isNumericalMaxText("P", "fn"), pfn, P, fn)
	register("isTightBound", isTightBoundText("P", "fn"), pfn, P, fn)
	register("isMaxAt", isMaxAtText("P", "v", "sc"), pvs, P, v, sc)
	register("maximal", maximalText("P", "v", "sc"), pvs, P, v, sc)
	register("attainable", attainableText("P", "v", "sc"), pvs, P, v, sc)
	register("isSlopeEstimate", isSlopeEstimateText("fn"), fnCtx, fn)
	register("destComputes", destComputesText("fn"), fnCtx, fn)
	register("isUpperBound", isUpperBoundText("P", "M"),
		map[string]core.HolType{"P": naddBool, "M": nadd}, P, M)
}
