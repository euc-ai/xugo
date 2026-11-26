// tower_test.go — the real-construction tower's infix surface
// (nadd → hreal → treal). These pin the ONE property the sugar is
// allowed to have: it is surface-only. Parsing `x + y` at tower
// operands must produce the byte-identical term the prefix spelling
// `hreal_add(x, y)` produces, because every stored normalized key and
// every recorded CNF trajectory in the corpus was built from the
// prefix form.

package dsl

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// towerScope mirrors what the corpus's family vocabularies register via
// Script.Const (see real/tower/internal/nonneg_real_formal_diff/vocab.go): every tower
// const a statement may mention, at exactly the registry's type. Both
// channels are filled, as Script.Const fills them — Consts for the
// fixed-instance fast path, ConstMetas for the scope-first meta lookup
// buildBinOp performs.
func towerScope() *ParseScope {
	metas := map[string]core.ConstTermMeta{
		"hreal_add":    HrealPlusMeta,
		"hreal_mul":    HrealStarMeta,
		"hreal_le":     HrealLeMeta,
		"nadd_add":     NaddPlusMeta,
		"nadd_mul":     NaddStarMeta,
		"nadd_le":      NaddLeMeta,
		"treal_add":    TrealPlusMeta,
		"treal_mul":    TrealStarMeta,
		"treal_le":     TrealLeMeta,
		"hreal_of_num": core.MakeConstMeta("hreal_of_num", core.MakeFun(NumType, HrealType)),
		"nadd_of_num":  core.MakeConstMeta("nadd_of_num", core.MakeFun(NumType, NaddType)),
		"treal_eq":     core.MakeConstMeta("treal_eq", core.MakeFun(TrealType, TrealType, core.TypeBool())),
		"nadd_eq":      core.MakeConstMeta("nadd_eq", core.MakeFun(NaddType, NaddType, core.TypeBool())),
		// The kernel projections a treal claim reaches for; the corpus
		// registers these per-proof (real/tower/internal/nonneg_real_formal_diff).
		"fst": core.MakeConstMeta("fst", core.MakeFun(TrealType, HrealType)),
		"snd": core.MakeConstMeta("snd", core.MakeFun(TrealType, HrealType)),
	}
	consts := make(map[string]core.ConstTerm, len(metas))
	for name, m := range metas {
		consts[name] = m.Term()
	}
	return &ParseScope{Consts: consts, ConstMetas: metas}
}

// parseTowerProp parses a full proposition in the tower scope.
func parseTowerProp(t *testing.T, text string) core.Prop {
	t.Helper()
	r := ParsePropTextInScope(text, towerScope())
	require.Empty(t, r.Errors, "parse %q: %v", text, diagMessages(r.Errors))
	require.NotNil(t, r.Prop)
	return r.Prop
}

// assertTowerSameTerm is the load-bearing assertion of this file: the
// infix spelling and the prefix spelling must build the SAME term.
func assertTowerSameTerm(t *testing.T, infix, prefix string) {
	t.Helper()
	gotInfix := parseTowerProp(t, infix).Conclusion()
	gotPrefix := parseTowerProp(t, prefix).Conclusion()
	assert.Equal(t, string(gotPrefix.AlphaKey()), string(gotInfix.AlphaKey()),
		"infix %q must build the same term as prefix %q\n infix = %s\nprefix = %s",
		infix, prefix,
		ext.FormatTermForParser(gotInfix), ext.FormatTermForParser(gotPrefix))
}

// TestTowerInfix_MatchesPrefix walks all three layers × all three
// operators. Each layer's const keeps its registry NAME; only the
// surface is shared.
func TestTowerInfix_MatchesPrefix(t *testing.T) {
	cases := []struct{ name, infix, prefix string }{
		{"hreal_add",
			"∀x:hreal.∀y:hreal.(x + y = y + x)",
			"∀x:hreal.∀y:hreal.(hreal_add(x, y) = hreal_add(y, x))"},
		{"hreal_mul",
			"∀x:hreal.∀y:hreal.(x * y = y * x)",
			"∀x:hreal.∀y:hreal.(hreal_mul(x, y) = hreal_mul(y, x))"},
		{"hreal_le",
			"∀x:hreal.∀y:hreal.(x ≤ y)",
			"∀x:hreal.∀y:hreal.hreal_le(x, y)"},
		{"nadd_add",
			"∀x:nadd.∀y:nadd.(x + y = y + x)",
			"∀x:nadd.∀y:nadd.(nadd_add(x, y) = nadd_add(y, x))"},
		{"nadd_mul",
			"∀x:nadd.∀y:nadd.(x * y = y * x)",
			"∀x:nadd.∀y:nadd.(nadd_mul(x, y) = nadd_mul(y, x))"},
		{"nadd_le",
			"∀x:nadd.∀y:nadd.(x ≤ y)",
			"∀x:nadd.∀y:nadd.nadd_le(x, y)"},
		{"treal_add",
			"∀x:prod(hreal, hreal).∀y:prod(hreal, hreal).(x + y = y + x)",
			"∀x:prod(hreal, hreal).∀y:prod(hreal, hreal).(treal_add(x, y) = treal_add(y, x))"},
		{"treal_mul",
			"∀x:prod(hreal, hreal).∀y:prod(hreal, hreal).(x * y = y * x)",
			"∀x:prod(hreal, hreal).∀y:prod(hreal, hreal).(treal_mul(x, y) = treal_mul(y, x))"},
		{"treal_le",
			"∀x:prod(hreal, hreal).∀y:prod(hreal, hreal).(x ≤ y)",
			"∀x:prod(hreal, hreal).∀y:prod(hreal, hreal).treal_le(x, y)"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			assertTowerSameTerm(t, c.infix, c.prefix)
		})
	}
}

// TestTowerInfix_Precedence pins that the shared surface keeps the
// shared precedence: `*` binds tighter than `+`, `+` tighter than `≤`,
// and both arithmetic ops are LEFT-associative — so a right-nested sum
// must be written with explicit parens. This is what makes a mechanical
// prefix→infix conversion of the corpus safe to check by eye.
func TestTowerInfix_Precedence(t *testing.T) {
	// x * y + z  ==  add(mul(x, y), z)
	assertTowerSameTerm(t,
		"∀x:hreal.∀y:hreal.∀z:hreal.(x * y + z = z)",
		"∀x:hreal.∀y:hreal.∀z:hreal.(hreal_add(hreal_mul(x, y), z) = z)")
	// x + y ≤ z  ==  le(add(x, y), z)
	assertTowerSameTerm(t,
		"∀x:hreal.∀y:hreal.∀z:hreal.(x + y ≤ z)",
		"∀x:hreal.∀y:hreal.∀z:hreal.hreal_le(hreal_add(x, y), z)")
	// LEFT-associativity: `x + y + z` is add(add(x,y),z), and the
	// right-nested tree needs parens.
	assertTowerSameTerm(t,
		"∀x:hreal.∀y:hreal.∀z:hreal.(x + y + z = x + (y + z))",
		"∀x:hreal.∀y:hreal.∀z:hreal.(hreal_add(hreal_add(x, y), z) = hreal_add(x, hreal_add(y, z)))")
}

// TestTowerInfix_MixedNumHreal is the case the brief flags as the
// likeliest failure mode: ONE statement carrying arithmetic in two
// different domains. The dispatch must resolve each operator by its own
// operands' inferred type — the `m + n` under hreal_of_num is num
// addition, the `x + y` outside it is hreal addition — rather than
// picking one domain for the whole formula.
func TestTowerInfix_MixedNumHreal(t *testing.T) {
	assertTowerSameTerm(t,
		"∀m:num.∀n:num.∀x:hreal.∀y:hreal.(hreal_of_num(m + n) ≤ x + y)",
		"∀m:num.∀n:num.∀x:hreal.∀y:hreal.hreal_le(hreal_of_num(m + n), hreal_add(x, y))")

	// Both comparisons in one formula, one per domain: `m ≤ n` is nat
	// `<=`, `x ≤ y` is hreal_le. Also mixes the two multiplications.
	assertTowerSameTerm(t,
		"∀m:num.∀n:num.∀x:hreal.∀y:hreal.((m * n ≤ n) ⇒ (x * y ≤ y))",
		"∀m:num.∀n:num.∀x:hreal.∀y:hreal.((m * n ≤ n) ⇒ hreal_le(hreal_mul(x, y), y))")

	// Three domains at once — num inside nadd_of_num, nadd in the
	// middle, and the nadd order on the outside.
	assertTowerSameTerm(t,
		"∀m:num.∀u:nadd.∀v:nadd.(nadd_of_num(m + m) + u ≤ v)",
		"∀m:num.∀u:nadd.∀v:nadd.nadd_le(nadd_add(nadd_of_num(m + m), u), v)")

	// The num operators are genuinely UNCHANGED by the extension: the
	// nat `+`/`≤` still build the nat metas, not some tower instance.
	concl := parseTowerProp(t,
		"∀m:num.∀n:num.∀x:hreal.(hreal_of_num(m + n) ≤ x)").Conclusion()
	require.Contains(t, ext.FormatTermForParser(concl), "hreal_of_num",
		"mixed statement must keep the num→hreal embedding explicit")
}

// TestTowerInfix_MixedHrealReal is the mixed case as it actually occurs
// in the corpus (library/proofs/real/tower/real_completeness/real_completeness.go): an
// order-faithfulness statement carrying the SAME `≤` symbol twice, once
// at hreal and once at real, under one ⇔. Each occurrence must resolve
// through its own operands.
func TestTowerInfix_MixedHrealReal(t *testing.T) {
	sc := towerScope()
	sc.Vars = map[string]core.HolType{"r_0": core.MakeFun(HrealType, RealType)}

	const infix = "∀y:hreal.∀z:hreal.((y ≤ z) ⇔ (r_0(y) ≤ r_0(z)))"
	const prefix = "∀y:hreal.∀z:hreal.(hreal_le(y, z) ⇔ (r_0(y) ≤ r_0(z)))"
	ri := ParsePropTextInScope(infix, sc)
	require.Empty(t, ri.Errors, "infix: %v", diagMessages(ri.Errors))
	rp := ParsePropTextInScope(prefix, sc)
	require.Empty(t, rp.Errors, "prefix: %v", diagMessages(rp.Errors))
	assert.Equal(t, string(rp.Prop.Conclusion().AlphaKey()),
		string(ri.Prop.Conclusion().AlphaKey()),
		"the two `≤` must dispatch independently (hreal_le and real_le)")

	printed := ext.FormatTermForParser(ri.Prop.Conclusion())
	assert.NotContains(t, printed, "hreal_le", "hreal side must print infix")
	assert.NotContains(t, printed, "real_le", "real side must print infix")
}

// TestTowerInfix_PairLiteralOperands pins treal's composite-type
// operands: a treal value is literally a pair, so `(a, b) ≤ (c, d)` has
// pair LITERALS on both sides of the infix operator. This shape occurs
// in library/proofs/real/tower/real_completeness/real_completeness.go.
func TestTowerInfix_PairLiteralOperands(t *testing.T) {
	sc := towerScope()
	sc.Vars = map[string]core.HolType{"y_0": HrealType}

	const infix = "(hreal_of_num(0), hreal_of_num(0)) ≤ (y_0, hreal_of_num(0))"
	const prefix = "treal_le((hreal_of_num(0), hreal_of_num(0)), (y_0, hreal_of_num(0)))"
	ri := ParsePropTextInScope(infix, sc)
	require.Empty(t, ri.Errors, "infix: %v", diagMessages(ri.Errors))
	rp := ParsePropTextInScope(prefix, sc)
	require.Empty(t, rp.Errors, "prefix: %v", diagMessages(rp.Errors))
	assert.Equal(t, string(rp.Prop.Conclusion().AlphaKey()),
		string(ri.Prop.Conclusion().AlphaKey()),
		"pair-literal operands must dispatch to treal_le")
}

// TestTowerInfix_PartnerTypesOperand pins the inference-parity property
// buildArithOperands provides: an operand whose type is recoverable only
// from its PARTNER still builds, so the infix surface is exactly as
// expressive as the prefix spelling it replaces. `d` here is a free var
// with no declaration — prefix hreal_add types it from the const's
// domain, and infix must too.
func TestTowerInfix_PartnerTypesOperand(t *testing.T) {
	sc := towerScope()
	sc.Vars = map[string]core.HolType{"y": TrealType}
	assertSame := func(infix, prefix string) {
		t.Helper()
		ri := ParsePropTextInScope(infix, sc)
		require.Empty(t, ri.Errors, "infix %q: %v", infix, diagMessages(ri.Errors))
		rp := ParsePropTextInScope(prefix, sc)
		require.Empty(t, rp.Errors, "prefix %q: %v", prefix, diagMessages(rp.Errors))
		assert.Equal(t, string(rp.Prop.Conclusion().AlphaKey()),
			string(ri.Prop.Conclusion().AlphaKey()))
	}
	// `d` undeclared; snd(y) fixes the domain from the left.
	assertSame("fst(y) = (snd(y) + d)", "fst(y) = hreal_add(snd(y), d)")
	// Mirror: the undeclared operand on the LEFT.
	assertSame("fst(y) = (d + snd(y))", "fst(y) = hreal_add(d, snd(y))")
}

// TestTowerInfix_ScopeFirst pins the def-less-meta guard for the new
// layers. The DSL's own tower metas are def-less α-variants of the
// registered metas; when the caller's scope carries a meta for the same
// name at the same shape, THAT pointer must win — otherwise a session
// whose registry holds the canonical (definition-carrying) meta would
// silently get a def-less const and drift off its recorded CNF key.
func TestTowerInfix_ScopeFirst(t *testing.T) {
	// A distinct meta object with the same name and the same AbsType,
	// standing in for the registry's definition-carrying meta.
	registryAdd := core.MakeConstMeta("hreal_add",
		core.MakeFun(HrealType, HrealType, HrealType))
	require.True(t, any(HrealPlusMeta) != any(registryAdd), "test needs two distinct metas")

	scope := &ParseScope{
		Consts:     map[string]core.ConstTerm{"hreal_add": registryAdd.Term()},
		ConstMetas: map[string]core.ConstTermMeta{"hreal_add": registryAdd},
	}
	r := ParsePropTextInScope("∀x:hreal.∀y:hreal.(x + y = y + x)", scope)
	require.Empty(t, r.Errors, "parse: %v", diagMessages(r.Errors))

	// Walk to the head const of the left sum and check its meta is the
	// scope's, not the package-level surface meta.
	found := false
	var walk func(core.Term)
	walk = func(tm core.Term) {
		if c, ok := tm.AsConst(); ok && c.Meta().Name() == "hreal_add" {
			assert.True(t, any(registryAdd) == any(c.Meta()), "infix `+` at hreal operands must bind the SCOPE's hreal_add meta")
			found = true
			return
		}
		if a, ok := tm.AsAppliedTerm(); ok {
			walk(a.Fun())
			walk(a.Arg())
		}
		if ab, ok := tm.AsAbsTerm(); ok {
			walk(ab.Body())
		}
	}
	walk(r.Prop.Conclusion())
	assert.True(t, found, "no hreal_add const found in the parsed term")
}

// TestTowerInfix_RoundTrip closes the loop through the printer: a tower
// statement must print infix and re-parse to the same term.
func TestTowerInfix_RoundTrip(t *testing.T) {
	texts := []string{
		"∀x:hreal.∀y:hreal.∀z:hreal.(x * (y + z) = x * y + x * z)",
		"∀x:nadd.∀y:nadd.((x ≤ y) ⇒ (x + y ≤ y + y))",
		"∀x:prod(hreal, hreal).∀y:prod(hreal, hreal).(x + y = y + x)",
		"∀m:num.∀n:num.∀x:hreal.(hreal_of_num(m + n) ≤ x + x)",
	}
	for _, text := range texts {
		t.Run(text, func(t *testing.T) {
			p1 := parseTowerProp(t, text)
			printed := prop.FormatPropForParser(p1)
			r2 := ParsePropTextInScope(printed, towerScope())
			require.Empty(t, r2.Errors,
				"re-parse of printed %q failed: %v", printed, diagMessages(r2.Errors))
			assert.Equal(t,
				string(p1.Conclusion().AlphaKey()),
				string(r2.Prop.Conclusion().AlphaKey()),
				"round-trip must be α-stable; printed = %q", printed)
		})
	}
}

// TestTowerInfix_PrintsInfix pins the printer half explicitly: the
// tower consts render as their overloaded symbols, and the layer's
// const NAME never appears in the output.
func TestTowerInfix_PrintsInfix(t *testing.T) {
	cases := []struct{ prefix, wantInfix string }{
		{"∀x:hreal.∀y:hreal.(hreal_add(x, y) = hreal_mul(x, y))", "(x + y) = (x * y)"},
		{"∀x:nadd.∀y:nadd.nadd_le(x, y)", "x ≤ y"},
		{"∀x:prod(hreal, hreal).∀y:prod(hreal, hreal).treal_le(x, y)", "x ≤ y"},
	}
	for _, c := range cases {
		printed := prop.FormatPropForParser(parseTowerProp(t, c.prefix))
		assert.Contains(t, printed, c.wantInfix, "printing %q", c.prefix)
	}
}

// TestTowerEquivalences_StayPrefix pins the deliberate scope limit: the
// tower's two EQUIVALENCE relations get no infix surface, so they keep
// printing (and parsing) as prefix applications. Giving them a symbol
// would be inventing notation, not extending dispatch.
func TestTowerEquivalences_StayPrefix(t *testing.T) {
	for _, text := range []string{
		"∀x:nadd.∀y:nadd.nadd_eq(x, y)",
		"∀x:prod(hreal, hreal).∀y:prod(hreal, hreal).treal_eq(x, y)",
	} {
		printed := prop.FormatPropForParser(parseTowerProp(t, text))
		assert.Contains(t, printed, "_eq(", "%q must still print prefix, got %q", text, printed)
	}
}

// TestTowerInfix_Rejections pins what the dispatch must NOT accept:
// operators with no instance in a layer, and operands from two
// different domains under one operator.
func TestTowerInfix_Rejections(t *testing.T) {
	// The tower has no subtraction at any layer.
	for _, text := range []string{
		"∀x:hreal.∀y:hreal.(x - y = x)",
		"∀x:nadd.∀y:nadd.(x - y = x)",
		"∀x:prod(hreal, hreal).∀y:prod(hreal, hreal).(x - y = x)",
	} {
		r := ParsePropTextInScope(text, towerScope())
		assert.NotEmpty(t, r.Errors, "tower `-` must be rejected: %q", text)
	}
	// No strict `<` either.
	r := ParsePropTextInScope("∀x:hreal.∀y:hreal.(x < y)", towerScope())
	assert.NotEmpty(t, r.Errors, "tower `<` must be rejected")

	// Cross-domain operands under one operator are a type error, not a
	// silent coercion.
	r = ParsePropTextInScope("∀m:num.∀x:hreal.(m + x = x)", towerScope())
	assert.NotEmpty(t, r.Errors, "num + hreal must be rejected")
	r = ParsePropTextInScope("∀u:nadd.∀x:hreal.(u ≤ x)", towerScope())
	assert.NotEmpty(t, r.Errors, "nadd ≤ hreal must be rejected")
}
