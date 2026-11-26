package proof

import (
	"sync"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
)

// A guard an instance spells at a record projection of a packed value —
// the law `∀t. t ∈ {s | src(s) ∈ O ∧ …} ⇒ …` grounded at the framed
// datum `zz_mk_m(x, y, f)` — is supplied by a context that holds the
// parts, `x ∈ O ∧ y ∈ O ∧ f ∈ H(x, y)`, and the discharge proves it
// in the reading that accepted it: the leaf read through its
// memberships and then its record projections (readLeaf), never a
// guard accepted in one reading and proved in another. The shape of
// category.FunctorFromHomIff's framed hom datum (#1445), where the
// acceptance proved the guard in the instance normal form and the
// discharge, reading memberships alone, met
// "antecedent accepted as resident is not".

var (
	recordGuardOnce  sync.Once
	recordGuardMetas map[string]core.ConstTermMeta
)

// recordGuardVocabulary is the set-builder vocabulary with its
// definitions, a record zz_mk_m packing three numbers into a num → num
// value, and its three projections — minted once, so the cases and the
// record equations spell one constant.
func recordGuardVocabulary() map[string]core.ConstTermMeta {
	recordGuardOnce.Do(func() {
		num := ext.NumType
		value := core.MakeFun(num, num)
		metas := map[string]core.ConstTermMeta{}
		for name, m := range setBuilderVocabulary() {
			metas[name] = m
		}
		metas["zz_mk_m"] = core.MakeConstMeta("zz_mk_m", core.MakeFun(num, num, num, value))
		for _, name := range []string{"zz_m_src", "zz_m_tgt", "zz_m_map"} {
			metas[name] = core.MakeConstMeta(core.TermName(name), core.MakeFun(value, num))
		}
		recordGuardMetas = metas
	})
	return recordGuardMetas
}

// recordGuardScope is recordGuardVocabulary with the variables of the
// cases.
func recordGuardScope() *dsl.ParseScope {
	num := ext.NumType
	value := core.MakeFun(num, num)
	return &dsl.ParseScope{
		Vars: map[string]core.HolType{
			"O": core.MakeFun(num, core.TypeBool()),
			"H": core.MakeFun(num, num, num, core.TypeBool()),
			"Q": core.MakeFun(num, core.TypeBool()),
			"R": core.MakeFun(value, core.TypeBool()),
			"p": core.MakeFun(num, num, num, num),
			"x": num, "y": num, "f": num,
		},
		ConstMetas: recordGuardVocabulary(),
	}
}

// installTripleRecord installs the three projection equations as record
// equations for the test's duration.
func installTripleRecord(t *testing.T) {
	scope := recordGuardScope()
	equations := map[string]core.ThmCert{}
	var records []tactic.RecordEquation
	for _, pr := range []struct{ head, part string }{{"zz_m_src", "a"}, {"zz_m_tgt", "b"}, {"zz_m_map", "c"}} {
		res := dsl.ParsePropTextInScope("∀a b c:num. "+pr.head+"(zz_mk_m(a, b, c)) = "+pr.part, scope)
		require.Empty(t, res.Errors, "%v", res.Errors)
		entry := pr.head + "_mk"
		equations[entry] = core.TestThm(res.Prop.Conclusion())
		records = append(records, tactic.RecordEquation{Head: pr.head, Constructor: "zz_mk_m", Entry: entry, Statement: res.Prop})
	}
	tactic.InstallRecordNormal(records, nil, func(entry string) *prop.PropWrapper {
		eq, ok := equations[entry]
		require.True(t, ok, "no record equation %s", entry)
		return prop.WrapProp(eq)
	})
	t.Cleanup(func() { tactic.InstallRecordNormal(nil, nil, nil) })
}

func TestApplyClose_GuardAtAProjectionSuppliedByTheParts(t *testing.T) {
	installTripleRecord(t)
	closes := func(text string, strips int) (bool, string, *GoalStackNode) {
		t.Helper()
		res := dsl.ParsePropTextInScope(text, recordGuardScope())
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		sec := NewScript(makeStepTestEnv()).Section(res.Prop)
		for range strips {
			sec.Do(StripImp())
		}
		var claims []*GoalStackNode
		closed, miss := applyClose(sec, &claims, nil, rungOpts{depth: antecedentApplies})
		return closed, miss, sec
	}
	for _, c := range []struct{ why, text string }{
		{"a guard at a projection, the part resident",
			"(Q(zz_m_src(zz_mk_m(x, y, f))) ⇒ R(zz_mk_m(x, y, f))) ⇒ Q(x) ⇒ R(zz_mk_m(x, y, f))"},
		{"the framed datum's membership, the goal at the projections",
			"(zz_mk_m(x, y, f) ∈ {s:(num → num) | zz_m_src(s) ∈ O ∧ zz_m_tgt(s) ∈ O ∧ zz_m_map(s) ∈ H(zz_m_src(s), zz_m_tgt(s))} ⇒ " +
				"p(zz_m_src(zz_mk_m(x, y, f)), zz_m_tgt(zz_mk_m(x, y, f)), zz_m_map(zz_mk_m(x, y, f))) ∈ Q) ⇒ " +
				"x ∈ O ∧ y ∈ O ∧ f ∈ H(x, y) ⇒ p(zz_m_src(zz_mk_m(x, y, f)), zz_m_tgt(zz_mk_m(x, y, f)), zz_m_map(zz_mk_m(x, y, f))) ∈ Q"},
		{"the framed datum's membership, the goal at the parts",
			"(zz_mk_m(x, y, f) ∈ {s:(num → num) | zz_m_src(s) ∈ O ∧ zz_m_tgt(s) ∈ O ∧ zz_m_map(s) ∈ H(zz_m_src(s), zz_m_tgt(s))} ⇒ " +
				"p(zz_m_src(zz_mk_m(x, y, f)), zz_m_tgt(zz_mk_m(x, y, f)), zz_m_map(zz_mk_m(x, y, f))) ∈ Q) ⇒ " +
				"x ∈ O ∧ y ∈ O ∧ f ∈ H(x, y) ⇒ p(x, y, f) ∈ Q"},
	} {
		closed, miss, sec := closes(c.text, 2)
		require.True(t, closed, "%s: %s", c.why, miss)
		require.True(t, sec.Proved(), "%s: the leaf is closed", c.why)
		tree := describeTree(sec)
		require.Contains(t, tree, "RecordRead", "%s: the discharge read the leaf's record projections:\n%s", c.why, tree)
	}
}
