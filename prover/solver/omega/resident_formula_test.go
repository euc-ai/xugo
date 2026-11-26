package omega

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// A formula a hypothesis asserts reads ⊤, one whose negation a
// hypothesis asserts reads ⊥ — whatever the formula is. The arithmetic
// layers decide the atoms they read from the hypotheses; a guard that
// is a membership, an opaque predicate or a propositional variable is
// no atom of theirs, and without this an implication guarded by it is
// dead to the decider though its guard is resident. The rule reads the
// hypothesis the same way in the target a hypothesis is decided as and
// in the conclusion.
func TestResidentFormula_ReadsAGuardTheContextAsserts(t *testing.T) {
	installTestBundle(t)
	p := ext.Var("P", core.TypeBool())
	h := ext.WrapTerm(core.Var("H", core.MakeFun(dsl.NumType, core.TypeBool())))
	hi := h.Apply(tn("i")).Core()
	notP := ext.Not(p).Core()
	reads := func(w *prop.PropWrapper, want Term) bool { return w != nil && prop.Rhs(w).AlphaEquals(want) }

	for _, row := range []struct {
		name   string
		hyps   []Term
		target Term
		want   Term
	}{
		{"a propositional guard", []Term{p.Core()}, p.Imply(tb("i <= n + 1")).Core(), tb("i <= n + 1")},
		{"an opaque predicate's guard", []Term{hi}, ext.WrapTerm(hi).Imply(tb("i <= n + 1")).Core(), tb("i <= n + 1")},
		{"a disjunct the context refutes", []Term{notP}, p.Or(tb("i <= n")).Core(), tb("i <= n")},
		{"a side of an ⇔", []Term{p.Core()}, p.Eq(tb("i <= n")).Core(), tb("i <= n")},
		{"the conclusion's conjunct", []Term{p.Core(), tb("i <= n + 1")}, p.And(tb("i <= n + 2")).Core(), prop.T},
	} {
		if w := ArithDecideWithHyps(row.hyps)(row.target); !reads(w, row.want) {
			t.Errorf("%s: %s under the context reads %v, want %s",
				row.name, ext.PrintTerm(row.target), w, ext.PrintTerm(row.want))
		}
	}

	// Without the hypothesis the guard stays: nothing decides it.
	guarded := p.Imply(tb("i <= n + 1")).Core()
	if w := ArithDecideWithHyps(nil)(guarded); w != nil {
		t.Errorf("with no hypothesis about P the guard must stay, got %s", ext.PrintTerm(prop.Rhs(w)))
	}
}
