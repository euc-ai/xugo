package gates

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// TestLintImplicitSpellingNeedsStructure — a statement leaves a
// component to the parser only under a structure over it.
//
// A constant that reads a structure's component as an implicit leading
// argument (`closed_in(T, c)`, `vec_add(add, u, v)`, `dot⟨n⟩(add, mul,
// u, v)`) may be written without it: the parser completes the argument
// from a binder of that name, or from the family's instance binding.
// The chapters use the choice to say something. A law over a structure
// — `∀T. is_topology(T) ⇒ … closed_in(c) …` — leaves the component
// implicit; a theorem that needs no structure spells it,
// `closed_in(T, c)`, and that spelling is how a reader sees at a glance
// that no axiom enters (constitution §Structures, "Implicit component
// arguments": `space.VecMono` spells `vec⟨m⟩(zero, u)` for exactly this
// reason).
//
// The parser cannot hold the line itself: it completes from ANY binder
// of the component's name, with or without the structure beside it, and
// the key is the same either way. This lint holds it: every implicit
// argument a registered statement's text leaves out, and that the parser
// completes to a variable of the statement, must be a variable some
// structure predicate in the statement is applied to. Completion to a
// family's instance component (WithInstance) is licensed by the family
// and not read here. Definitions are not read: a definition always
// spells the binders of the constant it defines.
func TestLintImplicitSpellingNeedsStructure(t *testing.T) {
	for _, e := range registry.All() {
		if e.Definition != proof.NotADefinition {
			continue
		}
		elided := e.ImplicitVariables()
		if len(elided) == 0 {
			continue
		}
		components := structureComponents(e.Statement().Prop)
		for _, v := range elided {
			if !components[v.Name] {
				t.Errorf("%s: `%s` leaves its component %s to the parser, and no structure "+
					"predicate in the statement is applied to %s — spell it (`%s(%s, …)`): a "+
					"statement with no structure over a component spells it, which is how a "+
					"reader sees that it needs no structure",
					e.Name, v.Const, v.Name, v.Name, v.Const, v.Name)
			}
		}
	}
}

// structureComponents collects the names of the variables some structure
// predicate is applied to, anywhere in p.
func structureComponents(p core.Prop) map[string]bool {
	out := map[string]bool{}
	var walk func(t core.Term)
	walk = func(t core.Term) {
		if app, ok := t.AsAppliedTerm(); ok {
			head, args := t, []core.Term(nil)
			for {
				a, ok := head.AsAppliedTerm()
				if !ok {
					break
				}
				args = append([]core.Term{a.Arg()}, args...)
				head = a.Fun()
			}
			if c, ok := head.AsConst(); ok && registry.IsStructurePredicate(string(c.Name())) {
				for _, a := range args {
					if v, ok := a.AsVar(); ok {
						out[string(v.Name())] = true
					}
				}
			}
			walk(app.Fun())
			walk(app.Arg())
			return
		}
		if abs, ok := t.AsAbsTerm(); ok {
			walk(abs.Body())
		}
	}
	walk(p.Conclusion())
	for h := range p.HypIter() {
		walk(h)
	}
	return out
}
