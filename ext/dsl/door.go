// door.go — how a text door reads a statement or a claim at a focus.
//
// Every door that reads a proposition text at a focus — the session's
// claim and lemma doors (engine), the Go Script's statement door
// (Script.MakePropText, behind ctx.Lemma, ctx.Theorem and a family's
// headline) and its claim door (Argument.parseClaim), and emit's check
// that a text it renders reads back at the door it is parsed at — reads
// it through ParsePropTextAtDoor, so the doors cannot read one text two
// ways.

package dsl

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// ParsePropTextAtDoor reads raw at the focus scope describes. A CLOSED
// text — one whose every name is bound by its own binders, a bundle
// binder `∀R:comm_ring(A).` binding R's components itself — is read
// closed: with nothing of the focus in scope, neither its variables nor
// its resident facts and their surface names, so an operator the text's
// own structure binds is never read beside a record the focus declares,
// and the text states what it states wherever it is read. The closed
// reading is taken when it reads, leaves no variable free, and takes no
// name the focus declares as a constant or as an implicit binding; any
// other text — one that names a variable of the focus, or an operator
// only a resident structure fact binds — is read at the focus, scope as
// given. A scope with no focus to set aside is read as it is.
//
// scope.ImplicitCompleted is told of the completions of the reading
// returned, once each.
func ParsePropTextAtDoor(raw string, scope *ParseScope) ParseResult {
	if scope == nil || (len(scope.Vars) == 0 && len(scope.ResidentFacts) == 0 && len(scope.ResidentNames) == 0) {
		return ParsePropTextInScope(raw, scope)
	}
	if closed, ok := parseClosedText(raw, scope); ok {
		return closed
	}
	return ParsePropTextInScope(raw, scope)
}

// _ImplicitCompletion is one call of a ParseScope.ImplicitCompleted
// observer, held until the reading it belongs to is the one returned.
type _ImplicitCompletion struct {
	constName, name string
	variable        bool
}

// parseClosedText is the closed reading of raw at scope's vocabulary:
// the parse with scope's variables, resident facts and surface names
// set aside, and whether it is the text's reading (ParsePropTextAtDoor).
func parseClosedText(raw string, scope *ParseScope) (ParseResult, bool) {
	closed := *scope
	closed.Vars, closed.ResidentFacts, closed.ResidentNames = nil, nil, nil
	focusNamed := false
	var completions []_ImplicitCompletion
	closed.ImplicitCompleted = func(constName, name string, variable bool) {
		if _, declared := scope.Vars[name]; declared && !variable {
			focusNamed = true
		}
		completions = append(completions, _ImplicitCompletion{constName, name, variable})
	}
	res := ParsePropTextInScope(raw, &closed)
	if len(res.Errors) > 0 || res.Prop == nil || focusNamed {
		return ParseResult{}, false
	}
	terms := append([]core.Term{res.Prop.Conclusion()}, res.Prop.Hyps()...)
	for _, t := range terms {
		if len(t.Frees(nil)) > 0 {
			return ParseResult{}, false
		}
	}
	for sub := range ext.SubTerms(terms...) {
		if c, ok := sub.AsConst(); ok {
			if _, declared := scope.Vars[string(c.Name())]; declared {
				return ParseResult{}, false
			}
		}
	}
	if scope.ImplicitCompleted != nil {
		for _, c := range completions {
			scope.ImplicitCompleted(c.constName, c.name, c.variable)
		}
	}
	return res, true
}
