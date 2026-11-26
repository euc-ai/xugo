package engine

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// GoalClass describes a goal's domain classification for capability boundary detection.
type GoalClass int

const (
	// GoalPropositional: all variables are bool, no quantifiers, no non-builtin constants.
	// CNF refutation is complete for this class — failure means invalid.
	GoalPropositional GoalClass = iota
	// GoalPureFOL: has quantifiers or non-bool variables but no non-builtin constants.
	// CNF refutation is incomplete — failure means unknown.
	GoalPureFOL
	// GoalSupported: has non-builtin constants, all in registered domains.
	GoalSupported
	// GoalPartiallySupported: mix of registered and unregistered constants.
	GoalPartiallySupported
	// GoalUnsupported: has non-builtin constants, none in registered domains.
	GoalUnsupported
)

// DomainRegistry maps non-builtin constant names to capability domain names.
// It starts empty — the "logic" domain is implicit (detected by absence
// of non-builtin constants); Register adds a domain's constants (bitops, etc.).
type DomainRegistry struct {
	domains map[string]string // constant_name → domain_name
}

// NewDomainRegistry creates an empty domain registry.
func NewDomainRegistry() *DomainRegistry {
	return &DomainRegistry{domains: make(map[string]string)}
}

// Register adds a constant → domain mapping.
func (r *DomainRegistry) Register(constName, domainName string) {
	r.domains[constName] = domainName
}

// Lookup returns the domain name for a constant, or "" if unregistered.
func (r *DomainRegistry) Lookup(constName string) string {
	return r.domains[constName]
}

// classifyGoal determines the goal class by inspecting the term structure.
// It walks the term tree once to check for quantifiers, non-bool free variables,
// and non-builtin constants.
func classifyGoal(p core.Prop, registry *DomainRegistry) (GoalClass, []string) {
	// Collect non-builtin constants.
	consts := make(map[core.TermKey]ext.ConstTerm)
	ext.CollectConstTerms(p.Conclusion(), consts)
	for i := range p.NumHyps() {
		ext.CollectConstTerms(p.Hyp(i), consts)
	}

	// If there are non-builtin constants, classify by domain registry.
	if len(consts) > 0 {
		var unsupported []string
		registered := 0
		for _, c := range consts {
			name := string(c.Name())
			if registry != nil && registry.Lookup(name) != "" {
				registered++
			} else {
				unsupported = append(unsupported, name)
			}
		}
		if registered == len(consts) {
			return GoalSupported, nil
		}
		if registered > 0 {
			return GoalPartiallySupported, unsupported
		}
		return GoalUnsupported, unsupported
	}

	// Pure logic — check if propositional or FOL.
	if isPropositional(p) {
		return GoalPropositional, nil
	}
	return GoalPureFOL, nil
}

// isPropositional returns true if the proposition is purely propositional:
// no quantifiers and all free variables are of type bool.
func isPropositional(p core.Prop) bool {
	if !termIsPropositional(p.Conclusion()) {
		return false
	}
	for i := range p.NumHyps() {
		if !termIsPropositional(p.Hyp(i)) {
			return false
		}
	}
	return true
}

// termIsPropositional walks a term tree and returns false if it contains
// quantifiers or free variables of non-bool type.
func termIsPropositional(t core.Term) bool {
	switch t := t.Core().(type) {
	case core.VarTerm:
		return t.Type().Equals(core.TypeBool())
	case ext.ConstTerm:
		name := t.Name()
		// Quantifiers make it FOL.
		if name == utils.ForAllStr || name == utils.ExistsStr || name == utils.UniqueStr {
			return false
		}
		return true
	case core.AppliedTerm:
		return termIsPropositional(t.Fun()) && termIsPropositional(t.Arg())
	case core.AbsTerm:
		// Lambda abstraction typically appears under quantifiers.
		// The bound variable type doesn't matter (it's local), but
		// check the body.
		return termIsPropositional(t.Body())
	default:
		return true
	}
}
