// Package engine — surface_alias.go: goal-local surface-name aliases
// for session claim/term texts.
//
// The session-side mirror of prover/proof's Argument-layer §"Surface
// names": a claim text may spell a statement binder's SURFACE name
// (`n`) where the goal's variable is the engine's minted spelling
// (`n₀`). In a Go proof body the alias environment is the enclosing
// Argument chain; in a session, "the enclosing scope" IS the focused
// goal, so the aliases are derived from the goal itself:
//
//   - every free variable whose name is a minted spelling (its
//     rename-inverted base differs — proof.SurfaceBase) makes its base
//     name a candidate alias;
//   - the alias exists only when it is UNAMBIGUOUS at this goal: no
//     other free variable inverts to the same base, and no free
//     variable is literally named the base (a genuine free `n` owns
//     the bare spelling).
//
// On ambiguity the session simply abstains — the minted spelling is
// always valid, exactly as in the Go layer. Resolution is a parse-scope
// seeding plus a capture-avoiding free-variable rename of the parsed
// result, never text substitution; a name the claim itself binds is
// untouched, and a name that resolves as a constant keeps resolving as
// the constant (the parser prefers consts for unbound names).
//
// Deliberately NOT alias-aware: `add-goal` (closed statements).

package engine

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/proof"
)

// goalSurfaceAliases derives the surface-name alias environment at a
// goal: base name → the (unique) free variable it denotes. Empty map
// when nothing aliases.
func goalSurfaceAliases(goal core.Prop) map[string]core.VarTerm {
	return termsSurfaceAliases(append([]core.Term{goal.Conclusion()}, goal.Hyps()...)...)
}

// termsSurfaceAliases is goalSurfaceAliases over terms that are not a
// goal — a term the output door prints on its own.
func termsSurfaceAliases(terms ...core.Term) map[string]core.VarTerm {
	frees := map[string]core.VarTerm{}
	for _, t := range terms {
		for _, v := range t.Frees(nil) {
			frees[string(v.Name())] = v
		}
	}
	candidates := map[string][]core.VarTerm{}
	for name, v := range frees {
		base := proof.SurfaceBase(name)
		if base == "" || base == name {
			continue
		}
		candidates[base] = append(candidates[base], v)
	}
	out := map[string]core.VarTerm{}
	for base, vs := range candidates {
		if len(vs) != 1 {
			continue // two mints share the base — ambiguous, abstain
		}
		if _, taken := frees[base]; taken {
			continue // a real free variable owns the bare spelling
		}
		out[base] = vs[0]
	}
	return out
}

// seedSurfaceAliases declares each alias name in `vars` at its minted
// variable's type (never overriding an existing entry) and returns the
// substitution list that renames the parsed frees to the minted
// variables. Callers apply the substitutions to the successful parse
// result — simultaneous and capture-avoiding via core.Substitute.
func seedSurfaceAliases(vars map[string]core.HolType, aliases map[string]core.VarTerm) []core.TermSubst {
	substs := make([]core.TermSubst, 0, len(aliases))
	for base, v := range aliases {
		if _, exists := vars[base]; exists {
			continue
		}
		vars[base] = v.Type()
		substs = append(substs, core.MakeTermSubst(core.Var(core.TermName(base), v.Type()), v))
	}
	return substs
}

// residentSurfaceNames lets the parser read structure components under
// the same aliases as the variables of a claim or tactic parameter.
func residentSurfaceNames(goal core.Prop) map[string]string {
	aliases := goalSurfaceAliases(goal)
	names := make(map[string]string, len(aliases))
	for name, variable := range aliases {
		names[string(variable.Name())] = name
	}
	return names
}

// substituteParsedProp applies a free-variable substitution to every
// part of a parsed Prop (conclusion + hyps).
func substituteParsedProp(p core.Prop, substs []core.TermSubst) core.Prop {
	if p == nil || len(substs) == 0 {
		return p
	}
	hyps := make([]core.Term, 0, p.NumHyps())
	for _, h := range p.Hyps() {
		hyps = append(hyps, h.Substitute(substs...))
	}
	return core.MakeProp(p.Conclusion().Substitute(substs...), hyps...)
}

// surfaceNamesView renders the goal's alias environment for inspect
// output: base name → the minted variable's printed spelling. Agents
// read it as "these bare names are valid claim/term spellings here".
func surfaceNamesView(goal core.Prop) map[string]string {
	aliases := goalSurfaceAliases(goal)
	if len(aliases) == 0 {
		return nil
	}
	out := make(map[string]string, len(aliases))
	for base, v := range aliases {
		out[base] = ext.PrintTerm(v)
	}
	return out
}
