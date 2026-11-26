// overload.go — an overloaded word: `sum(s, f)` for whichever of
// real_sum, nat_sum, int_sum f's values select.
//
// A constant's name carries its domain (the constant table is one
// namespace), and several domains have an operation mathematics calls
// by one word. A chapter declares that word on each such constant
// (registry.DefEntry.Overload), and a text may then write the word
// where it means the constant: the build reads the arguments and picks
// the one constant sharing the word that takes that many arguments and
// whose argument types they fit. Nothing new reaches the kernel — the
// term is the constant's own application, so a statement's key does
// not depend on which spelling its text used.
//
// Resolution order for an applied name: a bound variable, then a
// constant the caller's scope declares (a vocabulary row, a Script
// constant), then the overloaded word, then the scope's resolver. The
// word therefore beats a resolver constant of the same name: in a
// session, `sum(s, f)` is always the overloaded word.
//
// ChapterSpelling folds the other way (foldOverloads): an application
// of a constant declaring a word prints as the word, unless the word is
// already a name in the text. The consumers re-parse the short text
// under the full scope and keep it only when it builds the same
// statement, which is what settles every case the fold cannot see —
// arguments whose types do not pick the constant back out.

package dsl

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
)

// overloadWord reports whether name is an overloaded word in env's
// syntax table, with the constants declaring it.
func (env *typeEnv) overloadWord(name string) ([]string, bool) {
	if env.syntax == nil {
		return nil, false
	}
	cands := env.syntax.OverloadConsts(name)
	return cands, len(cands) > 0
}

// buildOverload builds `word(args)`: the constants declaring the word
// with len(args) arguments, narrowed to the one the arguments' types
// fit. A single constant at that arity builds its arguments against its
// own domains, exactly as the constant's own name would; several build
// the arguments on their own first and keep the constants whose type
// they fit — which must be exactly one. An argument built on its own
// reads a bare `&` as ℝ, the embedding's default, so `sgn(&0)` is
// real_sgn's and `max(&m, &n)` real_max's. Where that default fits NO
// candidate — `rem(n, &2)` with n an integer, `div(&7, &2)` — each
// candidate reads the arguments against its own domains instead,
// the way its name would: `int_rem(n, &2)` anchors the `&` at int,
// and `rem(n, 2)` embeds the natural numeral at that integer slot.
// The one that reads them is the constant; several reading them is
// still a refusal. An exact argument match always wins before embeddings.
func buildOverload(n *astApp, word string, cands []string, env *typeEnv) (core.Term, error) {
	var metas []core.ConstTermMeta
	var arities []string
	// A constant that declares dimensions answers to the word written
	// with that many in its ⟨…⟩, `dist⟨n⟩(u, v)`, and to no other
	// spelling (dimension.go); dimensioned names the first such
	// constant the text's arguments would otherwise have reached.
	var dimensioned string
	for _, name := range cands {
		meta, err := env.overloadMeta(name)
		if err != nil {
			return nil, fmt.Errorf("%s: %v", word, err)
		}
		arity := funArity(meta.AbsType())
		dims := 0
		if s := env.syntax.ConstSyntax(name); s != nil {
			dims = s.Dims
		}
		if dims > 0 {
			arities = append(arities, fmt.Sprintf("%s⟨%d⟩(%d)", name, dims, arity-dims))
		} else {
			arities = append(arities, fmt.Sprintf("%s(%d)", name, arity))
		}
		switch {
		case arity != len(n.args):
		case dims == n.dims:
			metas = append(metas, meta)
		case dimensioned == "":
			dimensioned = name
		}
	}
	switch len(metas) {
	case 0:
		if dimensioned != "" && n.dims == 0 {
			return nil, fmt.Errorf("%s: %s takes its dimension in the ⟨…⟩ after the word, not in the parentheses — write %s⟨…⟩(…)",
				word, dimensioned, word)
		}
		return nil, fmt.Errorf("%s takes no %d arguments: the constants it names are %s",
			word, len(n.args), strings.Join(arities, ", "))
	case 1:
		abs, _ := env.freshAbs(metas[0])
		args, err := buildArgsAgainstFunType(n.args, env, abs)
		if err != nil {
			return nil, err
		}
		return buildAppViaMeta(env, metas[0], args)
	}
	args := make([]core.Term, len(n.args))
	argTypes := make([]core.HolType, len(n.args))
	for i, a := range n.args {
		t, err := buildArg(a, env, nil)
		if err != nil {
			return nil, fmt.Errorf("%s: its arguments must type on their own to pick among %s (%v) — or write the constant",
				word, names(metas), err)
		}
		args[i], argTypes[i] = t, t.Type()
	}
	var fit []core.Term
	var fitMetas []core.ConstTermMeta
	var fitNames []string
	for _, meta := range metas {
		if t, err := buildAppViaMeta(env, meta, args); err == nil {
			fit = append(fit, t)
			fitMetas = append(fitMetas, meta)
			fitNames = append(fitNames, string(meta.Name()))
		}
	}
	switch len(fit) {
	case 1:
		// The constant picked, its arguments are read as its own name
		// would read them — against its domains — so a `&` the bare
		// build could only default (`abs(&n)`: strict mode refuses a
		// surviving default) is anchored by the constant the word named.
		// The anchored read builds fresh nodes; the defaulted ones no
		// longer survive into the statement.
		abs, _ := env.freshAbs(fitMetas[0])
		if anchored, err := buildArgsAgainstFunType(n.args, env, abs); err == nil {
			if t, err := buildAppViaMeta(env, fitMetas[0], anchored); err == nil {
				return t, nil
			}
		}
		return fit[0], nil
	case 0:
		// The bare reading fits nothing: let each candidate read the
		// arguments against its own domains, which retargets a `&` the
		// bare build defaulted to ℝ.
		if t, anchoredNames := buildOverloadAnchored(n, metas, env); len(anchoredNames) == 1 {
			return t, nil
		} else if len(anchoredNames) > 1 {
			return nil, fmt.Errorf("%s applied to (%s): the arguments fit %s alike — write the constant",
				word, formatHolTypes(argTypes), strings.Join(anchoredNames, " and "))
		}
		return nil, fmt.Errorf("%s applied to (%s): none of %s takes these arguments — write the constant",
			word, formatHolTypes(argTypes), names(metas))
	}
	return nil, fmt.Errorf("%s applied to (%s): the arguments fit %s alike — write the constant",
		word, formatHolTypes(argTypes), strings.Join(fitNames, " and "))
}

// buildOverloadAnchored reads the arguments against each candidate's
// own domains and returns the one application that built, with the
// names of every candidate that read them: one name is the reading,
// several an ambiguity the caller refuses, none a refusal too. A
// discarded reading leaves nothing in the statement, so a `&` it
// defaulted on the way is never the strict check's.
func buildOverloadAnchored(n *astApp, metas []core.ConstTermMeta, env *typeEnv) (core.Term, []string) {
	var built core.Term
	var read []string
	for _, meta := range metas {
		abs, _ := env.freshAbs(meta)
		args, err := buildArgsAgainstFunType(n.args, env, abs)
		if err != nil {
			continue
		}
		t, err := buildAppViaMeta(env, meta, args)
		if err != nil {
			continue
		}
		built = t
		read = append(read, string(meta.Name()))
	}
	if len(read) != 1 {
		return nil, read
	}
	return built, read
}

// overloadMeta is a constant an overloaded word names: the scope's own
// meta when the scope declares it, else the resolver's.
func (env *typeEnv) overloadMeta(name string) (core.ConstTermMeta, error) {
	if c, ok := env.scopeConsts[name]; ok {
		return c.Meta(), nil
	}
	return env.constMeta(name)
}

// funArity is the number of arguments a constant of type t takes to
// its full application: the arrows of its type.
func funArity(t core.HolType) int {
	n := 0
	for {
		c, ok := t.(core.CompositeType)
		if !ok || !c.Meta().Equals(core.MetaTypeFun()) {
			return n
		}
		n++
		t = c.SubType(1)
	}
}

func names(metas []core.ConstTermMeta) string {
	out := make([]string, len(metas))
	for i, m := range metas {
		out[i] = string(m.Name())
	}
	return strings.Join(out, ", ")
}

// overloadHint is the note for a word written bare that resolved to
// no constant (bareOverloadedWord): applied, or read as a value where
// its type is known, the word names one of them.
func (env *typeEnv) overloadHint(name string) string {
	cands, ok := env.overloadWord(name)
	if !ok {
		return ""
	}
	return fmt.Sprintf(" (%s is the overloaded word for %s — apply it to its arguments, write it where its type is known, or write the constant)",
		name, strings.Join(cands, ", "))
}

// ---------------------------------------------------------------------------
// The printer's half
// ---------------------------------------------------------------------------

// foldOverloads rewrites, bottom-up, every full application of a
// constant declaring an overloaded word into the word — when the word
// is no name the text already spells (textNames: a constant of that
// very name, a variable, a binder), and the head carries no `⟨…⟩`
// annotation (the printer put it there because the instance is not
// recoverable from the arguments, which is exactly when the word could
// not pick the constant back out).
func foldOverloads(node astNode, table SyntaxTable, textNames map[string]bool, bound map[string]int, declared map[string]bool, changed *bool) astNode {
	fold := func(n astNode) astNode { return foldOverloads(n, table, textNames, bound, declared, changed) }
	switch n := node.(type) {
	case *astVar:
		// A nullary constant written bare folds into its word anywhere
		// (`pi` → `π`); a word for applied constants folds only where the
		// parse will know the position's type — an application argument,
		// handled in the astApp case — and keeps its name elsewhere.
		if s := bareWordSyntax(n, table, textNames, bound, declared); s != nil && s.Overload.Arity == 0 {
			*changed = true
			return &astVar{name: s.Overload.Word, pos: n.pos}
		}
		return n
	case *astField:
		n.receiver = fold(n.receiver)
	case *astApp:
		for i, a := range n.args {
			n.args[i] = fold(a)
			// A constant read as a value in argument position — `real_sin`
			// in `real_derivative_at(real_sin, c, …)` — folds into its word:
			// the parse reads the argument against the head's domain
			// (bareOverloadedWord), and the consumer's round-trip check
			// settles a position that does not pick the constant back out.
			if v, isVar := n.args[i].(*astVar); isVar {
				if s := bareWordSyntax(v, table, textNames, bound, declared); s != nil && s.Overload.Arity > 0 {
					*changed = true
					n.args[i] = &astVar{name: s.Overload.Word, pos: v.pos}
				}
			}
		}
		head, isVar := n.fun.(*astVar)
		if !isVar {
			n.fun = fold(n.fun)
			return n
		}
		if bound[head.name] > 0 || declared[head.name] || len(head.typeAnnot) > 0 {
			return n
		}
		s := table.ConstSyntax(head.name)
		if s == nil || s.Overload == nil || s.Overload.Arity != len(n.args) || textNames[s.Overload.Word] {
			return n
		}
		*changed = true
		n.fun = &astVar{name: s.Overload.Word, pos: head.pos}
		return n
	case *astBinOp:
		n.left = fold(n.left)
		n.right = fold(n.right)
	case *astCong:
		n.left = fold(n.left)
		n.right = fold(n.right)
		n.modulus = fold(n.modulus)
	case *astTendsAt:
		n.fn = fold(n.fn)
		n.limit = fold(n.limit)
		n.point = fold(n.point)
	case *astNotNode:
		n.body = fold(n.body)
	case *astCoerce:
		n.operand = fold(n.operand)
	case *astNeg:
		n.operand = fold(n.operand)
	case *astOutfix:
		for i, a := range n.args {
			n.args[i] = fold(a)
		}
		if n.sub != nil {
			n.sub = fold(n.sub)
		}
	case *astQuantNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		n.body = fold(n.body)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astAbsNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		n.body = fold(n.body)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astPatternAbs:
		leaves := n.pat.leaves(nil)
		for _, lf := range leaves {
			bound[lf.name]++
		}
		n.body = fold(n.body)
		for _, lf := range leaves {
			bound[lf.name]--
		}
	case *astBigOp:
		n.bound = fold(n.bound)
		bound[n.binder]++
		n.body = fold(n.body)
		bound[n.binder]--
	}
	return node
}

// collectASTNames records every name root spells — the variables and
// constants it applies or mentions, and every binder it introduces.
func collectASTNames(root astNode, into map[string]bool) {
	walkAST(root, func(n astNode) {
		switch x := n.(type) {
		case *astVar:
			into[x.name] = true
		case *astQuantNode:
			into[x.varName] = true
		case *astAbsNode:
			into[x.varName] = true
		case *astPatternAbs:
			for _, lf := range x.pat.leaves(nil) {
				into[lf.name] = true
			}
		case *astBigOp:
			into[x.binder] = true
		}
	})
}

// bareOverloadedWord resolves a word written BARE — no arguments — to
// the constant it means here, or to nothing (nil, nil), in which case
// the caller reads the name as it always did. Two readings exist. A
// nullary constant declaring the word (`π` for pi) is the word
// itself. A word for applied constants read as a VALUE resolves only
// where the position's type is known — buildExpected stashes an
// application argument's expected type under the name, so
// `real_derivative_at(sin, c, cos(c))` reads `sin` at `real → real` —
// to the one constant declaring the word whose type that is; several
// candidates fitting, or none known, leave the word unresolved and the
// strict-resolution refusal names the constants (overloadHint).
func (env *typeEnv) bareOverloadedWord(name string) (core.Term, error) {
	cands, ok := env.overloadWord(name)
	if !ok {
		return nil, nil
	}
	target, known := env.inferred[name]
	var fits, nullary []core.Term
	for _, cand := range cands {
		meta, err := env.overloadMeta(cand)
		if err != nil {
			return nil, fmt.Errorf("%s: %v", name, err)
		}
		abs, _ := env.freshAbs(meta)
		if funArity(meta.AbsType()) == 0 {
			nullary = append(nullary, core.MakeConstTerm(meta, abs))
		}
		if known {
			if substs, ok := abs.Matches(target, utils.FullPredicate); ok {
				fits = append(fits, core.MakeConstTerm(meta, abs.Substitute(substs...)))
			}
		}
	}
	switch {
	case known && len(fits) == 1:
		return fits[0], nil
	case !known && len(nullary) == 1:
		return nullary[0], nil
	}
	return nil, nil
}

// bareWordSyntax is the syntax of a constant a bare name spells — nil
// when the name is a binder, a declared variable, carries a `⟨…⟩`
// annotation, declares no word, or its word is a name the text
// already spells.
func bareWordSyntax(v *astVar, table SyntaxTable, textNames map[string]bool, bound map[string]int, declared map[string]bool) *ConstSyntax {
	if bound[v.name] > 0 || declared[v.name] || len(v.typeAnnot) > 0 {
		return nil
	}
	s := table.ConstSyntax(v.name)
	if s == nil || s.Overload == nil || textNames[s.Overload.Word] {
		return nil
	}
	return s
}
