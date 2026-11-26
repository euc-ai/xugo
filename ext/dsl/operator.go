// operator.go — the operator notation form: `u + v`, `u - v`, `c • u`,
// `-u`, `a ⟶ l`, `f ⟶ l (at c)`.
//
// A chapter declares an operator notation for a constant at its
// definition (registry.DefEntry.Notation, spelled with the definition's
// own binders — `"u + v"` for `vadd(add, u, v)`, `"c • u"` for
// `vsmul(mul, c, u)`, `"-u"` for `vneg(neg, u)`, `"a ⟶ l"` for
// `real_converges_to(a, l)`, `"f ⟶ l (at c)"` for a function limit), and it
// arrives here as ConstSyntax.Operator (syntax.go). The symbol is one
// the grammar already parses — `+ - * /`, the order `≤ <`, the scalar
// action's `•` and the limit relation `⟶` as an infix, `-` as a
// prefix, `⟶` with its point clause as the one three-operand mixfix
// (`"x ≤ y"` for `extended_le(x, y)`) — so the parser reads
// `u + v` into the astBinOp it reads `x + y` into, and the BUILD tells
// the two apart by operand type, exactly as it tells num from real
// from int: the built-in domains are asked first, and where none
// serves the operand types the constant declaring the symbol at that
// arity is instantiated from them (`vadd` at `num → A`). `•` and `⟶`
// have no built-in domain at all, so for them the declaring constant
// is asked first and alone (isDeclaredOnlyOperator); the clause form
// is the same symbol at arity three, so a sequence's `⟶` and a
// function's `⟶ (at)` are two constants, told apart by the clause
// rather than by type. Its implicit prefix is completed here, at
// build time, by the rule implicit.go applies on the AST: a component
// is the name the scope binds, the field of that name of a record in
// scope — of the one the operands' types admit, where several records
// declare it — or the instance term the family binds it to, and
// where nothing binds it the operator is refused with the message a
// bare `vadd(u, v)` gets. So `u + v` under vector/euclidean is
// `vadd(real_add, u, v)`, under a ring record `R:ring_ops(A)` it is
// `vadd(R.add, u, v)`, and a vector `+` beside a real `+` in one
// statement are two operators, each on its own operands. Several
// constants may declare one symbol at one arity, each on its own
// carrier (`z * w` on ℂ beside `p * q` on the permutations), and the
// dispatch is the type check: the one declaring constant the operands
// fit is instantiated, and operands two of them fit alike are refused
// by name. Nothing below the AST changes: the kernel term is the
// plain application, and so are the key and every consumer.
//
// foldOperators is the printer's half, run by ChapterSpelling: a full
// application of a constant with an operator notation — its implicit
// prefix already elided — folds into the operator.

package dsl

import (
	"fmt"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// operatorSymbols is the alphabet a constant may declare, by arity: the
// symbols the grammar parses at that arity.
var operatorSymbols = map[int][]string{
	// At arity 3 the one form is the limit mixfix `f ⟶ l (at c)`: the
	// relation with its trailing point clause (parser.go's ⟶ arm).
	3: {"⟶"},
	2: {"+", "-", "*", "/", "•", "⟶", "^", "≤", "<"},
	1: {"-"},
}

// LimitPointClause is the clause word of the arity-3 form: `f ⟶ l (at c)`
// reads the point after `at` the way `x ≡ y (mod m)` reads the modulus
// after `mod`. The parser declines to fold a `(at …)` group into an
// application, and the define door spells the pattern with it.
const LimitPointClause = "at"

// isDeclaredOnlyOperator reports whether symbol is served by a
// chapter's declared constant alone — no built-in domain reads it, so
// its operands are built as they are and need not share a type: the
// scalar action `•` (a scalar beside a vector), the limit relation `⟶`
// (a sequence beside its limit; a function beside its limit and the
// point, in the clause form) and the power `^` (an element beside its
// exponent). The build's astBinOp arm dispatches these straight to
// buildDeclaredOperator, and buildTendsAt does the same for the clause
// form — except that `^` is first offered to the built-in power domains
// (num, real, int: buildPower), and reaches the declaring constant only
// for a base outside them.
func isDeclaredOnlyOperator(symbol string) bool {
	return symbol == "•" || symbol == "⟶" || symbol == "^"
}

// buildTendsAt lowers `f ⟶ l (at c)`: the three operands built as they
// are, then the constant declaring `⟶` at arity 3 instantiated from
// them. No built-in domain serves the form, so the only refusal is
// "no constant in scope declares it".
func buildTendsAt(n *astTendsAt, env *typeEnv) (core.Term, error) {
	operands := make([]core.Term, 3)
	for i, nd := range []astNode{n.fn, n.limit, n.point} {
		t, err := buildTerm(nd, env, false)
		if err != nil {
			return nil, err
		}
		operands[i] = t
	}
	if t, ok, err := buildDeclaredOperator(env, "⟶", operands); ok || err != nil {
		return t, err
	}
	return nil, fmt.Errorf("operator ⟶ (%s) has no instance for operand types %s, %s and %s (no constant in scope declares it)",
		LimitPointClause, ext.FormatType(operands[0].Type()), ext.FormatType(operands[1].Type()), ext.FormatType(operands[2].Type()))
}

// OperatorSymbolOK reports whether symbol is one a constant may declare
// at arity — the define door's check on a declared notation.
func OperatorSymbolOK(symbol string, arity int) bool {
	for _, s := range operatorSymbols[arity] {
		if s == symbol {
			return true
		}
	}
	return false
}

// constMeta resolves a constant the surface implies but never spells —
// the constant behind a declared operator or big operator: the scope's
// meta first (the pointer discipline setops.go documents), then the
// scope's resolver, the hit cached into the scope for the rest of the
// parse.
func (env *typeEnv) constMeta(name string) (core.ConstTermMeta, error) {
	if m, ok := env.scopeConstMetas[name]; ok {
		return m, nil
	}
	if c, ok := env.scopeConsts[name]; ok {
		return c.Meta(), nil
	}
	if env.resolver != nil {
		if m := env.resolver(name); !m.IsZero() {
			env.scopeConstMetas[name] = m
			return m, nil
		}
	}
	return core.ConstTermMeta{}, fmt.Errorf("constant %s is not in scope", name)
}

// mixedComponentSources refuses an implicit prefix that takes a
// component from a variable which is no component: strangers names the
// components read from a variable of the text or the scope to which no
// structure predicate is applied and whose type is no record's,
// elsewhere those a record's field or the family's instance supplies.
// The components of one application are bound together — by the
// variables a law is stated over, by records, by an instance — so a
// variable that carries no structure, beside a component read
// elsewhere, only shares a component's name: `∃e. … c ^ n …` under a
// monoid the family binds would read the power at the bound e. A
// component nothing supplies is in neither list, and its own refusal
// names it. nil where either list is empty.
func mixedComponentSources(constName string, names, strangers, elsewhere []string) error {
	if len(strangers) == 0 || len(elsewhere) == 0 {
		return nil
	}
	return &implicitArgError{fmt.Sprintf(
		"%s: its implicit arguments (%s) would be read from two places — %s from the variable %s in scope here, "+
			"to which no structure predicate is applied, and %s from a record or the family's instance. A variable "+
			"named like a component is no component of that structure: rename the variable, or spell the "+
			"application (%s) explicitly",
		constName, strings.Join(names, ", "), strings.Join(strangers, ", "), strings.Join(strangers, ", "),
		strings.Join(elsewhere, ", "), strings.Join(names, ", "))}
}

// isComponent reports whether the variable name, bound or declared, may
// stand for a component beside components read elsewhere: a structure
// predicate is applied to it (componentVariables), or its type is a
// record's.
func (env *typeEnv) isComponent(name string) bool {
	if env.components[name] {
		return true
	}
	ty, ok := env.lookupType(name)
	return ok && ty != nil && env.syntax != nil && env.syntax.StructSyntax(structTypeName(ty)) != nil
}

// implicitApplication applies the constant meta to its implicit prefix
// by apply, which builds the application with the operands after it and
// reports whether those components serve it. Each binder is the
// variable the text binds or the scope declares under that name, else
// the field of that name of a record in scope, else the instance term
// the family binds it to; a binder nothing binds refuses, naming it. A
// field several records declare is read from the one record the types
// pick, by the rule that picks the record of a short application in the
// text (implicit.go, chooseRecords): each reading — one record per such
// field, a name the prefix repeats read from one — is matched, its
// components and then the operands, against the constant's type
// (readingMatcher), and of those that stand the one apply builds is
// kept; records the operands fit alike are refused by name. ok is false
// when apply builds under no reading. A prefix that would take a
// component from a variable carrying no structure and another from
// elsewhere is refused (mixedComponentSources).
func (env *typeEnv) implicitApplication(meta core.ConstTermMeta, names []string, operands []core.Term, apply func(prefix []core.Term) (core.Term, bool)) (core.Term, bool, error) {
	constName := string(meta.Name())
	components := make([][]core.Term, len(names))
	var ambiguous string
	var ambiguousOwners []string
	var strangers, elsewhere []string
	for _, name := range names {
		_, isBound := env.bound[name]
		_, isDeclared := env.declared[name]
		switch {
		case isBound || isDeclared:
			if !env.isComponent(name) {
				strangers = append(strangers, name)
			}
		case env.implicitBindings[name] != nil ||
			len(recordComponentOwners(env.syntax, name, env.bound, env.declared, env.residentNames)) > 0:
			elsewhere = append(elsewhere, name)
		}
	}
	if err := mixedComponentSources(constName, names, strangers, elsewhere); err != nil {
		return nil, true, err
	}
	for i, name := range names {
		_, isBound := env.bound[name]
		_, isDeclared := env.declared[name]
		if isBound || isDeclared {
			t, err := buildVarTerm(name, env, false)
			if err != nil {
				return nil, true, err
			}
			components[i] = []core.Term{t}
			continue
		}
		owners := recordComponentOwners(env.syntax, name, env.bound, env.declared, env.residentNames)
		for _, owner := range owners {
			t, err := buildStructField(recordField(owner, name), env)
			if err != nil {
				return nil, true, err
			}
			components[i] = append(components[i], t)
		}
		if len(owners) > 1 && ambiguous == "" {
			ambiguous, ambiguousOwners = name, owners
		}
		if len(owners) > 0 {
			continue
		}
		if instance := env.implicitBindings[name]; instance != nil {
			components[i] = []core.Term{instance}
			continue
		}
		return nil, true, &implicitArgError{fmt.Sprintf(
			"%s: its implicit argument %s is not in scope — spell the application (%s) explicitly, "+
				"or state the law under the structure that binds them",
			constName, name, strings.Join(names, ", "))}
	}
	prefix := make([]core.Term, len(names))
	if ambiguous == "" {
		for i := range names {
			prefix[i] = components[i][0]
		}
		t, ok := apply(prefix)
		return t, ok, nil
	}
	written := make([]localTyping, len(operands))
	for i, operand := range operands {
		written[i] = termTyping(operand)
	}
	var fits []core.Term
	var walk func(m readingMatcher, i int)
	walk = func(m readingMatcher, i int) {
		if len(fits) > 1 {
			return
		}
		if i == len(names) {
			if !m.fits(written) {
				return
			}
			if t, ok := apply(slices.Clone(prefix)); ok {
				fits = append(fits, t)
			}
			return
		}
		candidates := components[i]
		if j := slices.Index(names, names[i]); j < i {
			candidates = prefix[j : j+1]
		}
		for _, t := range candidates {
			if next, ok := m.fit(termTyping(t)); ok {
				prefix[i] = t
				walk(next, i+1)
			}
		}
	}
	walk(newReadingMatcher(env.syntax, lettersApart(meta.AbsType())), 0)
	switch len(fits) {
	case 0:
		return nil, false, nil
	case 1:
		return fits[0], true, nil
	}
	return nil, true, &implicitArgError{fmt.Sprintf(
		"%s: its implicit argument %s is a field of more than one record in scope (%s) and the operands' types do not pick one — spell the record field explicitly",
		constName, ambiguous, strings.Join(ambiguousOwners, ", "))}
}

// lettersApart is a constant's type with its letters marked apart from
// the statement's (constLetterMark), as a reading matches it.
func lettersApart(t core.HolType) core.HolType {
	var apart []core.TypeSubst
	for _, v := range t.TypeVars() {
		apart = append(apart, core.TypeSubst{VarType: v, HolType: core.MakeVarType(constLetterMark + string(v.Name()))})
	}
	return t.Substitute(apart...)
}

// termTyping is a built term's type as a reading reads it: unknown where
// an occurrence's stand-in is still open in it (isStandIn), which the
// build's unifier may yet bind.
func termTyping(t core.Term) localTyping {
	ty := t.Type()
	if slices.ContainsFunc(ty.TypeVars(), isStandIn) {
		return localTyping{typ: ty}
	}
	return localTyping{ty, false, true}
}

// buildChapterOperator lowers `left σ right` (or `σ operand`) whose
// operand types no built-in domain serves, by what the chapter
// declares: a constant declaring σ at the operands' types
// (buildDeclaredOperator), else a resident structure's component or a
// structure value's field at those types (buildStructureOperator). A
// declaring constant whose implicit prefix the scope cannot complete
// declines like one whose types do not fit, and its refusal is
// reported only when nothing else serves the operands: `u + v` at the
// vectors of a module value is the module's addition, not vec_add's
// missing `add`. ok is false when nothing serves the operands.
func buildChapterOperator(env *typeEnv, symbol string, operands []core.Term) (core.Term, bool, error) {
	t, ok, err := buildDeclaredOperator(env, symbol, operands)
	if ok && err == nil {
		return t, true, nil
	}
	var prefixErr error
	if err != nil {
		if _, isPrefix := err.(*implicitArgError); !isPrefix {
			return nil, true, err
		}
		prefixErr = err
	}
	if t, ok, err := buildStructureOperator(env, symbol, operands); ok || err != nil {
		return t, ok, err
	}
	if prefixErr != nil {
		return nil, true, prefixErr
	}
	return nil, false, nil
}

// buildDeclaredOperator lowers `left σ right` (or `σ operand`) whose
// operand types no built-in domain serves: the constant declaring σ at
// that arity whose operands these are, applied to its implicit prefix
// and the operands in its argument order. Several constants may declare
// one symbol, each on its own carrier (`z * w` on ℂ, `p * q` on the
// permutations); the operands' types pick exactly one, and two that
// both fit are refused by name. ok is false when no declaring constant
// fits, so the caller reports the plain "no instance" refusal — or,
// when one could not even complete its implicit prefix, that refusal.
func buildDeclaredOperator(env *typeEnv, symbol string, operands []core.Term) (core.Term, bool, error) {
	if env.syntax == nil {
		return nil, false, nil
	}
	var (
		fits     []core.Term
		fitNames []string
		firstErr error
	)
	for _, name := range env.syntax.OperatorConsts(symbol, len(operands)) {
		t, ok, err := buildOperatorAt(env, name, symbol, operands)
		switch {
		case err != nil:
			if firstErr == nil {
				firstErr = err
			}
		case ok:
			fits, fitNames = append(fits, t), append(fitNames, name)
		}
	}
	switch len(fits) {
	case 1:
		return fits[0], true, nil
	case 0:
		if firstErr != nil {
			return nil, true, firstErr
		}
		return nil, false, nil
	}
	return nil, true, fmt.Errorf("operator %s: the operands fit %s alike — spell the constant",
		symbol, strings.Join(fitNames, " and "))
}

// buildOperatorAt is one declaring constant's reading of the operator:
// ok is false when the constant does not serve these operand types.
func buildOperatorAt(env *typeEnv, name, symbol string, operands []core.Term) (core.Term, bool, error) {
	syntax := env.syntax.ConstSyntax(name)
	if syntax == nil || syntax.Operator == nil || syntax.Operator.Arity() != len(operands) {
		return nil, false, nil
	}
	meta, err := env.constMeta(name)
	if err != nil {
		return nil, true, fmt.Errorf("operator %s: %v", symbol, err)
	}
	explicit := make([]core.Term, len(operands))
	for i, pos := range syntax.Operator.Args {
		explicit[pos] = operands[i]
	}
	// Where the declaring constant does not serve these operand types
	// (`vadd` at a scalar) it declines, and a resident structure's
	// component or the plain refusal follows.
	return env.implicitApplication(meta, syntax.Implicit, explicit, func(prefix []core.Term) (core.Term, bool) {
		t, err := buildAppViaMeta(env, meta, append(prefix, explicit...))
		return t, err == nil
	})
}

// foldOperators rewrites, bottom-up, every full application of a
// constant with an operator notation into the operator: the infix
// astBinOp, or the prefix astNeg.
func foldOperators(node astNode, table SyntaxTable, bound map[string]int, declared map[string]bool, changed *bool) astNode {
	switch n := node.(type) {
	case *astField:
		n.receiver = foldOperators(n.receiver, table, bound, declared, changed)
	case *astApp:
		for i, a := range n.args {
			n.args[i] = foldOperators(a, table, bound, declared, changed)
		}
		head, isVar := n.fun.(*astVar)
		if !isVar {
			n.fun = foldOperators(n.fun, table, bound, declared, changed)
			return n
		}
		if bound[head.name] > 0 || declared[head.name] || len(head.typeAnnot) > 0 {
			return n
		}
		// The built-in power domains: nat_pow, real_pow and int_pow are
		// the DSL's own `^` (the base's type picks them back out, build.go's
		// buildPower), so a full application folds into the symbol exactly
		// as the term printer writes it.
		if isBuiltinPower(head.name) && len(n.args) == 2 {
			*changed = true
			return &astBinOp{op: "^", left: n.args[0], right: n.args[1], pos: n.pos}
		}
		syntax := table.ConstSyntax(head.name)
		if syntax == nil || syntax.Operator == nil || len(n.args) < syntax.Operator.Arity() {
			return n
		}
		// A constant with implicit arguments folds only once the chapter
		// spelling dropped them: `monoid_pow(mul, one, x, n)` under no
		// binding of mul and one stays spelled.
		if len(syntax.Implicit) > 0 && !n.elided {
			return n
		}
		// The operation, applied to a point or not: `vadd(u, v, i)` is
		// `(u + v)(i)`.
		o := syntax.Operator
		*changed = true
		var folded astNode
		switch o.Arity() {
		case 1:
			folded = &astNeg{operand: n.args[o.Args[0]], pos: n.pos}
		case 3:
			folded = &astTendsAt{fn: n.args[o.Args[0]], limit: n.args[o.Args[1]], point: n.args[o.Args[2]], pos: n.pos}
		default:
			folded = &astBinOp{op: o.Symbol, left: n.args[o.Args[0]], right: n.args[o.Args[1]], pos: n.pos}
		}
		if rest := n.args[o.Arity():]; len(rest) > 0 {
			return &astApp{fun: folded, args: append([]astNode(nil), rest...), pos: n.pos}
		}
		return folded
	case *astBinOp:
		n.left = foldOperators(n.left, table, bound, declared, changed)
		n.right = foldOperators(n.right, table, bound, declared, changed)
	case *astCong:
		n.left = foldOperators(n.left, table, bound, declared, changed)
		n.right = foldOperators(n.right, table, bound, declared, changed)
		n.modulus = foldOperators(n.modulus, table, bound, declared, changed)
	case *astTendsAt:
		n.fn = foldOperators(n.fn, table, bound, declared, changed)
		n.limit = foldOperators(n.limit, table, bound, declared, changed)
		n.point = foldOperators(n.point, table, bound, declared, changed)
	case *astNotNode:
		n.body = foldOperators(n.body, table, bound, declared, changed)
	case *astCoerce:
		n.operand = foldOperators(n.operand, table, bound, declared, changed)
	case *astNeg:
		n.operand = foldOperators(n.operand, table, bound, declared, changed)
	case *astOutfix:
		for i, a := range n.args {
			n.args[i] = foldOperators(a, table, bound, declared, changed)
		}
		if n.sub != nil {
			n.sub = foldOperators(n.sub, table, bound, declared, changed)
		}
	case *astQuantNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		n.body = foldOperators(n.body, table, bound, declared, changed)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astAbsNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		n.body = foldOperators(n.body, table, bound, declared, changed)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astPatternAbs:
		leaves := n.pat.leaves(nil)
		for _, lf := range leaves {
			bound[lf.name]++
		}
		n.body = foldOperators(n.body, table, bound, declared, changed)
		for _, lf := range leaves {
			bound[lf.name]--
		}
	case *astBigOp:
		n.bound = foldOperators(n.bound, table, bound, declared, changed)
		bound[n.binder]++
		n.body = foldOperators(n.body, table, bound, declared, changed)
		bound[n.binder]--
	}
	return node
}

// isBuiltinPower reports whether name is a power constant the DSL's
// `^` reads at a built-in domain (arith.go's powDomainOperator): the
// names the chapter-spelling fold writes back as the symbol.
func isBuiltinPower(name string) bool {
	return name == "nat_pow" || name == "real_pow" || name == "int_pow"
}
