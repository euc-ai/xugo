// bigop.go — the big-operator notation form: `Σ_{i<m} body`,
// `Σ_{i∈s} body`.
//
// A sum is a fold — `iterated_op(op, s, f)` in the fold mechanism's
// vocabulary (iterate/monoidal) — and the corpus names the fold at a
// carrier's addition where it has grown algebra of its own: `sum` at
// ℝ, `nat_sum` at ℕ, `int_sum` at ℤ. A chapter declares such a constant the
// big operator at its carrier (registry.DefEntry.BigOp, `"Σ"`; a
// product declares `"Π"`), and it arrives here as ConstSyntax.BigOp
// (syntax.go). The text then writes
//
//	Σ_{i<m} body   ↦ real_sum({i:num | i < m}, λi:num. body)                   body : real
//	Σ_{i∈s} body   ↦ nat_sum(s, λi:A. body)                                   body : num
//	Σ_{i<m} body   ↦ iterated_op(vadd(real_add), {i:num | i < m}, λi:num. body)   body : num → real
//
// The index binds over the body and carries no annotation: its type is
// the range's — the bound's own type under `<` (the corpus's half-open
// range `{i | i < m}`), the set's element type under `∈`. The body is
// read at the scalar action's level (parseSmul): `Σ_{i<m} x(i) • e(i)`
// sums the terms, `Σ_{i<m} a(i) + b` adds b to the sum, and a sum whose
// terms add is parenthesized. The head is dispatched by the BODY's type
// at build time: the constant declaring the symbol at that carrier, or
// — where none does — the fold mechanism at that carrier's `+` (`*` for
// Π), the operator table's instance at the type: a built-in domain's,
// or a chapter's declared operator with its implicit prefix completed
// (`vadd(real_add)` at `num → real`). A carrier with neither is
// refused; at a type variable a chapter writes `iterated_op(add, s, f)`.
// No vector sum is minted for this: a sum of vectors IS the fold, and
// vector/vec_space's README says why.
//
// foldBigOps and printBigOp are the printer's half, run by
// ChapterSpelling: a declared sum applied to a set and a λ, or the fold
// mechanism at a declared `+` (`*`) applied to them, folds into the
// binder — `Σ_{i<m}` when the set is the half-open range below m,
// `Σ_{i∈s}` otherwise. A fold over a bare function (`iterated_op(vadd, s,
// F)`) has no λ to bind and keeps the application: the two spellings
// are one statement (keys are η-invariant, and the apply rung and the
// assumption step identify them) but two kernel terms, and a printed
// claim denotes the term the proof stated — so the binder is the
// author's choice, not the printer's.

package dsl

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// bigOpFoldSymbol is the operator symbol a big operator folds at where
// no constant declares it: Σ folds at `+`, Π at `*`.
var bigOpFoldSymbol = map[string]string{"Σ": "+", "Π": "*"}

// BigOpSymbolOK reports whether symbol is a big operator the grammar
// parses — the define door's check on a declared notation.
func BigOpSymbolOK(symbol string) bool {
	_, ok := bigOpFoldSymbol[symbol]
	return ok
}

// parseBigOp reads `Σ_{i<m} body` / `Σ_{i∈s} body` with the symbol
// token already peeked; the body is read at the scalar action's level.
func (p *parser) parseBigOp() (astNode, *InputDiagnostic) {
	tok := p.advance()
	refuse := func(at token, msg string) *InputDiagnostic {
		return &InputDiagnostic{
			Position: at.pos, Length: len(at.text), Code: CodeParseError,
			Message:    msg,
			Suggestion: fmt.Sprintf("write %s_{i<m} body or %s_{i∈s} body", tok.text, tok.text),
		}
	}
	if next := p.peek(); next.kind != tokIdent || next.text != "_" {
		return nil, refuse(next, fmt.Sprintf("%s binds its index in a `_{…}` subscript", tok.text))
	}
	p.advance()
	if _, err := p.expect(tokLBrace); err != nil {
		return nil, err
	}
	name, err := p.expect(tokIdent)
	if err != nil {
		return nil, err
	}
	var rel string
	switch p.peek().kind {
	case tokLt:
		rel = "<"
	case tokIn:
		rel = "∈"
	default:
		return nil, refuse(p.peek(), fmt.Sprintf("%s's index runs below a bound (`%s<m`) or over a set (`%s∈s`)", tok.text, name.text, name.text))
	}
	p.advance()
	bound, err := p.parseExpr()
	if err != nil {
		return nil, err
	}
	if _, err := p.expect(tokRBrace); err != nil {
		return nil, err
	}
	body, err := p.parseSmul()
	if err != nil {
		return nil, err
	}
	return &astBigOp{symbol: tok.text, binder: name.text, rel: rel, bound: bound, body: body, pos: tok.pos}, nil
}

// bigOpIndexType is the index's type as the range determines it: the
// bound's own type under `<`, the set's element type under `∈`.
func bigOpIndexType(n *astBigOp, env *typeEnv) (core.HolType, bool) {
	t, ok := inferAstType(n.bound, env)
	if !ok {
		return nil, false
	}
	if n.rel == "<" {
		return t, true
	}
	dom, cod, ok := splitFunType(t)
	if !ok || !cod.Equals(core.TypeBool()) {
		return nil, false
	}
	return dom, true
}

// walkBigOpScopeCollect walks a big operator for the type collectors:
// the range in the enclosing scope, the body with the index bound at
// the range's type — or, when the range's type is not yet known, with
// the index cleared so the body's own uses may pin it.
func walkBigOpScopeCollect(n *astBigOp, env *typeEnv, walk func(astNode, *typeEnv)) {
	walk(n.bound, env)
	prevBound, hadBound := env.bound[n.binder]
	prevInferred, hadInferred := env.inferred[n.binder]
	if indexTy, ok := bigOpIndexType(n, env); ok {
		env.bound[n.binder] = indexTy
	} else {
		delete(env.bound, n.binder)
		delete(env.inferred, n.binder)
	}
	walk(n.body, env)
	if hadBound {
		env.bound[n.binder] = prevBound
	} else {
		delete(env.bound, n.binder)
	}
	if hadInferred {
		env.inferred[n.binder] = prevInferred
	} else {
		delete(env.inferred, n.binder)
	}
}

// buildBigOp lowers a big operator: the range set, the terms as the
// function of the index, and the head the body's type selects.
func buildBigOp(n *astBigOp, env *typeEnv, expected core.HolType) (core.Term, error) {
	bound, err := buildTerm(n.bound, env, false)
	if err != nil {
		return nil, err
	}
	var indexTy core.HolType
	if n.rel == "<" {
		indexTy = bound.Type()
	} else {
		dom, cod, ok := splitFunType(bound.Type())
		if !ok || !cod.Equals(core.TypeBool()) {
			return nil, fmt.Errorf("%s_{%s∈…}: the range is not a set, it has type %s",
				n.symbol, n.binder, ext.FormatType(bound.Type()))
		}
		indexTy = dom
	}

	set := bound
	if n.rel == "<" {
		if set, err = buildTerm(belowRangeAST(n, indexTy), env, false); err != nil {
			return nil, err
		}
	}

	// The terms: λi. body with the index bound at the range's type,
	// the binding saved and restored around the body as buildAbs does.
	prevBound, hadBound := env.bound[n.binder]
	prevInferred, hadInferred := env.inferred[n.binder]
	prevUntyped, hadUntyped := env.untypedAbsVars[n.binder]
	env.bound[n.binder] = indexTy
	delete(env.untypedAbsVars, n.binder)
	body, err := buildExpected(n.body, env, expected)
	if hadBound {
		env.bound[n.binder] = prevBound
	} else {
		delete(env.bound, n.binder)
	}
	if hadInferred {
		env.inferred[n.binder] = prevInferred
	} else {
		delete(env.inferred, n.binder)
	}
	if hadUntyped {
		env.untypedAbsVars[n.binder] = prevUntyped
	} else {
		delete(env.untypedAbsVars, n.binder)
	}
	if err != nil {
		return nil, err
	}
	terms := core.Abs(core.Var(core.TermName(n.binder), indexTy), body)
	carrier := body.Type()

	// The head: the constant declaring the symbol at the carrier …
	if env.syntax != nil {
		if name := env.syntax.BigOpConst(n.symbol, carrier); name != "" {
			meta, err := env.constMeta(name)
			if err != nil {
				return nil, fmt.Errorf("%s at %s: %v", n.symbol, ext.FormatType(carrier), err)
			}
			return buildAppViaMeta(env, meta, []core.Term{set, terms})
		}
	}
	// … or the fold mechanism at the carrier's operation.
	op, err := bigOpFoldOperation(env, n.symbol, carrier)
	if err != nil {
		return nil, err
	}
	fold, err := env.constMeta("iterated_op")
	if err != nil {
		return nil, fmt.Errorf("%s at %s: the fold mechanism's %v", n.symbol, ext.FormatType(carrier), err)
	}
	return buildAppViaMeta(env, fold, []core.Term{op, set, terms})
}

// bigOpFoldOperation is the operation a big operator folds at, at a
// carrier no constant declares it for: the operator table's `+` (`*`)
// at the carrier — a built-in domain's constant, or a chapter's
// declared operator with its implicit prefix completed.
func bigOpFoldOperation(env *typeEnv, symbol string, carrier core.HolType) (core.Term, error) {
	opSymbol := bigOpFoldSymbol[symbol]
	if meta := arithDomainOperator(opSymbol, carrier); !meta.IsZero() {
		if m, ok := env.scopeConstMetas[string(meta.Name())]; ok && m.AbsType().Equals(meta.AbsType()) {
			meta = m
		}
		return meta.Term(), nil
	}
	if env.syntax != nil {
		// Of the constants declaring the symbol, the one that is an
		// operation on the carrier at the components the scope binds;
		// a constant that cannot complete its implicit prefix here is
		// passed over, and its refusal stands only when none serves.
		var firstErr error
		for _, name := range env.syntax.OperatorConsts(opSymbol, 2) {
			syntax := env.syntax.ConstSyntax(name)
			meta, err := env.constMeta(name)
			if err != nil {
				return nil, fmt.Errorf("%s at %s: %v", symbol, ext.FormatType(carrier), err)
			}
			op, ok, err := env.implicitApplication(meta, syntax.Implicit, nil, func(prefix []core.Term) (core.Term, bool) {
				op, err := buildAppViaMeta(env, meta, prefix)
				return op, err == nil && op.Type().Equals(core.MakeFun(carrier, carrier, carrier))
			})
			if err != nil {
				if firstErr == nil {
					firstErr = err
				}
				continue
			}
			if ok {
				return op, nil
			}
		}
		if firstErr != nil {
			return nil, firstErr
		}
	}
	// A resident structure's component at the carrier (structure.go): an
	// operation ON the carrier, which the fold needs.
	if op, err := env.structureOperation(opSymbol, []core.HolType{carrier, carrier}); err != nil {
		return nil, err
	} else if op != nil && op.Type().Equals(core.MakeFun(carrier, carrier, carrier)) {
		return op, nil
	}
	return nil, fmt.Errorf("%s has no instance at %s: no constant declares it there, %s has no instance at that type, "+
		"and no resident structure binds it there (write the fold: iterated_op(add, s, f))", symbol, ext.FormatType(carrier), opSymbol)
}

// belowRangeAST is the half-open range `{i:T | i < m}` a `<` big
// operator sums over, as the set-builder AST the parser would have
// read — its binder fresh against the bound, so a bound mentioning the
// index name (an outer variable of that name) is not captured.
func belowRangeAST(n *astBigOp, indexTy core.HolType) astNode {
	binder := n.binder
	for freeIn(n.bound, binder) {
		binder += "'"
	}
	v := &astVar{name: fmt.Sprintf("GEN%%PVAR%%%d", n.pos), pos: n.pos}
	x := &astVar{name: binder, pos: n.pos}
	ty := holTypeToAst(indexTy)
	comprehensionSpec := &astApp{
		fun:  &astVar{name: "comprehension_spec", pos: n.pos},
		args: []astNode{v, &astBinOp{op: "<", left: &astVar{name: binder, pos: n.pos}, right: n.bound, pos: n.pos}, x},
		pos:  n.pos,
	}
	exists := &astQuantNode{quantifier: utils.ExistsStr, varName: binder, varType: ty, body: comprehensionSpec, pos: n.pos}
	lambda := &astAbsNode{varName: v.name, varType: ty, body: exists, pos: n.pos}
	return &astApp{fun: &astVar{name: "set_comprehension", pos: n.pos}, args: []astNode{lambda}, pos: n.pos}
}

// holTypeToAst spells a HOL type as the type AST resolveType reads back
// to it.
func holTypeToAst(t core.HolType) astType {
	switch t := t.(type) {
	case core.VarType:
		return &astTypeNamed{name: "var:" + string(t.Name())}
	case core.CompositeType:
		if t.Meta().Equals(core.MetaTypeFun()) {
			return &astTypeFun{domain: holTypeToAst(t.SubType(0)), codomain: holTypeToAst(t.SubType(1))}
		}
		args := make([]astType, t.Meta().Arity())
		for i := range args {
			args[i] = holTypeToAst(t.SubType(i))
		}
		return &astTypeNamed{name: string(t.Meta().Name()), args: args}
	}
	panic(fmt.Sprintf("dsl: holTypeToAst: unexpected type %T", t))
}

// freeIn reports whether name occurs free in node.
func freeIn(node astNode, name string) bool {
	switch n := node.(type) {
	case *astVar:
		return n.name == name
	case *astField:
		return freeIn(n.receiver, name)
	case *astApp:
		if freeIn(n.fun, name) {
			return true
		}
		for _, a := range n.args {
			if freeIn(a, name) {
				return true
			}
		}
	case *astBinOp:
		return freeIn(n.left, name) || freeIn(n.right, name)
	case *astCong:
		return freeIn(n.left, name) || freeIn(n.right, name) || freeIn(n.modulus, name)
	case *astTendsAt:
		return freeIn(n.fn, name) || freeIn(n.limit, name) || freeIn(n.point, name)
	case *astNotNode:
		return freeIn(n.body, name)
	case *astCoerce:
		return freeIn(n.operand, name)
	case *astNeg:
		return freeIn(n.operand, name)
	case *astOutfix:
		for _, a := range n.args {
			if freeIn(a, name) {
				return true
			}
		}
		return n.sub != nil && freeIn(n.sub, name)
	case *astQuantNode:
		return n.varName != name && freeIn(n.body, name)
	case *astAbsNode:
		return n.varName != name && freeIn(n.body, name)
	case *astPatternAbs:
		for _, lf := range n.pat.leaves(nil) {
			if lf.name == name {
				return false
			}
		}
		return freeIn(n.body, name)
	case *astBigOp:
		return freeIn(n.bound, name) || (n.binder != name && freeIn(n.body, name))
	}
	return false
}

// ---------------------------------------------------------------------------
// The printer's half
// ---------------------------------------------------------------------------

// foldBigOps rewrites, bottom-up, every application that is a big
// operator into the binder: a constant declaring the symbol applied to
// a set and a λ, or the fold mechanism applied to an operation, a set
// and a λ where the operation is a constant declaring `+` (`*`) or a
// structure's bound component carrying it (structure.go).
func foldBigOps(node astNode, table SyntaxTable, structureOps map[string][]structureOperator, bound map[string]int, declared map[string]bool, changed *bool) astNode {
	fold := func(n astNode) astNode { return foldBigOps(n, table, structureOps, bound, declared, changed) }
	switch n := node.(type) {
	case *astField:
		n.receiver = fold(n.receiver)
	case *astApp:
		for i, a := range n.args {
			n.args[i] = fold(a)
		}
		head, isVar := n.fun.(*astVar)
		if !isVar {
			n.fun = fold(n.fun)
			return n
		}
		if bound[head.name] > 0 || declared[head.name] {
			return n
		}
		// The head may carry a `⟨…⟩` type annotation — the printer's
		// disambiguation where a polymorphic constant occurs at two
		// instances in one statement — and the binder needs none: its
		// instance is the body's type. A sum applied beyond its terms,
		// `iterated_op(vadd, s, F, j)`, is the binder applied: `(Σ_{i∈s} F(i))(j)`.
		applied := func(folded *astBigOp, rest []astNode) astNode {
			*changed = true
			if len(rest) == 0 {
				return folded
			}
			return &astApp{fun: folded, args: append([]astNode(nil), rest...), pos: n.pos}
		}
		if syntax := table.ConstSyntax(head.name); syntax != nil && syntax.BigOp != nil && len(n.args) >= 2 && (len(syntax.Implicit) == 0 || n.elided) {
			if lam, ok := n.args[1].(*astAbsNode); ok {
				return applied(bigOpOf(syntax.BigOp.Symbol, n.args[0], lam, n.pos), n.args[2:])
			}
		}
		if head.name == "iterated_op" && len(n.args) >= 3 {
			op, isVar := n.args[0].(*astVar)
			if !isVar || len(op.typeAnnot) > 0 {
				return n
			}
			opSymbol := foldOperationSymbol(op.name, table, structureOps, bound, declared)
			for symbol, wanted := range bigOpFoldSymbol {
				if wanted != opSymbol {
					continue
				}
				if lam, ok := n.args[2].(*astAbsNode); ok {
					return applied(bigOpOf(symbol, n.args[1], lam, n.pos), n.args[3:])
				}
			}
		}
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

// foldRecordBigOp reads a record field used as a fold operation under
// the exact binder types at its occurrence. A sum is printed only when
// the operator builder selects that same field.
func foldRecordBigOp(n *astApp, env *typeEnv) astNode {
	head, ok := n.fun.(*astVar)
	if !ok || head.name != "iterated_op" || len(n.args) < 3 {
		return nil
	}
	op, ok := n.args[0].(*astVar)
	if !ok || len(op.typeAnnot) > 0 {
		return nil
	}
	owner, name, ok := strings.Cut(op.name, ".")
	if !ok {
		return nil
	}
	typ, known := env.lookupType(owner)
	if !known || typ == nil {
		return nil
	}
	field, err := structFieldAt(env.syntax, typ, name)
	if err != nil || field.Arity != 2 {
		return nil
	}
	opTerm, err := buildStructField(&astField{receiver: &astVar{name: owner}, name: name}, env)
	if err != nil {
		return nil
	}
	lam, ok := n.args[2].(*astAbsNode)
	if !ok {
		return nil
	}
	for symbol, wanted := range bigOpFoldSymbol {
		if field.Symbol == wanted {
			carrier, _, isFun := splitFunType(opTerm.Type())
			if !isFun || env.syntax.BigOpConst(symbol, carrier) != "" {
				return nil
			}
			selected, err := bigOpFoldOperation(env, symbol, carrier)
			if err != nil || !selected.Equals(opTerm) {
				return nil
			}
			folded := bigOpOf(symbol, n.args[1], lam, n.pos)
			if len(n.args) == 3 {
				return folded
			}
			return &astApp{fun: folded, args: append([]astNode(nil), n.args[3:]...), pos: n.pos}
		}
	}
	return nil
}

// foldOperationSymbol is the binary operator symbol a bare operation
// name carries in the text: a constant declaring one (`vadd` ↦ `+`),
// or a structure's bound component (`add` ↦ `+` under the ring's
// fact) under the symbol the parser reads back as it
// (componentSymbol); "" for neither.
func foldOperationSymbol(name string, table SyntaxTable, structureOps map[string][]structureOperator, bound map[string]int, declared map[string]bool) string {
	if bound[name] == 0 && !declared[name] {
		if s := table.ConstSyntax(name); s != nil && s.Operator != nil && s.Operator.Arity() == 2 {
			return s.Operator.Symbol
		}
	}
	if bound[name] <= 1 {
		if symbol, ok := componentSymbol(structureOps, name, 2); ok {
			return symbol
		}
	}
	return ""
}

// bigOpOf is the binder a sum over set with terms lam folds into:
// `Σ_{i<m}` when the set is the half-open range below m and m does not
// mention the index name, `Σ_{i∈set}` otherwise. The index is the λ's
// own binder.
func bigOpOf(symbol string, set astNode, lam *astAbsNode, pos int) *astBigOp {
	if m, ok := belowRange(set); ok && !freeIn(m, lam.varName) {
		return &astBigOp{symbol: symbol, binder: lam.varName, rel: "<", bound: m, body: lam.body, pos: pos}
	}
	return &astBigOp{symbol: symbol, binder: lam.varName, rel: "∈", bound: set, body: lam.body, pos: pos}
}

// belowRange recognizes the half-open range `{x | x < m}` — the
// identity set-builder whose predicate is the binder strictly below a
// bound that does not mention it — and returns the bound.
func belowRange(set astNode) (astNode, bool) {
	app, ok := set.(*astApp)
	if !ok || len(app.args) != 1 {
		return nil, false
	}
	head, ok := app.fun.(*astVar)
	if !ok || head.name != "set_comprehension" || len(head.typeAnnot) > 0 {
		return nil, false
	}
	lam, ok := app.args[0].(*astAbsNode)
	if !ok {
		return nil, false
	}
	q, ok := lam.body.(*astQuantNode)
	if !ok || q.quantifier != utils.ExistsStr {
		return nil, false
	}
	ss, ok := q.body.(*astApp)
	if !ok || len(ss.args) != 3 {
		return nil, false
	}
	sf, ok := ss.fun.(*astVar)
	if !ok || sf.name != "comprehension_spec" || len(sf.typeAnnot) > 0 {
		return nil, false
	}
	v, ok := ss.args[0].(*astVar)
	if !ok || v.name != lam.varName || len(v.typeAnnot) > 0 {
		return nil, false
	}
	out, ok := ss.args[2].(*astVar)
	if !ok || out.name != q.varName || len(out.typeAnnot) > 0 {
		return nil, false
	}
	phi, ok := ss.args[1].(*astBinOp)
	if !ok || phi.op != "<" {
		return nil, false
	}
	x, ok := phi.left.(*astVar)
	if !ok || x.name != q.varName || len(x.typeAnnot) > 0 {
		return nil, false
	}
	if freeIn(phi.right, q.varName) || freeIn(phi.right, lam.varName) {
		return nil, false
	}
	return phi.right, true
}

// printBigOp renders a big operator. The body prints at the scalar
// action's level, where the parser reads it; the whole binder is
// parenthesized where the context would otherwise read what follows
// into the body — as a left operand of `•`, `*`, `/`, or anywhere a
// tighter operator's operand ends before the statement does.
func (p *stmtPrinter) printBigOp(n *astBigOp, ctxLev int, tail bool) (string, error) {
	parens := ctxLev > levAdd && !tail
	bound, err := p.node(n.bound, levExpr, true)
	if err != nil {
		return "", err
	}
	body, err := p.node(n.body, levSmul, tail || parens)
	if err != nil {
		return "", err
	}
	s := n.symbol + "_{" + prettyName(n.binder) + n.rel + bound + "} " + body
	if parens {
		return "(" + s + ")", nil
	}
	return s, nil
}
