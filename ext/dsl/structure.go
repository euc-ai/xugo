// structure.go — a structure's components carrying operator symbols.
//
// A structure is a predicate over explicit components on a free carrier
// (constitution §Structures): `comm_monoid(op, e)`, or a predicate of a
// record value holding them, `comm_ring(R)`, whose fields carry their
// own symbols (struct_fields.go). Under a law over a structure on
// component variables the components are ∀-bound variables, and at a
// type variable no operator has an instance — `+` at num is `+`, at
// real `real_add`, at `A` nothing — so its operations spell as
// applications, `op(c, d)`, beside a vector `c • u + d • u` whose
// operators the module's constants declare. The structure's definition
// may declare which of its components carry which symbol
// (registry.DefEntry.Symbols — `add ↦ +`, `sub ↦ -`, `mul ↦ *`, `neg ↦`
// prefix `-`), and it arrives here as ConstSyntax.Structure. Only a
// structure whose component has one fixed reading declares: a
// commutative monoid's `op` is ℝ's addition in one instance and its
// multiplication in another, and stays `op(x, y)`.
//
// The binding is read off the STRUCTURE factorial, never off a name: a text
// whose antecedent applies a declaring predicate to variables — a law's
// `S(add, zero, neg, mul) ⇒ …` for a declaring S — or a goal whose
// resident hypotheses do (ParseScope.ResidentFacts: a proof body's
// claims, a session's goal) binds, for each declared component, the
// symbol to THAT variable. The build resolves `x + y` at its operands —
// after the built-in domains and the declared operator constants both
// decline — to the bound variable whose type takes the operands' types
// in order: one carrier for the ring's `+`, a scalar then a vector for
// a module's `•` (`smul : A → B → B`), so a `+` on the ring's carrier
// and a `+` on vectors over it are two operators, each on its own
// operands, and a text with two structures at one signature is
// refused. The same rule serves the big operator's fold at the carrier:
// `Σ_{i∈s} F(i, j)` at `A` is `iterated_op(add, s, λi. F(i, j))`.
// foldStructureOperators is the printer's half.

package dsl

import (
	"fmt"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// StructureSyntax is what a structure's definition declares about its
// components' text: per component position, the operator symbol it
// carries ("" for none) and its arity as the operator (2 infix, 1
// prefix).
type StructureSyntax struct {
	Components []StructureComponent
}

// StructureComponent is one component's declaration.
type StructureComponent struct {
	Symbol string
	Arity  int
}

// structureOperator is one bound component: the variable's name and
// the arity the symbol takes it at.
type structureOperator struct {
	name  string
	arity int
	// seq is the binding's position in text order: the structure fact
	// that binds a component to a symbol first, counts first. One
	// component two structures spell differently — one declaring
	// structure's `*` and another's `+` on the same variable — folds
	// into the first fact's symbol, never into whichever a map walk
	// happens to yield.
	seq int
	// proj and typeName are set for a FIELD of a structure value
	// (struct_fields.go): the variable is of the structure type typeName
	// and the operation is the projection proj applied to it. "" for a
	// component variable a structure fact binds.
	proj, typeName string
	// reads is the printer's mark that the parser reads the symbol back
	// as this very component (markStructureSymbolsRead): the folds write
	// a symbol for a component only where it is set. The parser never
	// sets it.
	reads bool
	// shown is the printer's mark on a field of a record the text shows
	// without typing it (withShownRecords): the parser meets the record
	// at a type the text does not give. The parser never sets it.
	shown bool
}

// structureOperators reads the symbol bindings a parse works under:
// every application of a declaring structure predicate to variables in
// the roots (the text's own antecedents) and in the resident facts (the
// goal's hypotheses) binds its symbols to those variables, and every
// binder in the roots or declared variable of a structure type binds
// the symbols the type's fields carry, at the projection applied to
// the variable (struct_fields.go). Resident aliases are resolved at
// the use's binder scope.
// structureBoundNames is the set of variables some structure predicate
// is applied to anywhere in roots — `T` in `is_topology(T)`, `R` in
// `comm_ring(R)` — the variables a
// statement carries a structure over, whose implicit occurrences the
// chapter spelling may drop. The same criterion as the registration
// lint's (TestLintImplicitSpellingNeedsStructure), read off the text.
func structureBoundNames(table SyntaxTable, roots []astNode) map[string]bool {
	out := map[string]bool{}
	if table == nil {
		return out
	}
	for _, root := range roots {
		walkAST(root, func(n astNode) {
			app, ok := n.(*astApp)
			if !ok {
				return
			}
			head, ok := app.fun.(*astVar)
			if !ok || len(head.typeAnnot) > 0 {
				return
			}
			if s := table.ConstSyntax(head.name); s == nil || !s.StructurePredicate {
				return
			}
			for _, a := range app.args {
				if v, ok := a.(*astVar); ok {
					out[v.name] = true
				}
			}
		})
	}
	return out
}

// componentVariables is the set of variables a structure predicate is
// applied to in roots or in a resident fact, a resident fact's under
// their own names and the names the text spells them by (names). They
// are the variables a parse reads as components beside components a
// record or an instance supplies (operator.go, mixedComponentSources).
func componentVariables(table SyntaxTable, roots []astNode, resident []core.Term, names map[string]string) map[string]bool {
	out := structureBoundNames(table, roots)
	if table == nil {
		return out
	}
	var walk func(t core.Term)
	walk = func(t core.Term) {
		if app, ok := t.AsAppliedTerm(); ok {
			head, args := ext.MatchesApply(t)
			if c, ok := head.AsConst(); ok {
				if s := table.ConstSyntax(string(c.Name())); s != nil && s.StructurePredicate {
					for _, a := range args {
						if v, ok := a.AsVar(); ok {
							out[string(v.Name())] = true
							if spelled := names[string(v.Name())]; spelled != "" {
								out[spelled] = true
							}
						}
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
	for _, fact := range resident {
		walk(fact)
	}
	return out
}

func structureOperators(table SyntaxTable, roots []astNode, resident []core.Term, declared map[string]core.HolType) map[string][]structureOperator {
	if table == nil {
		return nil
	}
	ops := map[string][]structureOperator{}
	seq := 0
	add := func(symbol, name string, arity int) {
		for _, o := range ops[symbol] {
			if o.name == name && o.proj == "" && o.arity == arity {
				return
			}
		}
		ops[symbol] = append(ops[symbol], structureOperator{name: name, arity: arity, seq: seq})
		seq++
	}
	addFields := func(name, typeName string) {
		s := table.StructSyntax(typeName)
		if s == nil {
			return
		}
		for _, f := range s.Fields {
			if f.Symbol == "" {
				continue
			}
			dup := false
			for _, o := range ops[f.Symbol] {
				if o.name == name && o.proj == f.Const && o.arity == f.Arity {
					dup = true
				}
			}
			if dup {
				continue
			}
			ops[f.Symbol] = append(ops[f.Symbol], structureOperator{name: name, arity: f.Arity, seq: seq, proj: f.Const, typeName: typeName})
			seq++
		}
	}
	for _, root := range roots {
		walkAST(root, func(n astNode) {
			switch n := n.(type) {
			case *astQuantNode:
				if t, ok := n.varType.(*astTypeNamed); ok {
					addFields(n.varName, t.name)
				}
			case *astAbsNode:
				if t, ok := n.varType.(*astTypeNamed); ok {
					addFields(n.varName, t.name)
				}
			}
		})
	}
	names := make([]string, 0, len(declared))
	for name := range declared {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		addFields(name, structTypeName(declared[name]))
	}
	for _, root := range roots {
		walkAST(root, func(n astNode) {
			app, ok := n.(*astApp)
			if !ok {
				return
			}
			head, ok := app.fun.(*astVar)
			if !ok || len(head.typeAnnot) > 0 {
				return
			}
			s := table.ConstSyntax(head.name)
			if s == nil || s.Structure == nil || len(app.args) != len(s.Structure.Components) {
				return
			}
			for i, c := range s.Structure.Components {
				if c.Symbol == "" {
					continue
				}
				if v, ok := app.args[i].(*astVar); ok && len(v.typeAnnot) == 0 {
					add(c.Symbol, v.name, c.Arity)
				}
			}
		})
	}
	for _, fact := range resident {
		head, args := spineArgs(fact)
		c, ok := head.AsConst()
		if !ok {
			continue
		}
		s := table.ConstSyntax(string(c.Name()))
		if s == nil || s.Structure == nil || len(args) != len(s.Structure.Components) {
			continue
		}
		for i, comp := range s.Structure.Components {
			if comp.Symbol == "" {
				continue
			}
			if v, ok := args[i].AsVar(); ok {
				add(comp.Symbol, string(v.Name()), comp.Arity)
			}
		}
	}
	if len(ops) == 0 {
		return nil
	}
	return ops
}

// textTypes is the type every name the text binds or declares carries:
// a binder's annotation, a declaration's type; nil for a name some
// binder leaves unannotated, or that two binders or a binder and the
// declaration give different types. The binders a set-builder's parse
// mints (genPVarPrefix) are left out: nothing names them, so they are
// never a component or a record.
func textTypes(roots []astNode, declared map[string]core.HolType) map[string]core.HolType {
	out := make(map[string]core.HolType, len(declared))
	for name, t := range declared {
		out[name] = t
	}
	bind := func(name string, t astType) {
		if strings.HasPrefix(name, genPVarPrefix) {
			return
		}
		var typ core.HolType
		if t != nil {
			typ = resolveType(t)
		}
		if prev, seen := out[name]; seen && (prev == nil || typ == nil || !prev.Equals(typ)) {
			typ = nil
		}
		out[name] = typ
	}
	for _, root := range roots {
		walkAST(root, func(n astNode) {
			switch n := n.(type) {
			case *astQuantNode:
				bind(n.varName, n.varType)
			case *astAbsNode:
				bind(n.varName, n.varType)
			case *astPatternAbs:
				for _, lf := range n.pat.leaves(nil) {
					bind(lf.name, lf.ty)
				}
			case *astBigOp:
				bind(n.binder, nil)
			}
		})
	}
	return out
}

// markStructureSymbolsRead marks, for the printer, each bound component
// whose symbol the parser reads back as that component — the one
// condition under which a fold may write the symbol for it, a display
// having no key to check against.
//
// Where every name the reading of the symbol consults carries one type
// (textTypes) — the variable of each component and record bound to the
// symbol at that arity, and each implicit argument of a constant
// declaring it, as in a parse-faithful text — the parser's own reading
// decides: the symbol is built at the component's operand types, with
// the built-in domains, the declared operator constants, the fields of
// structure values and the two-structures refusal all in play, and
// must come out as the component applied (fieldSymbolFaithful asks a
// field the same question at its occurrence). The reading binds every
// typed name of the text at once, a superset of those in scope at any
// one occurrence: a symbol it reads as the component reads so wherever
// the component is applied, and one it refuses is printed by name. A
// component spelled as a field of a record value, `R.mul` in a
// declaring predicate applied to `R.add, …, R.mul, …`, is never bound
// by the parser,
// which writes it out as the projection before it reads the facts; its
// symbol reads back through the record's own field, and the build says
// whether it does.
//
// Where one of those names is untyped — a display's binders and
// Skolems, a record the text shows without typing it (shownRecords) —
// the types the parser will meet are unknown, and a symbol reads back
// only when it is bound on that one component at that arity, the
// component a variable: a symbol two holders share — two components,
// or a component and a record's field — is printed for neither (their
// names are the spelling that reads back either way), and a component
// spelled as a record's field is printed by its name, the parser never
// binding it. A field candidate's mark stays unset: its symbol is read
// at the occurrence, under the same condition (fieldHoldsSymbolAlone).
func markStructureSymbolsRead(ops map[string][]structureOperator, table SyntaxTable, types map[string]core.HolType, bindings map[string]core.Term) {
	if len(ops) == 0 {
		return
	}
	env := newTypeEnv()
	// A candidate's type letters are local; the component's carrier stays fixed.
	env.freshenMeta = true
	env.syntax = table
	env.resolver = table.ConstMeta
	env.implicitBindings = bindings
	env.structureOps = ops
	for name, t := range types {
		if t != nil {
			env.bound[name] = t
		}
	}
	typed := func(o *structureOperator) bool {
		receiver, _, _ := strings.Cut(o.name, ".")
		return env.bound[receiver] != nil
	}
	// declaredTyped is whether every implicit argument of the constants
	// declaring symbol at arity is typed or left to the bindings: a name
	// the text binds without one type could complete a constant at an
	// occurrence that the reading here cannot.
	declaredTyped := func(symbol string, arity int) bool {
		for _, name := range table.OperatorConsts(symbol, arity) {
			s := table.ConstSyntax(name)
			if s == nil {
				continue
			}
			for _, implicit := range s.Implicit {
				if t, seen := types[implicit]; seen && t == nil {
					return false
				}
			}
		}
		return true
	}
	for symbol, cands := range ops {
		for i := range cands {
			c := &cands[i]
			if c.proj != "" {
				continue
			}
			readable, others := declaredTyped(symbol, c.arity), 0
			for j := range cands {
				o := &cands[j]
				if o.arity != c.arity {
					continue
				}
				if !typed(o) {
					readable = false
				}
				if o.name != c.name || o.proj != "" {
					others++
				}
			}
			if readable {
				c.reads = symbolReadsBackAs(env, symbol, c)
				continue
			}
			c.reads = others == 0 && !strings.Contains(c.name, ".")
		}
	}
}

// symbolReadsBackAs reports whether symbol, built at the operand types
// of the component c, is c applied to those operands: the parse of
// `a σ b` (or `σ a`) at variables of exactly those types. The
// component is the variable env binds, or, for a record's field
// `R.mul`, the projection applied to the record.
func symbolReadsBackAs(env *typeEnv, symbol string, c *structureOperator) bool {
	var want core.Term
	if receiver, field, isField := strings.Cut(c.name, "."); isField {
		projection, err := buildStructField(&astField{receiver: &astVar{name: receiver}, name: field}, env)
		if err != nil {
			return false
		}
		want = projection
	} else {
		want = core.Var(core.TermName(c.name), env.bound[c.name])
	}
	parts := ext.MatchesFun(want.Type())
	if len(parts) <= c.arity {
		return false
	}
	args := make([]astNode, c.arity)
	for i := range args {
		v := core.Var(core.TermName(fmt.Sprintf("_operand%d", i)), parts[i])
		args[i] = &astTermLit{term: v}
		want = core.Apply(want, v)
	}
	var node astNode
	if c.arity == 1 {
		node = &astNeg{operand: args[0]}
	} else {
		node = &astBinOp{op: symbol, left: args[0], right: args[1]}
	}
	got, err := buildTerm(node, env, false)
	return err == nil && got.Equals(want)
}

// componentSymbol is the symbol a bound component prints under: of the
// symbols the structure facts bind it to at that arity and the parser
// reads back as it (structureOperator.reads), the one bound first in
// text order (structureOperator.seq) — a map walk alone would pick
// among several at random. ok is false when none reads back.
func componentSymbol(ops map[string][]structureOperator, name string, arity int) (symbol string, ok bool) {
	bestSeq := -1
	for candidate, cands := range ops {
		for _, c := range cands {
			if c.proj == "" && c.name == name && c.arity == arity && c.reads && (bestSeq < 0 || c.seq < bestSeq) {
				symbol, bestSeq = candidate, c.seq
			}
		}
	}
	return symbol, bestSeq >= 0
}

// structureOperation is the bound component that is the operation
// symbol at the operand types: the variable in scope whose type takes
// exactly those operands, in order — `A → A → A` for a ring's `+` at
// two members, `A → B → B` for a module's `•` at a scalar and a vector
// — whatever it then yields; or, for a field of a structure value, the
// projection applied to a variable of the type, where that takes the
// operands. Two candidates are two structures at one signature, which
// the text must spell.
func (env *typeEnv) structureOperation(symbol string, operands []core.HolType) (core.Term, error) {
	takes := func(t core.HolType) bool {
		parts := ext.MatchesFun(t)
		if len(parts) <= len(operands) {
			return false
		}
		for i, want := range operands {
			if !parts[i].Equals(want) {
				return false
			}
		}
		return true
	}
	var found core.Term
	for _, o := range env.structureOps[symbol] {
		if o.arity != len(operands) {
			continue
		}
		name := canonicalResidentName(o.name, env.bound, env.declared, env.residentNames)
		t, ok := env.lookupType(name)
		if !ok {
			continue
		}
		var v core.Term
		if o.proj != "" {
			if structTypeName(t) != o.typeName {
				continue
			}
			meta, err := env.constMeta(o.proj)
			if err != nil {
				continue
			}
			x, err := buildVarTerm(name, env, false)
			if err != nil {
				return nil, err
			}
			head, err := buildAppViaMeta(env, meta, []core.Term{x})
			if err != nil || !takes(head.Type()) {
				continue
			}
			v = head
		} else {
			if !takes(t) {
				continue
			}
			var err error
			v, err = buildVarTerm(name, env, false)
			if err != nil {
				return nil, err
			}
		}
		if found != nil {
			if found.AlphaEquals(v) {
				continue
			}
			return nil, fmt.Errorf("operator %s at %s is bound by two structures (%s and %s) — spell the component",
				symbol, formatOperandTypes(operands), ext.PrintTerm(found), ext.PrintTerm(v))
		}
		found = v
	}
	return found, nil
}

// formatOperandTypes spells an operator's operand types, `(A, B)`.
func formatOperandTypes(operands []core.HolType) string {
	out := "("
	for i, t := range operands {
		if i > 0 {
			out += ", "
		}
		out += ext.FormatType(t)
	}
	return out + ")"
}

// buildStructureOperator lowers `left σ right` (or `σ operand`) at
// operands a resident structure binds the symbol on. ok is false when
// no bound component serves the operands.
func buildStructureOperator(env *typeEnv, symbol string, operands []core.Term) (core.Term, bool, error) {
	if len(env.structureOps) == 0 || len(operands) == 0 {
		return nil, false, nil
	}
	types := make([]core.HolType, len(operands))
	for i, o := range operands {
		types[i] = o.Type()
	}
	op, err := env.structureOperation(symbol, types)
	if err != nil {
		return nil, true, err
	}
	if op == nil {
		return nil, false, nil
	}
	t := op
	for _, o := range operands {
		t = core.Apply(t, o)
	}
	return t, true, nil
}

// foldStructureOperators rewrites, bottom-up, every application of a
// bound component at its symbol's arity into the operator the parser
// reads back as that component (componentSymbol). A component is bound
// by the text's own antecedent, so it is a ∀-binder of the statement or
// a declared variable of the goal; a binder nested deeper with the same
// name shadows it and is left as an application.
func foldStructureOperators(node astNode, ops map[string][]structureOperator, bound map[string]int, declared map[string]bool, changed *bool) astNode {
	if len(ops) == 0 {
		return node
	}
	symbolOf := func(name string, arity int, depth int) (string, bool) {
		if depth > 1 {
			return "", false
		}
		return componentSymbol(ops, name, arity)
	}
	switch n := node.(type) {
	case *astField:
		n.receiver = foldStructureOperators(n.receiver, ops, bound, declared, changed)
	case *astApp:
		for i, a := range n.args {
			n.args[i] = foldStructureOperators(a, ops, bound, declared, changed)
		}
		head, isVar := n.fun.(*astVar)
		if !isVar {
			n.fun = foldStructureOperators(n.fun, ops, bound, declared, changed)
			return n
		}
		if len(head.typeAnnot) > 0 {
			return n
		}
		symbol, ok := symbolOf(head.name, len(n.args), bound[head.name])
		if !ok {
			return n
		}
		*changed = true
		if len(n.args) == 1 {
			return &astNeg{operand: n.args[0], pos: n.pos}
		}
		return &astBinOp{op: symbol, left: n.args[0], right: n.args[1], pos: n.pos}
	case *astBinOp:
		n.left = foldStructureOperators(n.left, ops, bound, declared, changed)
		n.right = foldStructureOperators(n.right, ops, bound, declared, changed)
	case *astCong:
		n.left = foldStructureOperators(n.left, ops, bound, declared, changed)
		n.right = foldStructureOperators(n.right, ops, bound, declared, changed)
		n.modulus = foldStructureOperators(n.modulus, ops, bound, declared, changed)
	case *astTendsAt:
		n.fn = foldStructureOperators(n.fn, ops, bound, declared, changed)
		n.limit = foldStructureOperators(n.limit, ops, bound, declared, changed)
		n.point = foldStructureOperators(n.point, ops, bound, declared, changed)
	case *astNotNode:
		n.body = foldStructureOperators(n.body, ops, bound, declared, changed)
	case *astCoerce:
		n.operand = foldStructureOperators(n.operand, ops, bound, declared, changed)
	case *astNeg:
		n.operand = foldStructureOperators(n.operand, ops, bound, declared, changed)
	case *astOutfix:
		for i, a := range n.args {
			n.args[i] = foldStructureOperators(a, ops, bound, declared, changed)
		}
		if n.sub != nil {
			n.sub = foldStructureOperators(n.sub, ops, bound, declared, changed)
		}
	case *astQuantNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		n.body = foldStructureOperators(n.body, ops, bound, declared, changed)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astAbsNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		n.body = foldStructureOperators(n.body, ops, bound, declared, changed)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astPatternAbs:
		leaves := n.pat.leaves(nil)
		for _, lf := range leaves {
			bound[lf.name]++
		}
		n.body = foldStructureOperators(n.body, ops, bound, declared, changed)
		for _, lf := range leaves {
			bound[lf.name]--
		}
	case *astBigOp:
		n.bound = foldStructureOperators(n.bound, ops, bound, declared, changed)
		bound[n.binder]++
		n.body = foldStructureOperators(n.body, ops, bound, declared, changed)
		bound[n.binder]--
	}
	return node
}

// spineArgs splits an application spine into its head and arguments.
func spineArgs(t core.Term) (head core.Term, args []core.Term) {
	for {
		app, ok := t.AsAppliedTerm()
		if !ok {
			return t, args
		}
		args = append([]core.Term{app.Arg()}, args...)
		t = app.Fun()
	}
}
