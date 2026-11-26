// implicit.go — implicit structure arguments.
//
// Derived operations retain the components they read as ordinary HOL
// arguments: vadd(add, u, v), dot⟨n⟩(add, mul, u, v). The text DSL may
// omit a constant's declared leading implicit parameters when the scope
// supplies them. It first uses a bound or declared name, then the
// corresponding field of a record in scope, then a family instance
// binding. A locally bound record therefore shadows the family
// default. A variable named like a component is one where it carries a
// structure — a structure predicate is applied to it, or it is a record
// — or where the prefix is read from variables alone; beside a
// component a record or the instance supplies, a variable that carries
// none only shares the component's name, and the prefix is refused
// (operator.go, mixedComponentSources). Thus a law over R:ring_ops(A) reads vadd(u, v)
// as vadd(R.add, u, v), and an instance reads its concrete addition.
//
// Explicit components remain explicit. Their types distinguish an
// operation supplied for a second structure from a short application;
// an explicit record field also selects the explicit reading when its
// arguments fit. Where several records declare the same field, the
// application's types pick the record (chooseRecords): records on
// different carriers are told apart by the arguments, records on one
// carrier are not, and the text must name the record. A prefix
// spelled only in part is refused unless its written arguments already
// form a well-typed explicit application.
//
// Completion runs on the AST before type collection and produces the
// explicit kernel application. ChapterSpelling (syntax.go) performs the
// inverse operation for surfaces printed under the same scope.

package dsl

import (
	"fmt"
	"maps"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// astTermLit is a pre-built term standing in an argument position: the
// instance's own component term, inserted by the completion pass so
// that what the parser builds is the instance theorem's term exactly —
// no re-parse of a spelling, no coercion inference, no strictness
// question. Never produced by the parser and never printed.
type astTermLit struct {
	term core.Term
	pos  int
}

func (a *astTermLit) nodePos() int { return a.pos }

// implicitCompletion is one parse's view of the implicit-argument
// vocabulary: which constants have implicit binders, what the names
// resolve to, and how an instance's component is inserted.
type implicitCompletion struct {
	syntax    SyntaxTable
	args      func(name string) []string
	completed func(constName, name string, variable bool)
	bindings  map[string]core.Term
	// declared reports whether the scope declares name as a free
	// variable (Vars, an in-text decl, a term parse's ctx) — the
	// section-binder case, where the component is the enclosing
	// section's own variable.
	declared func(name string) bool
	// surface is the scope's ResidentNames: a minted variable's name →
	// the surface name the block spells it by (`zero₀` → `zero`). An
	// argument spelling the minted variable a binder name stands for is
	// that component, as the binder name is (slotMatches).
	surface map[string]string
	// exact inserts an instance component as its TERM (the parse that
	// builds); false inserts its canonical spelling (the elision
	// round-trip, which compares ASTs).
	exact bool
	canon map[string][]astNode
	// constMeta resolves a constant of the scope to its meta — the
	// build's view (the scope's metas, its resolver), and the syntax
	// table's view during elision. declaredType is the
	// declared type of a declared name, nil where the scope declares
	// none. binderTypes is the annotated type of every quantifier and
	// λ binder on the walk's stack, nil for an unannotated one, keyed
	// like bound. The three feed spellsPrefix.
	constMeta     func(name string) core.ConstTermMeta
	declaredType  func(name string) core.HolType
	declaredTypes map[string]core.HolType
	binderTypes   map[string][]core.HolType
	// elideBinder, for the elision round-trip, says whether a component
	// bound to a VARIABLE of that name may be dropped: the chapter
	// spelling passes "some structure predicate in the text is applied
	// to it" (structureBoundNames). nil elides every bound component; a
	// component bound to an instance term is elided regardless.
	elideBinder func(name string) bool
	// definiendum is the name a definition's equation defines, declared
	// as a variable in its scope, with the prefix and the dimension
	// count its constant will carry (dimension.go); nil elsewhere.
	definiendum *Definiendum
	// components are the variables some structure predicate of the text
	// or of a resident fact is applied to (componentVariables).
	components map[string]bool
}

// isComponent reports whether the variable name, bound or declared, may
// stand for a component beside components read elsewhere: a structure
// predicate is applied to it, or its type is a record's.
func (c *implicitCompletion) isComponent(name string, bound map[string]int) bool {
	if c.components[name] {
		return true
	}
	ty, _, known := c.localType(&astVar{name: name}, bound)
	return known && ty != nil && c.syntax.StructSyntax(structTypeName(ty)) != nil
}

func newImplicitCompletion(scope *ParseScope, declared func(string) bool, exact bool) *implicitCompletion {
	if scope == nil || scope.Syntax == nil {
		return nil
	}
	table := scope.Syntax
	return &implicitCompletion{
		syntax: table,
		args: func(name string) []string {
			if s := table.ConstSyntax(name); s != nil {
				return s.Implicit
			}
			return nil
		},
		bindings:    scope.ImplicitBindings,
		completed:   scope.ImplicitCompleted,
		definiendum: scope.Definiendum,
		declared:    declared,
		surface:     scope.ResidentNames,
		exact:       exact,
		canon:       map[string][]astNode{},
		binderTypes: map[string][]core.HolType{},
	}
}

// implicitArgError is the completion's refusal: the constant, and what
// went wrong with its implicit prefix.
type implicitArgError struct {
	msg string
}

func (e *implicitArgError) Error() string { return e.msg }

// complete rewrites node so that every application of a constant with
// implicit binders carries them, and returns the rewritten node. bound
// is the quantifier/abstraction stack (name → depth) of the walk.
func (c *implicitCompletion) complete(node astNode, bound map[string]int) (astNode, error) {
	switch n := node.(type) {
	case *astVar:
		if bound[n.name] > 0 || c.declared(n.name) {
			return n, nil
		}
		names := c.args(n.name)
		if len(names) == 0 || !c.resolvesAny(names, bound) {
			return n, nil
		}
		// A bare head — `monoidal_op(vadd)`, `iterated_op(vadd, s, F)` — is the
		// constant applied to its components and nothing else.
		prefix, err := c.prefix(n.name, n.typeAnnot, names, nil, n.pos, bound)
		if err != nil {
			return nil, err
		}
		return &astApp{fun: n, args: prefix, pos: n.pos}, nil
	case *astField:
		var err error
		n.receiver, err = c.complete(n.receiver, bound)
		return n, err
	case *astApp:
		for i, a := range n.args {
			r, err := c.complete(a, bound)
			if err != nil {
				return nil, err
			}
			n.args[i] = r
		}
		head, isVar := n.fun.(*astVar)
		if !isVar {
			r, err := c.complete(n.fun, bound)
			if err != nil {
				return nil, err
			}
			n.fun = r
			return n, nil
		}
		// A constant's dimensions are placed, and one written in the
		// parentheses refused, before the prefix is read (dimension.go).
		if placed, handled, err := c.completeDimensions(n, head, bound); handled || err != nil {
			return placed, err
		}
		if bound[head.name] > 0 || c.declared(head.name) {
			return n, nil
		}
		names := c.args(head.name)
		if len(names) == 0 || !c.resolvesAny(names, bound) {
			return n, nil
		}
		matched := c.matchedPrefix(head.name, names, n.args, bound)
		recordPrefix := len(n.args) > 0 && c.recordSlotMatches(n.args[0], names[0], bound)
		switch {
		case matched == len(names):
			return n, nil
		case matched == 0:
			if c.spellsPrefix(head.name, head.typeAnnot, names, nil, n.args, bound, recordPrefix) {
				return n, nil
			}
			prefix, err := c.prefix(head.name, head.typeAnnot, names, n.args, n.pos, bound)
			if err != nil {
				return nil, err
			}
			n.args = append(prefix, n.args...)
			return n, nil
		default:
			// Leading arguments that spell bound components and then stop
			// are a prefix spelled in part — unless the arguments spell the
			// whole prefix explicitly, read by type as spellsPrefix reads a
			// prefix whose first argument is no bound component: a module's
			// ring components under the ring's own binders, followed by
			// the vectors' operations of an instance.
			if c.spellsPrefix(head.name, head.typeAnnot, names, nil, n.args, bound, recordPrefix) {
				return n, nil
			}
			return nil, &implicitArgError{fmt.Sprintf(
				"%s: its implicit arguments (%s) are spelled in part — spell all of them or none",
				head.name, strings.Join(names, ", "))}
		}
	case *astBinOp:
		var err error
		if n.left, err = c.complete(n.left, bound); err != nil {
			return nil, err
		}
		if n.right, err = c.complete(n.right, bound); err != nil {
			return nil, err
		}
		return n, nil
	case *astCong:
		var err error
		if n.left, err = c.complete(n.left, bound); err != nil {
			return nil, err
		}
		if n.right, err = c.complete(n.right, bound); err != nil {
			return nil, err
		}
		if n.modulus, err = c.complete(n.modulus, bound); err != nil {
			return nil, err
		}
		return n, nil
	case *astTendsAt:
		var err error
		if n.fn, err = c.complete(n.fn, bound); err != nil {
			return nil, err
		}
		if n.limit, err = c.complete(n.limit, bound); err != nil {
			return nil, err
		}
		if n.point, err = c.complete(n.point, bound); err != nil {
			return nil, err
		}
		return n, nil
	case *astNotNode:
		r, err := c.complete(n.body, bound)
		if err != nil {
			return nil, err
		}
		n.body = r
		return n, nil
	case *astCoerce:
		r, err := c.complete(n.operand, bound)
		if err != nil {
			return nil, err
		}
		n.operand = r
		return n, nil
	case *astNeg:
		r, err := c.complete(n.operand, bound)
		if err != nil {
			return nil, err
		}
		n.operand = r
		return n, nil
	case *astQuantNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		c.pushBinder(n.varName, n.varType)
		r, err := c.complete(n.body, bound)
		c.popBinder(n.varName)
		for _, name := range n.boundNames() {
			bound[name]--
		}
		if err != nil {
			return nil, err
		}
		n.body = r
		return n, nil
	case *astAbsNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		c.pushBinder(n.varName, n.varType)
		r, err := c.complete(n.body, bound)
		c.popBinder(n.varName)
		for _, name := range n.boundNames() {
			bound[name]--
		}
		if err != nil {
			return nil, err
		}
		n.body = r
		return n, nil
	case *astPatternAbs:
		leaves := n.pat.leaves(nil)
		for _, lf := range leaves {
			bound[lf.name]++
			c.pushBinder(lf.name, nil)
		}
		r, err := c.complete(n.body, bound)
		for _, lf := range leaves {
			c.popBinder(lf.name)
			bound[lf.name]--
		}
		if err != nil {
			return nil, err
		}
		n.body = r
		return n, nil
	case *astBigOp:
		r, err := c.complete(n.bound, bound)
		if err != nil {
			return nil, err
		}
		n.bound = r
		bound[n.binder]++
		c.pushBinder(n.binder, nil)
		r, err = c.complete(n.body, bound)
		c.popBinder(n.binder)
		bound[n.binder]--
		if err != nil {
			return nil, err
		}
		n.body = r
		return n, nil
	}
	// astNumLit, astConst, astTermLit: nothing to complete.
	return node, nil
}

// resolvesAny reports whether the scope binds at least one of the
// implicit names — the condition under which the completion pass
// reads an application at all.
func (c *implicitCompletion) resolvesAny(names []string, bound map[string]int) bool {
	for _, name := range names {
		if bound[name] > 0 || c.declared(name) || c.bindings[name] != nil {
			return true
		}
		if _, count := c.recordComponent(name, bound); count > 0 {
			return true
		}
	}
	return false
}

// recordComponent reads a component name from a record in scope: the
// field of the one record declaring it, and how many records do. Where
// several do, chooseRecords picks one by the application's types.
func (c *implicitCompletion) recordComponent(name string, bound map[string]int) (astNode, int) {
	owners := c.recordOwners(name, bound)
	if len(owners) == 0 {
		return nil, 0
	}
	return recordField(owners[0], name), len(owners)
}

// recordOwners lists the records in scope that declare the field name.
func (c *implicitCompletion) recordOwners(name string, bound map[string]int) []string {
	boundTypes := map[string]core.HolType{}
	for owner, depth := range bound {
		if depth > 0 {
			boundTypes[owner] = c.binderType(owner)
		}
	}
	return recordComponentOwners(c.syntax, name, boundTypes, c.declaredTypes, c.surface)
}

// componentOwners lists the records that may supply the implicit
// component name: none where the scope binds or declares the name
// itself, which is then the component.
func (c *implicitCompletion) componentOwners(name string, bound map[string]int) []string {
	if bound[name] > 0 || c.declared(name) {
		return nil
	}
	return c.recordOwners(name, bound)
}

func recordField(owner, name string) *astField {
	return &astField{receiver: &astVar{name: owner}, name: name}
}

// recordComponentOwners lists, in name order, the records in scope that
// declare the field name. A resident variable and its surface alias name
// one record. A bound variable shadowing that alias is a separate record.
func recordComponentOwners(syntax SyntaxTable, name string, bound, declared map[string]core.HolType, surface map[string]string) []string {
	var owners []string
	seen := map[string]bool{}
	visit := func(owner string, ty core.HolType) {
		if ty == nil || syntax == nil || seen[owner] {
			return
		}
		s := syntax.StructSyntax(structTypeName(ty))
		if s == nil || s.field(name) == nil {
			return
		}
		seen[owner] = true
		owners = append(owners, owner)
	}
	for owner, ty := range bound {
		visit(owner, ty)
	}
	for owner, ty := range declared {
		if _, shadowed := bound[owner]; shadowed {
			continue
		}
		visit(canonicalResidentName(owner, bound, declared, surface), ty)
	}
	slices.Sort(owners)
	return owners
}

func canonicalResidentName(name string, bound, declared map[string]core.HolType, surface map[string]string) string {
	if _, bound := bound[name]; bound {
		return name
	}
	if alias := surface[name]; alias != "" {
		_, shadowed := bound[alias]
		ty, aliasType := declared[name], declared[alias]
		if !shadowed && ty != nil && aliasType != nil && ty.Equals(aliasType) {
			return alias
		}
	}
	return name
}

// matchedPrefix counts how many of the leading args spell the implicit
// binders in order, stopping at the first that does not.
func (c *implicitCompletion) matchedPrefix(constName string, names []string, args []astNode, bound map[string]int) int {
	matched := 0
	for i, name := range names {
		if i >= len(args) || !c.slotMatches(args[i], name, bound) {
			break
		}
		matched++
	}
	return matched
}

// recordSlotMatches recognizes a field both as dotted text and as the
// projection application that the field pass expands it to.
func (c *implicitCompletion) recordSlotMatches(arg astNode, name string, bound map[string]int) bool {
	return c.recordFieldName(arg, bound) == name
}

// recordFieldName resolves an explicit field without requiring its name
// to match an implicit binder: a module's smul can supply a function
// operation whose implicit parameter is named mul.
func (c *implicitCompletion) recordFieldName(arg astNode, bound map[string]int) string {
	var receiver astNode
	name, projection := "", ""
	switch a := arg.(type) {
	case *astField:
		receiver, name = a.receiver, a.name
	case *astVar:
		if owner, field, ok := strings.Cut(a.name, "."); ok {
			receiver, name = &astVar{name: owner}, field
		}
	case *astApp:
		if head, ok := a.fun.(*astVar); ok && len(a.args) == 1 && bound[head.name] == 0 && !c.declared(head.name) {
			receiver, projection = a.args[0], head.name
		}
	}
	if receiver != nil {
		if ty, _, _ := c.localType(receiver, bound); ty != nil {
			if record := c.syntax.StructSyntax(structTypeName(ty)); record != nil {
				for _, field := range record.Fields {
					if name != "" && name == field.Name || projection != "" && projection == field.Const {
						return field.Name
					}
				}
			}
		}
	}
	return ""
}

// A pointwise operation such as fun_add(R.add) explicitly chooses its
// component just as R.add does. The surrounding application still has
// to fit the explicit reading in spellsPrefix.
func (c *implicitCompletion) recordComponentExpression(arg astNode, bound map[string]int) bool {
	if c.recordFieldName(arg, bound) != "" {
		return true
	}
	if app, ok := arg.(*astApp); ok {
		if c.recordComponentExpression(app.fun, bound) {
			return true
		}
		for _, a := range app.args {
			if c.recordComponentExpression(a, bound) {
				return true
			}
		}
	}
	return false
}

// slotMatches recognizes a component name, its resident spelling, an
// instance term, or an explicit record field of that name.
func (c *implicitCompletion) slotMatches(arg astNode, name string, bound map[string]int) bool {
	if c.recordSlotMatches(arg, name, bound) {
		return true
	}
	if v, ok := arg.(*astVar); ok && len(v.typeAnnot) == 0 && v.name == name &&
		(bound[name] > 0 || c.declared(name)) {
		return true
	}
	if v, ok := arg.(*astVar); ok && len(v.typeAnnot) == 0 && v.name != name &&
		bound[v.name] == 0 && bound[name] == 0 && c.surface[v.name] == name &&
		c.declared(v.name) && c.declared(name) {
		return true
	}
	if t, ok := c.bindings[name]; ok {
		for _, canon := range c.canonical(name, t) {
			if astNodeEqual(arg, canon) {
				return true
			}
		}
	}
	return false
}

// prefix builds the implicit arguments of constName applied to args, in
// order, a record's field read from the record chooseRecords picks.
func (c *implicitCompletion) prefix(constName string, annot []typeAnnotBinding, names []string, args []astNode, pos int, bound map[string]int) ([]astNode, error) {
	choice, err := c.chooseRecords(constName, annot, names, args, bound)
	if err != nil {
		return nil, err
	}
	var strangers, elsewhere []string
	for _, name := range names {
		switch {
		case bound[name] > 0 || c.declared(name):
			if !c.isComponent(name, bound) {
				strangers = append(strangers, name)
			}
		case choice[name] != "" || c.bindings[name] != nil:
			elsewhere = append(elsewhere, name)
		}
	}
	if err := mixedComponentSources(constName, names, strangers, elsewhere); err != nil {
		return nil, err
	}
	out := make([]astNode, 0, len(names))
	for _, name := range names {
		switch owner := choice[name]; {
		case bound[name] > 0 || c.declared(name):
			out = append(out, &astVar{name: name, pos: pos})
			if c.completed != nil {
				c.completed(constName, name, true)
			}
		case owner != "":
			out = append(out, recordField(owner, name))
			if c.completed != nil {
				c.completed(constName, owner, true)
			}
		case c.bindings[name] != nil:
			if c.completed != nil {
				c.completed(constName, name, false)
			}
			if c.exact {
				out = append(out, &astTermLit{term: c.bindings[name], pos: pos})
			} else {
				canon := c.canonical(name, c.bindings[name])
				if len(canon) == 0 {
					return nil, &implicitArgError{fmt.Sprintf(
						"%s: the instance component for %s (%s) has no spelling the text DSL reads",
						constName, name, ext.PrintTerm(c.bindings[name]))}
				}
				out = append(out, canon[0])
			}
		default:
			return nil, &implicitArgError{fmt.Sprintf(
				"%s: its implicit argument %s is not in scope — spell the arguments (%s) explicitly, "+
					"or state the law under the structure that binds them",
				constName, name, strings.Join(names, ", "))}
		}
	}
	return out, nil
}

// spellsPrefix reports whether an application whose leading argument
// is not a bound component spells its implicit prefix all the same —
// at components the scope does not bind: a chapter at ℤ stating the
// form of a real image, `dot⟨n⟩(real_add, real_mul, vec_of_int(u),
// vec_of_int(v))` under the integer ring; a set-valued constant at a
// SECOND space, `subtopology(real_topology, s)` under a binder `T`. The
// DSL resolves an operator by its operands' types; this is the same
// resolution for a prefix. The two readings — the explicit one, and
// the short one with the scope's components put in front — are each
// type-checked as ONE application (readingMatcher): every argument
// whose type the text fixes on its own (a constant's, a coercion's, an
// annotated binder's, a numeral's, and under the short reading the
// components themselves, whose types the binders, the records or the
// instance give) is matched against its slot under one substitution of
// the constant's letters, so a letter one argument pins is the letter
// every other argument is read at — `T : set(set(A))` in front pins the
// element type to A, and `real_topology : set(set(real))` no longer
// fits the next slot by taking A to be `real → bool`. The prefix is
// spelled when the explicit reading stands and the short one is
// contradicted — at every record a component several records declare
// may be read from (shortReadings). A partial prefix beginning with a
// record field or an operation built from its fields explicitly selects
// that reading when its arguments fit. Otherwise, where both fit
// (`vec_zero(0)`) or nothing local decides, the bound instance's reading
// stands.
//
// dims are the dimensions the text wrote in the head's ⟨…⟩
// (dimension.go), nil for an application without any: they stand behind
// the prefix under either reading — behind the first len(names) of args
// under the explicit one, which then needs that many, and in front of
// args under the short one.
func (c *implicitCompletion) spellsPrefix(constName string, annot []typeAnnotBinding, names []string, dims, args []astNode, bound map[string]int, recordPrefix bool) bool {
	constType, ok := c.constTypeApart(constName, annot, constLetterMark)
	if !ok {
		return false
	}
	slots := argumentSlots(constType)
	if len(slots) == 0 {
		return false
	}
	matcher := newReadingMatcher(c.syntax, constType)
	written := c.writtenTypings(args, bound)
	explicit, short := written, written
	if len(dims) > 0 {
		if len(args) < len(names) {
			return false
		}
		at := c.writtenTypings(dims, bound)
		explicit = slices.Concat(written[:len(names)], at, written[len(names):])
		short = slices.Concat(at, written)
	}
	if !matcher.fits(explicit) {
		return false
	}
	// A compound operation chooses its component, but an ordinary
	// operand may also contain fields. In particular polynomial_degree
	// reads a zero, so polynomial_degree(polynomial_mul(R.add, ...))
	// still needs that zero inserted before its polynomial operand; and
	// fun_add's operand fun_zero(M.zero), a function of the index type,
	// is no operation on the carrier, so fun_add(fun_zero(M.zero), u)
	// still needs the addition inserted before it.
	operationPrefix := len(args) > 0 && len(ext.MatchesFun(slots[0])) > 1 &&
		c.recordComponentExpression(args[0], bound) && mayFill(slots[0], written[0])
	return recordPrefix || operationPrefix || len(c.shortReadings(matcher, names, short, bound, 1)) == 0
}

// mayFill reports whether an argument the text types as r can stand in
// slot. A type the text fixes in full has been matched by the reading
// already; one it fixes in part — an application's result whose own
// letters (appliedLetterMark) the arguments leave open — must unify with
// the slot, the letters of both open and the statement's fixed.
func mayFill(slot core.HolType, r localTyping) bool {
	if r.known || r.typ == nil {
		return true
	}
	_, ok := unifyStandIns(slot, r.typ, func(v core.VarType) bool {
		return isConstLetter(v) || strings.HasPrefix(string(v.Name()), appliedLetterMark)
	})
	return ok
}

// chooseRecords is the record each implicit component of constName
// applied to args is read from, by component name: the one record in
// scope declaring that field, or, where several records declare it, the
// one the application's types pick — of the short readings shortReadings
// tries, the one that stands. Records on different carriers are told
// apart by the written arguments: `polynomial_eval(p, x)` with
// `p : num → B` under `F : field_on(A)` and `G : field_on(B)` reads G's
// fields. Records on one carrier, or arguments whose types the text
// leaves open, leave several readings standing; none is guessed, and the
// text names the record. A component the scope binds by its own name is
// not a record's, and one no record declares is the instance's.
func (c *implicitCompletion) chooseRecords(constName string, annot []typeAnnotBinding, names []string, args []astNode, bound map[string]int) (map[string]string, error) {
	choice := map[string]string{}
	var ambiguous string
	for _, name := range names {
		switch owners := c.componentOwners(name, bound); {
		case len(owners) == 1:
			choice[name] = owners[0]
		case len(owners) > 1 && ambiguous == "":
			ambiguous = name
		}
	}
	if ambiguous == "" {
		return choice, nil
	}
	if constType, ok := c.constTypeApart(constName, annot, constLetterMark); ok {
		readings := c.shortReadings(newReadingMatcher(c.syntax, constType), names, c.writtenTypings(args, bound), bound, 2)
		if len(readings) == 1 {
			return readings[0], nil
		}
	}
	return nil, &implicitArgError{fmt.Sprintf(
		"%s: its implicit argument %s is a field of more than one record in scope (%s) and the arguments' types do not pick one — spell the record field explicitly",
		constName, ambiguous, strings.Join(c.componentOwners(ambiguous, bound), ", "))}
}

// shortReadings returns, up to limit, the short readings of an
// application that its types leave standing: the components the scope
// supplies put in front of the written arguments and read by matcher as
// one application. A component several records declare is tried at
// each of them in turn, a choice that already contradicts its slot cut
// off there, so a reading is one record per record-supplied component,
// returned as component name → record.
func (c *implicitCompletion) shortReadings(matcher readingMatcher, names []string, written []localTyping, bound map[string]int, limit int) []map[string]string {
	var found []map[string]string
	choice := map[string]string{}
	var walk func(m readingMatcher, i int)
	walk = func(m readingMatcher, i int) {
		if len(found) >= limit {
			return
		}
		if i == len(names) {
			if m.fits(written) {
				found = append(found, maps.Clone(choice))
			}
			return
		}
		name := names[i]
		owners := c.componentOwners(name, bound)
		if len(owners) == 0 {
			if next, ok := m.fit(c.componentType(name, bound)); ok {
				walk(next, i+1)
			}
			return
		}
		// A name the prefix repeats is one component, read from one record.
		earlier, repeated := choice[name]
		if repeated {
			owners = []string{earlier}
		}
		for _, owner := range owners {
			ty, coercion, known := c.localType(recordField(owner, name), bound)
			if next, ok := m.fit(localTyping{ty, coercion, known}); ok {
				choice[name] = owner
				walk(next, i+1)
			}
		}
		if !repeated {
			delete(choice, name)
		}
	}
	walk(matcher, 0)
	return found
}

// writtenTypings is what the text fixes about each written argument of
// an application (localType); a constant standing bare is read at its
// declared type, letters and all.
func (c *implicitCompletion) writtenTypings(args []astNode, bound map[string]int) []localTyping {
	reading := make([]localTyping, 0, len(args))
	for _, arg := range args {
		ty, coercion, known := c.localType(arg, bound)
		if !known && !coercion {
			if head, ok := arg.(*astVar); ok && bound[head.name] == 0 && !c.declared(head.name) {
				if meta := c.constMeta(head.name); !meta.IsZero() {
					ty = meta.AbsType()
				}
			}
		}
		reading = append(reading, localTyping{ty, coercion, known})
	}
	return reading
}

// readingMatcher type-checks one reading of an application argument by
// argument, under one substitution of the constant's letters (marked
// constLetterMark): an argument whose type the text fixes must fit its
// slot as the earlier arguments pinned it. Past the spine the
// constant's RESULT stands, and it too is a type the text fixes: a
// reading that puts an argument beyond the last slot is contradicted
// unless the result is a type variable, which an instance may make a
// function (`iterate`'s carrier), and from there on anything fits. A
// predicate — `closed_in(S, c)` at a second space under a bound `T` —
// yields bool and takes nothing more, so a short reading there is
// contradicted by arity. A matcher is a value: fit returns the next one
// and leaves its receiver as it was, so a search may branch from it.
type readingMatcher struct {
	syntax SyntaxTable
	slots  []core.HolType
	result core.HolType
	sigma  []core.TypeSubst
	next   int
	open   bool
}

func newReadingMatcher(syntax SyntaxTable, constType core.HolType) readingMatcher {
	return readingMatcher{syntax: syntax, slots: argumentSlots(constType), result: spineResult(constType)}
}

func isConstLetter(v core.VarType) bool {
	return strings.HasPrefix(string(v.Name()), constLetterMark)
}

// fit reads the next argument of the reading: false when it contradicts
// its slot.
func (m readingMatcher) fit(r localTyping) (readingMatcher, bool) {
	if m.open {
		return m, true
	}
	var slot core.HolType
	if m.next < len(m.slots) {
		slot = m.slots[m.next].Substitute(m.sigma...)
	} else {
		result := m.result.Substitute(m.sigma...)
		if len(ext.MatchesFun(result)) < 2 {
			v, isVar := result.(core.VarType)
			m.open = isVar && isConstLetter(v)
			return m, m.open
		}
		slot, m.result = result.(core.CompositeType).SubType(0), result.(core.CompositeType).SubType(1)
	}
	m.next++
	switch {
	case !r.known:
		return m, r.typ == nil || !incompatibleTypeShape(slot, r.typ)
	case r.coercion:
		// A coercion is a real or an int, or the lift of one into a type
		// some constant is the declared coercion into (build.go,
		// buildCoerce) — never a num, never a function — so it fits a slot
		// at a type variable, at either numeric type, or at such a
		// codomain: the `&0` of `polynomial_eval(complex_add, &0, …)`,
		// whose slot the operation before it made ℂ.
		if _, isVar := slot.(core.VarType); isVar {
			return m, true
		}
		return m, slot.Equals(RealType) || slot.Equals(IntType) || m.syntax.CoercionConst(slot) != ""
	}
	more, ok := slot.Matches(r.typ, isConstLetter)
	if !ok {
		return m, false
	}
	m.sigma = append(slices.Clip(m.sigma), more...)
	return m, true
}

// fits reads the arguments of a reading in turn.
func (m readingMatcher) fits(reading []localTyping) bool {
	for _, r := range reading {
		var ok bool
		if m, ok = m.fit(r); !ok {
			return false
		}
	}
	return true
}

// incompatibleTypeShape refutes a reading from a polymorphic constant's
// fixed constructors alone. Its unpinned letters impose no equality
// constraints, but an operation cannot fit a predicate's bool result.
func incompatibleTypeShape(want, got core.HolType) bool {
	w, wok := want.(core.CompositeType)
	g, gok := got.(core.CompositeType)
	if !wok || !gok {
		return false
	}
	if !w.Meta().Equals(g.Meta()) {
		return true
	}
	for i := 0; i < w.Meta().Arity(); i++ {
		if incompatibleTypeShape(w.SubType(i), g.SubType(i)) {
			return true
		}
	}
	return false
}

// constLetterMark prefixes the constant's type letters while a reading
// is checked, so they are told from the statement's.
const constLetterMark = "?"

// localTyping is what the text fixes about one argument of a reading:
// its type, or that it is a coercion, or nothing.
type localTyping struct {
	typ      core.HolType
	coercion bool
	known    bool
}

// componentType is the type of an implicit component the scope binds —
// the binder's annotation, the declared name's type, the field of the
// one record declaring it, or the instance term's — unknown where the
// scope gives none, and where several records declare the field: which
// of them is read is a reading's choice (shortReadings).
func (c *implicitCompletion) componentType(name string, bound map[string]int) localTyping {
	switch {
	case bound[name] > 0:
		if ty := c.binderType(name); ty != nil {
			return localTyping{ty, false, true}
		}
	case c.declared(name):
		if c.declaredType != nil {
			if ty := c.declaredType(name); ty != nil {
				return localTyping{ty, false, true}
			}
		}
	}
	if field, count := c.recordComponent(name, bound); count == 1 {
		ty, coercion, known := c.localType(field, bound)
		return localTyping{ty, coercion, known}
	} else if count > 1 {
		return localTyping{}
	}
	if c.bindings[name] != nil {
		return localTyping{c.bindings[name].Type(), false, true}
	}
	return localTyping{}
}

// localType is the type the text fixes for arg without inference: a
// numeral's, a coercion's (reported as such — its numeric type is the
// context's), an annotated binder's or a declared name's, a constant's
// or an application's result, including a record field's projection
// and an operator's (localOperatorType), and a typed lambda's, read
// from its body. Unknown when the text does not pin the result's type
// letters.
func (c *implicitCompletion) localType(arg astNode, bound map[string]int) (argType core.HolType, coercion bool, known bool) {
	switch a := arg.(type) {
	case *astTermLit:
		return a.term.Type(), false, true
	case *astNumLit:
		return NumType, false, true
	case *astCoerce:
		return nil, true, true
	case *astBinOp:
		return c.localOperatorType(a.op, []astNode{a.left, a.right}, bound)
	case *astVar:
		if owner, field, ok := strings.Cut(a.name, "."); ok && (bound[owner] > 0 || c.declared(owner)) {
			return c.localType(&astField{receiver: &astVar{name: owner}, name: field}, bound)
		}
		if len(a.typeAnnot) > 0 {
			if bound[a.name] > 0 || c.declared(a.name) {
				return nil, false, false
			}
			return c.annotatedType(a.name, a.typeAnnot, nil, bound)
		}
		if bound[a.name] > 0 {
			if ty := c.binderType(a.name); ty != nil {
				return ty, false, true
			}
			return nil, false, false
		}
		if c.declared(a.name) {
			if c.declaredType != nil {
				if ty := c.declaredType(a.name); ty != nil {
					return ty, false, true
				}
			}
			return nil, false, false
		}
		return c.constantType(a.name, 0)
	case *astAbsNode:
		// A typed lambda carries its operation's type before the full
		// elaboration. Read its body under its own binder, including when
		// that name shadows an outer implicit component.
		if a.varType == nil {
			return nil, false, false
		}
		bound[a.varName]++
		c.pushBinder(a.varName, a.varType)
		ty, coercion, known := c.localType(a.body, bound)
		c.popBinder(a.varName)
		bound[a.varName]--
		if !known || coercion {
			return nil, false, false
		}
		return core.MakeFun(resolveType(a.varType), ty), false, true
	case *astField:
		ty, coercion, known := c.localType(a.receiver, bound)
		if !known || coercion {
			return nil, false, false
		}
		field, err := structFieldAt(c.syntax, ty, a.name)
		if err != nil {
			return nil, false, false
		}
		return c.appliedType(field.Const, []astNode{a.receiver}, bound)
	case *astApp:
		head, ok := a.fun.(*astVar)
		if !ok || bound[head.name] > 0 || c.declared(head.name) {
			if ty, coercion, known := c.localType(a.fun, bound); known && !coercion {
				return c.appliedTypeUnder(ty, a.args, bound)
			}
			return nil, false, false
		}
		if len(head.typeAnnot) > 0 {
			return c.annotatedType(head.name, head.typeAnnot, a.args, bound)
		}
		if ty, coercion, known := c.constantType(head.name, len(a.args)); known {
			return ty, coercion, known
		}
		return c.appliedType(head.name, a.args, bound)
	}
	return nil, false, false
}

// localOperatorType is the type the build gives an operator
// application, read in the build's order: an arithmetic symbol at its
// operands' common type and the power at its base, each in its
// built-in domain (build.go), and only where those types exclude that
// domain, the result type the symbol's applicable declarations agree
// on. The build reads every operand at its own type before it chooses
// a domain or a declaration, so an operand whose type the text does
// not fix leaves the application untyped: `c • (x + -y)` is a module's
// smul once x − y is read at the module's elements, though
// vec_scalar_mul, which declares `•`, takes any second operand of a
// type the text leaves open. Implicit components contribute types
// without choosing a record; ambiguity of values need not hide a common
// result type.
func (c *implicitCompletion) localOperatorType(symbol string, args []astNode, bound map[string]int) (core.HolType, bool, bool) {
	operands := make([]localTyping, 0, len(args))
	for _, arg := range args {
		ty, coercion, known := c.localType(arg, bound)
		if !known || coercion {
			return nil, false, false
		}
		operands = append(operands, localTyping{ty, coercion, known})
	}
	switch {
	case len(operands) == 2 && isArithOperator(symbol):
		if !operands[0].typ.Equals(operands[1].typ) {
			return nil, false, false
		}
		if meta := arithDomainOperator(symbol, operands[0].typ); !meta.IsZero() {
			return appliedTypeUnderReading(meta.AbsType(), operands)
		}
	case len(operands) == 2 && symbol == "^":
		if meta := powDomainOperator(operands[0].typ); !meta.IsZero() {
			return appliedTypeUnderReading(meta.AbsType(), operands)
		}
	}
	var result core.HolType
	for _, name := range c.syntax.OperatorConsts(symbol, len(args)) {
		t, ok := c.constTypeApart(name, nil, appliedLetterMark)
		if !ok {
			return nil, false, false
		}
		var reading []localTyping
		for _, component := range c.args(name) {
			reading = append(reading, c.componentType(component, bound))
		}
		explicit := make([]localTyping, len(operands))
		for i, pos := range c.syntax.ConstSyntax(name).Operator.Args {
			explicit[pos] = operands[i]
		}
		reading = append(reading, explicit...)
		ty, _, known := appliedTypeUnderReading(t, reading)
		if ty == nil {
			continue
		}
		if !known || result != nil && !result.Equals(ty) {
			return nil, false, false
		}
		result = ty
	}
	return result, false, result != nil
}

// constTypeApart is the type of the constant name with its letters
// renamed apart from the statement's by mark — both are spelled A, B,
// …, and a match binds the constant's while the statement's stand,
// which the shared spelling would hide (an identity match of A against
// A binds nothing, and a later slot could then take the statement's A
// anywhere) — and the letters an instance annotation `⟨A:τ⟩` on the
// head names fixed to the statement's types: the annotation is the
// most explicit type the text carries, and a reading under it is read
// at that instance. The renaming comes first: an annotation's type is
// the statement's (`⟨D:prod(B, C)⟩` under binders at B and C), and a
// constant whose own letter is also spelled C must not capture it.
// Unknown constants give no type.
func (c *implicitCompletion) constTypeApart(name string, annot []typeAnnotBinding, mark string) (core.HolType, bool) {
	if c.constMeta == nil {
		return nil, false
	}
	meta := c.constMeta(name)
	if meta.IsZero() {
		return nil, false
	}
	var apart []core.TypeSubst
	for _, v := range meta.AbsType().TypeVars() {
		if !slices.ContainsFunc(annot, func(b typeAnnotBinding) bool { return b.varName == string(v.Name()) }) {
			apart = append(apart, core.TypeSubst{VarType: v, HolType: core.MakeVarType(mark + string(v.Name()))})
		}
	}
	return meta.AbsType().Substitute(apart...).Substitute(resolveTypeAnnotation(annot)...), true
}

// annotatedType is the result type of a constant whose head carries an
// instance annotation, applied to args: the letters the annotation
// names are the statement's types, the rest are read off the arguments
// as appliedType reads them. `set_mul⟨A:A⟩` under a bound `mul` is an
// operation on sets of A, and `set_mul⟨A:A → bool⟩(set_mul⟨A:A⟩)` one
// on sets of sets — which is how the typed print of a statement, which
// pins every instance, reads back as the statement.
func (c *implicitCompletion) annotatedType(name string, annot []typeAnnotBinding, args []astNode, bound map[string]int) (core.HolType, bool, bool) {
	t, ok := c.constTypeApart(name, annot, appliedLetterMark)
	if !ok {
		return nil, false, false
	}
	return c.appliedTypeUnder(t, args, bound)
}

// appliedType is the result type of a POLYMORPHIC constant applied to
// args, known when the arguments' own local types fix every letter the
// result spells: `subtopology(T, s)` under `T : set(set(A))` is a
// `set(set(A))`, `product_topology(T, S)` a set of sets of pairs. The
// constant's letters are renamed apart from the statement's and matched
// slot by slot under one substitution, as a reading is; an argument
// whose type the text does not fix binds nothing, and a result still
// spelling a letter is unknown. This is what lets a reading see a
// compound first argument — a space built from the bound one,
// `subtopology(subtopology(T, s), t)` — as the family it is.
func (c *implicitCompletion) appliedType(name string, args []astNode, bound map[string]int) (core.HolType, bool, bool) {
	t, ok := c.constTypeApart(name, nil, appliedLetterMark)
	if !ok {
		return nil, false, false
	}
	return c.appliedTypeUnder(t, args, bound)
}

// appliedTypeUnder is appliedType for a constant type whose own letters
// are already marked apart (constTypeApart): the result after args,
// known when no marked letter remains in it.
func (c *implicitCompletion) appliedTypeUnder(t core.HolType, args []astNode, bound map[string]int) (core.HolType, bool, bool) {
	reading := make([]localTyping, 0, len(args))
	for _, arg := range args {
		ty, coercion, known := c.localType(arg, bound)
		reading = append(reading, localTyping{ty, coercion, known})
	}
	return appliedTypeUnderReading(t, reading)
}

func appliedTypeUnderReading(t core.HolType, reading []localTyping) (core.HolType, bool, bool) {
	isLetter := func(v core.VarType) bool { return strings.HasPrefix(string(v.Name()), appliedLetterMark) }
	var sigma []core.TypeSubst
	for _, arg := range reading {
		ft, ok := t.(core.CompositeType)
		if !ok || !ft.Meta().Equals(core.MetaTypeFun()) {
			return nil, false, false
		}
		if arg.known && !arg.coercion {
			more, ok := ft.SubType(0).Substitute(sigma...).Matches(arg.typ, isLetter)
			if !ok {
				return nil, false, false
			}
			sigma = append(sigma, more...)
		}
		t = ft.SubType(1)
	}
	t = t.Substitute(sigma...)
	for _, v := range t.TypeVars() {
		if isLetter(v) {
			return t, false, false
		}
	}
	return t, false, true
}

// appliedLetterMark prefixes a constant's type letters while an
// application's result is read off its arguments; it shares no prefix
// with constLetterMark, so a reading never takes one for its own.
const appliedLetterMark = "~"

// constantType is the result type of the constant name applied to
// `applied` arguments, known only when it is ground.
func (c *implicitCompletion) constantType(name string, applied int) (core.HolType, bool, bool) {
	meta := c.constMeta(name)
	if meta.IsZero() {
		return nil, false, false
	}
	t := meta.AbsType()
	for i := 0; i < applied; i++ {
		ft, ok := t.(core.CompositeType)
		if !ok || !ft.Meta().Equals(core.MetaTypeFun()) {
			return nil, false, false
		}
		t = ft.SubType(1)
	}
	if len(t.TypeVars()) > 0 {
		return nil, false, false
	}
	return t, false, true
}

// spineResult is the type at the end of the argument spine — what an
// application at every slot yields.
func spineResult(t core.HolType) core.HolType {
	for {
		ft, ok := t.(core.CompositeType)
		if !ok || !ft.Meta().Equals(core.MetaTypeFun()) {
			return t
		}
		t = ft.SubType(1)
	}
}

// argumentSlots is the type's argument spine — the domains along its
// arrows, in order.
func argumentSlots(t core.HolType) []core.HolType {
	var slots []core.HolType
	for {
		ft, ok := t.(core.CompositeType)
		if !ok || !ft.Meta().Equals(core.MetaTypeFun()) {
			return slots
		}
		slots = append(slots, ft.SubType(0))
		t = ft.SubType(1)
	}
}

// pushBinder / popBinder / binderType keep the annotated types of the
// walk's binders beside bound's depths.
func (c *implicitCompletion) pushBinder(name string, t astType) {
	var ty core.HolType
	if t != nil {
		ty = resolveType(t)
	}
	c.binderTypes[name] = append(c.binderTypes[name], ty)
}

func (c *implicitCompletion) popBinder(name string) {
	stack := c.binderTypes[name]
	c.binderTypes[name] = stack[:len(stack)-1]
}

func (c *implicitCompletion) binderType(name string) core.HolType {
	stack := c.binderTypes[name]
	if len(stack) == 0 {
		return nil
	}
	return stack[len(stack)-1]
}

// canonical returns the spellings of an instance component that count
// as explicit: the parser-faithful print of the term (what every
// printer emits — `real_add`, `&0`), and for a numeral coercion also
// its applied form (`real_of_num(0)`), since both lower to one term.
func (c *implicitCompletion) canonical(name string, t core.Term) []astNode {
	if nodes, ok := c.canon[name]; ok {
		return nodes
	}
	var nodes []astNode
	if n := parseCanonicalSpelling(ext.FormatTermForParser(t)); n != nil {
		nodes = append(nodes, n)
	}
	if app, ok := t.AsAppliedTerm(); ok {
		if head, ok := app.Fun().AsConst(); ok {
			if v, isNum := ext.NumeralValue(app.Arg()); isNum {
				nodes = append(nodes, &astApp{
					fun:  &astVar{name: string(head.Name())},
					args: []astNode{&astNumLit{value: v}},
				})
			}
		}
	}
	c.canon[name] = nodes
	return nodes
}

// parseCanonicalSpelling parses one term spelling to its AST, or nil
// when the spelling does not parse cleanly.
func parseCanonicalSpelling(text string) astNode {
	normalized, _ := NormalizeTextSymbols(text)
	tokens, lexErr := lex(normalized)
	if lexErr != nil {
		return nil
	}
	par := &parser{tokens: tokens}
	node, parseErr := par.parseExpr()
	if parseErr != nil || len(par.warnings) > 0 {
		return nil
	}
	if par.pos < len(par.tokens) && par.tokens[par.pos].kind != tokEOF {
		return nil
	}
	return node
}

// completeImplicitArgs runs the completion pass over a parse's roots
// under scope, or reports the refusal as a diagnostic.
func completeImplicitArgs(scope *ParseScope, env *typeEnv, roots []*astNode) *InputDiagnostic {
	c := newImplicitCompletion(scope, func(name string) bool {
		_, ok := env.declared[name]
		return ok
	}, true)
	if c == nil {
		return refuseDimensionsUnread(roots)
	}
	rootNodes := make([]astNode, len(roots))
	for i, r := range roots {
		rootNodes[i] = *r
	}
	c.components = componentVariables(scope.Syntax, rootNodes, scope.ResidentFacts, scope.ResidentNames)
	env.components = c.components
	c.constMeta = func(name string) core.ConstTermMeta {
		if m, ok := env.scopeConstMetas[name]; ok {
			return m
		}
		if ct, ok := env.scopeConsts[name]; ok {
			return ct.Meta()
		}
		if env.resolver != nil {
			return env.resolver(name)
		}
		return core.ConstTermMeta{}
	}
	c.declaredType = func(name string) core.HolType { return env.declared[name] }
	c.declaredTypes = env.declared
	for _, root := range roots {
		r, err := c.complete(*root, map[string]int{})
		if err != nil {
			suggestion := "an implicit argument is read from the name in scope; spell all of them to state the law at other components"
			if _, isDimension := err.(*dimensionError); isDimension {
				suggestion = dimensionSuggestion
			}
			return &InputDiagnostic{Code: CodeValidation, Message: err.Error(), Suggestion: suggestion}
		}
		*root = r
	}
	return nil
}

// ---------------------------------------------------------------------------
// The inverse: printing a statement back under the scope
// ---------------------------------------------------------------------------

// elide is complete's inverse walk: it drops the explicit implicit
// prefix of every application it would have completed.
func (c *implicitCompletion) elide(node astNode, bound map[string]int, changed *bool) astNode {
	switch n := node.(type) {
	case *astField:
		n.receiver = c.elide(n.receiver, bound, changed)
	case *astApp:
		// The records the prefix's fields would be read from are picked
		// before the arguments are elided: the completion picks them by
		// the types of the arguments as it has completed them, which are
		// these.
		head, isVar := n.fun.(*astVar)
		var names []string
		var choice map[string]string
		// An application a definition's equation states keeps its
		// prefix (astApp.stated).
		//
		// A text already in the ⟨…⟩ form has its dimensions in front of
		// the prefix (astApp.dims): the prefix is read behind them, and
		// the short reading that picks the records is the dimensions and
		// then the operands.
		if isVar && !n.stated && bound[head.name] == 0 && !c.declared(head.name) {
			names = c.args(head.name)
			if len(names) > 0 && len(n.args) >= n.dims+len(names) {
				short := slices.Concat(n.args[:n.dims], n.args[n.dims+len(names):])
				choice, _ = c.chooseRecords(head.name, head.typeAnnot, names, short, bound)
			}
		}
		for i, a := range n.args {
			n.args[i] = c.elide(a, bound, changed)
		}
		if !isVar {
			n.fun = c.elide(n.fun, bound, changed)
			return n
		}
		if choice == nil || !c.elidablePrefix(names, n.args[n.dims:], bound, choice) {
			return n
		}
		*changed = true
		rest := slices.Concat(n.args[:n.dims], n.args[n.dims+len(names):])
		if len(rest) == 0 {
			return head
		}
		n.args = rest
		n.elided = true
		return n
	case *astBinOp:
		n.left = c.elide(n.left, bound, changed)
		n.right = c.elide(n.right, bound, changed)
	case *astCong:
		n.left = c.elide(n.left, bound, changed)
		n.right = c.elide(n.right, bound, changed)
		n.modulus = c.elide(n.modulus, bound, changed)
	case *astTendsAt:
		n.fn = c.elide(n.fn, bound, changed)
		n.limit = c.elide(n.limit, bound, changed)
		n.point = c.elide(n.point, bound, changed)
	case *astNotNode:
		n.body = c.elide(n.body, bound, changed)
	case *astCoerce:
		n.operand = c.elide(n.operand, bound, changed)
	case *astNeg:
		n.operand = c.elide(n.operand, bound, changed)
	case *astQuantNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		c.binderTypes[n.varName] = append(c.binderTypes[n.varName], chapterBinderType(c.syntax, n.varType))
		n.body = c.elide(n.body, bound, changed)
		c.popBinder(n.varName)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astAbsNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		c.binderTypes[n.varName] = append(c.binderTypes[n.varName], chapterBinderType(c.syntax, n.varType))
		n.body = c.elide(n.body, bound, changed)
		c.popBinder(n.varName)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astPatternAbs:
		leaves := n.pat.leaves(nil)
		for _, lf := range leaves {
			bound[lf.name]++
			c.pushBinder(lf.name, nil)
		}
		n.body = c.elide(n.body, bound, changed)
		for _, lf := range leaves {
			c.popBinder(lf.name)
			bound[lf.name]--
		}
	case *astBigOp:
		n.bound = c.elide(n.bound, bound, changed)
		bound[n.binder]++
		c.pushBinder(n.binder, nil)
		n.body = c.elide(n.body, bound, changed)
		c.popBinder(n.binder)
		bound[n.binder]--
	}
	return node
}

// elidablePrefix requires the arguments the current scope would insert,
// rather than any arguments recognizable as an explicit prefix. A record
// field can be dropped only at the record choice names for it — the one
// record declaring it, or the one the application's types pick among
// several (chooseRecords) — under that structure.
func (c *implicitCompletion) elidablePrefix(names []string, args []astNode, bound map[string]int, choice map[string]string) bool {
	// A prefix the parser refuses to complete is not dropped: one read
	// partly from a variable that carries no structure and partly from
	// elsewhere (mixedComponentSources).
	strangers, elsewhere := 0, 0
	for _, name := range names {
		switch {
		case bound[name] > 0 || c.declared(name):
			if !c.isComponent(name, bound) {
				strangers++
			}
		case choice[name] != "" || c.bindings[name] != nil:
			elsewhere++
		}
	}
	if strangers > 0 && elsewhere > 0 {
		return false
	}
	for i, name := range names {
		if i >= len(args) {
			return false
		}
		if bound[name] > 0 || c.declared(name) {
			if c.elideBinder != nil && !c.elideBinder(name) {
				return false
			}
			v, ok := args[i].(*astVar)
			if !ok || len(v.typeAnnot) != 0 {
				return false
			}
			if v.name == name {
				continue
			}
			if bound[v.name] == 0 && bound[name] == 0 && c.surface[v.name] == name && c.declared(v.name) && c.declared(name) {
				continue
			}
			return false
		}
		if owner := choice[name]; owner != "" {
			f := recordField(owner, name)
			if c.elideBinder != nil && !c.elideBinder(owner) {
				return false
			}
			switch a := args[i].(type) {
			case *astField:
				if astNodeEqual(a, f) {
					continue
				}
			case *astVar:
				if a.name == owner+"."+name && len(a.typeAnnot) == 0 {
					continue
				}
			case *astApp:
				if len(a.args) == 1 && astNodeEqual(a.args[0], f.receiver) && c.recordSlotMatches(a, name, bound) {
					continue
				}
			}
			return false
		}
		term := c.bindings[name]
		if term == nil {
			return false
		}
		matches := false
		for _, canon := range c.canonical(name, term) {
			if astNodeEqual(args[i], canon) {
				matches = true
				break
			}
		}
		if !matches {
			return false
		}
	}
	return true
}
