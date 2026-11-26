// struct_fields.go — the fields of a record type: a part read off a
// value by a projection, written as a field of the value and, for an
// operation, by its symbol.
//
// A structure whose components are ONE VALUE — `ring_ops(A)` holding a
// ring's six operations and its carrier, `module_ops(A, B)` a module's
// own four and its carrier — is a record (registry.DefineData with one
// constructor and Fields), and reads a component off the value by a
// projection constant, `ring_add(R)`, `mod_zero(M)`. The record declares
// its fields (registry.DataField's Field and Symbol → StructSyntax): per
// field the projection, and for a field that is an operation or a map
// the operator symbol it carries. Under a binder or a declared variable of
// the type the text then writes a field as `R.add` and an operation by
// its symbol: `c + d` at the ring's carrier is `ring_add(R)(c, d)`,
// `u + v` at the vectors `mod_add(M)(u, v)`, `c • u` is
// `mod_smul(M)(c, u)`. A symbol is resolved at the operands' types
// among the struct-typed variables in scope exactly as a structure
// fact's components are (structure.go: the candidates share one table,
// the projection applied to the variable standing where the component
// variable stands), and two at one signature are refused. The binding
// is read off the variable's TYPE, so nothing is global: a text with no
// binder of the type sees no symbol, and two modules in scope at two
// carriers each take their own `+`. A field application reads as the
// projection applied to the receiver and the arguments in one
// application: `R.add(a, b)` types `a` and `b` at the field's domains
// as `ring_add(R, a, b)` does (appSpine).
//
// foldStructFields is the printer's half: `ring_add(R)` is written
// back as `R.add`, including expression receivers such as `P(n).add`.
// A field application prints as an operator only where the parser
// reads the operator back as that field. Where the receiver's type is
// declared or annotated and every name the reading consults is typed,
// the parser's own reading at the field's operand types decides
// (fieldSymbolFaithful). A display declares nothing: a variable it
// shows to be a record (shownRecords) prints a field as its symbol only
// where that field holds the symbol at its arity alone among the
// records the text shows and the components its structure facts bind
// (fieldHoldsSymbolAlone).

package dsl

import (
	"fmt"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// StructSyntax is what a chapter declares about a structure type's
// fields, in declaration order.
type StructSyntax struct {
	Fields []StructField
}

// StructField is one field: its name after the dot, the projection
// constant that reads it off a value, and the operator symbol it
// carries with that symbol's arity — 2 for an infix, 1 for a prefix,
// "" and 0 for a field that is no operation.
type StructField struct {
	Name   string
	Const  string
	Symbol string
	Arity  int
}

// field is the field named name, nil when the type declares none.
func (s *StructSyntax) field(name string) *StructField {
	for i := range s.Fields {
		if s.Fields[i].Name == name {
			return &s.Fields[i]
		}
	}
	return nil
}

// fieldOfProjection is the field constName reads, nil when none does.
func (s *StructSyntax) fieldOfProjection(constName string) *StructField {
	for i := range s.Fields {
		if s.Fields[i].Const == constName {
			return &s.Fields[i]
		}
	}
	return nil
}

// fieldNames spells the fields for a diagnostic.
func (s *StructSyntax) fieldNames() string {
	names := make([]string, len(s.Fields))
	for i, f := range s.Fields {
		names[i] = f.Name
	}
	return strings.Join(names, ", ")
}

// structTypeName is the constructor name of a composite type — the
// name a StructSyntax is declared under — "" for a type variable.
func structTypeName(t core.HolType) string {
	c, ok := t.(core.CompositeType)
	if !ok {
		return ""
	}
	return string(c.Meta().Name())
}

// chapterBinderType reads the value type behind a single-record bundle
// binder. The chapter's R:comm_ring_on(A) still binds a ring_ops(A)
// value when later folds ask which fields R supplies.
func chapterBinderType(table SyntaxTable, t astType) core.HolType {
	if t == nil {
		return nil
	}
	if named, ok := t.(*astTypeNamed); ok && table != nil {
		if syntax := table.ConstSyntax(named.name); syntax != nil && syntax.Bundle != nil {
			bundle := syntax.Bundle
			if bundle.Structure && bundle.Subject == 0 && len(bundle.Params) == 1 {
				pattern := apartTypes(bundle.Params)
				vars := unsolvedVars(pattern, nil)
				if len(vars) == len(named.args) {
					var subst []core.TypeSubst
					for i, v := range vars {
						subst = append(subst, core.MakeTypeSubst(v, resolveType(named.args[i])))
					}
					typ := pattern[0].Substitute(subst...)
					if table.StructSyntax(structTypeName(typ)) != nil {
						return typ
					}
				}
			}
		}
	}
	return resolveType(t)
}

// structField reads `R.add` at a variable or constant R of a record
// type as the field's projection applied to R. nil, nil when R is no
// record, and the bundle reading follows (bundle.go's field); an error
// when the type declares no such field. A constant is read unless a
// variable of its name is bound here: a structure fact whose subject
// it is, `comm_ring_on(int_ring)` resident or stated, makes it a
// bundle's component and shadows nothing.
func (sc *bundleScope) structField(n *astVar) (astNode, error) {
	name, comp, _ := strings.Cut(n.name, ".")
	t, ok := sc.types[name]
	if !ok && !sc.bound[name] {
		if meta := sc.table.ConstMeta(name); !meta.IsZero() {
			t, ok = meta.AbsType(), true
		}
	}
	if !ok || len(n.typeAnnot) > 0 {
		return nil, nil
	}
	s := sc.table.StructSyntax(structTypeName(t))
	if s == nil {
		return nil, nil
	}
	f := s.field(comp)
	if f == nil {
		return nil, &bundleError{n.pos, fmt.Sprintf("%s: %s has no field %s; the fields of %s are %s",
			n.name, name, comp, structTypeName(t), s.fieldNames())}
	}
	return &astApp{fun: &astVar{name: f.Const, pos: n.pos}, args: []astNode{&astVar{name: name, pos: n.pos}}, pos: n.pos}, nil
}

// spelledOut is node as the parser reads it: a field written on a
// record the scope types — `M.simplices(n)` under `M:simplicial_ops(B)`
// — is the projection applied to the record and the arguments in one
// application, `simplicial_simplices(M, n)`, and a bundle's field is
// its component. The bundle pass compares texts, and a layout's
// template is the kernel's spelling, which writes every projection
// out, where the text it is matched against may write the field; the
// two meet in this reading. Nodes the pass compares structurally
// (matchTemplate) are read through; node itself where nothing is read.
func (sc *bundleScope) spelledOut(node astNode) astNode {
	switch n := node.(type) {
	case *astVar:
		if !strings.Contains(n.name, ".") || n.name == ".." {
			return n
		}
		if app, err := sc.structField(n); app != nil && err == nil {
			return app
		}
		if comp, err := sc.field(n); comp != nil && err == nil {
			return comp
		}
		return n
	case *astApp:
		fun := sc.spelledOut(n.fun)
		args := make([]astNode, len(n.args))
		same := fun == n.fun
		for i, a := range n.args {
			args[i] = sc.spelledOut(a)
			same = same && args[i] == a
		}
		// An application of an application is one application, as the
		// parser reads it (appSpine): a field's, `P.d(n + 1)` once P.d is
		// the projection, and a curried head's, `F(n)(x)`.
		if inner, ok := fun.(*astApp); ok {
			return inner.appliedTo(args, n.pos)
		}
		if same {
			return n
		}
		return &astApp{fun: fun, args: args, pos: n.pos, dims: n.dims, dimsPlaced: n.dimsPlaced}
	case *astField:
		if r := sc.spelledOut(n.receiver); r != n.receiver {
			return &astField{receiver: r, name: n.name, pos: n.pos}
		}
	case *astBinOp:
		l, r := sc.spelledOut(n.left), sc.spelledOut(n.right)
		if l != n.left || r != n.right {
			return &astBinOp{op: n.op, left: l, right: r, pos: n.pos}
		}
	case *astNotNode:
		if b := sc.spelledOut(n.body); b != n.body {
			return &astNotNode{body: b, pos: n.pos}
		}
	case *astNeg:
		if o := sc.spelledOut(n.operand); o != n.operand {
			return &astNeg{operand: o, pos: n.pos}
		}
	case *astCoerce:
		if o := sc.spelledOut(n.operand); o != n.operand {
			return &astCoerce{operand: o, pos: n.pos}
		}
	}
	return node
}

// key is printKey in the parser's reading (spelledOut): the spelling
// two nodes are one term under, whichever way each writes a field.
func (sc *bundleScope) key(node astNode) string { return printKey(sc.spelledOut(node)) }

// fieldNode preserves the bundle spelling of a field on a name, and
// uses an expression receiver for every other field access.
func fieldNode(receiver astNode, name string, pos int) astNode {
	if v, ok := receiver.(*astVar); ok && len(v.typeAnnot) == 0 && !strings.Contains(v.name, ".") {
		return &astVar{name: v.name + "." + name, pos: pos}
	}
	return &astField{receiver: receiver, name: name, pos: pos}
}

func structFieldAt(table SyntaxTable, receiver core.HolType, name string) (*StructField, error) {
	typeName := structTypeName(receiver)
	if table == nil || table.StructSyntax(typeName) == nil {
		return nil, fmt.Errorf("field %s: receiver type %s declares no record fields", name, ext.FormatType(receiver))
	}
	s := table.StructSyntax(typeName)
	f := s.field(name)
	if f == nil {
		return nil, fmt.Errorf("%s has no field %s; the fields of %s are %s", typeName, name, typeName, s.fieldNames())
	}
	return f, nil
}

func buildStructField(n *astField, env *typeEnv) (core.Term, error) {
	receiver, err := buildTerm(n.receiver, env, false)
	if err != nil {
		return nil, err
	}
	f, err := structFieldAt(env.syntax, receiver.Type(), n.name)
	if err != nil {
		return nil, err
	}
	meta, err := env.constMeta(f.Const)
	if err != nil {
		return nil, err
	}
	return buildAppViaMeta(env, meta, []core.Term{receiver})
}

func inferStructFieldType(n *astField, env *typeEnv) (core.HolType, bool) {
	t, ok := inferAstType(n.receiver, env)
	if !ok {
		return nil, false
	}
	f, err := structFieldAt(env.syntax, t, n.name)
	if err != nil {
		return nil, false
	}
	meta, err := env.constMeta(f.Const)
	if err != nil {
		return nil, false
	}
	projection, err := buildAppViaMeta(env, meta, []core.Term{core.Var("_record", t)})
	if err != nil {
		return nil, false
	}
	return projection.Type(), true
}

// fieldSymbolFaithful asks the same operator builder as a parse, at
// the field's operand types. A symbol is printed only when it selects
// this very projection: ambiguity, an intrinsic arithmetic operator,
// or a different declared operator leaves the field explicit.
func fieldSymbolFaithful(receiver *astVar, field *StructField, env *typeEnv) bool {
	// An untyped binder can shadow an implicit component. Its type is
	// established by the build, so the spelling cannot select a symbol.
	for _, t := range env.bound {
		if t == nil {
			return false
		}
	}
	// A record the text shows without typing it (shownRecords) is a
	// holder of the symbol the build cannot weigh: the parser may meet
	// it at these operands, and refuses two holders there.
	for _, o := range env.structureOps[field.Symbol] {
		if o.arity == field.Arity && o.shown {
			return false
		}
	}
	op, err := buildStructField(&astField{receiver: receiver, name: field.Name}, env)
	if err != nil {
		return false
	}
	parts := ext.MatchesFun(op.Type())
	if len(parts) <= field.Arity {
		return false
	}
	args := make([]astNode, field.Arity)
	want := op
	for i := range args {
		v := core.Var(fmt.Sprintf("_operand%d", i), parts[i])
		args[i] = &astTermLit{term: v}
		want = core.Apply(want, v)
	}
	var symbol astNode
	if field.Arity == 1 {
		symbol = &astNeg{operand: args[0]}
	} else {
		symbol = &astBinOp{op: field.Symbol, left: args[0], right: args[1]}
	}
	got, err := buildTerm(symbol, env, false)
	return err == nil && got.Equals(want)
}

// fieldHoldsSymbolAlone reports whether the field f of the record
// receiver is the one holder of f's symbol at f's arity among ops: the
// record's own field is there, no structure fact binds the symbol to a
// component, and no second record's field carries it. It is the
// display's reading condition, the types the parser will meet being
// unknown there, as markStructureSymbolsRead's is for a component.
func fieldHoldsSymbolAlone(ops map[string][]structureOperator, receiver string, f *StructField) bool {
	held := false
	for _, o := range ops[f.Symbol] {
		if o.arity != f.Arity {
			continue
		}
		if o.name != receiver || o.proj != f.Const {
			return false
		}
		held = true
	}
	return held
}

// shownRecords is every record a text shows without typing it, at the
// type it is shown at: a variable no binder of the text binds and no
// declaration types, standing as an argument of a constant at a
// parameter whose type is a record — the receiver of a projection, `R`
// in `ring_add(R, a, b)`, or the subject of a predicate on records, `R`
// in `comm_ring_on(R)`. A display declares nothing, so these are the
// records among its free variables that it names; the parser meets them
// as the declared variables of the scope it reads the display in.
func shownRecords(table SyntaxTable, roots []astNode, declared map[string]bool) map[string]core.HolType {
	binders := map[string]bool{}
	for _, root := range roots {
		walkAST(root, func(n astNode) {
			switch n := n.(type) {
			case *astQuantNode:
				for _, name := range n.boundNames() {
					binders[name] = true
				}
			case *astAbsNode:
				binders[n.varName] = true
			case *astPatternAbs:
				for _, lf := range n.pat.leaves(nil) {
					binders[lf.name] = true
				}
			case *astBigOp:
				binders[n.binder] = true
			}
		})
	}
	shown := map[string]core.HolType{}
	for _, root := range roots {
		walkAST(root, func(n astNode) {
			app, ok := n.(*astApp)
			if !ok {
				return
			}
			head, ok := app.fun.(*astVar)
			if !ok || binders[head.name] || declared[head.name] {
				return
			}
			meta := table.ConstMeta(head.name)
			if meta.IsZero() {
				return
			}
			params := ext.MatchesFun(meta.AbsType())
			for i, a := range app.args {
				if i >= len(params)-1 {
					break
				}
				v, ok := a.(*astVar)
				if !ok || len(v.typeAnnot) > 0 || strings.Contains(v.name, ".") ||
					binders[v.name] || declared[v.name] || !table.ConstMeta(v.name).IsZero() {
					continue
				}
				if table.StructSyntax(structTypeName(params[i])) != nil {
					shown[v.name] = params[i]
				}
			}
		})
	}
	return shown
}

// withShownRecords adds to ops, for the printer, every field carrying a
// symbol of each record in shown (shownRecords), marked shown: a holder
// of its symbol wherever the text reads, whose type the text does not
// give. ops is returned, made when it was nil and a field was added.
func withShownRecords(ops map[string][]structureOperator, table SyntaxTable, shown map[string]core.HolType) map[string][]structureOperator {
	names := make([]string, 0, len(shown))
	for name := range shown {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		typeName := structTypeName(shown[name])
		for _, f := range table.StructSyntax(typeName).Fields {
			if f.Symbol == "" {
				continue
			}
			if ops == nil {
				ops = map[string][]structureOperator{}
			}
			ops[f.Symbol] = append(ops[f.Symbol], structureOperator{name: name, arity: f.Arity, proj: f.Const, typeName: typeName, shown: true})
		}
	}
	return ops
}

// foldStructFields rewrites projections into fields and field
// applications into operators whose reading is unchanged. env tracks
// the types and shadowing of every binder at the occurrence, as well
// as the declared variables, constants and operator candidates.
func foldStructFields(node astNode, env *typeEnv, changed *bool) astNode {
	table := env.syntax
	fold := func(n astNode) astNode { return foldStructFields(n, env, changed) }
	under := func(name string, t astType, body astNode) astNode {
		prev, had := env.bound[name]
		env.bound[name] = chapterBinderType(table, t)
		out := fold(body)
		if had {
			env.bound[name] = prev
		} else {
			delete(env.bound, name)
		}
		return out
	}
	switch n := node.(type) {
	case *astField:
		n.receiver = fold(n.receiver)
	case *astApp:
		for i, a := range n.args {
			n.args[i] = fold(a)
		}
		n.fun = fold(n.fun)
		head, ok := n.fun.(*astVar)
		if !ok {
			return n
		}
		// A projection applied to a record expression is the field,
		// applied to whatever follows — the printers write the curried
		// application flat, `mod_add(M, u, v)`, the text either way. The
		// instance annotation a printer puts on a constant standing at
		// two instances is dropped with the projection: the receiver's
		// type fixes the instance.
		_, bound := env.bound[head.name]
		_, declared := env.declared[head.name]
		if !bound && !declared {
			if folded := foldRecordBigOp(n, env); folded != nil {
				*changed = true
				return folded
			}
		}
		// projected is the field a projection head read, nil when the
		// text spelled the field itself.
		var projected *StructField
		if len(n.args) >= 1 && !bound && !declared {
			if meta := table.ConstMeta(head.name); !meta.IsZero() {
				parts := ext.MatchesFun(meta.AbsType())
				if s := table.StructSyntax(structTypeName(parts[0])); s != nil {
					if f := s.fieldOfProjection(head.name); f != nil {
						*changed = true
						field := fieldNode(n.args[0], f.Name, n.pos)
						if len(n.args) == 1 {
							return field
						}
						n = &astApp{fun: field, args: append([]astNode(nil), n.args[1:]...), pos: n.pos}
						head, ok = field.(*astVar)
						if !ok {
							return n
						}
						projected = f
					}
				}
			}
		}
		if len(head.typeAnnot) > 0 {
			return n
		}
		if v, field, isField := strings.Cut(head.name, "."); isField {
			var f *StructField
			reads := false
			switch ty, known := env.lookupType(v); {
			case known && ty != nil:
				var err error
				f, err = structFieldAt(table, ty, field)
				reads = err == nil && f.Symbol != "" && len(n.args) >= f.Arity && fieldSymbolFaithful(&astVar{name: v}, f, env)
			case !known && projected != nil && table.ConstMeta(v).IsZero():
				// A record the text shows without typing it: the type
				// the parser will meet is unknown, and the field's
				// symbol reads back only where nothing else holds it.
				f = projected
				reads = f.Symbol != "" && len(n.args) >= f.Arity && fieldHoldsSymbolAlone(env.structureOps, v, f)
			}
			if reads {
				*changed = true
				var folded astNode
				if f.Arity == 1 {
					folded = &astNeg{operand: n.args[0], pos: n.pos}
				} else {
					folded = &astBinOp{op: f.Symbol, left: n.args[0], right: n.args[1], pos: n.pos}
				}
				if rest := n.args[f.Arity:]; len(rest) > 0 {
					return &astApp{fun: folded, args: append([]astNode(nil), rest...), pos: n.pos}
				}
				return folded
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
		n.body = under(n.varName, n.varType, n.body)
	case *astAbsNode:
		n.body = under(n.varName, n.varType, n.body)
	case *astPatternAbs:
		leaves := n.pat.leaves(nil)
		saved := make(map[string]core.HolType, len(leaves))
		for _, lf := range leaves {
			if prev, had := env.bound[lf.name]; had {
				saved[lf.name] = prev
			}
			env.bound[lf.name] = nil
			if lf.ty != nil {
				env.bound[lf.name] = resolveType(lf.ty)
			}
		}
		n.body = fold(n.body)
		for _, lf := range leaves {
			delete(env.bound, lf.name)
		}
		for name, prev := range saved {
			env.bound[name] = prev
		}
	case *astBigOp:
		n.bound = fold(n.bound)
		n.body = under(n.binder, nil, n.body)
	}
	return node
}
