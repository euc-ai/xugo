package registry

import (
	"fmt"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/utils"
)

// ConstMetaManager is the process-global registry of the constants the
// corpus knows: the engine's built-ins (ext.InitConstMetaMap) and the
// constants chapters mint in Go — the define doors, the kernel's
// NewConstDef / NewTypeDef — registered through LoadOrStoreConstMeta.
// Nothing else reaches it. A name no chapter minted is unknown here,
// so a statement, a proof body, a vocabulary row or a serve bundle
// that spells one fails loudly at registration.
type ConstMetaManager struct {
	metaMap utils.Map[core.TermName, core.ConstTermMeta]
	// syntax holds, per minted constant, what its chapter declared
	// about its text — implicit leading binders and a notation
	// (registry.DefEntry.Implicit / Notation / BigOp); bigop maps a
	// symbol at a carrier to the one constant that declared it, outfix
	// a delimiter pair and operator a symbol at an arity to the
	// constants that declared it, in declaration order — each on its
	// own operand types, which the parse reads to pick one (an outfix
	// is shared only under one overloaded word, registerOutfix).
	// Registered by the define door with the mint; read by every text
	// parse through proof.ProofService.Syntax (the manager IS the
	// dsl.SyntaxTable).
	syntax utils.Map[core.TermName, *dsl.ConstSyntax]
	// structs holds, per record type, the fields its record declares
	// (DataField.Field and .Symbol, struct.go): the projection reading
	// each off a value and the symbol an operation carries
	// (dsl.StructSyntax).
	structs utils.Map[string, *dsl.StructSyntax]
	// provisional names the constants whose syntax holds only the
	// bundle layouts their definition declares, registered before the
	// definition's own equation is read so that its body may pass them
	// (ProvisionalBundleSyntax); the full syntax replaces it.
	provisional utils.Map[core.TermName, bool]
	outfixMu    sync.Mutex
	outfix      map[string][]core.TermName
	operatorMu  sync.Mutex
	operator    map[string][]core.TermName
	// overload maps an overloaded word to the constants declaring it,
	// in declaration order (dsl.Overload). A word is never a constant's
	// name: the two tables refuse each other.
	overloadMu sync.Mutex
	overload   map[string][]*dsl.Overload
	overloadOf map[string][]core.TermName

	// typeIndex is the type vocabulary the registered constants' types
	// spell — name → arity. A constant's type is read into it once, as
	// the constant is registered (readTypes): a built-in at the
	// manager's first use, a chapter mint at LoadOrStoreConstMeta, the
	// one door a constant comes in by. typeReads counts the constants
	// read.
	typeIndexMu sync.Mutex
	typeIndex   map[string]int
	typeReads   int
	bigop       utils.Map[string, core.TermName]
	// coercion is the constant declared as the embedding of the real
	// line into a type, by the type's key (dsl.Coercion).
	coercion utils.Map[string, core.TermName]

	// mintSource records, for every constant a chapter minted, the
	// chapter file and line that stored its meta (registrationSource):
	// a vocabulary-level mint (ext.ConstDef through a chapter's publish
	// helper) goes through no definition door and is attributed to its
	// chapter by this alone. The corpus index reads it.
	mintSource utils.Map[core.TermName, string]
	once       sync.Once
}

// operatorKey and bigOpKey are the operator and big-operator tables'
// keys: a symbol at an arity, a symbol at a carrier.
func operatorKey(symbol string, arity int) string { return fmt.Sprintf("%s/%d", symbol, arity) }
func bigOpKey(symbol string, carrier core.HolType) string {
	return symbol + "@" + string(carrier.Key())
}

var globalConstMetaManager ConstMetaManager

// GetConstMetaManager returns the process-global registry, seeded with
// the engine's built-in constants on first call.
func GetConstMetaManager() *ConstMetaManager {
	globalConstMetaManager.once.Do(func() {
		m := &globalConstMetaManager
		m.metaMap = *ext.InitConstMetaMap()
		m.metaMap.Range(func(_ core.TermName, meta core.ConstTermMeta) bool {
			m.readTypes(meta)
			return true
		})
	})
	return &globalConstMetaManager
}

// readTypes reads the type constructors a newly registered constant's
// type spells into the type vocabulary (TypeArity).
func (m *ConstMetaManager) readTypes(meta core.ConstTermMeta) {
	m.typeIndexMu.Lock()
	defer m.typeIndexMu.Unlock()
	if m.typeIndex == nil {
		m.typeIndex = map[string]int{}
	}
	collectTypeArities(meta.AbsType(), m.typeIndex)
	m.typeReads++
}

// LoadConstMeta resolves a registered constant by name: an engine
// built-in or a chapter mint. Nothing else answers.
func (m *ConstMetaManager) LoadConstMeta(name core.TermName) (core.ConstTermMeta, bool) {
	return m.metaMap.Load(name)
}

// LoadOrStoreConstMeta registers a chapter-minted meta. A name already
// registered is returned with loaded=true — the caller's exclusive
// mint check. An overloaded word is refused outright: a constant of
// that name could never be reached by it (dsl overload.go).
func (m *ConstMetaManager) LoadOrStoreConstMeta(meta core.ConstTermMeta) (core.ConstTermMeta, bool) {
	if m.isOverloadWord(meta.Name()) {
		panic(fmt.Sprintf("constant %q: the name is an overloaded word (%v)", meta.Name(), m.OverloadConsts(string(meta.Name()))))
	}
	actual, loaded := m.metaMap.LoadOrStore(meta.Name(), meta)
	if !loaded {
		m.readTypes(meta)
		if source := registrationSource(); source != "" {
			m.mintSource.Store(meta.Name(), source)
		}
	}
	return actual, loaded
}

// MintSource is the chapter file and line a chapter-minted constant's
// meta was stored from, relative to library/proofs; false for an
// engine built-in.
func (m *ConstMetaManager) MintSource(name core.TermName) (string, bool) {
	return m.mintSource.Load(name)
}

// RangeMintSources visits every chapter-minted constant with its
// source, in no particular order.
func (m *ConstMetaManager) RangeMintSources(yield func(name core.TermName, source string) bool) {
	m.mintSource.Range(yield)
}

// ClaimName is a definition door's first move: it asserts the name is
// free before the door's mint run. An error names why it is not —
// another chapter minted it, or it is a built-in of the engine.
func (m *ConstMetaManager) ClaimName(name core.TermName) error {
	if m.isOverloadWord(name) {
		return fmt.Errorf("%q is an overloaded word (%v), not a constant's name", name, m.OverloadConsts(string(name)))
	}
	if _, ok := m.metaMap.Load(name); ok {
		if _, builtin := ext.InitConstMetaMap().Load(name); builtin {
			return fmt.Errorf("constant %q is a built-in of the engine", name)
		}
		return fmt.Errorf("constant %q is already minted by a chapter", name)
	}
	return nil
}

// RegisterConstSyntax records what a chapter declared about a minted
// constant's text (dsl.ConstSyntax). Registered once, by the define
// door; a second registration for the name is a second mint and
// panics, and so does a notation another constant already owns — an
// outfix's opening delimiter, an operator's symbol at its arity, a big
// operator's symbol at its carrier.
// MarkStructurePredicate records that name is a structure's predicate
// (dsl.ConstSyntax.StructurePredicate) on its registered syntax, or
// registers a syntax that says only that: a structure declaring no
// Symbols and no implicit binders has no other syntax to carry it.
func (m *ConstMetaManager) MarkStructurePredicate(name core.TermName) {
	if v, ok := m.syntax.Load(name); ok {
		v.StructurePredicate = true
		return
	}
	m.syntax.Store(name, &dsl.ConstSyntax{StructurePredicate: true})
}

func (m *ConstMetaManager) RegisterConstSyntax(name core.TermName, s *dsl.ConstSyntax) {
	if s == nil || (len(s.Implicit) == 0 && s.Outfix == nil && s.Operator == nil && s.BigOp == nil && s.Structure == nil && s.Overload == nil && s.Coercion == nil && !s.StructurePredicate && s.Bundle == nil && s.Tuple == nil && s.Dims == 0) {
		return
	}
	if _, loaded := m.syntax.LoadOrStore(name, s); loaded {
		if _, isProvisional := m.provisional.LoadAndDelete(name); !isProvisional {
			panic(fmt.Sprintf("constant %q: syntax registered twice", name))
		}
		m.syntax.Store(name, s)
	}
	if s.Outfix != nil {
		m.registerOutfix(name, s)
	}
	if s.Operator != nil {
		m.operatorMu.Lock()
		if m.operator == nil {
			m.operator = map[string][]core.TermName{}
		}
		key := operatorKey(s.Operator.Symbol, s.Operator.Arity())
		m.operator[key] = append(m.operator[key], name)
		m.operatorMu.Unlock()
	}
	if s.BigOp != nil {
		if prev, loaded := m.bigop.LoadOrStore(bigOpKey(s.BigOp.Symbol, s.BigOp.Carrier), name); loaded {
			panic(fmt.Sprintf("constant %q: %s at %s is already %s's", name, s.BigOp.Symbol, ext.FormatType(s.BigOp.Carrier), prev))
		}
	}
	if s.Overload != nil {
		m.registerOverload(name, s.Overload)
	}
	if s.Coercion != nil {
		if prev, loaded := m.coercion.LoadOrStore(string(s.Coercion.Into.Key()), name); loaded {
			panic(fmt.Sprintf("constant %q: the coercion into %s is already %s's", name, ext.FormatType(s.Coercion.Into), prev))
		}
	}
}

// CoercionConst is the constant declared as the embedding of the real
// line into the type, "" when none is — dsl.SyntaxTable.
func (m *ConstMetaManager) CoercionConst(into core.HolType) string {
	if name, ok := m.coercion.Load(string(into.Key())); ok {
		return string(name)
	}
	return ""
}

// registerOverload records name under its overloaded word. It panics
// when the word is a constant's name, and when a constant already
// declaring the word takes as many arguments at a type either one
// instantiates to — the word could never tell the two apart.
func (m *ConstMetaManager) registerOverload(name core.TermName, o *dsl.Overload) {
	if _, minted := m.metaMap.Load(core.TermName(o.Word)); minted {
		panic(fmt.Sprintf("constant %q: the overloaded word %q is a constant's name", name, o.Word))
	}
	m.overloadMu.Lock()
	defer m.overloadMu.Unlock()
	if m.overload == nil {
		m.overload = map[string][]*dsl.Overload{}
		m.overloadOf = map[string][]core.TermName{}
	}
	for i, prev := range m.overload[o.Word] {
		if prev.Arity != o.Arity {
			continue
		}
		_, ab := prev.Type.Matches(o.Type, utils.FullPredicate)
		_, ba := o.Type.Matches(prev.Type, utils.FullPredicate)
		if ab || ba {
			panic(fmt.Sprintf("constant %q: %s at %s is indistinguishable from %s at %s under the word %q",
				name, name, ext.FormatType(o.Type), m.overloadOf[o.Word][i], ext.FormatType(prev.Type), o.Word))
		}
	}
	m.overload[o.Word] = append(m.overload[o.Word], o)
	m.overloadOf[o.Word] = append(m.overloadOf[o.Word], name)
}

// OverloadConsts returns the constants declaring word, in declaration
// order; nil when none does — dsl.SyntaxTable.
func (m *ConstMetaManager) OverloadConsts(word string) []string {
	m.overloadMu.Lock()
	defer m.overloadMu.Unlock()
	names := m.overloadOf[word]
	if len(names) == 0 {
		return nil
	}
	out := make([]string, len(names))
	for i, n := range names {
		out[i] = string(n)
	}
	return out
}

// isOverloadWord reports whether name is an overloaded word.
func (m *ConstMetaManager) isOverloadWord(name core.TermName) bool {
	m.overloadMu.Lock()
	defer m.overloadMu.Unlock()
	return len(m.overloadOf[string(name)]) > 0
}

// ConstSyntax returns the syntax registered for name, nil for a
// constant with none — dsl.SyntaxTable.
func (m *ConstMetaManager) ConstSyntax(name string) *dsl.ConstSyntax {
	s, _ := m.syntax.Load(core.TermName(name))
	return s
}

// ConstMeta supplies a constant's canonical metadata to the syntax table.
func (m *ConstMetaManager) ConstMeta(name string) core.ConstTermMeta {
	meta, _ := m.LoadConstMeta(core.TermName(name))
	return meta
}

// StructSyntax returns the fields declared on the structure type
// typeName, nil for a type that declares none.
func (m *ConstMetaManager) StructSyntax(typeName string) *dsl.StructSyntax {
	s, _ := m.structs.Load(typeName)
	return s
}

// registerStructSyntax records a structure type's fields, once.
func (m *ConstMetaManager) registerStructSyntax(typeName string, s *dsl.StructSyntax) error {
	if _, loaded := m.structs.LoadOrStore(typeName, s); loaded {
		return fmt.Errorf("type %s: fields declared twice", typeName)
	}
	return nil
}

// RangeConstSyntax visits every minted constant that declared syntax,
// in no particular order, until fn returns false: the census of what
// the chapters have declared, against which a gate's hand-kept table
// is checked COMPLETE — a table checked only entry by entry lets a new
// declaration pass by being absent from it.
func (m *ConstMetaManager) RangeConstSyntax(fn func(name string, s *dsl.ConstSyntax) bool) {
	m.syntax.Range(func(name core.TermName, s *dsl.ConstSyntax) bool { return fn(string(name), s) })
}

// registerOutfix records a constant's outfix notation under its
// delimiter pair. A pair belongs to one constant, or to several that
// declare one overloaded word and place their holes alike — `|x|` on
// real_abs, int_abs and complex_abs under `abs` — so that the notation
// reads as the word in delimiters (dsl.resolveOutfixNotation); anything
// else sharing the pair is refused by name. Two pairs with one opening
// delimiter are two notations: `⟦a, b⟧` and `⟦a, b⟭`.
func (m *ConstMetaManager) registerOutfix(name core.TermName, s *dsl.ConstSyntax) {
	m.outfixMu.Lock()
	defer m.outfixMu.Unlock()
	if m.outfix == nil {
		m.outfix = map[string][]core.TermName{}
	}
	key := outfixKey(s.Outfix.Open, s.Outfix.Close)
	if prev := m.outfix[key]; len(prev) > 0 {
		first, _ := m.syntax.Load(prev[0])
		switch {
		case s.Overload == nil || first.Overload == nil:
			panic(fmt.Sprintf("constant %q: the notation %s…%s is already %s's — a second constant shares it only under an overloaded word both declare", name, s.Outfix.Open, s.Outfix.Close, prev[0]))
		case s.Overload.Word != first.Overload.Word:
			panic(fmt.Sprintf("constant %q: the notation %s…%s is %s's under the word %q, not %q", name, s.Outfix.Open, s.Outfix.Close, prev[0], first.Overload.Word, s.Overload.Word))
		case !dsl.SameOutfixShape(s.Outfix, first.Outfix):
			panic(fmt.Sprintf("constant %q: the notation %s…%s places its holes differently from %s's", name, s.Outfix.Open, s.Outfix.Close, prev[0]))
		}
	}
	m.outfix[key] = append(m.outfix[key], name)
}

// outfixKey is the outfix table's key: a delimiter pair.
func outfixKey(open, close string) string { return open + "…" + close }

// OutfixConsts returns the constants whose notation is the delimiter
// pair open…close, in declaration order; nil when none does —
// dsl.SyntaxTable.
func (m *ConstMetaManager) OutfixConsts(open, close string) []string {
	m.outfixMu.Lock()
	defer m.outfixMu.Unlock()
	var names []string
	for _, n := range m.outfix[outfixKey(open, close)] {
		names = append(names, string(n))
	}
	return names
}

// OperatorConsts returns the constants declaring symbol at arity, in
// declaration order; nil when none does — dsl.SyntaxTable.
func (m *ConstMetaManager) OperatorConsts(symbol string, arity int) []string {
	m.operatorMu.Lock()
	defer m.operatorMu.Unlock()
	names := m.operator[operatorKey(symbol, arity)]
	if len(names) == 0 {
		return nil
	}
	out := make([]string, len(names))
	for i, n := range names {
		out[i] = string(n)
	}
	return out
}

// BigOpConst returns the constant declaring symbol at the carrier, ""
// when none does — dsl.SyntaxTable.
func (m *ConstMetaManager) BigOpConst(symbol string, carrier core.HolType) string {
	name, _ := m.bigop.Load(bigOpKey(symbol, carrier))
	return string(name)
}

// TypeArity is the corpus's type vocabulary for the text parser
// (dsl.ParseScope.TypeResolver): the arity of a type the engine mints
// for itself (dsl.BuiltinTypeArity), the type the postulate introduces,
// or a type constructor some registered constant's type mentions,
// ok=false for every other name.
// Under this a statement's type position cannot name a type the corpus
// does not have — before it, an unknown name parsed to a phantom
// composite type with every gate green.
func (m *ConstMetaManager) TypeArity(name string) (int, bool) {
	if arity, ok := dsl.BuiltinTypeArity(name); ok {
		return arity, true
	}
	if postulate != nil && postulate.Build.Postulate.Type == name {
		return 0, true
	}
	m.typeIndexMu.Lock()
	defer m.typeIndexMu.Unlock()
	arity, ok := m.typeIndex[name]
	return arity, ok
}

func collectTypeArities(t core.HolType, into map[string]int) {
	c, ok := t.(core.CompositeType)
	if !ok {
		return
	}
	into[string(c.Meta().Name())] = c.Meta().Arity()
	for i := range c.Meta().Arity() {
		collectTypeArities(c.SubType(i), into)
	}
}

// Range visits every registered constant. For the readers that ask a
// question of every constant's TYPE (is this type name in use?).
func (m *ConstMetaManager) Range(yield func(core.ConstTermMeta) bool) {
	m.metaMap.Range(func(_ core.TermName, meta core.ConstTermMeta) bool {
		return yield(meta)
	})
}
