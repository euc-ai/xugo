// syntax.go — the syntax record a minted constant carries, and the
// chapter's spelling of a statement.
//
// The sugars the DSL knows by itself (`∅`, `{x | φ}`, `⋃`, `&n`, `∘`)
// are spellings of constants the DSL owns. A chapter's constants are
// minted in Go, and the DSL learns their syntax from the chapter: the
// define door registers a ConstSyntax with the mint, and every parse
// scope reaches it through ParseScope.Syntax. Six facts live in the
// record — the leading IMPLICIT binders (implicit.go), the DIMENSIONS
// after them (dimension.go), an OUTFIX notation (outfix.go), an
// OPERATOR notation (operator.go), a BIG-OPERATOR notation (bigop.go)
// and an OVERLOADED word (overload.go); a further notation form would
// be a further field here and its own file.
//
// ChapterSpelling is the inverse of all of them, for the surfaces that
// print a statement back: implicit arguments the scope reads are
// dropped and applications of a constant with a notation are folded
// into it, and the result is checked to print and parse as one AST.
// DisplaySpelling is the same reading for a display printer's text —
// the engine's output door and emit's labels, which serve what the
// chapter writes without touching the kernel printers.

package dsl

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
)

// ConstSyntax is what a chapter declares about one minted constant's
// text: its implicit leading binders and, optionally, its outfix
// notation. Registered with the mint (the define door), served to the
// parser through ParseScope.Syntax.
type ConstSyntax struct {
	// Implicit names the leading binders a scope completes — see
	// implicit.go.
	Implicit []string
	// Outfix is the constant's outfix notation, nil when it has none.
	Outfix *Outfix
	// Operator is the constant's infix or prefix operator notation, nil
	// when it has none — see operator.go.
	Operator *Operator
	// BigOp is the constant's big-operator notation — the constant IS
	// `Σ` (or `Π`) at its carrier — nil when it has none; see bigop.go.
	BigOp *BigOp
	// Structure is a structure predicate's declaration of the operator
	// symbols its components carry, nil for a constant that is not a
	// declaring structure — see structure.go.
	Structure *StructureSyntax
	// Overload is the word the constant answers to among the constants
	// that share it — `sum` for real_sum, nat_sum and int_sum — nil
	// when it has none; see overload.go.
	Overload *Overload
	// Coercion marks the constant as the embedding `&` writes into its
	// codomain from the real line — complex_of_real into ℂ — nil for
	// every other constant. The build lifts a real operand through it
	// where that codomain is expected or a partner has it, and a num
	// operand through the real line first (build.go's buildCoerce); the
	// chapter spelling writes the application back as `&` where its
	// position types it (coercion.go).
	Coercion *Coercion
	// StructurePredicate marks a structure's predicate — `is_topology`,
	// `comm_ring`, `metric_space` — whether or not it declares Symbols:
	// the constants whose application to variables makes those
	// variables a structure's components. The chapter spelling elides a
	// VARIABLE component only where such an application over it stands
	// in the text (ChapterSpelling): a statement that carries no
	// structure over a component spells it, and the served text keeps
	// that spelling — the chapter's visible sign that the statement
	// needs no structure (constitution §Structures).
	StructurePredicate bool
	// Bundle is where a bundle of a structure goes among the constant's
	// parameters — a structure's own components and sub-structures, a
	// definition's declared Bundles — nil when nowhere; see bundle.go.
	Bundle *BundleSyntax
	// Tuple marks the name as a family's tuple of terms rather than a
	// constant: it stands among an application's arguments and is
	// spliced there; see bundle.go.
	Tuple *TupleSyntax
	// Dims is the number of the constant's leading EXPLICIT arguments
	// that are dimensions — one for `vec⟨n⟩(zero, u)`, two for
	// `matrix⟨n, m⟩(zero, A)` — which the text writes in the ⟨…⟩ after
	// the constant's name; zero for a constant that declares none. See
	// dimension.go.
	Dims int
}

// Coercion is a declared embedding: Into is the codomain the constant
// lifts the real line into. NumeralsOnly marks a lift that is an
// embedding on the nonnegative line alone (extended_of_real into
// [0, ∞] sends a negative real to 0): `&` lifts a num through it, read
// on the real line, and never a real, so a text's `&` into the type
// always names a value the lift keeps.
type Coercion struct {
	Into         core.HolType
	NumeralsOnly bool
}

// Overload is one overloaded word: the word, and the number of
// arguments the constant takes (its full application, the only form
// the word spells). Which constant `word(a₁, …, aₖ)` means is read off
// the arguments — the constants sharing the word with k arguments,
// narrowed to the one their types fit.
type Overload struct {
	Word  string
	Arity int
	// Type is the constant's type, which the registration reads to
	// refuse two constants a word could never tell apart.
	Type core.HolType
}

// Operator is one operator notation: the symbol, and which of the
// constant's EXPLICIT argument positions (0-based, after the implicit
// prefix) the operands fill, in reading order — two for an infix
// `u + v`, one for a prefix `-u`, three for the limit mixfix
// `f ⟶ l (at c)` (the function, the limit, the point). The symbol is
// one the grammar already parses (`+ - * / • ⟶` infix, `-` prefix, `⟶`
// with its point clause at arity three); the build resolves it to this
// constant when no built-in domain serves the operand types.
type Operator struct {
	Symbol string
	Args   []int
}

// Arity is the number of explicit arguments the notation spells.
func (o *Operator) Arity() int { return len(o.Args) }

// BigOp is one big-operator notation: the symbol, and the carrier the
// constant folds over — the result type of
// `sum : (A → bool) → (A → real) → real`. A big operator at a carrier no
// constant declares is the fold mechanism at that carrier's `+` (or
// `*`) — see bigop.go.
type BigOp struct {
	Symbol  string
	Carrier core.HolType
}

// Outfix is one outfix notation: the delimiters, and which of the
// constant's EXPLICIT argument positions (0-based, after the implicit
// prefix) the body holes and the subscript fill. Arity is the number of
// explicit arguments the notation supplies — the constant applied to
// exactly that many (after its implicit prefix) prints in the notation.
type Outfix struct {
	Open, Close string
	Body        []int // argument position of each body hole, in reading order
	Sub         int   // argument position of the subscript; -1 when the notation has none
}

// Arity is the number of explicit arguments the notation spells.
func (o *Outfix) Arity() int {
	if o.Sub >= 0 {
		return len(o.Body) + 1
	}
	return len(o.Body)
}

// SyntaxTable is the parser's view of the corpus's constant syntax:
// the record of a constant by name, and the constants that own a
// delimiter pair. The process constant registry
// implements it; a test supplies its own.
type SyntaxTable interface {
	ConstSyntax(name string) *ConstSyntax
	// ConstMeta supplies a constant's canonical metadata for type-directed
	// field spelling and operator resolution; nil for an unknown name.
	ConstMeta(name string) core.ConstTermMeta
	// OutfixConsts is every constant whose notation is the delimiter
	// pair open…close, in declaration order; nil when none does.
	// Several share a pair only under one overloaded word (outfix.go).
	OutfixConsts(open, close string) []string
	// OperatorConsts is every constant declaring symbol at arity (2
	// for an infix, 1 for a prefix), in the order they were declared;
	// nil when none does. The operands' types pick one (operator.go).
	OperatorConsts(symbol string, arity int) []string
	// BigOpConst is the constant declaring symbol at the carrier, ""
	// when none does.
	BigOpConst(symbol string, carrier core.HolType) string
	// OverloadConsts is every constant declaring word, in the order
	// they were declared; nil when none does.
	OverloadConsts(word string) []string
	// CoercionConst is the constant declared as the embedding of the
	// real line into the type, "" when none is.
	CoercionConst(into core.HolType) string
	// TupleNames is every tuple a family declared, in declaration order
	// (bundle.go).
	TupleNames() []string
	// StructSyntax is the fields a structure type declares, nil for a
	// type that declares none (struct_fields.go).
	StructSyntax(typeName string) *StructSyntax
}

// ---------------------------------------------------------------------------
// The inverse: printing a statement in the chapter's spelling
// ---------------------------------------------------------------------------

// ChapterSpelling rewrites raw — a statement in the text DSL, as the
// parser-faithful printers emit it — into the spelling a chapter with
// this syntax table and these instance bindings writes: implicit
// arguments the scope reads back are dropped (implicit.go), full
// applications of a constant with a notation are folded into it — an
// outfix, an operator, a big operator, an overloaded word — a
// constant's dimensions are written in its ⟨…⟩ (dimension.go), a declared
// coercion is written `&` where its position types it (coercion.go),
// and an integer literal beside a partner that types it is written
// `&n` (intliteral.go). The folded AST is printed and
// the print is checked to parse back to that same AST (the print and
// the parse being each other's inverse is what the check pins; the
// folds themselves are the structural rewrites the build inverts by
// type, and the consumer that serves the spelling re-parses it under
// the full scope and compares keys); a text the check refuses comes
// back unchanged with the error. A nil table returns raw as it is.
func ChapterSpelling(raw string, table SyntaxTable, bindings map[string]core.Term) (string, error) {
	out, _, err := ChapterSpellingFolded(raw, table, bindings)
	return out, err
}

// ChapterSpellingFolded is ChapterSpelling reporting besides whether a
// fold fired — an implicit prefix dropped, a notation, an overloaded
// word or a big operator folded — as against a re-print alone of a text
// already in the chapter's spelling. A reader of an AUTHORED text keeps
// the author's own where nothing folded (the index's headlines); a
// reader of a printer's text takes the re-print either way.
func ChapterSpellingFolded(raw string, table SyntaxTable, bindings map[string]core.Term) (out string, folded bool, err error) {
	if table == nil {
		return raw, false, nil
	}
	work, err := parseStmtAST(raw)
	if err != nil {
		return raw, false, err
	}
	declared := map[string]bool{}
	declaredTypes := map[string]core.HolType{}
	for _, d := range work.decls {
		if d.name != "" && d.typeStr != nil {
			declared[d.name] = true
			declaredTypes[d.name] = chapterBinderType(table, d.typeStr)
		}
	}
	scope := &ParseScope{Syntax: table, ImplicitBindings: bindings}
	c := newImplicitCompletion(scope, func(name string) bool { return declared[name] }, false)
	c.constMeta = table.ConstMeta
	c.declaredType = func(name string) core.HolType { return declaredTypes[name] }
	c.declaredTypes = declaredTypes
	// The text's own structure facts — a law's antecedent, a goal's
	// hypotheses printed before ⊢ — bind the symbols their components
	// declare (structure.go), and license the elision of a variable
	// component: an implicit argument bound to a variable is dropped
	// only where a structure predicate over that variable stands in the
	// text, so a statement that needs no structure is served spelling
	// its components as the chapter writes them.
	roots := []astNode{work.body}
	for i := range work.decls {
		if work.decls[i].hyp != nil {
			roots = append(roots, work.decls[i].hyp)
		}
	}
	structured := structureBoundNames(table, roots)
	// A bundle binder `∀P:zz_fib_cx(B).` stands for the structure fact
	// at its components, so the components it leaves to the predicate's
	// own names are bound by a structure too.
	for _, d := range work.decls {
		t, ok := d.typeStr.(*astTypeNamed)
		if !ok || d.name == "" {
			continue
		}
		syn := table.ConstSyntax(t.name)
		if syn == nil || syn.Bundle == nil || !syn.Bundle.Structure {
			continue
		}
		for i, p := range syn.Bundle.Params {
			if i != syn.Bundle.Subject {
				structured[p.Name] = true
			}
		}
	}
	c.elideBinder = func(name string) bool { return structured[name] }
	c.components = structured
	// A record the text shows without declaring it — a display's free
	// variable that a projection reads, `R` in `ring_add(R, a, b)` —
	// holds its fields' symbols as a declared one does where the parser
	// reads the text (struct_fields.go).
	structureOps := withShownRecords(structureOperators(table, roots, nil, declaredTypes), table, shownRecords(table, roots, declared))
	markStructureSymbolsRead(structureOps, table, textTypes(roots, declaredTypes), bindings)
	fieldEnv := newTypeEnv()
	// Operator probes keep declared carrier letters rigid, as the statement door does.
	fieldEnv.freshenMeta = true
	fieldEnv.syntax = table
	fieldEnv.resolver = table.ConstMeta
	fieldEnv.declared = declaredTypes
	fieldEnv.implicitBindings = bindings
	fieldEnv.structureOps = structureOps
	// Every name the text spells: an overloaded word already standing in
	// it (a constant of that very name, a variable) keeps a constant of
	// its family from folding into it (overload.go).
	textNames := map[string]bool{}
	for _, r := range roots {
		collectASTNames(r, textNames)
	}
	for name := range declared {
		textNames[name] = true
	}
	changed := false
	// Bundles fold first, while every structure fact and constant is
	// still spelled out (bundle.go); the elision below then reads the
	// folded text.
	bundleScope := &bundleScope{table: table, bundles: map[string]*bundle{}, types: map[string]core.HolType{},
		avoid: map[string]bool{}, bound: map[string]bool{}, declared: map[string]bool{}, root: true}
	for name := range declared {
		bundleScope.avoid[name] = true
		bundleScope.bound[name] = true
		bundleScope.declared[name] = true
	}
	for _, d := range work.decls {
		if d.name != "" && d.typeStr != nil {
			bundleScope.types[d.name] = resolveType(d.typeStr)
		}
	}
	tuples := table.TupleNames()
	bodyScope := bundleScope
	for i := range work.decls {
		if work.decls[i].hyp != nil {
			bodyScope = bodyScope.withBundles(bundleScope.factsOf(work.decls[i].hyp))
		}
	}
	for i := range work.decls {
		if work.decls[i].hyp != nil {
			work.decls[i].hyp = foldBundles(work.decls[i].hyp, bundleScope, tuples, &changed)
		}
	}
	work.body = foldBundles(work.body, bodyScope, tuples, &changed)
	rewrite := func(node astNode) astNode {
		node = c.elide(node, map[string]int{}, &changed)
		node = foldOutfix(node, table, map[string]int{}, declared, &changed)
		// What no notation took: a constant's dimensions go to the ⟨…⟩
		// after its name (dimension.go).
		node = foldDimensions(node, table, map[string]int{}, declared, &changed)
		node = foldOperators(node, table, map[string]int{}, declared, &changed)
		node = foldStructFields(node, fieldEnv, &changed)
		node = foldStructureOperators(node, structureOps, map[string]int{}, declared, &changed)
		node = foldBigOps(node, table, structureOps, map[string]int{}, declared, &changed)
		node = foldOverloads(node, table, textNames, map[string]int{}, declared, &changed)
		// Over the text as the folds above leave it: a declared coercion
		// folds into `&` where the position the build reads it at types
		// it (coercion.go), an integer literal beside the partner that
		// types it (intliteral.go).
		node = c.foldCoercions(node, nil, map[string]int{}, &changed)
		return foldIntLiterals(node, map[string]int{}, declared, &changed)
	}
	work.body = rewrite(work.body)
	for i := range work.decls {
		if work.decls[i].hyp != nil {
			work.decls[i].hyp = rewrite(work.decls[i].hyp)
		}
	}
	// The text is re-printed whether or not a fold fired: the printer's
	// form is the chapter's — binders grouped, the left-associated ∧
	// unbracketed, a comprehension in braces — where the display
	// printers the text came from parenthesize every node, and a
	// statement with nothing to fold must not come out in the kernel's
	// form because its neighbour folded and came out in the chapter's.
	var pr stmtPrinter
	out, perr := pr.prop(work)
	if perr != nil {
		return raw, false, perr
	}
	back, err := parseStmtAST(out)
	if err != nil {
		return raw, false, fmt.Errorf("chapter spelling does not re-parse (%q): %w", out, err)
	}
	canonGenPVars(work)
	canonGenPVars(back)
	if !astPropEqual(work, back) {
		return raw, false, fmt.Errorf("chapter spelling does not print and parse as one AST (%q)", out)
	}
	return out, changed, nil
}

// displayTurnstile is the display printers' spelling of a statement
// with no hypotheses (prop.PrintProp): a leading turnstile with nothing
// declared before it, which the statement grammar does not read.
const displayTurnstile = "⊢ "

// DisplaySpelling is ChapterSpelling for the text of a display printer
// (prop.PrintProp, ext.PrintTerm): the output door's reading of a
// goal, a hypothesis or a term served back to its author. The
// display's leading turnstile on a hypothesis-free statement is set
// aside and put back; a hypothesis list before the turnstile, a term
// on its own, read as the statement grammar's. A text the spelling
// cannot read, or that it leaves unchanged, comes back as it is — a
// display is never withheld, and never a different text than the
// printer's beyond the chapter's folds. Nothing is checked beyond the
// spelling's own print–parse round trip: a display has no key, so the
// folds must be sound by construction — an application whose implicit
// prefix the elision could not drop keeps its call form (astApp.elided
// is what the operator and big-operator folds read).
func DisplaySpelling(text string, table SyntaxTable, bindings map[string]core.Term) string {
	prefix := ""
	body := text
	if rest, ok := strings.CutPrefix(text, displayTurnstile); ok {
		prefix, body = displayTurnstile, rest
	}
	out, err := ChapterSpelling(body, table, bindings)
	if err != nil {
		return text
	}
	return prefix + out
}
