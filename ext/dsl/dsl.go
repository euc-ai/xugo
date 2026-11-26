// Package dsl is the text DSL — agent-facing surface syntax for
// `core.Prop`. A lexer + recursive-descent parser + type inference
// lower hand-written input into `core.Prop`, returning structured
// diagnostics on failure.
//
// This file holds the public entry points and the result/diagnostic
// types. The pipeline is split across sibling files: lex.go (lexer),
// ast.go (AST nodes), parser.go (grammar), infer.go (type inference),
// build.go (lowering to core.Term/Prop), normalize.go (symbol
// normalization). The nat-arithmetic vocabulary lives in arith.go.
//
// Entry points:
//   - ParsePropText(raw string) ParseResult
//   - ParseTermText(raw string, ctx map[string]core.HolType, expected core.HolType) ParseResult
//   - ParseTypeText(raw string) (core.HolType, error)
//
// The proto path (lossless reconstruction of arbitrary props) is owned
// by `ext/proto.go`, not here.
//
// # Notation
//
// The package reads statement text and prints it back; its grammar is
// the manual's §"Text format" (engine/xugo-engine.md). Notation comes
// from two places. The sugars the DSL knows by itself (`∅`, `{x | φ}`,
// `⋃`, `&n`, `∘`) are spellings of constants the DSL owns, built into
// its lexer and parser. A chapter's constants are minted in Go, and the
// DSL learns their syntax from the chapter: the define door registers a
// ConstSyntax with the mint — the leading implicit binders, an outfix
// (`|x|`), an operator, a big operator (`Σ`), an overloaded word — and
// every parse scope reaches it through ParseScope.Syntax (syntax.go).
// A further notation form is a further field of that record and a file
// of its own.
//
// One invariant holds for both: NOTATION IS KEY-NEUTRAL. A sugared text
// parses to the SAME core term as its longhand, so declaring or using a
// notation moves no statement key and no recorded certificate, and
// converting a chapter's texts to it is a pure edit — the members
// replay unchanged. The printers enforce this instead of assuming it: a
// chapter spelling is served only when it prints and parses back as one
// AST (ChapterSpelling), and the gate TestStatementPrintRoundTrip
// (library/integrity/gates) holds every registered statement to it.
//
// A lowering takes the constant it builds from the caller's scope first
// and from the DSL's own surface constant only when the scope has none
// of that name and type. The two have one name and one type, so every
// key agrees either way; what differs is the definition the scope's
// constant carries, and a term built on the bare one is a term no
// unfolding opens.
package dsl

import (
	"fmt"
	"os"
	"runtime"
	"runtime/debug"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// ParseResult is the output of the text DSL parser. Whether `Prop` or
// `Term` is populated depends on which entry point was called
// (ParsePropText / ParseTermText). At most one is non-nil on success.
type ParseResult struct {
	// If non-nil, ParsePropText succeeded. Safe to pass to the engine.
	Prop core.Prop `json:"-"`

	// If non-nil, ParseTermText succeeded. Safe to pass to the engine.
	Term core.Term `json:"-"`

	// Non-fatal issues (normalizations applied, warnings).
	Warnings []InputDiagnostic `json:"warnings,omitempty"`

	// Fatal issues. If non-empty, Prop / Term are nil.
	Errors []InputDiagnostic `json:"errors,omitempty"`

	// The input after symbol normalization (always populated).
	NormalizedInput string `json:"normalized_input"`
}

// InputDiagnostic describes a single issue found during input processing.
type InputDiagnostic struct {
	Position       int               `json:"position"`                  // byte offset in input
	Length         int               `json:"length"`                    // span of the problematic text
	Code           string            `json:"code"`                      // machine-readable code
	Message        string            `json:"message"`                   // explanation
	Suggestion     string            `json:"suggestion,omitempty"`      // concrete fix
	AutoFixed      bool              `json:"auto_fixed,omitempty"`      // true if auto-corrected
	SuggestedTypes map[string]string `json:"suggested_types,omitempty"` // var → formatted type (on type errors)
}

// Diagnostic codes.
const (
	CodeParseError    = "parse_error"
	CodeMissingType   = "missing_type"
	CodeTypeMismatch  = "type_mismatch"
	CodeArityMismatch = "arity_mismatch"
	CodeUnknownSymbol = "unknown_symbol"
	CodeCorePanic     = "core_panic"
	CodeValidation    = "validation_error"
	// CodeUnknownType: a type name no registered constant's type
	// mentions (typenames.go). CodeSetApplied: an application consumed
	// a binder's set(…) position (setspelling.go).
	CodeUnknownType = "unknown_type"
	CodeSetApplied  = "set_applied"
	// CodeNumeralDomain is a warning: a relation between `&` numerals
	// alone, whose type the scope's domain decided and nothing in the
	// text names (build.go, numeralWarnings).
	CodeNumeralDomain = "numeral_domain"
)

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

// ParsePropText parses a text-format proposition into a `core.Prop`.
//
// Grammar (after normalization):
//
//	prop      := hyps "⊢" expr  |  decls "⊢" expr  |  expr
//	decls     := decl ("," decl)*
//	decl      := NAME ":" type       (variable type declaration)
//	          |  expr                 (hypothesis)
//	expr      := quant | iff
//	quant     := ("∀"|"∃"|"ε") NAME ":" type "." expr
//	iff       := impl ("⇔" impl)*
//	impl      := disj ("⇒" impl)?    (right-associative)
//	disj      := conj ("∨" conj)*
//	conj      := unary ("∧" unary)*
//	unary     := "¬" unary | atom
//	atom      := NAME "(" args ")"   (application)
//	          |  atom "=" atom        (equality, handled at this level)
//	          |  NAME
//	          |  "⊤" | "⊥"
//	          |  "(" expr ")"
//	args      := expr ("," expr)*
//	type      := tvar "→" type | tvar
//	tvar      := NAME | "bool" | "(" type ")"
func ParsePropText(raw string) ParseResult {
	return ParsePropTextInScope(raw, nil)
}

// ParseScope carries a caller-supplied symbol table for parsing.
// `Script` uses it to thread the proof's declared
// vars and consts into the parser so emit-output text forms can name
// non-well-known consts (`subset`, `int_of_num`, …) and free vars.
//
// Consts maps a const name to an already-instantiated `core.ConstTerm`
// — buildVarTerm / buildApp use the term directly, bypassing the
// default "treat unknown name as variable" path. Each entry's
// instantiated type is fixed; if a name needs multiple instantiations
// in the same prop (rare polymorphic case), only the entry in scope
// wins and the other use-sites end up as Var, which the caller's
// alpha-key compare will catch as a round-trip miss.
//
// Vars seeds typeEnv.declared with free-var types, analogous to
// ParseTermText's `ctx` argument. Quantifier-bound vars (introduced
// inline via `∀x:T...`) don't need to be in Vars.
//
// A nil scope behaves identically to the original ParsePropText
// surface — only well-known nat-encoding consts are recognized; all
// other names default to variables.
type ParseScope struct {
	// Consts: fixed instantiation. When a section uses the const at
	// this exact type, the parser plugs the term in directly. Fast
	// path; populated by emit's first-walked instance per name and by
	// Script.Const at runtime.
	Consts map[string]core.ConstTerm

	// ConstMetas: polymorphic-aware fallback. When Consts misses (or
	// Consts has a different type instance than the section needs),
	// the parser re-instantiates the meta from the application's
	// argument types via instantiateConstMeta. Lets one scope handle
	// the same polymorphic const at multiple types in the same proof
	// (e.g. `==` at num and int in num_congruent; COND at any type).
	ConstMetas map[string]core.ConstTermMeta

	// Vars: free-var type bindings.
	Vars map[string]core.HolType

	// ConstResolver, when set, supplies polymorphic ConstTermMetas for
	// names that occur in the input but are not present in Consts or
	// ConstMetas. The DSL never imports the registry directly; the engine
	// (or any caller with access to a const registry) plugs its lookup in
	// here so a claim text can name a registered constant — e.g. `dest_nadd`
	// in an assert claim whose goal happens not to mention `dest_nadd` —
	// without the agent having to predeclare it. A miss returns nil.
	// Names already bound by a quantifier in the input are not queried.
	// A name that resolves here is treated identically to a same-named
	// entry in Consts / ConstMetas, including the polymorphic-instantiation
	// path used by `COND`-style heads.
	ConstResolver func(name string) core.ConstTermMeta

	// TypeResolver, when set, is the corpus's type vocabulary: the
	// arity of a registered type constructor by name, ok=false for a
	// name no registered constant's type mentions. Under it an unknown
	// type name in any type position is an error (typenames.go); nil
	// keeps a bare parse loose about names it cannot know. Wired
	// beside ConstResolver from the same registry.
	TypeResolver func(name string) (arity int, ok bool)

	// StrictResolution, when set, turns silent name-freshening in a
	// PROP parse into an error: an identifier that resolves to no
	// constant (scope, resolver, or well-known default) and is neither
	// quantifier-bound nor a declared variable (Vars, or an in-text
	// `name:type ⊢` decl) is rejected with a repair-naming diagnostic
	// instead of parsing as a fresh free variable at an inferred type.
	// Statement doors set this (family registration, member
	// scripts, session statement RPCs); the machine dialect (generated
	// Stmts, emit) and bare test/agent surfaces stay loose. Term parses
	// are unaffected — the term/claim paths carry their own post-parse
	// contracts (Script.TermText's assert, Argument's claim check).
	StrictResolution bool

	// StrictMint, when set, additionally requires every type variable
	// of a parsed PROP to be ANCHORED — spelled by the author through a
	// binder/variable type or a `⟨V:T⟩` tie — never inherited from a
	// bare polymorphic head's own abstract letters (buildAppViaMeta
	// instantiates meta.AbsType verbatim, so an unpinned head freezes
	// its letters into the statement: a DIFFERENT theorem that prints
	// identically — the class-2 false-mint shape). Mint doors set this
	// (conjecture / mint / add-goal text); statement registration does
	// NOT — it reads a member's statement with FreshenMetaLetters and
	// refuses an unpinned letter itself (UnpinnedLetters).
	StrictMint bool

	// CoerceDomain declares the scope's ambient numeric domain for the
	// type-directed `&` coercion (nil, RealType, or IntType): an
	// UNANCHORED `&` — one no neighbouring operand pins — lowers into
	// the declared domain instead of the global real_of_num default.
	// Anchors keep winning: an operand type the author spelled is
	// intent, and the reconcile retargets a declared-default coercion
	// to the partner's domain in either direction, so mixed-domain
	// bridge statements cost nothing. The domain is real, int, or a
	// type some constant is the declared coercion into (ConstSyntax.
	// Coercion — ℂ through complex_of_real): there `&` of a REAL is
	// that lift, and a num is still read on the real line, lifting
	// only where a position or a partner asks. Under StrictResolution, an
	// unanchored `&` in a scope with NO declared domain is an ERROR
	// naming the repairs — the silent defaults-to-ℝ receipts die at
	// the door. Applies to prop AND term parses (bodies pay the same
	// trap); the strict guard is prop-only like the other switches.
	CoerceDomain core.HolType

	// StrictCoercion is the `&` half of StrictResolution by itself: a
	// PROP parse under it refuses an unanchored `&` where the scope
	// declares no domain, and resolves names as loosely as it would
	// without. The claim doors set it: they clear StrictResolution to
	// report an undeclared name themselves, after the parse, and the
	// guard on `&` must not go with it — a claim and the statement it
	// serves are read by one rule. StrictResolution implies it.
	StrictCoercion bool

	// FreshenMetaLetters, when set, renames a polymorphic const meta's
	// internal letters to fresh occurrence-local names at every
	// instantiation, so a meta letter can never capture (or be
	// captured by) a same-named author letter — the parse's meaning
	// becomes invariant under renaming the author's letters, which is
	// the defect the powers/words receipts measured. `⟨⟩` ties keep
	// addressing the meta's canonical letters (translated internally),
	// and the unifier's bindings for fresh letters are substituted
	// back into already-built arguments — sound exactly because fresh
	// letters are occurrence-local. Deterministic (per-parse counter):
	// identical text parses to the identical statement. Census flag
	// for now; doors flip after the corpus diff is measured.
	FreshenMetaLetters bool

	// Syntax is the corpus's constant syntax — a minted constant's
	// implicit leading binders (implicit.go) and its outfix notation
	// (outfix.go), declared at the constant's definition and registered
	// with its mint. nil disables both: no completion, no notation.
	Syntax SyntaxTable

	// Definiendum is the name a definition's equation defines, which
	// the scope declares as a variable (Vars), with the implicit prefix
	// and the dimension count its constant will carry: the equation
	// writes the definiendum's dimensions in its ⟨…⟩ as every later
	// text writes the constant's (dimension.go). nil outside a
	// definition's equation, and for a definiendum that declares none.
	Definiendum *Definiendum

	// ImplicitBindings maps an implicit binder NAME to the term it
	// stands for where the text binds nothing of that name — a family
	// working at an instance of the structure (`add ↦ real_add`,
	// `zero ↦ &0`, read off the instance theorem). A name the text
	// binds by a quantifier, or the scope declares as a variable, wins
	// over an entry here.
	ImplicitBindings map[string]core.Term

	// ImplicitCompleted, when set, is told of every implicit argument
	// the completion pass supplies: the constant, the binder name, and
	// whether the argument is a variable the text binds or declares
	// (true) or an instance component from ImplicitBindings (false). An
	// observer only — it changes nothing parsed. The implicit-spelling
	// lint reads a registered statement's completions through it.
	ImplicitCompleted func(constName, name string, variable bool)

	// ResidentFacts are the goal's hypotheses a claim or term text is
	// read under: a structure fact among them — a predicate declaring
	// component symbols, applied to variables — binds those symbols to
	// the variables, as the text's own antecedent would (structure.go);
	// a record variable's fields carry theirs by its type
	// (struct_fields.go).
	ResidentFacts []core.Term
	// ResidentNames are the names the text spells a resident fact's
	// variables by, keyed by the variables' own names — a proof block's
	// surface aliases (prover/proof/derive.go, "Surface names"), under
	// which a resident fact states its bundles (bundle.go).
	ResidentNames map[string]string

	// Abbreviations is the statement's table (abbreviation.go): what a
	// «Name» in the text expands to, before any name resolves. nil
	// refuses every «Name». AbbreviationBinders names the statement's
	// own leading binders, the names its entries are written over: a
	// leading quantifier of the text binding one of them is the
	// statement binding its own variable, not a capture. The statement
	// door sets it; the claim and term doors leave it nil, so a claim
	// that rebinds a name an entry spells is refused.
	Abbreviations       *AbbreviationTable
	AbbreviationBinders map[string]bool
}

// ParsePropTextInScope is the scope-aware variant of ParsePropText.
// Pass scope = nil for the bare grammar with no caller-supplied
// symbols.
func ParsePropTextInScope(raw string, scope *ParseScope) ParseResult {
	normalized, _ := NormalizeTextSymbols(raw)
	result := ParseResult{NormalizedInput: normalized}

	// Lex.
	tokens, lexErr := lex(normalized)
	if lexErr != nil {
		result.Errors = append(result.Errors, *lexErr)
		return result
	}

	// Parse to AST.
	par := &parser{tokens: tokens}
	ast, parseErr := par.parseProp()
	result.Warnings = append(result.Warnings, par.warnings...)
	if parseErr != nil {
		result.Errors = append(result.Errors, *parseErr)
		return result
	}
	if par.pos < len(par.tokens) && par.tokens[par.pos].kind != tokEOF {
		tok := par.tokens[par.pos]
		result.Errors = append(result.Errors, InputDiagnostic{
			Position:   tok.pos,
			Length:     len(tok.text),
			Code:       CodeParseError,
			Message:    fmt.Sprintf("unexpected token %q after complete expression", tok.text),
			Suggestion: "check for missing operators or extra characters",
		})
		return result
	}

	// Abbreviations expand before any pass reads a name (abbreviation.go).
	if diag := expandProp(ast, scope); diag != nil {
		result.Errors = append(result.Errors, *diag)
		return result
	}
	if errs := checkTypeNames(withoutBundleBinders(par.typeNames, scope), scopeTypeResolver(scope)); len(errs) > 0 {
		result.Errors = append(result.Errors, errs...)
		return result
	}
	if errs := checkSetApplications(ast); len(errs) > 0 {
		result.Errors = append(result.Errors, errs...)
		return result
	}

	// Resolve types and build core.Prop.
	prop, buildErrs := buildProp(ast, scope, &result.Warnings)
	if len(buildErrs) > 0 {
		result.Errors = append(result.Errors, buildErrs...)
		return result
	}
	result.Prop = prop
	return result
}

// ParseTermText parses a single (non-prop) expression into a
// `core.Term`. Used by tactics that accept a term parameter — `trans`
// (middle of a transitive equality), `witness` (existential witness),
// `instantiate` (universal-hyp witness) — so the agent can construct
// novel terms that are not already subterms of the goal.
//
// `ctx` provides type bindings for free variables. The caller is
// expected to pre-populate it with the goal's free-var types: nat-arith
// operators (`*`, `+`, `suc`) constrain operand types in the build pass,
// not the inference pass, so without ctx a bare-var occurrence like
// `m * suc(n+p)` cannot resolve `m`, `n`, `p`. Names that also have
// inferred types from the expression itself (rare for term input)
// take precedence over ctx entries that disagree.
//
// If `expected` is non-nil, the parsed term's type must equal it; a
// mismatch returns a type-error diagnostic. The caller passes the
// expected type from the surrounding tactic context (e.g. the type of
// an equality's sides, the type of a ∀/∃ binder).
//
// Boolean expressions are accepted — `ParseTermText("x = y", ctx, boolT)`
// works for the same reason `ParsePropText("x = y")` does. The
// difference is purely the agent's surface: `ParseTermText` does not
// require the result to be `bool` and does not expose hypotheses or
// pre-⊢ type declarations.
func ParseTermText(raw string, ctx map[string]core.HolType, expected core.HolType) ParseResult {
	return ParseTermTextInScope(raw, ctx, nil, expected)
}

// ParseTermTextInScope is the scope-aware variant of ParseTermText.
// `scope` supplies constant bindings (ParseScope.Consts /
// ParseScope.ConstMetas) so a name like `predecessor` resolves as the defined
// constant it actually is rather than defaulting to a free variable —
// the same channel buildApp / buildVarTerm already understand for emit
// output. Tactic term-parameter resolution seeds this from the goal's
// constants, so a witness / instantiate / trans / assert term can name
// any constant already present in the goal, not just the four built-in
// nat encoders (_0, bit0, bit1, suc). `ctx` (free-var types)
// takes precedence over scope.Vars on a name collision. A nil scope
// behaves identically to the original ParseTermText surface.
func ParseTermTextInScope(raw string, ctx map[string]core.HolType, scope *ParseScope, expected core.HolType) ParseResult {
	normalized, _ := NormalizeTextSymbols(raw)
	result := ParseResult{NormalizedInput: normalized}

	tokens, lexErr := lex(normalized)
	if lexErr != nil {
		result.Errors = append(result.Errors, *lexErr)
		return result
	}

	par := &parser{tokens: tokens}
	// Reject `⊢` in term input — terms are sub-sequents, not sequents.
	// Using hasTurnstile here lets the agent see the right diagnostic
	// instead of a generic parse error when it accidentally passes a
	// full Prop where a Term was expected.
	if hasTurnstile(par.tokens, par.pos) {
		return ParseResult{
			NormalizedInput: normalized,
			Errors: []InputDiagnostic{{
				Position:   par.peek().pos,
				Code:       CodeParseError,
				Message:    "term input must not contain ⊢",
				Suggestion: "drop the hypothesis/declaration prefix; only the bare expression is expected",
			}},
		}
	}

	exprAST, parseErr := par.parseExpr()
	result.Warnings = append(result.Warnings, par.warnings...)
	if parseErr != nil {
		result.Errors = append(result.Errors, *parseErr)
		return result
	}
	if par.pos < len(par.tokens) && par.tokens[par.pos].kind != tokEOF {
		tok := par.tokens[par.pos]
		result.Errors = append(result.Errors, InputDiagnostic{
			Position:   tok.pos,
			Length:     len(tok.text),
			Code:       CodeParseError,
			Message:    fmt.Sprintf("unexpected token %q after complete expression", tok.text),
			Suggestion: "check for missing operators or extra characters",
		})
		return result
	}
	// Abbreviations expand before any pass reads a name (abbreviation.go).
	// A term is read under no leading binders of its own.
	x := &abbrevExpansion{vars: map[string]core.HolType{}}
	if scope != nil {
		x.table, x.generic = scope.Abbreviations, scope.FreshenMetaLetters
		for name, ty := range scope.Vars {
			x.vars[name] = ty
		}
	}
	for name, ty := range ctx {
		x.vars[name] = ty
	}
	expanded, diag := expandAbbreviations(exprAST, x)
	if diag != nil {
		result.Errors = append(result.Errors, *diag)
		return result
	}
	exprAST = expanded
	if errs := checkTypeNames(withoutBundleBinders(par.typeNames, scope), scopeTypeResolver(scope)); len(errs) > 0 {
		result.Errors = append(result.Errors, errs...)
		return result
	}
	if errs := checkSetApplications(exprAST); len(errs) > 0 {
		result.Errors = append(result.Errors, errs...)
		return result
	}

	env := newTypeEnv()
	for name, ty := range ctx {
		env.declared[name] = ty
	}
	if scope != nil {
		// Caller scope merges onto the env's seeded default nat encoders
		// (newTypeEnv pre-fills scopeConsts/scopeConstMetas with the
		// nat-encoding constants). Default entries win on name
		// collision: a well-known name beats caller scope.
		for name, c := range scope.Consts {
			if _, ok := env.scopeConsts[name]; !ok {
				env.scopeConsts[name] = c
			}
		}
		for name, m := range scope.ConstMetas {
			if _, ok := env.scopeConstMetas[name]; !ok {
				env.scopeConstMetas[name] = m
			}
		}
		// ctx (the goal's free-var types) is authoritative for this goal,
		// so only adopt a scope.Vars binding for a name ctx didn't cover.
		for name, ty := range scope.Vars {
			if _, ok := env.declared[name]; !ok {
				env.declared[name] = ty
			}
		}
		// The declared coercion domain applies to term texts too — the
		// nothing-but-a-coercion receipt bites bodies (`&(val(w))` as a
		// witness has no operator application to anchor it). The strict
		// survival guard stays prop-only.
		env.coerceDomain = scope.CoerceDomain
		env.freshenMeta = scope.FreshenMetaLetters
		env.syntax = scope.Syntax
		env.implicitBindings = scope.ImplicitBindings
		env.residentNames = scope.ResidentNames
		env.resolver = scope.ConstResolver
	}
	// Same resolver pre-seed as buildProp: inject ConstTermMetas
	// for unknown names that scope.ConstResolver can resolve, so a term
	// can name a registered constant the goal happens not to mention. See
	// the comment in buildProp for the broader rationale.
	// A notation names its constant before the resolver pre-seed asks
	// after the names (outfix.go).
	if diag := resolveNotationRoots(scope, []*astNode{&exprAST}); diag != nil {
		return ParseResult{NormalizedInput: normalized, Warnings: result.Warnings, Errors: []InputDiagnostic{*diag}}
	}
	// Bundles — the goal's resident structure facts state them — are
	// written out before anything reads the text's names (bundle.go).
	if diag := expandBundleRoots(scope, env.declared, []*astNode{&exprAST}); diag != nil {
		return ParseResult{NormalizedInput: normalized, Warnings: result.Warnings, Errors: []InputDiagnostic{*diag}}
	}
	if scope != nil && scope.ConstResolver != nil {
		seedResolverConsts(exprAST, env, scope.ConstResolver)
	}
	// Implicit structure arguments are completed before the type
	// collectors read argument positions off the head's type (implicit.go).
	if diag := completeImplicitArgs(scope, env, []*astNode{&exprAST}); diag != nil {
		return ParseResult{NormalizedInput: normalized, Warnings: result.Warnings, Errors: []InputDiagnostic{*diag}}
	}
	// A structure fact resident in the goal binds the symbols its
	// components declare (structure.go); a term text has no antecedent
	// of its own.
	if scope != nil {
		env.structureOps = structureOperators(scope.Syntax, []astNode{exprAST}, scope.ResidentFacts, env.declared)
	}
	// Set-theory surface metas seeded LAST — same discipline as
	// buildProp: caller-provided canonical corpus metas win, then the
	// caller's const resolver (asked through the pre-seed for every
	// set name the text lowers to), and only a name nothing supplied
	// falls through to the DSL-side setops.go metas so bare set-theory
	// syntax still parses in test / agent surfaces.
	seedSetScopeConstFallback(env.scopeConstMetas)
	collectAstTypes(exprAST, env)
	collectTypeGuesses(exprAST, env)

	term, diag, buildErr := safeBuildTerm(func() (core.Term, error) {
		// When the caller gave an expected type, thread it through
		// buildExpected so a non-bool expectation reaches an undeclared
		// head — whether the top-level term is an application (`g(0)` :
		// num) or a lambda whose body is one (`λ….predecessor(g(c))`). Routing
		// through buildTerm would collapse `expected` to the bool-only
		// boolCtx and lose it.
		if expected != nil {
			return buildExpected(exprAST, env, expected)
		}
		return buildTerm(exprAST, env, false)
	})
	if diag != nil {
		enrichTypeDiagnostic(diag, env, buildErr)
		return ParseResult{
			NormalizedInput: normalized,
			Warnings:        result.Warnings,
			Errors:          append(env.errors, *diag),
		}
	}
	if len(env.errors) > 0 {
		return ParseResult{
			NormalizedInput: normalized,
			Warnings:        result.Warnings,
			Errors:          env.errors,
		}
	}

	if expected != nil && env.freshenMeta {
		term = readAtExpected(term, expected)
	}
	if expected != nil && !term.Type().Equals(expected) {
		return ParseResult{
			NormalizedInput: normalized,
			Warnings:        result.Warnings,
			Errors: []InputDiagnostic{{
				Code: CodeTypeMismatch,
				Message: fmt.Sprintf(
					"term has type %s but expected %s",
					ext.FormatType(term.Type()), ext.FormatType(expected)),
			}},
		}
	}

	result.Term = term
	return result
}

// illTypedApplicationRepair is the repair an application whose argument
// its slot cannot take is reported with, by the kernel or by the builder.
const illTypedApplicationRepair = "check the number and types of arguments in each " +
	"application; for a genuine pair domain, apply the function in " +
	"curried form or use the pair/product type."

// panicToBuildDiagnostic maps a panic recovered while building a core
// term/prop from parsed DSL into a structured diagnostic.
//
// The kernel enforces well-typedness with Assert (core.Apply, core.Eq, …),
// which panics with the generic "Should not happen." on a type/arity
// mismatch. In the DSL→core build context that is a USER error — a malformed
// application in the input — not an engine fault, so it must read as a
// type_mismatch with actionable guidance, NOT "internal error: Should not
// happen." (which looks like an engine bug and misled an agent into recording
// a false capability wall). Any OTHER panic string is genuinely unexpected
// and keeps the core_panic framing.
func panicToBuildDiagnostic(r any) *InputDiagnostic {
	msg := fmt.Sprintf("%v", r)
	var diag *InputDiagnostic
	if strings.Contains(msg, "Should not happen.") {
		diag = &InputDiagnostic{
			Code: CodeTypeMismatch,
			Message: "ill-typed term: a function application has mismatched " +
				"argument types or arity (the kernel rejected the constructed " +
				"term). Note that a tuple-looking arrow type such as " +
				"`(num,num)→num` parses as a CURRIED `num→num→num`, so applying " +
				"such an `f` to a pair `f(,(a,b))` is ill-typed.",
			Suggestion: illTypedApplicationRepair,
		}
	} else {
		diag = &InputDiagnostic{
			Code:    CodeCorePanic,
			Message: fmt.Sprintf("internal error: %v", r),
			Suggestion: "this usually means a type mismatch in the input; " +
				"check that all function applications have the correct " +
				"number and types of arguments",
		}
	}
	if os.Getenv("PARSE_PANIC_TRACE") != "" {
		diag.Message += "\n" + string(debug.Stack())
	}
	return diag
}

// safeBuildTerm mirrors safeBuildProp: panics inside buildTerm (kernel
// type mismatches typically surface as panics) are converted to a
// structured diagnostic instead of crashing the engine.
func safeBuildTerm(fn func() (core.Term, error)) (core.Term, *InputDiagnostic, error) {
	var term core.Term
	var diag *InputDiagnostic
	var origErr error
	func() {
		defer func() {
			if r := recover(); r != nil {
				diag = panicToBuildDiagnostic(r)
			}
		}()
		var err error
		term, err = fn()
		if err != nil {
			origErr = err
			diag = &InputDiagnostic{Code: CodeValidation, Message: err.Error()}
		}
	}()
	return term, diag, origErr
}

// ParseTypeText parses a type expression (e.g. "A→bool", "var:Repty",
// "num") into a `core.HolType`.
func ParseTypeText(raw string) (core.HolType, error) {
	return ParseTypeTextInScope(raw, nil)
}

// ParseTypeTextInScope is ParseTypeText under a scope's type
// vocabulary: with scope.TypeResolver set, a type name no registered
// constant's type mentions is an error (typenames.go). The definition
// doors read a `Type:` row through here.
func ParseTypeTextInScope(raw string, scope *ParseScope) (core.HolType, error) {
	normalized, _ := NormalizeTextSymbols(raw)
	tokens, lexErr := lex(normalized)
	if lexErr != nil {
		return nil, fmt.Errorf("lex type: %s", lexErr.Message)
	}
	par := &parser{tokens: tokens}
	ast, perr := par.parseType()
	if perr != nil {
		return nil, fmt.Errorf("parse type: %s", perr.Message)
	}
	if par.pos < len(par.tokens) && par.tokens[par.pos].kind != tokEOF {
		return nil, fmt.Errorf("unexpected trailing tokens after type")
	}
	if errs := checkTypeNames(withoutBundleBinders(par.typeNames, scope), scopeTypeResolver(scope)); len(errs) > 0 {
		return nil, fmt.Errorf("type %q: %s", raw, errs[0].Message)
	}
	return resolveType(ast), nil
}

// MustParseProp parses raw via ParsePropText and returns the resulting
// Prop. Panics with a caller-located diagnostic if parsing fails. The
// panic message is prefixed with `<caller-file>:<line>:` via
// runtime.Caller, so the offending call site is reported even when the
// helper is buried inside a build function. Mirrors Go stdlib's
// MustCompile / template.Must idiom.
//
// Intended for: tests, debug code, and hand-written reference proofs
// where a parse failure is a programming bug (not user input). Real
// agent-facing entry points must keep using ParsePropText so the
// structured diagnostic envelope reaches the caller intact.
//
// Warnings (auto-fixes, etc.) on successful parses are silently
// dropped — callers that need them must use ParsePropText directly.
func MustParseProp(raw string) core.Prop {
	res := ParsePropText(raw)
	if len(res.Errors) == 0 && res.Prop != nil {
		return res.Prop
	}
	panic(formatMustParseFailure(raw, res, 2))
}

// formatMustParseFailure builds the panic string. Separate from
// MustParseProp so depth-adjustment is explicit when this gets reused
// by other Must* helpers (e.g. a future MustParseType).
func formatMustParseFailure(raw string, res ParseResult, callerSkip int) string {
	var b strings.Builder
	if _, file, line, ok := runtime.Caller(callerSkip); ok {
		fmt.Fprintf(&b, "%s:%d: ", file, line)
	}
	fmt.Fprintf(&b, "MustParseProp failed for %q", raw)
	if res.NormalizedInput != "" && res.NormalizedInput != raw {
		fmt.Fprintf(&b, " (normalized: %q)", res.NormalizedInput)
	}
	b.WriteString(":")
	for _, e := range res.Errors {
		fmt.Fprintf(&b, "\n  [%s @ %d] %s", e.Code, e.Position, e.Message)
		if e.Suggestion != "" {
			fmt.Fprintf(&b, " (suggestion: %s)", e.Suggestion)
		}
	}
	for _, w := range res.Warnings {
		fmt.Fprintf(&b, "\n  warning [%s @ %d] %s", w.Code, w.Position, w.Message)
	}
	return b.String()
}

// ---------------------------------------------------------------------------
// Panic recovery
// ---------------------------------------------------------------------------

func safeBuildProp(fn func() (core.Prop, error)) (core.Prop, *InputDiagnostic, error) {
	var prop core.Prop
	var diag *InputDiagnostic
	var origErr error
	func() {
		defer func() {
			if r := recover(); r != nil {
				diag = panicToBuildDiagnostic(r)
			}
		}()
		var err error
		prop, err = fn()
		if err != nil {
			origErr = err
			diag = &InputDiagnostic{Code: CodeValidation, Message: err.Error()}
		}
	}()
	return prop, diag, origErr
}

// ---------------------------------------------------------------------------
// Lexer
// ---------------------------------------------------------------------------
