// AST node types produced by the parser and consumed by the
// type-inference and lowering passes.

package dsl

import (
	"math/big"
	"slices"

	"github.com/euc-ai/xugo/core"
)

// astNode is a node in the parsed AST (before core.Term construction).
type astNode interface {
	nodePos() int
}

type astProp struct {
	decls   []astDecl // type declarations and hypotheses before ⊢
	body    astNode   // the conclusion expression
	pos     int
	hasTurn bool // whether ⊢ was explicit
}

func (a *astProp) nodePos() int { return a.pos }

// astDecl is either a type declaration (Name : Type) or a hypothesis (expr).
type astDecl struct {
	name    string  // non-empty for type declarations
	typeStr astType // non-nil for type declarations
	hyp     astNode // non-nil for hypothesis expressions
	pos     int
}

// astType represents a parsed type expression.
type astType interface {
	typePos() int
	// typeEnd is the byte offset just past the type's text in the
	// normalized input; a parenthesized type's span includes its
	// parens. With typePos it is the span a surface rewrite splices.
	typeEnd() int
	setSpan(start, end int)
}

type astTypeVar struct {
	name string
	pos  int
	end  int
}

func (a *astTypeVar) typePos() int           { return a.pos }
func (a *astTypeVar) typeEnd() int           { return a.end }
func (a *astTypeVar) setSpan(start, end int) { a.pos, a.end = start, end }

type astTypeFun struct {
	domain   astType
	codomain astType
	pos      int
	end      int
	// tuple marks a node the parser synthesized from the multi-argument
	// sugar `(A, B) → C`: its subterms have no contiguous text of their
	// own, so a surface rewrite must not splice inside it.
	tuple bool
}

func (a *astTypeFun) typePos() int           { return a.pos }
func (a *astTypeFun) typeEnd() int           { return a.end }
func (a *astTypeFun) setSpan(start, end int) { a.pos, a.end = start, end }

type astTypeNamed struct {
	name string
	args []astType
	pos  int
	end  int
}

func (a *astTypeNamed) typePos() int           { return a.pos }
func (a *astTypeNamed) typeEnd() int           { return a.end }
func (a *astTypeNamed) setSpan(start, end int) { a.pos, a.end = start, end }

// Expression AST nodes.

// typeAnnotBinding is one `V:T` (or `V=T`) pair inside a `⟨...⟩`
// polymorphic type-substitution annotation. `varName` is the abstract
// type-variable name from the const's meta (as the formatter's
// `ConstInstPairs` emits it); `ty` is the concrete instantiation.
type typeAnnotBinding struct {
	varName string
	ty      astType
	pos     int
}

// astVar is an identifier atom. When `typeAnnot` is non-nil the
// identifier carried a `⟨...⟩` polymorphic type-substitution suffix in
// the source (`universe⟨A:bool⟩`, `set_member⟨A:var:B⟩(...)`). buildVarTerm /
// buildApp resolve each binding's type via `resolveType` and instantiate
// the scope-const meta accordingly — the annotation wins over any
// fixed instance in scopeConsts, so the printer's formatConstTypeAnnotation
// output round-trips to the exact meta+instType it came from.
type astVar struct {
	name      string
	typeAnnot []typeAnnotBinding
	pos       int
}

func (a *astVar) nodePos() int { return a.pos }

// astAbbrev is an abbreviation `«Name»` as parsed: the name of an
// entry of the scope's table (abbreviation.go). The expansion pass
// replaces the node by the entry's own AST before any pass that
// resolves names runs; a node that survives to the build is a text
// read with no table, and the expansion names it.
type astAbbrev struct {
	name string
	// ties is the `⟨A:T⟩` suffix of a use, `«Name»⟨A:T⟩`: the type
	// the use takes for a letter the entry is written at, where nothing
	// else in the text fixes it (abbreviation.go, instantiateLetters).
	ties []typeAnnotBinding
	pos  int
}

func (a *astAbbrev) nodePos() int { return a.pos }

// astField is a record field on an expression, such as P(n).zero.
// The receiver's type selects the projection during lowering.
type astField struct {
	receiver astNode
	name     string
	pos      int
}

func (a *astField) nodePos() int { return a.pos }

type astApp struct {
	fun  astNode
	args []astNode
	pos  int
	// reduced marks the application of an abbreviation whose text is a
	// λ — «P»(m) for P ≔ λx. body — which reads as body[m/x], the term
	// the author abbreviated at the argument (abbreviation.go's
	// expandNode); the builder reduces the head redex the expansion
	// left (buildApp), through the kernel's capture-avoiding
	// substitution.
	reduced bool
	// letters are the type letters the abbreviation's λ-binders that
	// the arguments fill are written at and nothing else fixes: the
	// builder reads them off the built arguments before it builds the λ
	// (abbreviation.go instantiateLetters, build.go entryLetterTypes).
	letters []string
	// elided marks an application whose implicit prefix the chapter
	// spelling dropped (implicit.go's elide): the operator and big-op
	// folds fold a constant with implicit arguments only then — with
	// the prefix still spelled, its first arguments are the components,
	// not the operands.
	elided bool
	// stated marks an application a definition's equation states
	// (bundle.go's markStatements): the definiendum on the left of its
	// ⇔, and on the right each conjunct — through ∀ binders and ⇒
	// guards, as the registry reads a structure's layouts — that applies
	// a structure predicate. The folds that write a structure fact short
	// because a fact in scope gives its components (foldArgs, elide)
	// would read the body's statements as restating the left side, which
	// states nothing for them: a stated application is spelled in full.
	stated bool
	// dims counts the leading args the text wrote in the head's ⟨…⟩ —
	// `vec⟨n⟩(u)` is vec applied to n and u with dims 1 (dimension.go).
	// They stand first whatever the parentheses hold, so
	// `vec⟨n⟩(zero, u)` is [n, zero, u] here; the completion pass, which
	// decides whether the parentheses spell the implicit prefix, moves
	// them behind it and clears the count.
	dims int
	// dimsPlaced marks an application whose dimensions stand in the
	// constant's argument order by the DSL's own hand — the completion
	// pass's output, and the application a notation stands for, whose
	// subscript is the dimension. The pass refuses a dimension the text
	// wrote in parentheses, and reads neither of these as one.
	dimsPlaced bool
}

func (a *astApp) nodePos() int { return a.pos }

// appliedTo is the one application that a, applied to further arguments,
// reads as: a's head at a's arguments and then args — `f(x)(y, z)` is
// `f(x, y, z)`. What a's text wrote in its head's ⟨…⟩ is still what the
// suffix holds, `vec⟨n⟩(u)` at v being `vec⟨n⟩(u, v)`, so the count and
// the placement of a's dimensions are the application's.
func (a *astApp) appliedTo(args []astNode, pos int) *astApp {
	return &astApp{fun: a.fun, args: slices.Concat(a.args, args), pos: pos, dims: a.dims, dimsPlaced: a.dimsPlaced}
}

type astNumLit struct {
	value *big.Int
	pos   int
}

func (a *astNumLit) nodePos() int { return a.pos }

type astBinOp struct {
	op     string // "∧", "∨", "⇒", "⇔", "="
	left   astNode
	right  astNode
	pos    int
	parens bool // true if this node was explicitly parenthesized
}

func (a *astBinOp) nodePos() int { return a.pos }

// astCong is the congruence mixfix `x ≡ y (mod m)` — three operands,
// non-associative, at relational precedence. Lowered by buildCong
// (cong.go) to `nat_cong(x, y, m)` over num and to `int_cong(x, y, m)`
// over int, with the domain read off the operand types (a `&` coercion
// operand always means int here, since num is impossible for a coercion
// and real is not dispatched).
type astCong struct {
	left    astNode
	right   astNode
	modulus astNode
	pos     int
}

func (a *astCong) nodePos() int { return a.pos }

// astTendsAt is the limit mixfix `f ⟶ l (at c)` — three operands,
// non-associative, at relational precedence: the declared relation
// `⟶` with a trailing point clause, the copy of the congruence
// production's `(mod m)`. Where the clause is absent, `a ⟶ l` is the
// two-operand astBinOp the declared-operator path reads; with it, the
// build asks the constant declaring `⟶` at arity THREE (operator.go),
// so a chapter's `real_limit_at`-shaped constant owns the clause form the
// way the sequences chapter's owns the bare one.
type astTendsAt struct {
	fn    astNode
	limit astNode
	point astNode
	pos   int
}

func (a *astTendsAt) nodePos() int { return a.pos }

type astNotNode struct {
	body astNode
	pos  int
}

func (a *astNotNode) nodePos() int { return a.pos }

// astCoerce is the `&n` numeric-literal coercion prefix (num → real|int).
// Its target type is RESOLVED AT BUILD TIME by context, not fixed by the
// parser: the default is real_of_num (backward-compatible), but when an
// expected int type is threaded (buildExpected) or a sibling operand in a
// binary op is int-typed, it lowers to int_of_num instead. This is the
// type-directed `&` coercion — `x:int + &3` yields `int_of_num 3`, `&3`
// alone yields `real_of_num 3`.
type astCoerce struct {
	operand astNode
	pos     int
}

func (a *astCoerce) nodePos() int { return a.pos }

// astNeg is the unary-minus prefix `-x` (real_neg | int_neg). Unlike
// astCoerce its target is SELF-determined by the operand's type — real_neg
// for a real operand, int_neg for an int operand (num has no negation). It is
// the first negation surface in the DSL; the printer renders it back as a
// tight `-` prefix.
type astNeg struct {
	operand astNode
	pos     int
}

func (a *astNeg) nodePos() int { return a.pos }

// astQuantNode is a quantifier binder `∀x:T. body` / `∃x:T. body` /
// `∃!x:T. body` / `εx:T. body`. The body must be boolean (except for
// `ε`, whose result type is the binder type).
//
// `varType` is nil for the untyped form `∀x. body`, mirroring the
// untyped lambda. The first collect pass that walks an untyped
// QuantNode stashes its discovery on `resolvedVarType` so later passes
// and buildQuant can read it without re-walking — same protocol as
// astAbsNode. This is what lets an agent write `∃y. ẋ = g(y) ∧ set_member(y, s)`
// when `y`'s required type is a goal-local type-variable they have no
// concrete spelling for (e.g. `?71143`).
type astQuantNode struct {
	quantifier      string // "∀", "∃", "∃!", or "ε"
	varName         string
	varType         astType
	body            astNode
	resolvedVarType core.HolType // set lazily for untyped binders (varType==nil)
	pos             int
	// binds are the names a BUNDLE BINDER the chapter spelling folded
	// binds besides varName — the structure's other components, which
	// the expansion mints — so that the folds after it read them as
	// bound (bundle.go, foldBinderAt).
	binds []string
}

func (a *astQuantNode) nodePos() int { return a.pos }

// boundNames is every name the binder binds: its own, and a folded
// bundle binder's components.
func (a *astQuantNode) boundNames() []string { return append([]string{a.varName}, a.binds...) }

// astAbsNode is a bare lambda binder `λx:T. body`. Distinct from
// astQuantNode because lambdas do not wrap their body with a
// quantifier const and the body need not be boolean — `λx:num. x+1`
// is num→num, valid as a function argument (the dominant use case:
// `set_comprehension(λv:T. ...)`).
//
// `varType` is nil for the untyped form `λx. body`; the binder's type
// is then inferred (in order): the codomain peeled off an enclosing
// `expected` function type, then env.inferred[varName] populated by
// the body's collect-pass walk, then env.guesses[varName], then a
// fresh type variable `var:_<varName>`. The first collect pass that
// walks an untyped AbsNode stashes its discovery on `resolvedVarType`
// so the later passes and buildAbs can read it without re-walking.
type astAbsNode struct {
	varName         string
	varType         astType
	body            astNode
	resolvedVarType core.HolType // set lazily for untyped binders (varType==nil)
	pos             int
}

func (a *astAbsNode) nodePos() int { return a.pos }

// boundNames is the one name the abstraction binds.
func (a *astAbsNode) boundNames() []string { return []string{a.varName} }

// astBigOp is a big-operator binder `Σ_{i<m} body` / `Σ_{i∈s} body`
// (bigop.go): the symbol, the index it binds, the range — `<` with the
// bound the index runs below, or `∈` with the set it runs over — and
// the body. The index's type is the range's (the bound's own type
// under `<`, the set's element type under `∈`), so the binder carries
// no annotation. Lowered at build time, once the body's type is known,
// to the corpus's sum at that type applied to the range set and
// `λi. body`.
type astBigOp struct {
	symbol string // "Σ" or "Π"
	binder string
	rel    string // "<" or "∈"
	bound  astNode
	body   astNode
	pos    int
}

func (a *astBigOp) nodePos() int { return a.pos }

type astConst struct {
	name string // "⊤" or "⊥"
	pos  int
}

func (a *astConst) nodePos() int { return a.pos }

// astPat is one node of a λ-pattern tree (`λ(u, x). body` /
// `λ((a, b), c). body`): either a leaf binder — name plus optional
// explicit type — or a pair node with two children. `resolvedTy` is the
// collect-pass stash for untyped leaves, same protocol as
// astAbsNode.resolvedVarType.
type astPat struct {
	name        string  // leaf binder name; "" for pair nodes
	ty          astType // leaf: nil = untyped, inferred at build time
	resolvedTy  core.HolType
	left, right *astPat // pair-node children; nil on leaves
	pos         int
}

func (a *astPat) isLeaf() bool { return a.left == nil }

// leaves appends the pattern's leaf nodes in order to dst.
func (a *astPat) leaves(dst []*astPat) []*astPat {
	if a.isLeaf() {
		return append(dst, a)
	}
	return a.right.leaves(a.left.leaves(dst))
}

// astPatternAbs is a pair-pattern lambda `λ(u:T₁, x:T₂). body` — the
// pattern abstraction surface. buildPatternAbs lowers it to the
// canonical pattern_abstraction encoding
//
//	pattern_abstraction(λf. ∀u x. f((u, x)) = body)
//
// with a fresh internal binder f (chosen to avoid every name in the
// built body), so the shadow capture that motivated the printer's
// matchPatternLambda sugar can never re-enter through the parse
// direction. Distinct from the paren-grouped multi-binder form
// `λ(x:T) (y:T). body`, which is plain currying — the pattern form is
// recognized by the `,` inside one paren group.
type astPatternAbs struct {
	pat  *astPat
	body astNode
	pos  int
}

func (a *astPatternAbs) nodePos() int { return a.pos }

// ---------------------------------------------------------------------------
// Parser (recursive descent)
// ---------------------------------------------------------------------------
