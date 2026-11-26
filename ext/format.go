package ext

import (
	"cmp"
	"fmt"
	"slices"
	"strings"
	"unicode"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
)

// FormatType is display-only. Lossless reconstruction uses proto
// (`HolPropProto` bytes); nothing parses this string back.

// ConstInstPairs returns the type substitutions applied to a const term's
// abstract type, as a sorted slice of (typeVarName, formattedType) pairs.
// Returns nil if the const has no instantiation metadata (i.e., it is used at
// its abstract type, or its meta has no type variables).
//
// The disambiguating printer (formatConstTypeAnnotation below) reads it.
func ConstInstPairs(c ConstTerm) [][2]string {
	inst := c.TypeSubsts()
	if len(inst) == 0 {
		return nil
	}
	pairs := make([][2]string, len(inst))
	for i, s := range inst {
		pairs[i] = [2]string{string(s.VarType.Name()), FormatType(s.HolType)}
	}
	slices.SortFunc(pairs, func(a, b [2]string) int {
		return cmp.Compare(a[0], b[0])
	})
	return pairs
}

// collectTypeVarNames returns the set of type-variable names occurring in t.
// Used by formatConstTypeAnnotation to synthesize explicit identity pairs
// for an abstract-instance occurrence of a conflicted polymorphic const.
// (ext/dsl has its own copy for annotation validation — the two walk the
// same two type shapes and must stay in sync.)
func collectTypeVarNames(t HolType) map[string]bool {
	seen := map[string]bool{}
	var walk func(HolType)
	walk = func(t HolType) {
		switch x := t.(type) {
		case VarType:
			seen[string(x.Name())] = true
		case CompositeType:
			for i := 0; i < x.Meta().Arity(); i++ {
				walk(x.SubType(i))
			}
		}
	}
	walk(t)
	return seen
}

// collectConstConflicts walks a term and returns the set of const names whose
// occurrences in the term carry more than one distinct holType. These are the
// constants that the default printer would render identically despite being
// structurally different terms — e.g. finite(universe:(A#B)->bool) and
// finite(universe:A->bool) both print as finite(universe).
//
// The printer contract we want to preserve: if two terms produce identical
// output strings, they must be AlphaEquals. Annotating conflicted consts with
// their type instantiation restores this invariant.
func collectConstConflicts(t Term) map[TermName]bool {
	return ConstConflictSet(t)
}

// ConstConflictSet is collectConstConflicts generalized to several terms
// sharing one output scope. A prop's hypotheses and conclusion are parsed
// against a SINGLE symbol scope, so a const name used at different type
// instances in two different terms of the same prop is just as ambiguous
// as one conflicted within a single term — the conflict set (and hence
// the annotation decision) must be computed across all of them. Used by
// prop.FormatPropForParser with FormatTermForParserInConflicts.
func ConstConflictSet(terms ...Term) map[TermName]bool {
	byName := map[TermName][]HolType{}
	undetermined := map[TermName]bool{}
	// The GLOBAL recoverability criterion — the round-trip needs more
	// than prop-local conflict detection: an occurrence whose instance
	// the printed term cannot re-derive (a lone `finite(𝕌)`, lambda's
	// dimension letter, a zero-extension's result width) must annotate
	// even when its name appears at only ONE instance in the prop — an
	// un-annotated render re-parses at whatever instance the scope
	// offers, silently a different theorem. collectUnrecoverable mirrors
	// the parser's two directions of inference and records the names
	// whose occurrences escape both.
	for _, t := range terms {
		collectUnrecoverable(t, false, undetermined)
	}
	var walk func(Term, int)
	walk = func(t Term, argsApplied int) {
		switch t := t.Core().(type) {
		case ConstTerm:
			if t.Name() == utils.EqStr ||
				t.Name() == utils.HilbertStr ||
				t.Name() == utils.ForAllStr ||
				t.Name() == utils.ExistsStr ||
				t.Name() == utils.UniqueStr ||
				t.Name() == CommaConstMeta.Name() ||
				isArgDeterminedSetOp(t.Name()) {
				// The pair constructor `,` is exempt for the same reason
				// as `=`: its instance is fully determined by its argument
				// types, so the infix `(a, b)` render round-trips without a
				// type annotation. Two pairs printing identically forces
				// their components to print identically, hence (inductively)
				// be alpha-equal, hence share the `,` instance — the printer
				// contract holds with no annotation. Without this exemption a
				// nested heterogeneous tuple `(a, (b, c))` (outer and inner
				// `,` at different instances) would fall back to the noisy
				// annotated prefix form.
				//
				// The set-theory ops with a lossless render — the six binary
				// infix (∈ ⊆ ⊊ ∪ ∩ ∖) and the two unary big-op prefixes
				// (⋃ ⋂) — join the exemption by the SAME argument: element
				// type A is fully determined by an operand written out
				// verbatim (set_member: A→(A→bool)→bool; subset/union/…: their
				// (A→bool) operands; big_union/big_intersection: their ((A→bool)→bool)
				// operand), and the parser re-infers A from that operand
				// (buildBinOp/unary dispatch → buildAppViaMeta), so the render
				// round-trips without the `⟨A:T⟩` annotation. This is what lets
				// a mixed-instance term like set_basic.InImage's goal —
				// `(y ∈ image(f,s)) ⇔ ∃x. (x ∈ s) ∧ …` (set_member at both B and A) —
				// print with `∈` instead of falling back to `set_member⟨A:B⟩(...)`.
				// See isArgDeterminedSetOp for the full list and rationale.
				//
				// NOT exempt (they keep the `⟨A:T⟩` fallback under conflict):
				// the NULLARY consts (∅, 𝕌 : A→bool), where A is determined by
				// no operand; and set_comprehension/comprehension_spec, whose `{x|φ}` set-builder
				// elides the binder that carries A, so the shorthand can hide
				// the instance. An un-annotated occurrence of either would
				// resolve against the scope's single fixed instance and could
				// mis-type.
				return
			}
			existing := byName[t.Name()]
			for _, ht := range existing {
				if ht.Equals(t.Type()) {
					return
				}
			}
			byName[t.Name()] = append(existing, t.Type())
		case AppliedTerm:
			walk(t.Fun(), argsApplied+1)
			walk(t.Arg(), 0)
		case AbsTerm:
			walk(t.Body(), 0)
		}
	}
	for _, t := range terms {
		walk(t, 0)
	}

	var conflicts map[TermName]bool
	for name, types := range byName {
		if len(types) > 1 {
			if conflicts == nil {
				conflicts = map[TermName]bool{}
			}
			conflicts[name] = true
		}
	}
	for name := range undetermined {
		if conflicts == nil {
			conflicts = map[TermName]bool{}
		}
		conflicts[name] = true
	}
	return conflicts
}

// recoverability mirrors the parser's two directions of type inference
// over a printed term and records the names of polymorphic-const
// occurrences whose instance NEITHER direction can re-derive:
//
//   - bottom-up: a head's letter is grounded when it occurs in the
//     abstract domain of an argument position whose argument is itself
//     recoverable (buildAppViaMeta unifies domains against arg types);
//   - top-down: once a head's instance is grounded (or imposed from
//     above), its remaining arguments have their types imposed
//     (buildArgsAgainstFunType threads domains into arguments, λ
//     bodies included via buildExpected).
//
// Variables print their types verbatim (binders and decl preludes), so
// they always ground; a lone `finite(𝕌)` grounds nothing in either
// direction and both names are recorded; `insert(1, ∅)` grounds
// insert's letter through the numeral and then imposes ∅'s instance,
// so the enumeration sugar stays annotation-free. selfOK is memoized
// by node (shared-DAG hits included), making the analysis linear.
type recoverability struct {
	out      map[TermName]bool
	selfMemo map[Term]bool
}

func collectUnrecoverable(t Term, imposed bool, out map[TermName]bool) {
	r := &recoverability{out: out, selfMemo: map[Term]bool{}}
	r.record(t, imposed)
}

// spine flattens an application into head + args.
func spine(t Term) (Term, []Term) {
	var args []Term
	head := t
	for {
		app, ok := head.Core().(AppliedTerm)
		if !ok {
			break
		}
		args = append(append([]Term{}, app.Arg()), args...)
		head = app.Fun()
	}
	return head, args
}

// headMetaLetters returns the head's poly meta letters (nil when the
// head is not a polymorphic const), its abstract domain types — one
// per applied argument position — and the abstract RESULT remainder
// after those arguments.
func headMetaLetters(head Term, nArgs int) (map[string]bool, []HolType, HolType) {
	hc, ok := head.Core().(ConstTerm)
	if !ok || hc.Meta().IsZero() {
		return nil, nil, nil
	}
	letters := collectTypeVarNames(hc.Meta().AbsType())
	if len(letters) == 0 {
		return nil, nil, nil
	}
	domains := make([]HolType, 0, nArgs)
	at := hc.Meta().AbsType()
	for i := 0; i < nArgs && IsFunType(at); i++ {
		ct := at.(CompositeType)
		domains = append(domains, ct.SubType(0))
		at = ct.SubType(1)
	}
	return letters, domains, at
}

// selfOK reports whether t's TYPE is recoverable from its printed form
// alone — no imposition from an enclosing context.
func (r *recoverability) selfOK(t Term) bool {
	if v, ok := r.selfMemo[t]; ok {
		return v
	}
	v := r.computeSelfOK(t)
	r.selfMemo[t] = v
	return v
}

func (r *recoverability) computeSelfOK(t Term) bool {
	switch x := t.Core().(type) {
	case VarTerm:
		return true
	case ConstTerm:
		return x.Meta().IsZero() || len(collectTypeVarNames(x.Meta().AbsType())) == 0
	case AbsTerm:
		// The binder type is printed; the abstraction's type is known
		// exactly when the body's is.
		return r.selfOK(x.Body())
	case AppliedTerm:
		head, args := spine(t)
		letters, domains, _ := headMetaLetters(head, len(args))
		if letters == nil {
			// Mono const, variable, or λ head: the head's type is known
			// on its own, so the application's type is too.
			if _, isConst := head.Core().(ConstTerm); !isConst {
				return r.selfOK(head)
			}
			return true
		}
		grounded := map[string]bool{}
		for i, a := range args {
			if i < len(domains) && r.selfOK(a) {
				for name := range collectTypeVarNames(domains[i]) {
					grounded[name] = true
				}
			}
		}
		for name := range letters {
			if !grounded[name] {
				return false
			}
		}
		return true
	}
	return true
}

// record walks t once, using memoized selfOK verdicts for grounding,
// and records every occurrence neither grounded nor imposed. selfOK
// speaks only to a node's own TYPE — a bool-typed equality is selfOK
// while `card(𝕌)` rots inside it — so the walk descends
// everywhere.
func (r *recoverability) record(t Term, imposed bool) {
	switch x := t.Core().(type) {
	case ConstTerm:
		if !imposed && !annotationExempt(x.Name()) {
			r.out[x.Name()] = true
		}
	case AbsTerm:
		// The parser threads an imposed abstraction type into the body
		// (buildExpected on lambdas), so imposition survives the binder.
		r.record(x.Body(), imposed)
	case AppliedTerm:
		head, args := spine(t)
		letters, domains, result := headMetaLetters(head, len(args))
		if letters == nil {
			if _, isConst := head.Core().(ConstTerm); !isConst {
				r.record(head, false)
			}
			for _, a := range args {
				// A mono/var/λ head's domains are known on their own, so
				// each argument's TYPE is imposed (what that recovers is
				// bounded by the argument's own result letters below).
				r.record(a, true)
			}
			return
		}
		// Bottom-up: a selfOK argument grounds its abstract domain's
		// letters — order-free, buildAppViaMeta unifies against all
		// argument types at once.
		grounded := map[string]bool{}
		selfGrounded := make([]bool, len(args))
		for i, a := range args {
			if i < len(domains) && r.selfOK(a) {
				selfGrounded[i] = true
				for name := range collectTypeVarNames(domains[i]) {
					grounded[name] = true
				}
			}
		}
		// Top-down imposition does NOT reach a poly-const-headed
		// application: the meta build path drops the caller's expected
		// type (buildApp's scopeConstMetas branch unifies from the
		// argument types alone), so a result-only letter —
		// finite_index's dimension under `Q(finite_index(i))`, a bare
		// `word(…)` mask under word_and — is unrecoverable however
		// well-typed the context. Only LEAF constants receive an
		// imposed type (buildExpected stashes it for buildVarTerm).
		_ = result
		headOK := true
		for name := range letters {
			if !grounded[name] {
				headOK = false
				break
			}
		}
		if !headOK && !annotationExempt(nameOfConstHead(head)) {
			// The logical heads and the lossless-render ops never carry
			// the annotation themselves — their letters reach the
			// reparse through operands, which record their OWN failures
			// (`∅ = 𝕌` annotates ∅ and 𝕌, not `=`).
			r.out[nameOfConstHead(head)] = true
		}
		// Argument imposition is ORDERED (buildArgsAgainstFunType
		// threads domains left to right: an argument is pinned only by
		// what earlier arguments and the head's own recovery already
		// ground) — and `=` does not impose into built operands at all
		// except the bare-atom retry (buildEqOperands), so under an
		// equality only a bare-leaf operand counts as imposed.
		eqHead := nameOfConstHead(head) == utils.EqStr
		// NOTE: the parent-imposed result letters are deliberately NOT
		// seeded here. They make the head's final instance determined
		// (headOK above), but the arguments were already built
		// left-to-right by then — a bare word_INT_MIN in argument one
		// is not retro-typed by a unification that happens after it,
		// so only earlier SELF-grounded siblings count for imposition.
		groundedSoFar := map[string]bool{}
		for i, a := range args {
			if selfGrounded[i] {
				for name := range collectTypeVarNames(domains[i]) {
					groundedSoFar[name] = true
				}
				// Its own type self-derives; the interior still needs
				// the walk (a mono head can hide an unrecoverable
				// subterm — suc(card(∅))).
				r.record(a, true)
				continue
			}
			argImposed := false
			if i < len(domains) {
				argImposed = true
				for name := range collectTypeVarNames(domains[i]) {
					if !groundedSoFar[name] {
						argImposed = false
						break
					}
				}
			}
			if eqHead {
				_, isLeafConst := a.Core().(ConstTerm)
				argImposed = argImposed && isLeafConst
			}
			r.record(a, argImposed)
		}
	}
}

func nameOfConstHead(head Term) TermName {
	if hc, ok := head.Core().(ConstTerm); ok {
		return hc.Name()
	}
	return ""
}

// isArgDeterminedSetOp reports whether name is a set-theory operator whose
// polymorphic instance is fully determined by its operand types AND whose
// notation writes those operands out verbatim (a "lossless" render). Such a
// const is exempt from the conflict-annotation pass (see the exemption block
// in ConstConflictSet): its render round-trips without a `⟨A:T⟩` suffix
// because the parser re-infers the element type from the operands. The names
// match the addConstFmt registrations in initConstFmts and the setOperator /
// unarySetOperator dispatch in ext/dsl/setops.go.
//
//   - The six binary infix ops (∈ ⊆ ⊊ ∪ ∩ ∖): element type A appears in an
//     operand written verbatim, e.g. `x ∈ s` fixes A = type(x).
//   - The two unary big-op prefixes (⋃ ⋂): big_union/big_intersection take one operand of
//     type ((A→bool)→bool) rendered in full, so `⋃s` fixes A from type(s).
//     They introduce NO fresh binder (unlike set_comprehension's `{x|φ}` sugar), so the
//     render is lossless the same way the infix ops are.
//
// Excluded, and why they must keep the `⟨A:T⟩` fallback under a conflict:
//   - Nullary empty_set/universe (∅ 𝕌): no operand determines A.
//   - set_comprehension/comprehension_spec: the `{x|φ}` set-builder elides the λ-binder that carries
//     A (re-synthesized at parse), so the shorthand can hide the instance —
//     its operand is not written verbatim the way ⋃'s is.
func isArgDeterminedSetOp(name TermName) bool {
	switch name {
	case "set_member", "subset", "proper_subset", "union", "intersection", "set_difference", "big_union", "big_intersection":
		return true
	}
	return false
}

// matchesSetMember reads `set_member(x, s)`, the application the `∈`
// infix renders, as its element and its set.
func matchesSetMember(t Term) (Term, Term, bool) {
	c, args := MatchesApply(t)
	if len(args) != 2 {
		return nil, nil, false
	}
	if c, ok := c.AsConst(); ok && c.Name() == "set_member" {
		return args[0], args[1], true
	}
	return nil, nil, false
}

// annotationExempt names the consts that never carry the `⟨⟩` suffix
// themselves: the logical heads (binder/operand types are printed
// verbatim) and the lossless-render ops (the `,` pair and the set-op
// notation, whose operands are written out in full). They still
// participate in the recoverability computation — only the RECORDING
// is skipped, so their operands annotate instead.
func annotationExempt(name TermName) bool {
	return name == utils.EqStr ||
		name == utils.HilbertStr ||
		name == utils.ForAllStr ||
		name == utils.ExistsStr ||
		name == utils.UniqueStr ||
		name == CommaConstMeta.Name() ||
		isArgDeterminedSetOp(name)
}

// formatConstTypeAnnotation produces a disambiguating suffix for a polymorphic
// const term, mirroring the JSON marshaler's convention exactly:
//
//   - Non-empty TypeSubsts → ⟨A=foo,B=bar⟩ (plain) or
//     _{\langle A=foo,B=bar \rangle} (latex), where the pairs are the same ones
//     ConstInstPairs returns, and also the same ones the JSON inst map carries.
//   - Empty TypeSubsts → "" (no annotation).
//
// The empty-TypeSubsts case corresponds to either a monomorphic const or a
// polymorphic const used at its ABSTRACT type. A monomorphic const can never
// be in a conflict set (it has exactly one type), so it keeps the bare
// render. An abstract-instance occurrence inside a conflict set, however,
// gets EXPLICIT IDENTITY pairs (`card⟨A:var:A⟩`): leaving it bare makes
// the text ambiguous for the parser — an un-annotated occurrence of a
// conflicted name resolves against the scope's single fixed instance, which
// may be a DIFFERENT instantiation, silently mis-typing the term. The
// identity annotation pins the
// abstract instance the same way a concrete annotation pins its
// substitution, restoring the printer contract (identical output ⇒
// AlphaEquals) and the print→parse round-trip. JSON is unaffected — it
// still omits `inst` for abstract instances (ConstInstPairs is unchanged).
func formatConstTypeAnnotation(c ConstTerm, latex bool) string {
	// An annotation is COMPLETE or it is a lie. ConstInstPairs reports
	// only the letters whose instance DIFFERS from the abstract type, so
	// a letter sitting at its identity is omitted — and under
	// FreshenMetaLetters (which every real door sets: the registry's
	// statement door, emit, the session, prover/proof, the CLI) an
	// omitted letter parses back as a FRESH occurrence-local one, not as
	// the author's same-named letter. A partial annotation therefore
	// unties exactly what an annotation is written to tie:
	// `real_sum⟨A:var:A⟩ = iterated_op⟨B:real⟩(real_add)` re-parses with two
	// different A's, because `iterate`'s own A was left to a freshened
	// letter while `sum`'s was pinned. The author's source spells the
	// complete tie (`iterated_op⟨A:A, B:real⟩`); the printer must too.
	// So every one of the meta's type variables is listed, identities
	// included — which also subsumes the abstract-instance case, where
	// EVERY pair is an identity (`card⟨A:var:A⟩`).
	pairs := ConstInstPairs(c)
	covered := map[string]bool{}
	for _, p := range pairs {
		covered[p[0]] = true
	}
	for name := range collectTypeVarNames(c.Meta().AbsType()) {
		if !covered[name] {
			pairs = append(pairs, [2]string{name, "var:" + name})
		}
	}
	slices.SortFunc(pairs, func(a, b [2]string) int {
		return cmp.Compare(a[0], b[0])
	})
	if len(pairs) == 0 {
		return ""
	}
	parts := make([]string, len(pairs))
	for i, p := range pairs {
		parts[i] = fmt.Sprintf("%s:%s", p[0], p[1])
	}
	content := strings.Join(parts, ",")
	if latex {
		return fmt.Sprintf("_{\\langle %s \\rangle}", content)
	}
	return "⟨" + content + "⟩"
}

var basicConstFmts = map[TermName]_ConstTermFormat{
	utils.TrueStr:    {Latex: "\\top"},
	utils.FalseStr:   {Latex: "\\bot"},
	utils.NegStr:     {Latex: "\\neg"},
	utils.HilbertStr: {Latex: "\\varepsilon", IsQuantifier: true},
	utils.ForAllStr:  {Latex: "\\forall", IsQuantifier: true},
	utils.ExistsStr:  {Latex: "\\exists", IsQuantifier: true},
	utils.UniqueStr:  {Latex: "\\exists!", IsQuantifier: true},
	utils.EqStr:      defaultInfix("=", "="),
	utils.IffStr:     defaultInfix(utils.IffStr, "\\iff"),
	utils.NeqStr:     defaultInfix(utils.NeqStr, "\\neq"),
	utils.XorStr:     defaultInfix(utils.XorStr, "\\oplus"),
	utils.AndStr:     defaultInfix("∧", "\\wedge"),
	utils.OrStr:      defaultInfix("∨", "\\vee"),
	utils.ImplyStr:   defaultInfix("⇒", "\\Rightarrow"),
}

var specialCharacters = map[string]string{
	utils.F_HOOK:     "\\mathsf{f}",
	utils.H_STROKE:   "\\hbar",
	utils.Z_STROKE:   "\\dot{z}",
	utils.X_DOT:      "\\dot{x}",
	utils.AlphaStr:   "\\alpha",
	utils.PrimeStr:   "'",
	utils.PercentStr: "\\%",
}

var extraConstFmts = map[TermName]_ConstTermFormat{}

func addConstFmt(n TermName, f _ConstTermFormat) { extraConstFmts[n] = f }

// FormatTypeForParser is FormatType in parser-safe mode. Differs only
// for function types of curry-depth ≥ 3: FormatType collapses them
// into tuple form `((A, B) → C)` for human readability, but the parser
// only grammars right-associative `→`, so parser mode emits the
// nested form `(A → (B → C))` instead. Other shapes match FormatType.
func FormatTypeForParser(t HolType) string {
	switch t := t.(type) {
	case VarType:
		return "var:" + string(t.Name())
	case CompositeType:
		// Fun is the only meta where FormatType deviates from the
		// "name(<subs>)" template — always render binary, recurse.
		if t.Meta().Equals(core.MetaTypeFun()) {
			return fmt.Sprintf("(%s %s %s)",
				FormatTypeForParser(t.SubType(0)),
				utils.FunStr,
				FormatTypeForParser(t.SubType(1)))
		}
		if t.Meta().Arity() == 0 {
			return string(t.Meta().Name())
		}
		syntax := string(t.Meta().Name()) + "("
		for i := range t.Meta().Arity() {
			syntax += FormatTypeForParser(t.SubType(i))
			if i+1 < t.Meta().Arity() {
				syntax += ", "
			}
		}
		syntax += ")"
		return syntax
	}
	panic("Invalid type.")
}

// FormatType renders a HolType as a string for display and generated JSON.
// `VarType` is encoded as `var:<name>`; arity-0 `CompositeType` is bare.
func FormatType(t HolType) string {
	switch t := t.(type) {
	case VarType:
		return "var:" + string(t.Name())
	case CompositeType:
		if types := MatchesFun(t); len(types) > 1 {
			formattedTypes := make([]string, len(types))
			for i, s := range types {
				formattedTypes[i] = FormatType(s)
			}
			if len(formattedTypes) == 2 {
				return fmt.Sprintf("(%s %s %s)",
					FormatType(t.SubType(0)), utils.FunStr, FormatType(t.SubType(1)))
			}
			return fmt.Sprintf("((%s) %s %s)",
				strings.Join(utils.BeforeLast(formattedTypes), ", "),
				utils.FunStr,
				utils.Last(formattedTypes))
		}
		syntax := string(t.Meta().Name())
		if t.Meta().Arity() > 0 {
			syntax += "("
			for i := range t.Meta().Arity() {
				syntax += FormatType(t.SubType(i))
				if i+1 < t.Meta().Arity() {
					syntax += ","
				}
			}
			syntax += ")"
		}
		return syntax
	}
	panic("Invalid type.")
}

type FmtTemplate struct {
	Arity       int
	FmtCallback func(...string) string
}

type _ConstTermFormat struct {
	Format       string
	Latex        string
	IsQuantifier bool
	Invisible    bool
	FmtTempl     FmtTemplate
	LatexTempl   FmtTemplate
}

func defaultInfix(fmtStr, latexStr string) _ConstTermFormat {
	return _ConstTermFormat{
		Format: fmtStr,
		Latex:  latexStr,
		FmtTempl: FmtTemplate{
			2,
			func(s ...string) string {
				return fmt.Sprintf("%s %s %s", s[0], fmtStr, s[1])
			}},
		LatexTempl: FmtTemplate{
			2,
			func(s ...string) string {
				return fmt.Sprintf("%s%s%s", s[0], latexStr, s[1])
			}},
	}
}

func formatVar(v VarTerm, latex bool) string {
	n := string(v.Name())
	if latex {
		for k, v := range specialCharacters {
			n = strings.ReplaceAll(n, k, v)
		}
		return fmt.Sprintf("{%s}", n)
	}
	return utils.FormatSubscript(n)
}

func formatConst(c ConstTerm, latex bool, conflicts map[TermName]bool) string {
	base := formatConstBase(c, latex)
	if conflicts != nil && conflicts[c.Name()] {
		base += formatConstTypeAnnotation(c, latex)
	}
	return base
}

// formatConstBase renders a const term without any type annotation — the
// original pre-disambiguation output. formatConst wraps this and appends an
// annotation when the const name is in the caller's conflict set.
//
// All registered const-name shortcuts (`_0`→"0", infix `+`, `≤`, etc.)
// survive the parser round-trip: the parser handles the operators
// natively, and bare "0" lowers to the `_0` const so printing `_0` as
// "0" reparses alpha-equal.
func formatConstBase(c ConstTerm, latex bool) string {
	if f, ok := basicConstFmts[c.Name()]; ok {
		if c.Equals(core.IFF()) {
			f = basicConstFmts[utils.IffStr]
			if latex {
				return f.Latex
			}
			return f.Format
		}
		if latex && f.Latex != "" {
			return f.Latex
		}
		if !latex && f.Format != "" {
			return f.Format
		}
	}
	if f, ok := extraConstFmts[c.Name()]; ok {
		if latex && f.Latex != "" {
			return fmt.Sprintf("{%s}", f.Latex)
		}
		if !latex && f.Format != "" {
			// Overloaded OPERATOR aliases (real_add/int_mul/… render as
			// "+"/"*"/… via their infix/prefix FmtTempl) apply only in the
			// template positions, which don't go through this function. A
			// BARE occurrence (first-class value position:
			// `monoidal_op(real_add)`, or the head of a partial application)
			// must print the const's own identifier instead: the bare symbol
			// re-parses to the nat const of that name (e.g. `+`), so
			// `monoidal_op(+)` for real_add would collide with nat_sum.MonoidalNatAdd's
			// num statement — violating the printer contract (identical
			// output ⇒ AlphaEquals) and breaking the text round-trip.
			// Scope of the rule:
			//   - only templated entries (FmtTempl.Arity > 0): a plain
			//     display rename with no template (e.g. `_0`→"0") keeps its
			//     alias everywhere — "0" re-lowers to `_0` via the numeral
			//     literal path, so it round-trips;
			//   - only identifier-shaped names: consts whose NAME is itself
			//     the symbol (nat's "+", "*", "<=", …) keep the alias —
			//     symbol and identity coincide, and the parser's
			//     bare-operator atom resolves them.
			if f.FmtTempl.Arity > 0 && f.Format != string(c.Name()) &&
				isLexerIdentName(string(c.Name())) {
				return string(c.Name())
			}
			return f.Format
		}
	}
	if latex {
		return fmt.Sprintf("\\textsf{%s}", c.Name())
	}
	return string(c.Name())
}

// isLexerIdentName reports whether name tokenizes as a single identifier
// in the text DSL's lexer (letters/_ start; letters/digits/_/'/% continue)
// — i.e. whether a bare occurrence of the name in printed text re-parses
// as that name. Symbolic const names ("+", "<=", "..") fail this and keep
// their display alias. Mirrors ext/dsl's isIdentStart/isIdentChar; the two
// must stay in sync (dsl imports ext, so the rule can't live there).
func isLexerIdentName(name string) bool {
	if name == "" {
		return false
	}
	for i, r := range name {
		if i == 0 {
			if !(unicode.IsLetter(r) || r == '_') {
				return false
			}
			continue
		}
		if !(unicode.IsLetter(r) || unicode.IsDigit(r) || r == '_' || r == '\'' || r == '%') {
			return false
		}
	}
	return true
}

func isConstQuantifier(c ConstTerm) bool {
	if f, ok := basicConstFmts[c.Name()]; ok && f.IsQuantifier {
		return true
	}
	if f, ok := extraConstFmts[c.Name()]; ok && f.IsQuantifier {
		return true
	}

	return false
}

func isConstInvisible(c ConstTerm) bool {
	if f, ok := basicConstFmts[c.Name()]; ok && f.Invisible {
		return true
	}
	if f, ok := extraConstFmts[c.Name()]; ok && f.Invisible {
		return true
	}
	return false
}

func shouldBeBracketed(t Term, binderTypes binderTypeMode) bool {
	switch t := t.Core().(type) {
	case AppliedTerm:
		// A pair-pattern lambda prints as `λ(x, y). body` in every
		// profile but the name-faithful one: a λ in the text, bracketed
		// where a λ is — unbracketed on the left of an infix, its body
		// would read on through the operator.
		if binderTypes != binderAllNameFaithful {
			if _, _, ok := matchPatternLambda(t); ok {
				return true
			}
		}
		if t, ok := t.AsAppliedTerm(); ok {
			if tFun, ok := t.Fun().AsConst(); ok {
				if isConstQuantifier(tFun) {
					return true
				}
			}
		}
		if _t := MatchesNOT(t); _t != nil {
			if _, _, ok := MatchesEQ(_t); ok {
				// because we use "≠" in this case.
				return true
			}
			if _, _, ok := matchesSetMember(_t); ok {
				// and "∉" in this one.
				return true
			}
		}
		// Template-rendered applications need brackets only for the INFIX
		// templates (arity ≥ 2); an arity-1 template is a tight prefix (e.g.
		// real_of_num's `&`) whose output never needs parent parens.
		if c, args := MatchesApply(t); len(args) > 1 {
			if c, ok := c.AsConst(); ok {
				if f, ok := basicConstFmts[c.Name()]; ok &&
					f.FmtTempl.Arity == len(args) {
					return true
				}
				if f, ok := extraConstFmts[c.Name()]; ok &&
					f.FmtTempl.Arity == len(args) {
					return true
				}
			}
		}
		// The congruence mixfix `x ≡ y (mod m)` renders at relational
		// looseness, so argument/operand positions bracket it like any
		// infix-templated application.
		if _, _, _, ok := matchCongApp(t); ok {
			return true
		}
	case AbsTerm:
		return true
	}
	return false
}

func addBracket(s string, latex bool) string {
	if latex {
		return fmt.Sprintf("\\left(%s\\right)", s)
	}
	return fmt.Sprintf("(%s)", s)
}

// stopAtBody, when non-nil, halts the decomposition as soon as the
// REMAINING term satisfies it — the display-abbreviation hook: a
// quantifier spine normally swallows every inner binder into one
// prefix, so a registered fold nested under outer quantifiers would
// never surface as a standalone node without this stop.
func decomposeQuantifiers(t Term, latex bool, conflicts map[TermName]bool,
	stopAtBody func(Term) bool) ([]VarTerm, []string, Term, bool) {
	if t, ok := t.AsAppliedTerm(); ok {
		if tFun, ok := t.Fun().AsConst(); ok && isConstQuantifier(tFun) {
			if tArg, ok := t.Arg().AsAbsTerm(); ok {
				body := tArg.Body()
				var vars []VarTerm
				var symbols []string
				if stopAtBody == nil || !stopAtBody(body) {
					vars, symbols, body, _ = decomposeQuantifiers(body, latex, conflicts, stopAtBody)
				}
				return append([]VarTerm{tArg.Var()}, vars...),
					append([]string{formatConst(tFun, latex, conflicts)}, symbols...),
					body, true
			}
		}
	}
	return nil, nil, t.Core(), false
}

// binderTypeMode controls how quantifier-/lambda-bound vars print their type
// annotation. The three modes correspond to display profiles:
//
//   - binderNone: no annotation; the default for human-readable output (e.g.
//     PrintTerm / FormatTerm).
//   - binderAll: every bound var gets `:type` regardless of shape; the parser
//     round-trip profile (FormatTermForParser).
//   - binderPoly: annotation iff the binder's type contains a VarType (i.e.
//     the binder is polymorphic). Used for inspect's hyp display, where
//     surfacing the type-var preserves the information an agent needs to keep
//     the lemma's polymorphism in view across `instantiate` peels — without
//     drowning concrete num/bool binders in noise.
type binderTypeMode int

const (
	binderNone binderTypeMode = iota
	binderAll
	binderPoly
	// binderAllNameFaithful is binderAll with name-DROPPING shorthands
	// disabled: the `{x | φ}` / `{t | x | φ}` set-builders lose the set_comprehension
	// λ-binder's name (parse re-synthesizes a position-derived
	// GEN%PVAR%<pos>), so under this profile those shapes render as
	// explicit set_comprehension(λ<name>. …) and parse(print(t)) reproduces t's
	// binder names EXACTLY — the one exception being a binder that
	// shadows a same-named different-typed free variable, which no
	// text can spell faithfully (RenameShadowedBinders). Used for
	// replay-parsed proof payloads — see
	// prop.FormatPropForParserNameFaithful.
	binderAllNameFaithful
)

// shouldAnnotateBinder is the per-binder decision for the chosen mode.
func shouldAnnotateBinder(t HolType, m binderTypeMode) bool {
	switch m {
	case binderAll, binderAllNameFaithful:
		return true
	case binderPoly:
		return TypeAnyVar(t, utils.FullPredicate)
	}
	return false
}

// matchIdentitySetBuilder detects the printer-friendly identity set-builder
// shape produced by the DSL's `{x | φ(x)}` desugar:
//
//	set_comprehension(λv:T. ∃x:T. comprehension_spec(v, φ, x))
//
// v and x are two distinct bound vars at the same element type T; the
// comprehension_spec's first arg equals the λv binder and its third arg equals the
// ∃x binder. The second arg (φ) is the predicate. Returns (∃-binder,
// predicate, true) on match; ("", nil, false) otherwise.
//
// A polymorphic-const conflict on set_comprehension or comprehension_spec does NOT make this
// canonical shape ambiguous: formatIdentitySetBuilder writes the element
// type on the surviving ∃-binder (`{x:T | φ}`) whenever the display profile
// or the conflict requires it. That binder type pins the hidden set_comprehension λ-binder
// and both const instances on re-parse. Non-canonical set_comprehension/comprehension_spec shapes
// still fall through to the annotated prefix form.
//
// Non-identity shapes intentionally fall through here; the separate general
// matcher below handles only the explicit-binder-list form the parser can
// reconstruct exactly.
func matchIdentitySetBuilder(t AppliedTerm) (VarTerm, Term, bool) {
	setComprehension, ok := t.Fun().AsConst()
	if !ok || setComprehension.Name() != TermName("set_comprehension") {
		return VarTerm{}, nil, false
	}
	lam, ok := t.Arg().AsAbsTerm()
	if !ok {
		return VarTerm{}, nil, false
	}
	existsApp, ok := lam.Body().AsAppliedTerm()
	if !ok {
		return VarTerm{}, nil, false
	}
	existsFun, ok := existsApp.Fun().AsConst()
	if !ok || existsFun.Name() != TermName(utils.ExistsStr) {
		return VarTerm{}, nil, false
	}
	innerAbs, ok := existsApp.Arg().AsAbsTerm()
	if !ok {
		return VarTerm{}, nil, false
	}
	comprehensionSpecHead, comprehensionSpecArgs := MatchesApply(innerAbs.Body())
	if len(comprehensionSpecArgs) != 3 {
		return VarTerm{}, nil, false
	}
	ss, ok := comprehensionSpecHead.AsConst()
	if !ok || ss.Name() != TermName("comprehension_spec") {
		return VarTerm{}, nil, false
	}
	// An ∃ binder shadowing the λ binder (same name+type) makes comprehension_spec's
	// first-arg occurrence reference the ∃ binder; the Equals checks below
	// cannot tell the two apart. Decline — the shorthand's re-parse would
	// bind that occurrence to the OUTER fresh binder instead.
	if innerAbs.Var().Equals(lam.Var()) {
		return VarTerm{}, nil, false
	}
	v0, ok := comprehensionSpecArgs[0].AsVar()
	if !ok || !v0.Equals(lam.Var()) {
		return VarTerm{}, nil, false
	}
	v2, ok := comprehensionSpecArgs[2].AsVar()
	if !ok || !v2.Equals(innerAbs.Var()) {
		return VarTerm{}, nil, false
	}
	// The λv binder's name is dropped by the shorthand and re-synthesized
	// at parse. That is only faithful (up to α) when v's SOLE occurrence is
	// comprehension_spec's first argument — an occurrence inside φ would come back as
	// a DIFFERENT (free) variable after the round-trip.
	if comprehensionSpecArgs[1].HasFree(v0) {
		return VarTerm{}, nil, false
	}
	return innerAbs.Var(), comprehensionSpecArgs[1], true
}

// matchGeneralSetBuilder detects the general set-builder shape produced by
// the DSL's three-part `{t | x₁, …, xₙ | φ}` desugar:
//
//	set_comprehension(λv. ∃x₁. … ∃xₙ. comprehension_spec(v, φ, t))     n ≥ 1
//
// v is the λ binder whose SOLE occurrence is comprehension_spec's first argument
// (its name is dropped by the shorthand — an occurrence inside φ or t
// would not survive the round-trip, so those shapes decline); the
// ∃-chain between the λ and the comprehension_spec is the explicit binder list, in
// order; φ is the predicate and t the output expression. Returns
// (binder list, φ, t, true) on match.
//
// Like the identity matcher, this accepts a canonical comprehension even
// under a set_comprehension/comprehension_spec conflict. formatGeneralSetBuilder then writes the
// element type on the output (`{t:T | x | φ}`), which is the type of the
// hidden λ-binder and of both const instances. The identity shape (n == 1,
// t ≡ x₁) also matches here; callers keep the shorter `{x | φ}` by running
// matchIdentitySetBuilder first.
func matchGeneralSetBuilder(t AppliedTerm) ([]VarTerm, Term, Term, bool) {
	setComprehension, ok := t.Fun().AsConst()
	if !ok || setComprehension.Name() != TermName("set_comprehension") {
		return nil, nil, nil, false
	}
	lam, ok := t.Arg().AsAbsTerm()
	if !ok {
		return nil, nil, nil, false
	}
	// Collect the ∃-chain down to the comprehension_spec body.
	var binders []VarTerm
	body := lam.Body()
	for {
		existsApp, ok := body.AsAppliedTerm()
		if !ok {
			return nil, nil, nil, false
		}
		existsFun, ok := existsApp.Fun().AsConst()
		if !ok || existsFun.Name() != TermName(utils.ExistsStr) {
			break
		}
		innerAbs, ok := existsApp.Arg().AsAbsTerm()
		if !ok {
			return nil, nil, nil, false
		}
		binders = append(binders, innerAbs.Var())
		body = innerAbs.Body()
	}
	if len(binders) == 0 {
		return nil, nil, nil, false
	}
	comprehensionSpecHead, comprehensionSpecArgs := MatchesApply(body)
	if len(comprehensionSpecArgs) != 3 {
		return nil, nil, nil, false
	}
	ss, ok := comprehensionSpecHead.AsConst()
	if !ok || ss.Name() != TermName("comprehension_spec") {
		return nil, nil, nil, false
	}
	v0, ok := comprehensionSpecArgs[0].AsVar()
	if !ok || !v0.Equals(lam.Var()) {
		return nil, nil, nil, false
	}
	// A binder shadowing v would make comprehension_spec's first arg reference the
	// ∃ binder, not the λ binder; the v0.Equals check above cannot tell
	// them apart (same name, same type). Decline shadowed shapes.
	for _, b := range binders {
		if b.Equals(v0) {
			return nil, nil, nil, false
		}
	}
	if comprehensionSpecArgs[1].HasFree(v0) || comprehensionSpecArgs[2].HasFree(v0) {
		return nil, nil, nil, false
	}
	return binders, comprehensionSpecArgs[1], comprehensionSpecArgs[2], true
}

// formatIdentitySetBuilder renders a matched identity set-builder as
// `{binder | pred}` (or LaTeX `\{binder \mid pred\}`). Shared by the
// arity-1 branch of formatTermImpl (where set_comprehension(λ...) is the whole
// applied term) and — potentially — over-application sites via the
// recursive descent.
func formatIdentitySetBuilder(binder VarTerm, pred Term, latex bool, conflicts map[TermName]bool, binderTypes binderTypeMode) string {
	binderStr := formatTermImpl(binder, latex, conflicts, binderTypes)
	if shouldAnnotateBinder(binder.Type(), binderTypes) || setBuilderHasTypeConflict(conflicts) {
		// Match FormatTermForParser's binder-type discipline: emit the
		// parser-safe curry form via FormatTypeForParser so the round-
		// trip through the DSL's parseSetBuilder is exact.
		binderStr = fmt.Sprintf("%s:%s", binderStr, FormatTypeForParser(binder.Type()))
	}
	predStr := formatTermImpl(pred, latex, conflicts, binderTypes)
	if latex {
		return fmt.Sprintf("\\{%s \\mid %s\\}", binderStr, predStr)
	}
	return fmt.Sprintf("{%s | %s}", binderStr, predStr)
}

// setBuilderHasTypeConflict reports whether the canonical comprehension is
// hiding an occurrence from either conflicted const name. One natural type
// witness on the surviving surface form disambiguates both: set_comprehension's element
// type and comprehension_spec's first/third-argument type are identical by the matchers.
func setBuilderHasTypeConflict(conflicts map[TermName]bool) bool {
	return conflicts != nil && (conflicts[TermName("set_comprehension")] || conflicts[TermName("comprehension_spec")])
}

// formatGeneralSetBuilder renders a matched general set-builder as the
// three-part `{t | x₁, …, xₙ | φ}` (or LaTeX `\{t \mid ẋ \mid φ\}`). In
// parser mode — and in every profile under a set_comprehension/comprehension_spec conflict — the
// output carries its type: `{t:T | x₁:T₁, … | φ}`. T is precisely the hidden
// set_comprehension λ-binder's type, so this local witness replaces both noisy const
// annotations while keeping print → parse sound.
func formatGeneralSetBuilder(binders []VarTerm, pred, out Term, latex bool, conflicts map[TermName]bool, binderTypes binderTypeMode) string {
	outStr := formatTermImpl(out, latex, conflicts, binderTypes)
	if shouldAnnotateBinder(out.Type(), binderTypes) || setBuilderHasTypeConflict(conflicts) {
		outStr = fmt.Sprintf("%s:%s", outStr, FormatTypeForParser(out.Type()))
	}
	binderStrs := make([]string, len(binders))
	for i, b := range binders {
		s := formatTermImpl(b, latex, conflicts, binderTypes)
		if shouldAnnotateBinder(b.Type(), binderTypes) {
			s = fmt.Sprintf("%s:%s", s, FormatTypeForParser(b.Type()))
		}
		binderStrs[i] = s
	}
	predStr := formatTermImpl(pred, latex, conflicts, binderTypes)
	if latex {
		return fmt.Sprintf("\\{%s \\mid %s \\mid %s\\}",
			outStr, strings.Join(binderStrs, ", "), predStr)
	}
	return fmt.Sprintf("{%s | %s | %s}", outStr, strings.Join(binderStrs, ", "), predStr)
}

// matchInsertChain detects the printer-friendly insert-chain shape
// terminating in empty_set produced by the DSL's `{a₁, a₂, …, aₙ}` desugar:
//
//	insert(a₁, insert(a₂, …, insert(aₙ, empty_set)))
//
// Returns the ordered element list on match; nil / false otherwise. The
// last insert's tail must be a bare empty_set constant — anything else
// (variable set, another set expression) surfaces as literal
// `insert(a, s)` since the enumeration parser cannot reconstruct it.
//
// Refuses to match under a polymorphic-const type conflict on insert or
// empty_set — the annotated `insert⟨A:T⟩` fallback surfaces the instance the
// shorthand would hide.
func matchInsertChain(t AppliedTerm, conflicts map[TermName]bool) ([]Term, bool) {
	var elems []Term
	var cur Term = t
	for {
		at, ok := cur.AsAppliedTerm()
		if !ok {
			return nil, false
		}
		head, args := MatchesApply(at)
		if len(args) != 2 {
			return nil, false
		}
		hc, ok := head.AsConst()
		if !ok || hc.Name() != TermName("insert") {
			return nil, false
		}
		if conflicts != nil && conflicts[hc.Name()] {
			return nil, false
		}
		elems = append(elems, args[0])
		cur = args[1]
		// Terminate when the tail is a bare empty_set const.
		if ec, ok := cur.AsConst(); ok && ec.Name() == TermName("empty_set") {
			if conflicts != nil && conflicts[ec.Name()] {
				return nil, false
			}
			return elems, true
		}
	}
}

// matchCongApp detects the two shapes the ≡ congruence mixfix parses to
// (`x ≡ y (mod m)`, dsl/cong.go): ℕ's `nat_cong(x, y, m)` and ℤ's
// `int_cong(x, y, m)` — one three-place relation per domain, read in
// the order the mixfix spells it.
//
// Any other congruence-shaped relation is deliberately NOT
// matched — `≡` means nat_cong or
// int_cong, so printing another relation with the mixfix would produce text
// that reparses to a different constant. It prints longhand.
func matchCongApp(t Term) (x, y, m Term, ok bool) {
	f, args := MatchesApply(t)
	if len(args) != 3 {
		return nil, nil, nil, false
	}
	c, isConst := f.AsConst()
	if !isConst {
		return nil, nil, nil, false
	}
	if c.Name() != TermName("nat_cong") && c.Name() != TermName("int_cong") {
		return nil, nil, nil, false
	}
	return args[0], args[1], args[2], true
}

// bracketCongOperand formats one ≡ operand, bracketing it exactly the
// way formatConstTemplate brackets an infix template's argument. The
// modulus never goes through this — its `(mod …)` clause is
// self-delimiting.
func bracketCongOperand(t Term, latex bool, conflicts map[TermName]bool, binderTypes binderTypeMode) string {
	s := formatTermImpl(t, latex, conflicts, binderTypes)
	if shouldBeBracketed(t, binderTypes) {
		s = addBracket(s, latex)
	}
	return s
}

// formatSetEnum renders `{a₁, a₂, …, aₙ}`. Elements are formatted
// without individual bracketing — `,` is the lowest-precedence
// separator inside the braces, so `{a * b, c + d}` reads
// unambiguously. Same convention as tuple / paren-arg rendering.
func formatSetEnum(elems []Term, latex bool, conflicts map[TermName]bool, binderTypes binderTypeMode) string {
	parts := make([]string, len(elems))
	for i, e := range elems {
		parts[i] = formatTermImpl(e, latex, conflicts, binderTypes)
	}
	joined := strings.Join(parts, ", ")
	if latex {
		return fmt.Sprintf("\\{%s\\}", joined)
	}
	return fmt.Sprintf("{%s}", joined)
}

// matchPatternLambda detects the canonical pattern_abstraction pair-pattern encoding —
// the lowering of `λ(u, x). body`:
//
//	pattern_abstraction(λf:(prod(..)→R). ∀v₁ … ∀vₖ. f(pat) = body)
//
// where pat is a pair-tree (right-nested `,` applications) whose leaves
// are EXACTLY the ∀-chain vars v₁…vₖ in order, with pairwise-distinct
// names, and the internal binder f occurs nowhere but at the equation's
// head. On match it returns (pat, body) and the term renders as the
// pattern lambda `λ(u, x). body` — the internal f never reaches the
// text, which removes
// the main shadow-collision source (f under an ambient same-named var).
//
// Non-canonical pattern_abstraction shapes (extra/missing ∀ vars,
// duplicate pattern names, f free in body, pattern_abstraction applied to further
// arguments) fall through to the explicit annotated `pattern_abstraction(λf. …)` form.
//
// A polymorphic-const conflict on pattern_abstraction or `,` does not block the sugar:
// the hidden instances are fully pinned on re-parse by the pattern
// binder type annotations plus the body's type, so no `⟨…⟩` annotation
// site is needed.
func matchPatternLambda(t AppliedTerm) (pat, body Term, ok bool) {
	patternAbstraction, isConst := t.Fun().AsConst()
	if !isConst || patternAbstraction.Name() != TermName("pattern_abstraction") {
		return nil, nil, false
	}
	spec, isAbs := t.Arg().AsAbsTerm()
	if !isAbs {
		return nil, nil, false
	}
	f := spec.Var()
	var chain []VarTerm
	cur := spec.Body()
	for {
		abs := MatchesFORALL(cur)
		if abs.IsZero() {
			break
		}
		chain = append(chain, abs.Var())
		cur = abs.Body()
	}
	if len(chain) < 2 {
		return nil, nil, false
	}
	lhs, rhs, isEq := core.MatchesEQ(cur)
	if !isEq {
		return nil, nil, false
	}
	lApp, isApp := lhs.AsAppliedTerm()
	if !isApp {
		return nil, nil, false
	}
	head, isVar := lApp.Fun().AsVar()
	if !isVar || !head.Equals(f) {
		return nil, nil, false
	}
	leaves, isPat := patternPairLeaves(lApp.Arg())
	if !isPat || len(leaves) != len(chain) {
		return nil, nil, false
	}
	names := map[TermName]bool{}
	for i, leaf := range leaves {
		if !leaf.Equals(chain[i]) || names[leaf.Name()] {
			return nil, nil, false
		}
		names[leaf.Name()] = true
		// A ∀ var identical to the spec binder would make the equation
		// head's binding ambiguous (kernel-side the ∀ var wins) — the
		// head.Equals(f) check above cannot tell them apart, so decline.
		if leaf.Equals(f) {
			return nil, nil, false
		}
	}
	if rhs.HasFree(f) {
		return nil, nil, false
	}
	return lApp.Arg(), rhs, true
}

// patternPairLeaves flattens a pair-tree of `,` applications into its
// in-order leaf variables. The root must be a pair node (a bare var is
// not a pattern); nested pair nodes are allowed on either side.
func patternPairLeaves(t Term) ([]VarTerm, bool) {
	f, args := MatchesApply(t)
	c, isConst := f.AsConst()
	if !isConst || c.Name() != CommaConstMeta.Name() || len(args) != 2 {
		return nil, false
	}
	var walk func(Term) ([]VarTerm, bool)
	walk = func(t Term) ([]VarTerm, bool) {
		if v, ok := t.AsVar(); ok {
			return []VarTerm{v}, true
		}
		f, args := MatchesApply(t)
		c, isConst := f.AsConst()
		if !isConst || c.Name() != CommaConstMeta.Name() || len(args) != 2 {
			return nil, false
		}
		left, ok := walk(args[0])
		if !ok {
			return nil, false
		}
		right, ok := walk(args[1])
		if !ok {
			return nil, false
		}
		return append(left, right...), true
	}
	return walk(t)
}

// formatPatternLambda renders a matched pattern lambda as
// `λ(u:T, x:T). body` (annotations per the binder mode, like any other
// binder). The pattern tree mirrors the term's pair nesting.
func formatPatternLambda(pat, body Term, latex bool, conflicts map[TermName]bool, binderTypes binderTypeMode) string {
	var patStr func(Term) string
	patStr = func(t Term) string {
		if v, ok := t.AsVar(); ok {
			s := formatTermImpl(v, latex, conflicts, binderTypes)
			if shouldAnnotateBinder(v.Type(), binderTypes) {
				s = fmt.Sprintf("%s:%s", s, FormatTypeForParser(v.Type()))
			}
			return s
		}
		_, args := MatchesApply(t)
		return addBracket(fmt.Sprintf("%s, %s", patStr(args[0]), patStr(args[1])), latex)
	}
	lambda := utils.LambdaStr
	if latex {
		lambda = "\\lambda"
	}
	bodyStr := formatTermImpl(body, latex, conflicts, binderTypes)
	if shouldBeBracketed(body, binderTypes) {
		bodyStr = addBracket(bodyStr, latex)
	}
	return fmt.Sprintf("%s%s.%s", lambda, patStr(pat), bodyStr)
}

func formatConstTemplate(
	c ConstTerm, args []Term, latex bool, conflicts map[TermName]bool, binderTypes binderTypeMode) (string, bool) {
	// If this const participates in a type-annotation conflict, skip the
	// infix/template rendering path. The annotated form needs to appear on the
	// const name itself, so fall through to the generic function-application
	// rendering which routes through formatConst (annotated).
	if conflicts != nil && conflicts[c.Name()] {
		return "", false
	}

	f, ok := _ConstTermFormat{}, false
	if _f, _ok := basicConstFmts[c.Name()]; _ok &&
		_f.FmtTempl.Arity == len(args) {
		if c.Equals(core.IFF()) {
			_f = basicConstFmts[utils.IffStr]
		}
		f, ok = _f, true
	}
	if !ok {
		if _f, _ok := extraConstFmts[c.Name()]; _ok &&
			_f.FmtTempl.Arity == len(args) {
			f, ok = _f, true
		}
	}

	if ok && f.FmtTempl.Arity == len(args) {
		argsStr := make([]string, len(args))
		for i, arg := range args {
			argsStr[i] = formatTermImpl(arg, latex, conflicts, binderTypes)
			if shouldBeBracketed(arg, binderTypes) {
				argsStr[i] = addBracket(argsStr[i], latex)
			}
		}
		if !latex {
			return f.FmtTempl.FmtCallback(argsStr...), true
		} else {
			Assert(f.LatexTempl.Arity == len(args))
			return f.LatexTempl.FmtCallback(argsStr...), true
		}
	}
	return "", false
}

// FormatTerm renders a term as a string.
//
// Printer contract: if two terms produce identical output strings, they must
// be AlphaEquals. To preserve this under type-erasing pretty-printing, any
// polymorphic constant that appears in the term with more than one distinct
// holType is annotated with its type instantiation (see collectConstConflicts
// and formatConstTypeAnnotation). Monomorphic terms and terms without
// polymorphic conflicts produce output identical to the original printer.
func FormatTerm(t Term, latex bool) string {
	conflicts := collectConstConflicts(t)
	return formatTermImpl(t, latex, conflicts, binderNone)
}

// HOL kernel variable identity is the (name, type) pair, so a term may
// legally bind `f:(prod(C,P)→bool)` inside a scope where a DIFFERENT
// `f:(A→B)` occurs free in the inner binder's body — the pair-pattern
// encoding produces exactly this under an ambient `f`
// (its fresh-name choice only avoids exact name+type clashes). The text surface,
// however, resolves occurrences lexically by NAME: printing both vars as
// a bare `f` makes the parser capture the outer occurrences at the inner
// binder's type, and no parse of the bare-name text can denote the
// original term. RenameShadowedBinders restores the printable invariant
// "within any scope path a name denotes one variable" by α-renaming the
// INNER binder to a primed variant — the exact transformation validated
// against two paired-λ recursion statements (renaming the inner
// pattern_abstraction binder makes the text parse and α-match).
//
// Every parser profile applies this, the name-faithful one
// (FormatTermForParserInConflictsNameFaithful) included: renaming a
// bound var is α-neutral, which is what every profile's round-trip gate
// (AlphaKey) requires. The name-faithful profile's exactness promise is
// kept wherever a faithful text EXISTS — a term without a same-name/
// different-type pair comes back pointer-identical and prints its
// binder names verbatim. A collision term has no faithful text at all;
// for it the α-faithful primed spelling replaces no text (the callers
// would otherwise omit the field or fall back to the Go form), and the
// only name that moves is the shadowing binder's.

// RenameShadowedBinders returns t with every binder whose body contains
// a FREE variable of the same name but a different type renamed to a
// primed variant that collides with no name occurring in the body. Terms
// without any same-name/different-type variable pair (the overwhelmingly
// common case) are returned unchanged, pointer-identical.
//
// The walk is bottom-up, so nested collisions resolve innermost-first:
// after a deeper binder is renamed, an enclosing binder only renames if
// a conflict remains in the REWRITTEN body. Free variables are never
// renamed (they are part of the statement's identity); a same-name/
// different-type pair of free variables therefore remains unprintable
// and must keep failing the caller's round-trip gate.
func RenameShadowedBinders(t Term) Term {
	if !hasSameNameDiffTypeVars(t) {
		return t
	}
	return renameShadowedWalk(t)
}

// hasSameNameDiffTypeVars is the cheap single-walk gate: does any
// variable name (bound or free, binder or occurrence) appear at two
// distinct types anywhere in t?
func hasSameNameDiffTypeVars(t Term) bool {
	seen := map[TermName]core.TypeKey{}
	var walk func(Term) bool
	walk = func(t Term) bool {
		switch tt := t.Core().(type) {
		case core.VarTerm:
			k := tt.Type().Key()
			if prev, ok := seen[tt.Name()]; ok {
				return prev != k
			}
			seen[tt.Name()] = k
		case core.AppliedTerm:
			return walk(tt.Fun()) || walk(tt.Arg())
		case core.AbsTerm:
			return walk(tt.Var()) || walk(tt.Body())
		}
		return false
	}
	return walk(t)
}

func renameShadowedWalk(t Term) Term {
	switch tt := t.Core().(type) {
	case core.AppliedTerm:
		f := renameShadowedWalk(tt.Fun())
		a := renameShadowedWalk(tt.Arg())
		if f.Core() == tt.Fun().Core() && a.Core() == tt.Arg().Core() {
			return t
		}
		return core.Apply(f, a)
	case core.AbsTerm:
		body := renameShadowedWalk(tt.Body())
		res := tt
		if body.Core() != tt.Body().Core() {
			res = core.Abs(tt.Var(), body)
		}
		v := res.Var()
		if hasFreeVarNameOtherType(res.Body(), v.Name(), v.Type(), map[core.TypeKey]bool{}) {
			// Primed variant avoiding EVERY name in the body (vars bound
			// or free, and const names) — ChangeAbsVar substitutes the
			// binder's occurrences and asserts the new name is not free
			// in the body, and avoiding all names also rules out
			// creating a fresh collision one level deeper.
			n := utils.NextName(v.Name())
			for res.Body().HasName(n) {
				n = utils.NextName(n)
			}
			res = res.ChangeAbsVar(n)
		}
		return res
	}
	return t
}

// hasFreeVarNameOtherType reports whether t contains a FREE occurrence
// of a variable named `name` whose type differs from `ty`. boundTys
// tracks the types at which `name` is bound by enclosing binders inside
// the walk — kernel binding is by (name, type), so a same-named binder
// at a different type does NOT bind the occurrence we are looking for.
func hasFreeVarNameOtherType(t Term, name TermName, ty core.HolType, boundTys map[core.TypeKey]bool) bool {
	switch tt := t.Core().(type) {
	case core.VarTerm:
		return tt.Name() == name && !tt.Type().Equals(ty) && !boundTys[tt.Type().Key()]
	case core.AppliedTerm:
		return hasFreeVarNameOtherType(tt.Fun(), name, ty, boundTys) ||
			hasFreeVarNameOtherType(tt.Arg(), name, ty, boundTys)
	case core.AbsTerm:
		v := tt.Var()
		if v.Name() != name {
			return hasFreeVarNameOtherType(tt.Body(), name, ty, boundTys)
		}
		k := v.Type().Key()
		if boundTys[k] {
			return hasFreeVarNameOtherType(tt.Body(), name, ty, boundTys)
		}
		boundTys[k] = true
		found := hasFreeVarNameOtherType(tt.Body(), name, ty, boundTys)
		delete(boundTys, k)
		return found
	}
	return false
}

// FormatTermWithPolyBinders is FormatTerm with polymorphic ∀/∃/∃!/λ binders
// annotated `var:type` — e.g. `∀f:((var:A, var:B) → var:B). …` — and concrete
// binders left bare as in FormatTerm. The agent-facing inspect uses this for
// hyp display so a residual polymorphic binder's type is visible BEFORE a
// downstream `instantiate` collides with the type. The output remains
// non-latex; latex callers can use this through formatTermImpl directly.
//
// Polymorphism is detected via TypeAnyVar(FullPredicate), so any binder whose
// type contains at least one VarType qualifies (including function types like
// `(A,B)→B` and parametric composites). A binder whose type is purely concrete
// — `num`, `bool`, `num→num`, `list(num)`, … — prints exactly as in FormatTerm.
func FormatTermWithPolyBinders(t Term, latex bool) string {
	conflicts := collectConstConflicts(t)
	return formatTermImpl(t, latex, conflicts, binderPoly)
}

// FormatTermForParser is FormatTerm with quantifier-bound vars
// annotated `var:type` (`∀m:num.` instead of `∀m.`). Used by emit's
// "section text form" path: the parser requires bound
// types since bound-var inference is a separate deferred work item.
// Output stays non-latex; everything else (connective syntax, sub-app
// nesting, multi-binder collapse) matches FormatTerm exactly.
func FormatTermForParser(t Term) string {
	t = RenameShadowedBinders(t)
	conflicts := collectConstConflicts(t)
	return formatTermImpl(t, false, conflicts, binderAll)
}

// FormatTermForParserInConflicts is FormatTermForParser with a caller-
// supplied conflict set — for prop-level formatting, where the set must
// span the prop's hypotheses AND conclusion (ConstConflictSet) because
// they parse against one shared scope. A term-local set would leave a
// cross-term multi-instance const un-annotated in the term where it
// happens to occur at a single instance (the round-trip failure of
// cardinality.HasSizeFunspaceUniv: the conclusion's has_size parsed at a hyp's
// instance, invisibly breaking alpha-equality).
//
// All three parser-profile entries apply RenameShadowedBinders first: a
// binder shadowing a same-named DIFFERENT-typed free var of its body
// (legal for the kernel's (name,type) var identity, e.g. the
// pattern_abstraction-internal `f` under an ambient `f:(A→B)`) has no bare-name text
// the parser can resolve back — the α-neutral primed rename is the only
// printable form.
func FormatTermForParserInConflicts(t Term, conflicts map[TermName]bool) string {
	t = RenameShadowedBinders(t)
	return formatTermImpl(t, false, conflicts, binderAll)
}

// FormatTermForParserInConflictsNameFaithful is the name-faithful parser
// profile: name-dropping shorthands (the set-builders) are disabled so
// the round-trip reproduces bound-variable names exactly — except a
// binder that shadows a same-named different-typed free variable, which
// has no faithful spelling and prints under RenameShadowedBinders'
// variant (see its comment). See binderAllNameFaithful /
// prop.FormatPropForParserNameFaithful.
func FormatTermForParserInConflictsNameFaithful(t Term, conflicts map[TermName]bool) string {
	t = RenameShadowedBinders(t)
	return formatTermImpl(t, false, conflicts, binderAllNameFaithful)
}

// formatTermImpl is the recursive workhorse. It must be called with a conflicts
// map computed once at the top level — never re-computed per subterm, since a
// conflict is a property of the whole term under a single call.
// binderTypes selects the bound-var type-annotation mode (see binderTypeMode):
// binderNone for human-comment use, binderAll for parser round-trip,
// binderPoly for "annotate only polymorphic binders" (the inspect surface).
func formatTermImpl(t Term, latex bool, conflicts map[TermName]bool, binderTypes binderTypeMode) string {
	// Display-abbreviation folds (render.go) — DISPLAY profiles
	// only. The parser round-trip profiles (binderAll /
	// binderAllNameFaithful) render payload text and must stay
	// registry-blind, byte-identical to a fold-free build.
	if binderTypes == binderNone || binderTypes == binderPoly {
		if s, ok := formatDisplayAbbrev(t, latex, conflicts, binderTypes); ok {
			return s
		}
	}
	switch t := t.Core().(type) {
	case VarTerm:
		return formatVar(t, latex)
	case ConstTerm:
		return formatConst(t, latex, conflicts)
	case AppliedTerm:
		// Decimal collapse: a ground, canonical BIT-tower (bit0/bit1 over
		// _0) renders as its decimal value instead of the raw bit spine —
		// `5`, not `bit1(bit0(bit1(_0)))`. Display-only and round-trip
		// safe: the parser maps "5" back to the identical tower, so
		// collapse→reparse is alpha-equal. Guarded by IsCanonicalNumeral,
		// so a non-normal tower or a bit0(n) with a variable n (the hazard
		// the comment on formatConstBase guards against) still prints
		// symbolically.
		if IsCanonicalNumeral(t) {
			v, _ := NumeralValue(t)
			return v.String()
		}
		// insert-chain shortcut: an outer `insert(a₁, …, insert(aₙ, empty_set))`
		// terminating in a bare empty_set renders as `{a₁, …, aₙ}` — matching the
		// DSL's `{...}` enumeration parser. Checked BEFORE the generic
		// multi-arg App branch so we catch the chain at its top insert
		// application; the recursive descent inside formatSetEnum handles
		// nested set expressions (a set-typed element like `{a, {b, c}}`).
		if elems, ok := matchInsertChain(t, conflicts); ok {
			return formatSetEnum(elems, latex, conflicts, binderTypes)
		}

		if f, args := MatchesApply(t); len(args) > 1 {
			if c, ok := f.AsConst(); ok {
				// Pair constructor `,` renders as the natural tuple form
				// `(a, b)` instead of the prefix `,(a, b)`. The leading-
				// comma prefix is logically misleading — it hides the
				// pairing node behind a function name — and the infix form
				// is what a reader (human or model) expects. The structural
				// `,` node is not lost: a pair always appears in argument
				// position, where the surrounding `addBracket` yields the
				// double-paren `f((a, b))` that distinguishes it from a
				// curried two-arg call `f(a, b)`.
				//
				// Components are NOT individually bracketed — `,` is the
				// lowest-precedence separator, so `(a * b, c + d)` is
				// unambiguous. Suppressed under a type-annotation conflict
				// (collectConstConflicts), where `,` must show its instance:
				// it falls through to the annotated prefix form, which still
				// round-trips via the parser's retained `,(...)` branch.
				if len(args) == 2 && c.Name() == CommaConstMeta.Name() &&
					(conflicts == nil || !conflicts[c.Name()]) {
					aStr := formatTermImpl(args[0], latex, conflicts, binderTypes)
					bStr := formatTermImpl(args[1], latex, conflicts, binderTypes)
					if latex {
						return fmt.Sprintf("\\left(%s, %s\\right)", aStr, bStr)
					}
					return fmt.Sprintf("(%s, %s)", aStr, bStr)
				}
				// Congruence mixfix: `nat_cong(x, y, m)` and
				// `int_cong(x, y, m)` render as `x ≡ y (mod m)` — the
				// same sugar the parser accepts, so print→parse rebuilds
				// the identical term.
				// Unconditional across profiles (the ∣-class precedent:
				// nothing is name-dropped, so the name-faithful payload
				// profile is safe), and deliberately NOT suppressed under
				// a `==` type-annotation conflict: reparse re-derives the
				// instance from the operand types, so the ⟨A:τ⟩ annotation
				// the conflict would demand is redundant in this form. The
				// general `==(x, y, rel)` — rel a variable, or real_mod —
				// falls through to the ordinary application rendering.
				if x, y, m, ok := matchCongApp(t); ok {
					xStr := bracketCongOperand(x, latex, conflicts, binderTypes)
					yStr := bracketCongOperand(y, latex, conflicts, binderTypes)
					mStr := formatTermImpl(m, latex, conflicts, binderTypes)
					if latex {
						return fmt.Sprintf("%s \\equiv %s \\pmod{%s}", xStr, yStr, mStr)
					}
					return fmt.Sprintf("%s ≡ %s (mod %s)", xStr, yStr, mStr)
				}
				if s, ok := formatConstTemplate(c, args, latex, conflicts, binderTypes); ok {
					return s
				}
				// Function composition applied to a point: `o(f, g, x)`
				// misses the arity-2 template, and the applied spelling
				// does not round-trip, because `o` is one of the few
				// consts the DSL declines to seed by name (a one-letter
				// identifier is a plausible binder — see funcops.go). So
				// a scope-less reparse of `o(f, g, x)` recovers a free
				// VARIABLE, not this const. Keeping the sugar on the
				// composition and applying the rest makes the output
				// self-identifying: `∘` always builds the const, in any
				// scope.
				if c.Name() == "o" && len(args) > 2 &&
					(conflicts == nil || !conflicts[c.Name()]) {
					if head, ok := formatConstTemplate(
						c, args[:2], latex, conflicts, binderTypes); ok {
						restStr := make([]string, len(args)-2)
						for i, arg := range args[2:] {
							restStr[i] = formatTermImpl(arg, latex, conflicts, binderTypes)
						}
						return addBracket(head, latex) +
							addBracket(strings.Join(restStr, ", "), latex)
					}
				}
			}

			fStr := formatTermImpl(f, latex, conflicts, binderTypes)
			if _, ok := f.AsAbsTerm(); ok {
				fStr = addBracket(fStr, latex)
			}

			if c, ok := f.AsConst(); ok &&
				c.Meta().Name() == utils.HilbertStr {
				f = Apply(f, args[0])
				fStr = formatTermImpl(f, latex, conflicts, binderTypes)
				args = args[1:]
				// An ε-term in FUNCTION position is bracketed: a binder's
				// body runs to the end of the expression, so `εx.P(x)(s)`
				// reads back as an ε whose body is `P(x)(s)` — a different
				// term, and usually one the kernel rejects outright. The
				// same reason the raw λ head above is bracketed.
				fStr = addBracket(fStr, latex)
			}

			argsStr := make([]string, len(args))
			for i, arg := range args {
				argsStr[i] = formatTermImpl(arg, latex, conflicts, binderTypes)
			}
			argStr := addBracket(strings.Join(argsStr, ", "), latex)

			return fmt.Sprintf("%s%s", fStr, argStr)
		}

		var stopAtAbbrev func(Term) bool
		if (binderTypes == binderNone || binderTypes == binderPoly) && anyDisplayAbbrevs() {
			stopAtAbbrev = matchesAnyDisplayAbbrev
		}
		if vars, symbols, body, ok := decomposeQuantifiers(t, latex, conflicts, stopAtAbbrev); ok {
			Assert(len(vars) == len(symbols))
			quantifierStr := make([]string, len(vars))
			for i := range vars {
				varStr := formatTermImpl(vars[i], latex, conflicts, binderTypes)
				if shouldAnnotateBinder(vars[i].Type(), binderTypes) {
					// FormatTypeForParser emits curry form for fun
					// types instead of FormatType's tuple shortcut
					// (`((A, B) → C)`), which the parser doesn't
					// grammar; binderPoly inherits the same form so the
					// inspect display is parser-faithful too.
					varStr = fmt.Sprintf("%s:%s", varStr, FormatTypeForParser(vars[i].Type()))
				}
				quantifierStr[i] = fmt.Sprintf("%s%s.", symbols[i], varStr)
			}
			bodyStr := formatTermImpl(body, latex, conflicts, binderTypes)
			if shouldBeBracketed(body, binderTypes) && !isSingleDisplayFold(bodyStr) {
				bodyStr = addBracket(bodyStr, latex)
			}
			return fmt.Sprintf("%s%s", strings.Join(quantifierStr, ""), bodyStr)
		}

		// Set-builder shortcuts, checked BEFORE the arity-1 template branch —
		// set_comprehension has no template of its own, but the set-builder detectors need
		// to run before falling through to the generic `set_comprehension(...)` rendering.
		// Under a poly-const type conflict on set_comprehension/comprehension_spec the matchers
		// decline, so the annotated `set_comprehension⟨A:T⟩(...)` fallback is preserved.
		//
		// Both set-builder shorthands drop the set_comprehension λ-binder's NAME (the
		// parse re-synthesizes a position-derived GEN%PVAR%<pos>), so the
		// name-faithful profile skips them — see binderAllNameFaithful.
		if binderTypes != binderAllNameFaithful {
			// Identity form first: `set_comprehension(λv:T. ∃x:T. comprehension_spec(v, φ, x))` renders
			// as `{x | φ}`; the general matcher would also accept that shape, so
			// the order encodes the preference for the shorter form.
			if binder, pred, ok := matchIdentitySetBuilder(t); ok {
				return formatIdentitySetBuilder(binder, pred, latex, conflicts, binderTypes)
			}
			// General form: `set_comprehension(λv. ∃x₁…∃xₙ. comprehension_spec(v, φ, t))` renders as the
			// explicit-binder-list three-part `{t | x₁, …, xₙ | φ}`.
			if binders, pred, out, ok := matchGeneralSetBuilder(t); ok {
				return formatGeneralSetBuilder(binders, pred, out, latex, conflicts, binderTypes)
			}
			// Pair-pattern lambda: the canonical `pattern_abstraction(λf. ∀v⃗. f(pat) = body)`
			// encoding renders as `λ(u, x). body`. Name-dropping
			// (the internal f binder vanishes), hence gated out of the
			// name-faithful profile with the set-builders above.
			if pat, body, ok := matchPatternLambda(t); ok {
				return formatPatternLambda(pat, body, latex, conflicts, binderTypes)
			}
		}

		// Unary const application with a registered arity-1 template (e.g.
		// real_of_num → the `&` coercion prefix). Checked after the quantifier
		// branch, so binder consts are unaffected; consts without a template
		// fall through to the generic f(arg) rendering below.
		if c, ok := t.Fun().AsConst(); ok {
			if s, ok := formatConstTemplate(c, []Term{t.Arg()}, latex, conflicts, binderTypes); ok {
				return s
			}
		}

		funStr := formatTermImpl(t.Fun(), latex, conflicts, binderTypes)
		argStr := formatTermImpl(t.Arg(), latex, conflicts, binderTypes)
		if _, ok := t.Fun().AsAbsTerm(); ok {
			funStr = addBracket(funStr, latex)
		}

		if c, ok := t.Fun().AsConst(); ok && isConstInvisible(c) {
			return argStr
		}

		argStr = addBracket(argStr, latex)

		if f, ok := t.Fun().AsConst(); ok {
			if f.Equals(NOT) {
				// override above for vars and consts.
				if _, ok := t.Arg().AsVar(); ok {
					argStr = formatTermImpl(t.Arg(), latex, conflicts, binderTypes)
				}
				if _, ok := t.Arg().AsConst(); ok {
					argStr = formatTermImpl(t.Arg(), latex, conflicts, binderTypes)
				}
				if _, ok := t.Arg().AsAppliedTerm(); ok {
					if !shouldBeBracketed(t.Arg(), binderTypes) {
						argStr = formatTermImpl(t.Arg(), latex, conflicts, binderTypes)
					}
					if l, r, ok := MatchesEQ(t.Arg()); ok {
						lStr := formatTermImpl(l, latex, conflicts, binderTypes)
						rStr := formatTermImpl(r, latex, conflicts, binderTypes)
						if shouldBeBracketed(l, binderTypes) {
							lStr = addBracket(lStr, latex)
						}
						if shouldBeBracketed(r, binderTypes) {
							rStr = addBracket(rStr, latex)
						}
						str := TermName(utils.NeqStr)
						if IsBool(l) {
							if binderTypes == binderAll || binderTypes == binderAllNameFaithful {
								// The parser round-trip profiles print what the
								// DSL reads. `⊕` is a display sugar with no lexer
								// token, so a negated bool equation keeps the
								// `¬(l ⇔ r)` spelling, which parses back to
								// `¬(l = r)` at bool — the form a headline author
								// writes.
								return fmt.Sprintf("%s(%s %s %s)", funStr, lStr, utils.IffStr, rStr)
							}
							str = TermName(utils.XorStr)
						}
						if !latex {
							return fmt.Sprintf(
								"%s %s %s", lStr, str, rStr)
						} else {
							return fmt.Sprintf(
								"%s%s%s", lStr, basicConstFmts[str].Latex, rStr)
						}
					}
					// ¬(x ∈ s) prints `x ∉ s` wherever its `x ∈ s` would
					// print infix: a type conflict on set_member keeps the
					// annotated prefix form, negated (formatConstTemplate).
					if l, r, ok := matchesSetMember(t.Arg()); ok && !conflicts["set_member"] {
						lStr := formatTermImpl(l, latex, conflicts, binderTypes)
						rStr := formatTermImpl(r, latex, conflicts, binderTypes)
						if shouldBeBracketed(l, binderTypes) {
							lStr = addBracket(lStr, latex)
						}
						if shouldBeBracketed(r, binderTypes) {
							rStr = addBracket(rStr, latex)
						}
						if !latex {
							return fmt.Sprintf("%s ∉ %s", lStr, rStr)
						}
						return fmt.Sprintf("%s\\notin%s", lStr, rStr)
					}
				}
			}
		}
		return fmt.Sprintf("%s%s", funStr, argStr)

	case AbsTerm:
		vars, body := MatchesAbs(t)

		varsStr := make([]string, len(vars))
		lambda := utils.LambdaStr
		if latex {
			lambda = "\\lambda"
		}
		for i := range vars {
			varStr := formatTermImpl(vars[i], latex, conflicts, binderTypes)
			if shouldAnnotateBinder(vars[i].Type(), binderTypes) {
				// Same convention as quantifiers: emit `:type` so the
				// parser doesn't need bound-var inference. Curry-form
				// fun types via FormatTypeForParser since the parser
				// doesn't grammar FormatType's tuple shortcut.
				varStr = fmt.Sprintf("%s:%s", varStr, FormatTypeForParser(vars[i].Type()))
			}
			varsStr[i] = fmt.Sprintf("%s%s.", lambda, varStr)
		}
		bodyStr := formatTermImpl(body, latex, conflicts, binderTypes)
		if shouldBeBracketed(body, binderTypes) {
			bodyStr = addBracket(bodyStr, latex)
		}
		return fmt.Sprintf("%s%s", strings.Join(varsStr, ""), bodyStr)
	}
	panic("Wrong term type.")
}

func PrintTerm(t TermLike) string { return FormatTerm(t.Core(), false) }

// PrintTermWithPolyBinders is the non-latex shortcut for
// FormatTermWithPolyBinders — the right printer for any agent-facing surface
// where a polymorphic binder must stay visible. Concrete binders print
// exactly as PrintTerm.
func PrintTermWithPolyBinders(t Term) string {
	return FormatTermWithPolyBinders(t, false)
}

// Add common math symbol formats.
func initConstFmt() {
	addConstFmt("<=", defaultInfix("≤", "\\le"))
	addConstFmt(">=", defaultInfix("≥", "\\ge"))
	addConstFmt("<<", defaultInfix("≪", "\\ll"))
	addConstFmt(">>", defaultInfix("≫", "\\gg"))
	// Divisibility renders as U+2223 DIVIDES (`d ∣ n`) — NOT the ASCII
	// set-builder pipe; the parser dispatches the symbol to
	// nat_divides / int_divides by operand type (dsl arithOperator).
	addConstFmt("nat_divides", defaultInfix("∣", "\\mid"))
	addConstFmt("int_divides", defaultInfix("∣", "\\mid"))
	addConstFmt("<", defaultInfix("<", "<"))
	addConstFmt(">", defaultInfix(">", ">"))
	addConstFmt("+", defaultInfix("+", "+"))
	addConstFmt("-", defaultInfix("-", "-"))
	addConstFmt("*", defaultInfix("*", "\\times"))
	// The numeric segment `m..n` (closed interval, both endpoints
	// inclusive). The const has type num → num → (num → bool); the infix
	// dispatcher fires when exactly the first two args are applied —
	// producing `m..n` as a set term. A subsequent membership application
	// `(m..n)(p)` falls through to function-application rendering with
	// `m..n` as the function head, round-tripping via the parser's
	// parseSegment.
	addConstFmt("..", defaultInfix("..", ".."))
	// The powers display as the infix `^` at every domain that has one;
	// the parser re-resolves the symbol by the base's type (dsl/arith.go's
	// powDomainOperator), so round-trip is preserved. A bare occurrence
	// keeps the constant's name (formatConstBase's rule for templated
	// identifier-named consts).
	addConstFmt("nat_pow", powInfix())
	addConstFmt("real_pow", powInfix())
	addConstFmt("int_pow", powInfix())
	addConstFmt("_0",
		_ConstTermFormat{Format: "0", Latex: "0"})
	// Real operators carry their domain const names (real_add/…, dsl/arith.go)
	// but display as their overloaded infix symbols; the parser re-resolves a
	// symbol to the real instance by operand type, so round-trip is preserved.
	addConstFmt("real_add", defaultInfix("+", "+"))
	addConstFmt("real_mul", defaultInfix("*", "\\times"))
	// real_div is the one infix with no num twin, so `/` on the way back
	// in is unambiguously real (dsl/arith.go's isArithOperator).
	addConstFmt("real_div", defaultInfix("/", "\\div"))
	addConstFmt("real_lt", defaultInfix("<", "<"))
	addConstFmt("real_le", defaultInfix("≤", "\\le"))
	addConstFmt("real_gt", defaultInfix(">", ">"))
	addConstFmt("real_ge", defaultInfix("≥", "\\ge"))
	// Applied real_of_num displays as the parser's tight `&` coercion prefix.
	// Plain concatenation round-trips: a complex argument arrives already
	// bracketed (shouldBeBracketed), so the output is `&2`, `&m`, `&(m + n)` —
	// all parseSpine-valid after `&`.
	addConstFmt("real_of_num", _ConstTermFormat{
		FmtTempl: FmtTemplate{
			Arity:       1,
			FmtCallback: func(s ...string) string { return "&" + s[0] }},
		LatexTempl: FmtTemplate{
			Arity:       1,
			FmtCallback: func(s ...string) string { return "\\&" + s[0] }},
	})
	// real subtraction / negation display as their overloaded infix `-` /
	// prefix `-`; the parser re-resolves `-` to real_sub (binary) / real_neg
	// (unary) by operand type. real_sub is TOTAL (not num's monus).
	addConstFmt("real_sub", defaultInfix("-", "-"))
	addConstFmt("real_neg", negPrefixFmt())
	// Integer operators carry their domain const names (int_add/…, dsl/arith.go)
	// and display as their overloaded infix symbols, like the real operators;
	// the parser re-resolves the symbol to the int instance by operand type.
	addConstFmt("int_add", defaultInfix("+", "+"))
	addConstFmt("int_mul", defaultInfix("*", "\\times"))
	addConstFmt("int_sub", defaultInfix("-", "-"))
	addConstFmt("int_neg", negPrefixFmt())
	addConstFmt("int_lt", defaultInfix("<", "<"))
	addConstFmt("int_le", defaultInfix("≤", "\\le"))
	addConstFmt("int_gt", defaultInfix(">", ">"))
	addConstFmt("int_ge", defaultInfix("≥", "\\ge"))
	// NOTE: int_of_num is deliberately NOT registered as `&` (unlike
	// real_of_num): `&` re-parses to real by default, so an int literal must
	// print as the explicit `int_of_num(n)` to round-trip unambiguously — the
	// operator infix above re-resolves to int by the int_of_num operand type.

	// The real-construction tower (nadd → hreal → treal). Same treatment as
	// the real and int layers: the consts keep their layer names
	// (hreal_add/nadd_mul/treal_le/…, dsl/arith.go) and display as the
	// overloaded infix symbols, with the parser re-resolving each symbol to
	// the right layer by operand type (arithDomainOperator). Each layer has
	// only `+ * ≤` — no subtraction anywhere in the tower, and no strict `<`.
	//
	// The tower's two EQUIVALENCE relations (nadd_eq, treal_eq) are
	// deliberately absent: they are not overloads of a symbol the surface
	// already spells, so an infix form would be new notation rather than a
	// new instance of existing notation. They keep printing prefix. The num
	// embeddings (hreal_of_num/…) and the inverses/negation are omitted for
	// the same reason.
	addConstFmt("hreal_add", defaultInfix("+", "+"))
	addConstFmt("hreal_mul", defaultInfix("*", "\\times"))
	addConstFmt("hreal_le", defaultInfix("≤", "\\le"))
	addConstFmt("nadd_add", defaultInfix("+", "+"))
	addConstFmt("nadd_mul", defaultInfix("*", "\\times"))
	addConstFmt("nadd_le", defaultInfix("≤", "\\le"))
	addConstFmt("treal_add", defaultInfix("+", "+"))
	addConstFmt("treal_mul", defaultInfix("*", "\\times"))
	addConstFmt("treal_le", defaultInfix("≤", "\\le"))

	// Set-theory infix operators. The parser (ext/dsl/setops.go's
	// setOperator dispatch, wired at the relational/set-additive/set-
	// multiplicative precedence layers in parser.go) resolves the symbol
	// back to the named const meta, so print↔parse round-trips.
	// Under a polymorphic-const type conflict (collectConstConflicts),
	// formatConstTemplate skips these — the fallback annotated prefix
	// form (e.g. `set_member⟨A:num⟩(x, s)`) surfaces the type instance the infix
	// form would hide.
	addConstFmt("set_member", defaultInfix("∈", "\\in"))
	addConstFmt("subset", defaultInfix("⊆", "\\subseteq"))
	addConstFmt("proper_subset", defaultInfix("⊊", "\\subsetneq"))
	addConstFmt("union", defaultInfix("∪", "\\cup"))
	addConstFmt("intersection", defaultInfix("∩", "\\cap"))
	addConstFmt("set_difference", defaultInfix("∖", "\\setminus"))

	// Function composition. The template's arity is 2, so it fires on the
	// PARTIAL application a composition IS. An over-applied `o(f, g, x)`
	// misses it here and is caught by formatTermImpl's own branch, which
	// keeps the infix head and applies the rest — `(f ∘ g)(x)`. That is
	// not cosmetic: `o` is one of the few consts the DSL declines to seed
	// into scope by name, so the applied spelling reparses to a free
	// VARIABLE wherever `o` is undeclared, and the sugar never does.
	addConstFmt("o", defaultInfix("∘", "\\circ"))

	// Set-theory nullary polymorphic consts. Renders bare — Arity 0 so the
	// bare-value-position fallback (formatConstBase, line 414) does NOT
	// swap back to the ident name; both `∅` and its printed form always
	// appear at value positions. Under a polymorphic-const type conflict,
	// formatConst appends the standard `⟨A:T⟩` annotation, which the
	// parser accepts on the ∅/𝕌 tokens directly.
	addConstFmt("empty_set", _ConstTermFormat{Format: "∅", Latex: "\\varnothing"})
	addConstFmt("universe", _ConstTermFormat{Format: "𝕌", Latex: "\\mathbb{U}"})

	// Set-theory unary big-op prefixes. Arity-1 template — the arg comes
	// pre-bracketed only when compound (shouldBeBracketed), so `⋃s` /
	// `⋃(s ∪ t)` / `⋂s` all round-trip. Symbol-only (not ident-shaped)
	// so the bare-value fallback in formatConstBase doesn't apply.
	addConstFmt("big_union", _ConstTermFormat{
		FmtTempl: FmtTemplate{
			Arity:       1,
			FmtCallback: func(s ...string) string { return "⋃" + s[0] }},
		LatexTempl: FmtTemplate{
			Arity:       1,
			FmtCallback: func(s ...string) string { return "\\bigcup " + s[0] }},
	})
	addConstFmt("big_intersection", _ConstTermFormat{
		FmtTempl: FmtTemplate{
			Arity:       1,
			FmtCallback: func(s ...string) string { return "⋂" + s[0] }},
		LatexTempl: FmtTemplate{
			Arity:       1,
			FmtCallback: func(s ...string) string { return "\\bigcap " + s[0] }},
	})
}

// negPrefixFmt is the arity-1 unary-minus prefix template shared by real_neg
// and int_neg. The operand arrives already bracketed when compound
// (shouldBeBracketed), so the output is `-x` / `-(a + b)` — all valid after the
// parser's unary `-`.
// powInfix renders a power `base ^ exponent`. A compound operand arrives
// bracketed already (shouldBeBracketed: an infix-templated application,
// a λ, a quantifier); the one it leaves bare that the parser would
// misread is a prefix negation as the BASE — `-x ^ 2` parses as
// `-(x ^ 2)` (parser.go's parsePower) — so a base printed with a leading
// `-` is bracketed here. In LaTeX the exponent is set as a superscript.
func powInfix() _ConstTermFormat {
	return _ConstTermFormat{
		FmtTempl: FmtTemplate{
			Arity: 2,
			FmtCallback: func(s ...string) string {
				base := s[0]
				if strings.HasPrefix(base, "-") {
					base = "(" + base + ")"
				}
				return fmt.Sprintf("%s ^ %s", base, s[1])
			}},
		LatexTempl: FmtTemplate{
			Arity: 2,
			FmtCallback: func(s ...string) string {
				return fmt.Sprintf("{%s}^{%s}", s[0], s[1])
			}},
	}
}

func negPrefixFmt() _ConstTermFormat {
	return _ConstTermFormat{
		FmtTempl: FmtTemplate{
			Arity:       1,
			FmtCallback: func(s ...string) string { return "-" + s[0] }},
		LatexTempl: FmtTemplate{
			Arity:       1,
			FmtCallback: func(s ...string) string { return "-" + s[0] }},
	}
}

func init() { initConstFmt() }
