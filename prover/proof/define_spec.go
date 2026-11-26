// define_spec.go — the definition move's `spec:` shape: one or more
// constants introduced by CHOICE against a specification as
// a composite of the define family.
//
// The author states the SPECIFICATION — the characterizing statement,
// with the constants applied — and proves the POINTWISE existence
// obligation: at every point of the specification's ∀-prefix, some
// values satisfy it. Everything between those two surfaces is
// ceremony this file absorbs as a pure kernel derivation
// (deterministic, refuter-free — the equation compiler's discipline):
// Skolemize the closed obligation into function form by explicit
// Hilbert-ε witnesses, condition each constant's stored existence
// claim (name-tag binders, inner function-form existentials,
// pair-literal application arguments through the served fst/snd
// rows), and MP through the prop.ExistentialConstDef bridges in
// definition order; the last bridge's conclusion is the
// characterizing statement.
//
// Two provenances, one executor. A FRESH spec definition mints its
// constants here (nested tag-free ε payloads — c₁ := εf₁.∃f₂…∀x̄.B,
// c₂ := εf₂.∀x̄.B[c₁], …). An IMPORTED specification constant
// (nat_div/nat_mod, int_div/int_rem, int_gcd) already carries its tagged payload on
// the meta, and the compiler reads the STORED shape instead of
// assuming its own — which is what lets the corpus CLAIM the
// imported constants' definitions through the same door that mints
// fresh ones, retiring the hand-written ε-witness/StripQuant/name-tag
// ceremony at those sites.

package proof

import (
	"fmt"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// SpecFstName / SpecSndName are the library-theorem names the spec
// compiler reads the pair projections under when a constant is
// applied at a pair literal (int_gcd's genre) — served by the entries
// the member declares as typed deps (the pairs chapter's), the WF
// schema-row convention. SpecFstConst / SpecSndConst are the
// projection constants those rows are about.
const (
	SpecFstName  = "fst_of_pair"
	SpecSndName  = "snd_of_pair"
	SpecFstConst = "fst"
	SpecSndConst = "snd"
)

// SpecDefinition is the analyzed form of a spec definition: the
// characterizing GOAL (the specification at the constants) decomposed
// against the ordered constant list.
type SpecDefinition struct {
	// Consts are the spec-defined constants, in definition order (the
	// order their stored existence claims nest — the specification's
	// own chain).
	Consts []ConstTerm
	// Goal is the characterizing statement the section records.
	Goal Prop
	// Binders is the goal's ∀-prefix, in the author's order.
	Binders []VarTerm
	// Matrix is the goal under the prefix.
	Matrix Term
	// AppArgs[i] is the FIXED argument list constant i is applied at,
	// everywhere it occurs in Matrix (plain goal binders, or pair
	// literals of binders).
	AppArgs [][]Term
	// ValueVars[i] is the fresh value variable that replaces constant
	// i's application in the obligation.
	ValueVars []VarTerm
	// Obligation is the pointwise existence statement the composite
	// surfaces as its one child:
	//
	//	∀Binders. ∃ValueVars. Matrix[Consts[i](AppArgs[i]) := ValueVars[i]]
	Obligation Prop
}

// AnalyzeSpecGoal decomposes a characterizing statement against its
// ordered constant list and computes the pointwise obligation.
// Strict, repair-naming errors. It is
// the one analysis both provenances share: registration analyzes the
// parsed Spec text, and the ministep's apply re-analyzes the recorded
// goal, so replay recomputes the obligation deterministically from
// goal + payload alone.
func AnalyzeSpecGoal(goal Prop, consts []ConstTerm) (*SpecDefinition, error) {
	if goal == nil || len(consts) == 0 {
		return nil, fmt.Errorf("spec definition needs a statement and at least one constant")
	}
	if goal.NumHyps() != 0 {
		return nil, fmt.Errorf("a spec definition's statement must be hyp-free")
	}
	if len(goal.Conclusion().Frees(nil)) != 0 {
		return nil, fmt.Errorf(
			"a spec definition's statement must be closed — ∀-bind its variables")
	}
	binderList, matrix := DecomposesFORALL(goal.Conclusion())
	binders := make([]VarTerm, 0, binderList.Size())
	for v := range binderList.Iter() {
		binders = append(binders, v)
	}

	sd := &SpecDefinition{
		Consts:  consts,
		Goal:    goal,
		Binders: binders,
		Matrix:  matrix,
	}
	avoid := make([]Term, 0, len(binders)+len(consts))
	for _, b := range binders {
		avoid = append(avoid, b)
	}

	pointwise := matrix
	for _, c := range consts {
		args, err := uniformApplicationArgs(matrix, func(head Term) bool {
			hc, ok := head.AsConst()
			// Const identity is by META EQUALITY (name-keyed), not
			// pointer: the DSL's default-scope operator metas (nat_div, nat_mod)
			// are identity-equal to, but distinct pointers from, the
			// registered def-carrying metas the claim rides.
			return ok && hc.Meta().Equals(c.Meta())
		}, string(c.Name()))
		if err != nil {
			return nil, err
		}
		for _, a := range args {
			if err := validateSpecAppArg(a, binders); err != nil {
				return nil, fmt.Errorf("constant %q: %v", c.Name(), err)
			}
		}
		v := Var(TermName("v_"+sanitizeBinderName(string(c.Name()))),
			applicationResultType(c.Type(), len(args))).
			Core().(VarTerm).RenameToAvoid(avoid...)
		avoid = append(avoid, v)
		app := Apply(c, args...).Core()
		replaced, count := replaceTermEverywhere(pointwise, app, v)
		if count == 0 {
			return nil, fmt.Errorf(
				"constant %q does not occur applied in the specification", c.Name())
		}
		pointwise = replaced
		sd.AppArgs = append(sd.AppArgs, args)
		sd.ValueVars = append(sd.ValueVars, v)
	}
	// A constant surviving into the pointwise matrix would be an
	// occurrence outside the uniform application form.
	for i, c := range consts {
		if termMentionsConstMeta(pointwise, c) {
			return nil, fmt.Errorf(
				"constant %q occurs outside its application form %s — a spec "+
					"definition applies each constant one fixed way",
				c.Name(), PrintTerm(Apply(c, sd.AppArgs[i]...).Core()))
		}
	}

	obligation := pointwise
	for i := len(sd.ValueVars) - 1; i >= 0; i-- {
		obligation = Exists(WrapTerm(sd.ValueVars[i]))(WrapTerm(obligation)).Core()
	}
	for i := len(binders) - 1; i >= 0; i-- {
		obligation = ForAll(WrapTerm(binders[i]))(WrapTerm(obligation)).Core()
	}
	sd.Obligation = core.MakeProp(obligation)
	return sd, nil
}

// sanitizeBinderName keeps generated value-binder names printable for
// operator-named constants.
func sanitizeBinderName(name string) string {
	clean := strings.Map(func(r rune) rune {
		if r >= 'a' && r <= 'z' || r >= 'A' && r <= 'Z' || r >= '0' && r <= '9' || r == '_' {
			return r
		}
		return -1
	}, name)
	if clean == "" {
		return "c"
	}
	return clean
}

// applicationResultType peels argCount function-type steps off a
// type.
func applicationResultType(t HolType, argCount int) HolType {
	for range argCount {
		ct, ok := t.(CompositeType)
		if !ok || !ext.IsFunType(ct) {
			return t
		}
		t = ct.SubType(1)
	}
	return t
}

// uniformApplicationArgs finds the application spine of the head
// matched by isHead in the matrix and checks every occurrence shares
// ONE argument list. The matched head is never re-walked bare; its
// arguments are.
func uniformApplicationArgs(matrix Term, isHead func(Term) bool, name string) ([]Term, error) {
	var found []Term
	var walk func(t Term) error
	walk = func(t Term) error {
		if isHead(t) {
			return fmt.Errorf(
				"%q occurs unapplied in the statement — the spec shape defines "+
					"constants by their applied behavior", name)
		}
		if abs, ok := t.AsAbsTerm(); ok {
			return walk(abs.Body())
		}
		head, args := MatchesApply(t)
		if len(args) == 0 {
			return nil
		}
		if isHead(head) {
			if found == nil {
				found = args
			} else {
				if len(found) != len(args) {
					return fmt.Errorf(
						"%q is applied at two arities (%d vs %d) — a spec definition "+
							"applies each constant at ONE fixed argument form",
						name, len(found), len(args))
				}
				for i := range args {
					if !args[i].Equals(found[i]) {
						return fmt.Errorf(
							"%q is applied two different ways (…%s… vs …%s…) — a spec "+
								"definition applies each constant at ONE fixed argument form",
							name, PrintTerm(found[i]), PrintTerm(args[i]))
					}
				}
			}
			for _, a := range args {
				if err := walk(a); err != nil {
					return err
				}
			}
			return nil
		}
		if err := walk(head); err != nil {
			return err
		}
		for _, a := range args {
			if err := walk(a); err != nil {
				return err
			}
		}
		return nil
	}
	if err := walk(matrix); err != nil {
		return nil, err
	}
	if found == nil {
		return nil, fmt.Errorf("%q does not occur in the statement", name)
	}
	return found, nil
}

// validateSpecAppArg admits the v1 application-argument grammar: a
// goal binder, or a pair literal over admitted arguments (int_gcd's
// `(a, b)` genre).
func validateSpecAppArg(a Term, binders []VarTerm) error {
	if v, ok := a.AsVar(); ok {
		if slices.IndexFunc(binders, v.EqualsVar) < 0 {
			return fmt.Errorf(
				"application argument %q is not a ∀-binder of the statement",
				PrintTerm(a))
		}
		return nil
	}
	if l, r, ok := matchesPairLiteral(a); ok {
		if err := validateSpecAppArg(l, binders); err != nil {
			return err
		}
		return validateSpecAppArg(r, binders)
	}
	return fmt.Errorf(
		"application argument %q is neither a ∀-binder nor a pair of binders — "+
			"the v1 spec shape applies constants at binder tuples", PrintTerm(a))
}

// matchesPairLiteral matches `(l, r)` — the pair constructor applied
// to two arguments.
func matchesPairLiteral(t Term) (l, r Term, ok bool) {
	head, args := MatchesApply(t)
	hc, isConst := head.AsConst()
	if !isConst || len(args) != 2 || hc.Name() != ext.CommaConstMeta.Name() {
		return nil, nil, false
	}
	return args[0], args[1], true
}

// replaceTermEverywhere substitutes every occurrence of `from`
// (matched by Equals) by `to`, counting replacements. Capture cannot
// arise for the shapes analysis admits: `from` is a head applied at
// outer binders, and an inner binder shadowing one of them makes the
// inner occurrence a different term.
func replaceTermEverywhere(t, from, to Term) (Term, int) {
	if t.Equals(from) {
		return to, 1
	}
	if abs, ok := t.AsAbsTerm(); ok {
		b, n := replaceTermEverywhere(abs.Body(), from, to)
		if n == 0 {
			return t, 0
		}
		return Abs(abs.Var(), b), n
	}
	head, args := MatchesApply(t)
	if len(args) == 0 {
		return t, 0
	}
	total := 0
	newHead, n := replaceTermEverywhere(head, from, to)
	total += n
	newArgs := make([]Term, len(args))
	for i, a := range args {
		newArgs[i], n = replaceTermEverywhere(a, from, to)
		total += n
	}
	if total == 0 {
		return t, 0
	}
	return Apply(newHead, newArgs...).Core(), total
}

func termMentionsConstMeta(t Term, c ConstTerm) bool {
	if tc, ok := t.AsConst(); ok {
		return tc.Meta().Equals(c.Meta())
	}
	if abs, ok := t.AsAbsTerm(); ok {
		return termMentionsConstMeta(abs.Body(), c)
	}
	head, args := MatchesApply(t)
	if len(args) == 0 {
		return false
	}
	if termMentionsConstMeta(head, c) {
		return true
	}
	for _, a := range args {
		if termMentionsConstMeta(a, c) {
			return true
		}
	}
	return false
}

// ---------------------------------------------------------------------------
// The fresh mint — nested tag-free ε payloads
// ---------------------------------------------------------------------------

// ParseSpecStatement parses a spec-definition statement literal with
// every DEFINIENDUM declared as a variable of its stated type — the
// multi-constant ParseDefinitionEquation. Names and types are
// positional pairs; each name must be fresh in base. Both strict
// switches are forced on (the one-door invariant).
func ParseSpecStatement(specText string, names, typeTexts []string, base *dsl.ParseScope) (Prop, []VarTerm, error) {
	if len(names) == 0 || len(names) != len(typeTexts) {
		return nil, nil, fmt.Errorf("spec definition needs matching name/type lists")
	}
	var scope dsl.ParseScope
	if base != nil {
		scope = *base
	}
	vars := make(map[string]HolType, len(scope.Vars)+len(names))
	for k, v := range scope.Vars {
		vars[k] = v
	}
	defVars := make([]VarTerm, len(names))
	for i, name := range names {
		typ, err := dsl.ParseTypeTextInScope(typeTexts[i], base)
		if err != nil {
			return nil, nil, fmt.Errorf("definition type %q: %v", typeTexts[i], err)
		}
		if base != nil && scopeResolvesConst(base, name) {
			return nil, nil, fmt.Errorf(
				"define spec: %q already names a constant in scope — a definition "+
					"mints a FRESH name; pick another", name)
		}
		vars[name] = typ
		defVars[i] = Var(TermName(name), typ).Core().(VarTerm)
	}
	scope.Vars = vars
	scope.StrictResolution = true
	scope.StrictMint = true
	scope.FreshenMetaLetters = true

	res := dsl.ParsePropTextInScope(specText, &scope)
	if len(res.Errors) > 0 {
		return nil, nil, fmt.Errorf("parse spec statement: %s", res.Errors[0].Message)
	}
	return res.Prop, defVars, nil
}

// MintSpecDefinition performs the kernel mints for a fresh spec
// definition — the nested specification chain, tag-free:
//
//	c₁ := εf₁. ∃f₂…f_k. body
//	c₂ := εf₂. ∃f₃…f_k. body[f₁ := c₁]
//	…
//
// under the same exclusive registration as every define mint. The
// statement arrives in DEFINIENDUM-VARIABLE form; returns the minted
// constants (definition order) and the characterizing statement (the
// spec at the constants), UNPROVED — proving it is the definition
// section's job via the _DefineSpecStep executor.
func MintSpecDefinition(env *ProverEnv, specStmt Prop, defVars []VarTerm) ([]ConstTerm, Prop, error) {
	names := make([]TermName, len(defVars))
	for i, dv := range defVars {
		names[i] = dv.Name()
	}
	return MintSpecDefinitionAs(env, specStmt, defVars, names)
}

// MintSpecDefinitionAs is MintSpecDefinition minting the i-th constant
// under names[i] rather than its definiendum variable's own — the
// stand-in spelling case: a constant the text DSL keeps for its own
// surface (nat_div, nat_mod) is spelled by a stand-in in the specification
// and minted under its real name.
func MintSpecDefinitionAs(env *ProverEnv, specStmt Prop, defVars []VarTerm, names []TermName) ([]ConstTerm, Prop, error) {
	if specStmt == nil || len(defVars) == 0 || len(names) != len(defVars) {
		return nil, nil, fmt.Errorf("nil spec definition")
	}
	for _, v := range specStmt.Conclusion().Frees(nil) {
		if slices.IndexFunc(defVars, v.EqualsVar) < 0 {
			return nil, nil, fmt.Errorf(
				"spec statement has a free variable %q besides the definienda — "+
					"∀-bind it or fix the spelling", PrintTerm(v))
		}
	}

	consts := make([]ConstTerm, len(defVars))
	current := specStmt.Conclusion()
	for i, dv := range defVars {
		payload := current
		for j := len(defVars) - 1; j > i; j-- {
			payload = Exists(WrapTerm(defVars[j]))(WrapTerm(payload)).Core()
		}
		eps := WrapTerm(dv).SuchThat(WrapTerm(payload)).Core()
		c, err := mintDefinedConst(env, names[i], eps)
		if err != nil {
			return nil, nil, err
		}
		consts[i] = c
		current = current.Substitute(MakeTermSubst(dv, c))
	}
	return consts, core.MakeProp(current), nil
}

// ---------------------------------------------------------------------------
// The spec existence compiler — pure kernel derivation
// ---------------------------------------------------------------------------

// specClaimShape is the parsed prefix of one constant's stored
// existence claim (the ExistentialConstDef bridge's hypothesis):
//
//	∃f. ∀tags…. ∃g₁…g_j. ∀ȳ. matrix
//
// f is the constant's own function binder; tags are dead binders an
// imported specification threads through (absent on fresh
// mints) — classified by USE: a ∀-binder that vanishes under the
// pointwise value substitution reads nothing but the function
// applications; the g's are inner FUNCTION existentials (the later
// constants of a chain, function-form); ȳ are the point binders.
// When no ∃-group follows, tags and points share one ∀-run and the
// tags must lead it.
type specClaimShape struct {
	claim   Term
	fVar    VarTerm
	tags    []VarTerm
	gVars   []VarTerm
	binders []VarTerm
	matrix  Term
	// fnVars/fnApps: f then the g's, with each one's uniform
	// application argument list in the matrix.
	fnVars []VarTerm
	fnApps [][]Term
}

// parseSpecClaimShape decomposes a stored existence claim against the
// grammar above.
func parseSpecClaimShape(claim Term) (*specClaimShape, error) {
	s := &specClaimShape{claim: claim}
	abs := MatchesEXISTS(claim)
	if abs.IsZero() {
		return nil, fmt.Errorf("stored existence claim %q is not ∃-headed",
			PrintTerm(claim))
	}
	s.fVar = abs.Var()
	rest := abs.Body()

	var run1 []VarTerm
	for {
		fa := MatchesFORALL(rest)
		if fa.IsZero() {
			break
		}
		run1 = append(run1, fa.Var())
		rest = fa.Body()
	}
	for {
		ex := MatchesEXISTS(rest)
		if ex.IsZero() {
			break
		}
		s.gVars = append(s.gVars, ex.Var())
		rest = ex.Body()
	}
	var run2 []VarTerm
	for {
		fa := MatchesFORALL(rest)
		if fa.IsZero() {
			break
		}
		run2 = append(run2, fa.Var())
		rest = fa.Body()
	}
	s.matrix = rest

	s.fnVars = append([]VarTerm{s.fVar}, s.gVars...)
	for _, fv := range s.fnVars {
		args, err := uniformApplicationArgs(s.matrix, func(head Term) bool {
			hv, ok := head.AsVar()
			return ok && hv.EqualsVar(fv)
		}, string(fv.Name()))
		if err != nil {
			return nil, fmt.Errorf("stored existence claim: %v", err)
		}
		s.fnApps = append(s.fnApps, args)
	}

	// Classify run1/run2 by use. A binder is DEAD (a tag) when the
	// pointwise substitution removes every occurrence; live binders
	// are points. With an ∃-group present, run1 must be all-dead and
	// run2 all-live; without one, the dead binders must lead run1.
	pw := s.matrix
	for i, fv := range s.fnVars {
		app := Apply(fv, s.fnApps[i]...).Core()
		hole := Var(TermName(fmt.Sprintf("_spec_hole_%d", i)),
			applicationResultTypeOfVar(fv, len(s.fnApps[i]))).Core()
		pw, _ = replaceTermEverywhere(pw, app, hole)
	}
	dead := func(v VarTerm) bool { return !pw.HasFree(v) }
	if len(s.gVars) > 0 {
		for _, v := range run1 {
			if !dead(v) {
				return nil, fmt.Errorf(
					"stored existence claim: pre-∃ binder %q is read by the matrix — "+
						"unsupported claim shape", v.Name())
			}
		}
		for _, v := range run2 {
			if dead(v) {
				return nil, fmt.Errorf(
					"stored existence claim: point binder %q is dead — unsupported "+
						"claim shape", v.Name())
			}
		}
		s.tags, s.binders = run1, run2
	} else {
		if len(run2) != 0 {
			return nil, fmt.Errorf("internal: ∀-run after no ∃-group")
		}
		split := 0
		for split < len(run1) && dead(run1[split]) {
			split++
		}
		for _, v := range run1[split:] {
			if dead(v) {
				return nil, fmt.Errorf(
					"stored existence claim: dead binder %q follows a live one — "+
						"unsupported claim shape", v.Name())
			}
		}
		s.tags, s.binders = run1[:split], run1[split:]
	}
	return s, nil
}

func applicationResultTypeOfVar(f VarTerm, argCount int) HolType {
	return applicationResultType(f.Type(), argCount)
}

// pointwiseStatement builds the claim's pointwise reading —
// ∀points. ∃values. matrix[apps := values] — the arrangement-bridge
// target the running derivation state must reach before the
// ε-witness construction runs. Returns the statement and the value
// binders (fnVars order).
func (s *specClaimShape) pointwiseStatement() (Prop, []VarTerm, error) {
	avoid := make([]Term, 0, len(s.binders))
	for _, b := range s.binders {
		avoid = append(avoid, b)
	}
	pw := s.matrix
	values := make([]VarTerm, len(s.fnVars))
	for i, fv := range s.fnVars {
		v := Var(TermName("v_"+sanitizeBinderName(string(fv.Name()))),
			applicationResultTypeOfVar(fv, len(s.fnApps[i]))).
			Core().(VarTerm).RenameToAvoid(avoid...)
		avoid = append(avoid, v)
		app := Apply(fv, s.fnApps[i]...).Core()
		replaced, n := replaceTermEverywhere(pw, app, v)
		if n == 0 {
			return nil, nil, fmt.Errorf(
				"internal: claim binder %q's application vanished from the matrix",
				fv.Name())
		}
		pw = replaced
		values[i] = v
	}
	for _, fv := range s.fnVars {
		if pw.HasFree(fv) {
			return nil, nil, fmt.Errorf(
				"claim binder %q occurs outside its application form in the stored "+
					"claim — unsupported claim shape", fv.Name())
		}
	}
	for i := len(values) - 1; i >= 0; i-- {
		pw = Exists(WrapTerm(values[i]))(WrapTerm(pw)).Core()
	}
	for i := len(s.binders) - 1; i >= 0; i-- {
		pw = ForAll(WrapTerm(s.binders[i]))(WrapTerm(pw)).Core()
	}
	return core.MakeProp(pw), values, nil
}

// CompileSpecExistence derives the characterizing statement from the
// author's closed pointwise obligation — the spec compiler. env
// serves the fst/snd rows when a claim applies a constant at a pair
// literal (served by the entries the member declares as deps);
// otherwise no library rows are
// consumed. The result is P(c_k) in the last bridge's own
// arrangement; the ministep BridgeNormalizes it onto the recorded
// goal.
func CompileSpecExistence(env *ProverEnv, sd *SpecDefinition, obligation Prop) (Prop, error) {
	if obligation == nil {
		return nil, fmt.Errorf("nil obligation theorem")
	}
	cur := obligation
	for _, c := range sd.Consts {
		bridge := prop.ExistentialConstDef(c)
		if bridge.IsZero() || bridge.NumHyps() != 1 {
			return nil, fmt.Errorf(
				"constant %q does not carry a Hilbert-shape definition", c.Name())
		}
		shape, err := parseSpecClaimShape(bridge.Hyps()[0])
		if err != nil {
			return nil, fmt.Errorf("constant %q: %v", c.Name(), err)
		}
		pwStmt, values, err := shape.pointwiseStatement()
		if err != nil {
			return nil, fmt.Errorf("constant %q: %v", c.Name(), err)
		}
		pwCur, err := toPointwise(cur)
		if err != nil {
			return nil, fmt.Errorf("constant %q: %v", c.Name(), err)
		}
		bridged := BridgeNormalize(pwStmt, pwCur)
		if bridged == nil {
			return nil, fmt.Errorf(
				"the obligation is not normalize-equivalent to constant %q's stored "+
					"specification\n  have: %s\n  need: %s\n— re-arrange the statement "+
					"toward the stored form", c.Name(), PrintProp(pwCur),
				PrintProp(pwStmt))
		}
		claimThm, err := deriveShapedExistence(env, shape, len(values), bridged)
		if err != nil {
			return nil, fmt.Errorf("constant %q: %v", c.Name(), err)
		}
		hypProp := core.MakeProp(bridge.Hyps()[0])
		weakened := prop.WeakenTo(claimThm, hypProp)
		cur = WrapProp(bridge).DeriveHypFrom(weakened).Prop
	}
	return cur, nil
}

// toPointwise conditions the running derivation state into pointwise
// form: a ∀-headed state passes through (the obligation itself); a
// function-form state — ∃g's. ∀ȳ. M, the previous bridge's
// conclusion — has its functions chosen (Select), its points
// stripped, and its values re-∃-introduced at the chosen
// applications.
func toPointwise(cur Prop) (Prop, error) {
	if MatchesEXISTS(cur.Conclusion()).IsZero() {
		return cur, nil
	}
	var gVars []VarTerm
	rest := cur.Conclusion()
	for {
		ex := MatchesEXISTS(rest)
		if ex.IsZero() {
			break
		}
		gVars = append(gVars, ex.Var())
		rest = ex.Body()
	}
	binderList, matrix := DecomposesFORALL(rest)
	var binders []VarTerm
	for v := range binderList.Iter() {
		binders = append(binders, v)
	}
	gApps := make([][]Term, len(gVars))
	for i, g := range gVars {
		args, err := uniformApplicationArgs(matrix, func(head Term) bool {
			hv, ok := head.AsVar()
			return ok && hv.EqualsVar(g)
		}, string(g.Name()))
		if err != nil {
			return nil, err
		}
		gApps[i] = args
	}

	// Select each function in order, tracking the running ∃-spine so
	// each ε-term is spelled against the already-chosen predecessors.
	w := WrapProp(cur)
	chosen := make([]Term, len(gVars))
	spine := cur.Conclusion()
	for i, g := range gVars {
		ex := MatchesEXISTS(spine)
		if ex.IsZero() || !ex.Var().EqualsVar(g) {
			return nil, fmt.Errorf("internal: Select walk lost the ∃-spine")
		}
		lambda := Abs(ex.Var(), ex.Body())
		w = w.DeriveTrans(prop.SelectExists(lambda))
		eps := core.Hilbert(ex.Var(), ex.Body())
		chosen[i] = eps
		spine = ex.Body().Substitute(MakeTermSubst(g, eps))
	}
	stripped, freed := w.StripConclForAll()
	if len(freed) != len(binders) {
		return nil, fmt.Errorf("internal: point strip freed %d of %d binders",
			len(freed), len(binders))
	}
	renames := make([]TermSubst, 0, len(binders))
	for i, b := range binders {
		if !freed[i].EqualsVar(b) {
			renames = append(renames, MakeTermSubst(b, freed[i]))
		}
	}
	atFreed := func(t Term) Term {
		if len(renames) == 0 {
			return t
		}
		return t.Substitute(renames...)
	}

	// Re-∃-introduce values at the chosen applications, innermost
	// first, then re-∀-close the points.
	target := stripped.Conclusion()
	avoid := make([]Term, 0, len(freed))
	for _, f := range freed {
		avoid = append(avoid, f)
	}
	values := make([]VarTerm, len(gVars))
	chosenApps := make([]Term, len(gVars))
	for i, g := range gVars {
		values[i] = Var(TermName("v_"+sanitizeBinderName(string(g.Name()))),
			applicationResultTypeOfVar(g, len(gApps[i]))).
			Core().(VarTerm).RenameToAvoid(avoid...)
		avoid = append(avoid, values[i])
		args := make([]Term, len(gApps[i]))
		for j, a := range gApps[i] {
			args[j] = atFreed(a)
		}
		chosenApps[i] = Apply(chosen[i], args...).Core()
	}
	for i := len(gVars) - 1; i >= 0; i-- {
		replaced, n := replaceTermEverywhere(target, chosenApps[i], values[i])
		if n == 0 {
			return nil, fmt.Errorf(
				"internal: chosen application %q not found while re-introducing values",
				PrintTerm(chosenApps[i]))
		}
		exStmt := Exists(WrapTerm(values[i]))(WrapTerm(replaced)).Core()
		stripped = stripped.DeriveTrans(prop.InstExists(exStmt, chosenApps[i]))
		target = exStmt
	}
	return stripped.ConclForAllList(freed...).Prop, nil
}

// deriveShapedExistence derives one stored existence claim from the
// arrangement-bridged pointwise theorem: choose every value by ε at
// the point (the Select chain), wrap the chosen terms into the
// claim's function witnesses (tag slots absorbed, pair-literal slots
// unpacked through fst/snd), β/pair-reduce the witness instance back
// onto the chosen form, and re-assemble the claim's quantifier
// prefix — ∀points, ∃g's at their witnesses, ∀tags, ∃f at its
// witness.
func deriveShapedExistence(env *ProverEnv, shape *specClaimShape, valueCount int, pw Prop) (Prop, error) {
	stripped, freed := WrapProp(pw).StripConclForAll()
	if len(freed) != len(shape.binders) {
		return nil, fmt.Errorf("internal: obligation freed %d of %d point binders",
			len(freed), len(shape.binders))
	}

	chosen := make([]Term, 0, valueCount)
	spine := stripped.Conclusion()
	for range valueCount {
		ex := MatchesEXISTS(spine)
		if ex.IsZero() {
			return nil, fmt.Errorf("internal: Select chain expected ∃, got %q",
				PrintTerm(spine))
		}
		lambda := Abs(ex.Var(), ex.Body())
		stripped = stripped.DeriveTrans(prop.SelectExists(lambda))
		eps := core.Hilbert(ex.Var(), ex.Body())
		chosen = append(chosen, eps)
		spine = ex.Body().Substitute(MakeTermSubst(ex.Var(), eps))
	}
	if len(chosen) != len(shape.fnVars) {
		return nil, fmt.Errorf("internal: %d chosen values for %d claim functions",
			len(chosen), len(shape.fnVars))
	}
	// stripped: ⊢ matrix-pointwise[values := chosen ε-terms], freed
	// points free.

	pairs, err := newSpecPairRows(env, shape)
	if err != nil {
		return nil, err
	}

	// Function witnesses: wᵢ λ-abstracts the claim's argument slots —
	// tag slots dead, data slots unpacked into the ε-term's point
	// variables (pair literals through fst/snd of the slot).
	pointIndex := func(v VarTerm) int {
		return slices.IndexFunc(shape.binders, v.EqualsVar)
	}
	tagSet := make(map[string]bool, len(shape.tags))
	for _, t := range shape.tags {
		tagSet[string(t.Name())] = true
	}
	witnesses := make([]Term, len(shape.fnVars))
	avoid := make([]Term, 0, len(freed)+len(chosen))
	for _, f := range freed {
		avoid = append(avoid, f)
	}
	avoid = append(avoid, chosen...)
	for i := range shape.fnVars {
		args := shape.fnApps[i]
		lamVars := make([]VarTerm, len(args))
		var slotSubst []TermSubst
		for j, a := range args {
			z := Var(TermName(fmt.Sprintf("z%d", j)), a.Type()).
				Core().(VarTerm).RenameToAvoid(avoid...)
			avoid = append(avoid, z)
			lamVars[j] = z
			if v, ok := a.AsVar(); ok && tagSet[string(v.Name())] {
				continue // dead slot — nothing reads it
			}
			subst, err := unpackSlot(a, z, pointIndex, freed, pairs)
			if err != nil {
				return nil, err
			}
			slotSubst = append(slotSubst, subst...)
		}
		wBody := chosen[i]
		covered := make(map[string]bool, len(slotSubst))
		for _, s := range slotSubst {
			covered[string(s.VarTerm.Name())] = true
		}
		for _, fr := range wBody.Frees(nil) {
			if slices.IndexFunc(freed, fr.EqualsVar) >= 0 && !covered[string(fr.Name())] {
				return nil, fmt.Errorf(
					"the application of %q does not determine point %q — every "+
						"specification point must appear in the application arguments",
					shape.fnVars[i].Name(), fr.Name())
			}
		}
		if len(slotSubst) > 0 {
			wBody = wBody.Substitute(slotSubst...)
		}
		for j := len(lamVars) - 1; j >= 0; j-- {
			wBody = Abs(lamVars[j], wBody)
		}
		witnesses[i] = wBody
	}

	// The target instance: the claim's matrix at the witnesses and
	// the freed points; equal to the chosen form after β +
	// pair-projection computation.
	inst := shape.matrix
	for i, fv := range shape.fnVars {
		inst = inst.Substitute(MakeTermSubst(fv, witnesses[i]))
	}
	pointSubst := make([]TermSubst, 0, len(freed))
	for i, b := range shape.binders {
		if !b.EqualsVar(freed[i]) {
			pointSubst = append(pointSubst, MakeTermSubst(b, freed[i]))
		}
	}
	if len(pointSubst) > 0 {
		inst = inst.Substitute(pointSubst...)
	}
	reduce := DeepBeta
	if pairs != nil {
		reduce = prop.DeepRewrite(DeepBeta, pairs.rewrite)
	}
	instEq := reduce(inst)
	want := stripped.Conclusion()
	if instEq == nil || !Rhs(instEq.Prop).AlphaEquals(want) {
		got := "(no reduction)"
		if instEq != nil {
			got = PrintTerm(Rhs(instEq.Prop))
		}
		return nil, fmt.Errorf(
			"internal: witness instance did not reduce onto the chosen form\n"+
				"  instance: %s\n  reduced:  %s\n  chosen:   %s",
			PrintTerm(inst), got, PrintTerm(want))
	}
	derived := instEq.EqSym().EqMP(stripped)

	// Reassemble the prefix.
	derived = derived.ConclForAllList(freed...)
	exF := MatchesEXISTS(shape.claim)
	underF := exF.Body().Substitute(MakeTermSubst(shape.fVar, witnesses[0]))
	cursor := underF
	for range shape.tags {
		fa := MatchesFORALL(cursor)
		if fa.IsZero() {
			return nil, fmt.Errorf("internal: tag spine mismatch")
		}
		cursor = fa.Body()
	}
	gSpines := make([]Term, len(shape.gVars))
	for i := range shape.gVars {
		gSpines[i] = cursor
		ex := MatchesEXISTS(cursor)
		if ex.IsZero() {
			return nil, fmt.Errorf("internal: g spine mismatch")
		}
		cursor = ex.Body().Substitute(MakeTermSubst(shape.gVars[i], witnesses[i+1]))
	}
	for i := len(shape.gVars) - 1; i >= 0; i-- {
		derived = derived.DeriveTrans(prop.InstExists(gSpines[i], witnesses[i+1]))
	}
	if len(shape.tags) > 0 {
		derived = derived.ConclForAllList(shape.tags...)
	}
	derived = derived.DeriveTrans(prop.InstExists(shape.claim, witnesses[0]))
	return derived.Prop, nil
}

// unpackSlot maps one application argument onto the fresh λ-slot
// variable: a plain point yields freed-point := z; a pair literal
// yields its components := fst(z)/snd(z) recursively.
func unpackSlot(arg Term, z Term, pointIndex func(VarTerm) int, freed []VarTerm, pairs *specPairRows) ([]TermSubst, error) {
	if v, ok := arg.AsVar(); ok {
		idx := pointIndex(v)
		if idx < 0 {
			return nil, fmt.Errorf(
				"application argument %q is not a specification point", v.Name())
		}
		return []TermSubst{MakeTermSubst(freed[idx], z)}, nil
	}
	if l, r, ok := matchesPairLiteral(arg); ok {
		if pairs == nil {
			return nil, fmt.Errorf(
				"internal: pair-literal slot with no projection rows loaded")
		}
		fst, snd, err := pairs.projections(arg.Type())
		if err != nil {
			return nil, err
		}
		ls, err := unpackSlot(l, Apply(fst, z).Core(), pointIndex, freed, pairs)
		if err != nil {
			return nil, err
		}
		rs, err := unpackSlot(r, Apply(snd, z).Core(), pointIndex, freed, pairs)
		if err != nil {
			return nil, err
		}
		return append(ls, rs...), nil
	}
	return nil, fmt.Errorf("unsupported application argument %q", PrintTerm(arg))
}

// specPairRows carries the served fst/snd rows conditioned for the
// compiler — needed exactly when a claim applies a constant at a
// pair literal.
type specPairRows struct {
	fst, snd *prop.PropWrapper // fst((x,y)) = x / snd((x,y)) = y, x y free
}

// newSpecPairRows loads and conditions the projection rows when the
// shape needs them; nil otherwise.
func newSpecPairRows(env *ProverEnv, shape *specClaimShape) (*specPairRows, error) {
	needed := false
	for _, args := range shape.fnApps {
		for _, a := range args {
			if _, _, ok := matchesPairLiteral(a); ok {
				needed = true
			}
		}
	}
	if !needed {
		return nil, nil
	}
	if env == nil {
		return nil, fmt.Errorf(
			"pair-literal application arguments need the served %s/%s rows — no env",
			SpecFstName, SpecSndName)
	}
	load := func(name, projection string) (*prop.PropWrapper, error) {
		thm, ok := env.LookupLibraryThm(name)
		if !ok {
			return nil, fmt.Errorf(
				"library theorem %q is not bound — declare the entry serving it in Deps", name)
		}
		w, _ := WrapProp(thm).StripConclForAll()
		l, r, ok := MatchesEQ(w.Conclusion())
		if !ok {
			return nil, fmt.Errorf("served %s row is not an equation", name)
		}
		isProj := func(t Term) bool {
			head, args := MatchesApply(t)
			hc, isConst := head.AsConst()
			return isConst && len(args) == 1 && string(hc.Name()) == projection
		}
		switch {
		case isProj(l):
			return w, nil
		case isProj(r):
			return w.EqSym(), nil
		}
		return nil, fmt.Errorf("served %s row has no projection side", name)
	}
	fst, err := load(SpecFstName, SpecFstConst)
	if err != nil {
		return nil, err
	}
	snd, err := load(SpecSndName, SpecSndConst)
	if err != nil {
		return nil, err
	}
	return &specPairRows{fst: fst, snd: snd}, nil
}

// row returns the conditioned row for a projection name, nil for any
// other head.
func (p *specPairRows) row(name TermName) *prop.PropWrapper {
	switch string(name) {
	case SpecFstConst:
		return p.fst
	case SpecSndConst:
		return p.snd
	}
	return nil
}

// projections builds the fst/snd const instances at a pair type,
// sharing the served rows' metas so term identity holds.
func (p *specPairRows) projections(pairType HolType) (fst, snd Term, err error) {
	inst := func(w *prop.PropWrapper) (Term, error) {
		l, _, _ := MatchesEQ(w.Conclusion())
		head, args := MatchesApply(l)
		hc, _ := head.AsConst()
		pl, pr, ok := matchesPairLiteral(args[0])
		if !ok {
			return nil, fmt.Errorf("internal: projection row lost its pair literal")
		}
		substs, okM := MakeProdType(pl.Type(), pr.Type()).
			Matches(pairType, func(core.VarType) bool { return true })
		if !okM {
			return nil, fmt.Errorf("projection row cannot instantiate at %s",
				FormatType(pairType))
		}
		return MakeConstTerm(hc.Meta(), hc.Type().Substitute(substs...)), nil
	}
	f, err := inst(p.fst)
	if err != nil {
		return nil, nil, err
	}
	s, err := inst(p.snd)
	if err != nil {
		return nil, nil, err
	}
	return f, s, nil
}

// rewrite is the projection-computation Rewrite: fst((l,r)) → l,
// snd((l,r)) → r, by the served rows type- and term-instantiated at
// the literal.
func (p *specPairRows) rewrite(t Term) *prop.PropWrapper {
	head, args := MatchesApply(t)
	hc, ok := head.AsConst()
	if !ok || len(args) != 1 {
		return nil
	}
	row := p.row(hc.Name())
	if row == nil {
		return nil
	}
	l, r, isPair := matchesPairLiteral(args[0])
	if !isPair {
		return nil
	}
	rowL, _, _ := MatchesEQ(row.Conclusion())
	_, rowArgs := MatchesApply(rowL)
	pl, pr, ok := matchesPairLiteral(rowArgs[0])
	if !ok {
		return nil
	}
	plVar, okL := pl.AsVar()
	prVar, okR := pr.AsVar()
	if !okL || !okR {
		return nil
	}
	substs, okM := MakeProdType(plVar.Type(), prVar.Type()).
		Matches(args[0].Type(), func(core.VarType) bool { return true })
	if !okM {
		return nil
	}
	instRow := row.TypeInst(substs...)
	rowLi, _, _ := MatchesEQ(instRow.Conclusion())
	_, rowArgsI := MatchesApply(rowLi)
	pli, pri, ok := matchesPairLiteral(rowArgsI[0])
	if !ok {
		return nil
	}
	plv, _ := pli.AsVar()
	prv, _ := pri.AsVar()
	return instRow.TermInst(MakeTermSubst(plv, l), MakeTermSubst(prv, r))
}
