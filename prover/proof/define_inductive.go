// define_inductive.go — the inductive-definition move's analysis, mint
// and derivation spine (Isabelle's
// `inductive`): what the session `define` RPC's `inductive:` payload,
// the chapter door family.DefineInductive and the _DefineInductiveStep
// composite (step_define.go) share, the way define_data.go serves the
// datatype move and define_type.go the type definition.
//
// An inductive definition is a RULE SET for one predicate R over
// declared parameters p̄ and indices x̄:
//
//	∀v̄. H₁ ∧ … ∧ Hₖ ⇒ R(p̄, t̄)        (or ∀v̄. R(p̄, t̄), unconditional)
//
// where every Hᵢ is either R-free (a side condition) or POSITIVE —
// `∀ū. G ⇒ R(p̄, s̄)` with G R-free, the ∀ and the guard each optional.
// That fragment is the door's first charter: it covers a bare recursive
// premise (finite, is_num), a premise under ∀ (is_recspace's `∀n.
// Z(r(n))`), a guarded one (accessibility's `∀y. R(y, x) ⇒ Acc(R, y)`)
// and a parameterized relation with two premises (transitive closure).
// Mutual definitions and premises with R under ∃ / ∨ / ¬ are refused
// by name; they are the fragment's next slice, not this one.
//
// R is minted as the SMALLEST relation closed under the rules — the
// closure form:
//
//	R = λp̄. λx̄. ∀R'. (∀ā. D₁(ā) ∨ … ∨ Dₘ(ā) ⇒ R'(ā)) ⇒ R'(x̄)
//
// with one canonical disjunct per rule, `Dⱼ(ā) = ∃w̄. ā = t̄ ∧ Hs[R']`
// where an index whose argument is a rule variable is substituted away
// rather than equated (`TC R x y` reads
// `R(a₀, a₁)`, not `∃x y. a₀ = x ∧ a₁ = y ∧ R(x, y)`).
//
// The three theorems a definition comes with are derived from that
// body by kernel rules alone — deterministic, refuter-free,
// close-or-fail, the datatype kit's discipline:
//
//	Rules         ∀p̄. rule₁ ∧ … ∧ ruleₘ                    (the rule set verbatim)
//	Induct        ∀p̄ P x̄. rules[P] ∧ R(p̄, x̄) ⇒ P(x̄)      (weak rule induction)
//	Cases         ∀p̄. ∀ā. R(p̄, ā) ⇔ D₁(ā) ∨ … ∨ Dₘ(ā)      (with R for R')
//	InductStrong  ∀p̄ P x̄. rules⁺[P] ∧ R(p̄, x̄) ⇒ P(x̄)     (each recursive premise R ∧ P)
//
// The two inductions are in the standard form, every binder in front:
// the rules at P, one hypothesis each, then the guard R(p̄, x̄).
// Induct is the closure read at P: its hypothesis rules[P] says P is
// closed, and the case analysis over the disjunction is the whole
// proof. Rules needs the premises MONOTONE in R, which the positive
// fragment makes a fixed recipe (∀-intro, ⇒-intro, ∧). Cases is Rules read
// backwards and Induct read at the disjunction predicate. InductStrong
// is Induct at λx̄. R(p̄, x̄) ∧ P(x̄) fed Rules; the door mints it only
// where some rule has a premise to strengthen.
//
// The rules are the definition's identity: the closure body does not
// determine them (a substituted index equation and a premise equation
// read alike), so they ride the composite's record beside the constant
// — the WF measure's precedent — and the analysis is re-run on them at
// every replay, checked against the minted body.

package proof

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// InductivePremise is one conjunct of a rule's antecedent.
type InductivePremise struct {
	// Side is an R-free conjunct, kept verbatim; nil for a positive
	// premise.
	Side Term
	// A positive premise ∀Vars. Guard ⇒ R(p̄, Args): Vars and Guard are
	// each optional (nil / empty).
	Vars  []VarTerm
	Guard Term
	Args  []Term
}

// Positive reports whether the premise mentions the relation.
func (pr *InductivePremise) Positive() bool { return pr.Side == nil }

// inductiveAnt is a rule's antecedent as the ∧-tree the author wrote
// (the DSL associates ∧ to the left; the tree keeps whatever the text
// said), leaves being premises.
type inductiveAnt struct {
	leaf        *InductivePremise
	left, right *inductiveAnt
}

// leaves lists the tree's premises in order.
func (a *inductiveAnt) leaves() []*InductivePremise {
	if a == nil {
		return nil
	}
	if a.leaf != nil {
		return []*InductivePremise{a.leaf}
	}
	return append(a.left.leaves(), a.right.leaves()...)
}

// InductiveRule is one analyzed rule.
type InductiveRule struct {
	// Vars are the rule's ∀-binders in stated order.
	Vars []VarTerm
	// Ant is the antecedent tree; nil for an unconditional rule.
	Ant *inductiveAnt
	// Args are the conclusion's index arguments t̄.
	Args []Term
	// substituted[i] is the rule variable index i is identified with in
	// the canonical disjunct (its argument is that variable, first
	// occurrence), or nil when the disjunct keeps the equation aᵢ = tᵢ.
	substituted []VarTerm
	// bound are the disjunct's ∃-binders: Vars minus the substituted
	// ones, in Vars order.
	bound []VarTerm
}

// InductiveDefinition is the analyzed form of one inductive
// definition: the rule set, the closure body the mint stores, and the
// canonical pieces the derivations read.
type InductiveDefinition struct {
	// DefVar is the definiendum as the variable the rules are stated
	// with — the pre-mint spelling, the wire form of each rule.
	DefVar VarTerm
	// Params are the declared parameters, the leading arguments of
	// every R-application.
	Params []VarTerm
	// IndexTypes are the remaining argument types.
	IndexTypes []HolType
	// Rules are the analyzed rules; RuleTerms their stated terms
	// (closed but for DefVar and Params).
	Rules     []InductiveRule
	RuleTerms []Term
	// Body is the closure λ the mint stores as R's definition.
	Body Term

	// subject ā: the canonical index variables; rel R': the bound
	// relation of the closure, over the indices alone.
	subject []VarTerm
	rel     VarTerm
	// disjuncts[j] is Dⱼ(ā) at R'; disjunction their left-nested ∨.
	disjuncts   []Term
	disjunction Term
}

// InductiveTheoremKind names the three derived theorems, in canonical
// order.
type InductiveTheoremKind int

const (
	InductiveRules InductiveTheoremKind = iota
	InductiveInduct
	InductiveCases
	// InductiveInductStrong is the strengthened rule induction: each
	// rule's recursive premises carry the relation ALONGSIDE the
	// property. It exists only when some rule has a positive premise —
	// with none, strengthening changes nothing and the statement is
	// Induct's own (InductiveDefinition.Kinds).
	InductiveInductStrong
)

func (k InductiveTheoremKind) String() string {
	switch k {
	case InductiveRules:
		return "rules"
	case InductiveInduct:
		return "induction"
	case InductiveCases:
		return "cases"
	case InductiveInductStrong:
		return "induction_strong"
	}
	return fmt.Sprintf("InductiveTheoremKind(%d)", int(k))
}

// InductiveKinds lists every kind in canonical order — the vocabulary,
// not one definition's output (see InductiveDefinition.Kinds).
func InductiveKinds() []InductiveTheoremKind {
	return []InductiveTheoremKind{InductiveRules, InductiveInduct, InductiveCases, InductiveInductStrong}
}

// Kinds lists the theorems THIS definition comes with, in canonical
// order. Every definition has its rules, its induction principle and
// its case analysis; the strengthened induction is there only when
// some rule has a positive premise to strengthen — with none it IS the
// plain induction, and two entries would carry one key.
func (d *InductiveDefinition) Kinds() []InductiveTheoremKind {
	out := []InductiveTheoremKind{InductiveRules, InductiveInduct, InductiveCases}
	if d.hasPositivePremise() {
		out = append(out, InductiveInductStrong)
	}
	return out
}

// hasPositivePremise reports whether any rule mentions the relation in
// a premise — what strengthening has to act on.
func (d *InductiveDefinition) hasPositivePremise() bool {
	for j := range d.Rules {
		for _, pr := range d.Rules[j].Ant.leaves() {
			if pr.Positive() {
				return true
			}
		}
	}
	return false
}

// EntrySuffix is the registered-name suffix a chapter door gives the
// kind's entry (<Name>Rules / <Name>Induct / <Name>Cases).
func (k InductiveTheoremKind) EntrySuffix() string {
	switch k {
	case InductiveRules:
		return "Rules"
	case InductiveInduct:
		return "Induct"
	case InductiveCases:
		return "Cases"
	case InductiveInductStrong:
		return "InductStrong"
	}
	panic(fmt.Sprintf("InductiveTheoremKind.EntrySuffix: unknown kind %v", k))
}

// PrincipleName is the theorem's library name (finite_rules,
// finite_induction, finite_cases).
func (d *InductiveDefinition) PrincipleName(k InductiveTheoremKind) string {
	return string(d.DefVar.Name()) + "_" + k.String()
}

// ParseInductiveRule reads one rule's text with the definiendum
// declared as a variable at typeText and each parameter as a variable
// at its slot of that type, both strict switches on — the definition
// equation's discipline (ParseDefinitionEquation). Returns the rule as
// a hyp-free Prop, the definiendum variable and the parameter
// variables.
func ParseInductiveRule(ruleText, name, typeText string, params []string, base *dsl.ParseScope) (Prop, VarTerm, []VarTerm, error) {
	typ, err := dsl.ParseTypeTextInScope(typeText, base)
	if err != nil {
		return nil, VarTerm{}, nil, fmt.Errorf("definition type %q: %v", typeText, err)
	}
	if base != nil && scopeResolvesConst(base, name) {
		return nil, VarTerm{}, nil, fmt.Errorf(
			"define inductive: %q already names a constant in scope — a definition mints a "+
				"FRESH name; pick another", name)
	}
	paramVars, err := inductiveParamVars(typ, params)
	if err != nil {
		return nil, VarTerm{}, nil, err
	}
	var scope dsl.ParseScope
	if base != nil {
		scope = *base
	}
	vars := make(map[string]HolType, len(scope.Vars)+1+len(params))
	for k, v := range scope.Vars {
		vars[k] = v
	}
	vars[name] = typ
	for _, p := range paramVars {
		if _, taken := vars[string(p.Name())]; taken && string(p.Name()) != name {
			// A parameter shadowing a scope variable is the author's;
			// only the definiendum's own name is refused.
		}
		vars[string(p.Name())] = p.Type()
	}
	scope.Vars = vars
	scope.StrictResolution = true
	scope.StrictMint = true
	scope.FreshenMetaLetters = true

	res := dsl.ParsePropTextInScope(ruleText, &scope)
	if len(res.Errors) > 0 {
		return nil, VarTerm{}, nil, fmt.Errorf("parse rule %q: %s", ruleText, res.Errors[0].Message)
	}
	defVar := Var(TermName(name), typ).Core().(VarTerm)
	return res.Prop, defVar, paramVars, nil
}

// inductiveParamVars types the declared parameter names off the
// leading argument slots of the definiendum's type.
func inductiveParamVars(typ HolType, params []string) ([]VarTerm, error) {
	argTypes, result := funTypeParts(typ)
	if !result.Equals(TypeBool) {
		return nil, fmt.Errorf("define inductive: the type %s does not end in bool — an inductive "+
			"definition defines a predicate", ext.FormatType(typ))
	}
	if len(params) >= len(argTypes) {
		return nil, fmt.Errorf("define inductive: %d parameter(s) declared but the type %s has %d "+
			"argument(s) — at least one index is required", len(params), ext.FormatType(typ), len(argTypes))
	}
	out := make([]VarTerm, len(params))
	seen := map[string]bool{}
	for i, p := range params {
		if p == "" || seen[p] {
			return nil, fmt.Errorf("define inductive: parameter %d (%q) is empty or repeated", i, p)
		}
		seen[p] = true
		out[i] = Var(TermName(p), argTypes[i]).Core().(VarTerm)
	}
	return out, nil
}

// AnalyzeInductiveDefinition reads a rule set against the definiendum
// variable and the declared parameters: every rule's shape is checked
// against the positive fragment, the canonical disjuncts are computed,
// and the closure body is built. Pure analysis, no mint.
func AnalyzeInductiveDefinition(defVar VarTerm, params []VarTerm, rules []Prop) (*InductiveDefinition, error) {
	if len(rules) == 0 {
		return nil, fmt.Errorf("define inductive: at least one rule is required")
	}
	argTypes, result := funTypeParts(defVar.Type())
	if !result.Equals(TypeBool) || len(params) >= len(argTypes) {
		return nil, fmt.Errorf("define inductive: %s : %s is not a predicate with at least one index "+
			"beyond its %d parameter(s)", defVar.Name(), ext.FormatType(defVar.Type()), len(params))
	}
	for i, p := range params {
		if !p.Type().Equals(argTypes[i]) {
			return nil, fmt.Errorf("define inductive: parameter %s : %s does not match argument slot %d "+
				"of %s (%s)", p.Name(), ext.FormatType(p.Type()), i, defVar.Name(), ext.FormatType(argTypes[i]))
		}
	}
	d := &InductiveDefinition{
		DefVar:     defVar,
		Params:     params,
		IndexTypes: argTypes[len(params):],
	}
	// Everything the fresh names below must stay clear of: the rules,
	// the parameters, the definiendum.
	avoid := []Term{defVar}
	for _, p := range params {
		avoid = append(avoid, p)
	}
	for i, r := range rules {
		if r.NumHyps() != 0 {
			return nil, fmt.Errorf("define inductive: rule %d carries hypotheses", i)
		}
		if !core.IsBool(r.Conclusion()) {
			return nil, fmt.Errorf("define inductive: rule %d is not a proposition", i)
		}
		avoid = append(avoid, r.Conclusion())
	}
	for i, r := range rules {
		rule, err := d.analyzeRule(r.Conclusion())
		if err != nil {
			return nil, fmt.Errorf("define inductive: rule %d (%s): %v", i, PrintTerm(r.Conclusion()), err)
		}
		d.Rules = append(d.Rules, *rule)
		d.RuleTerms = append(d.RuleTerms, r.Conclusion())
	}

	// The canonical subject ā and the closure's bound relation R'.
	d.subject = make([]VarTerm, len(d.IndexTypes))
	for i, t := range d.IndexTypes {
		v := Var(TermName(fmt.Sprintf("a%d", i)), t).Core().(VarTerm).RenameToAvoid(avoid...)
		d.subject[i] = v
		avoid = append(avoid, v)
	}
	d.rel = Var(defVar.Name()+"'", funTypeOf(d.IndexTypes, TypeBool)).Core().(VarTerm).RenameToAvoid(avoid...)
	avoid = append(avoid, d.rel)

	// The canonical disjuncts at ā and R'. A rule's ∃-binders are its
	// own variables, which the subject and the relation were renamed
	// clear of, so no capture is possible here; instantiations at other
	// subjects go through the kernel's capture-avoiding Substitute.
	subjectTerms := termsOf(d.subject)
	for j := range d.Rules {
		disjunct, err := d.disjunctOf(j, subjectTerms, d.rel)
		if err != nil {
			return nil, fmt.Errorf("define inductive: rule %d: %v", j, err)
		}
		d.disjuncts = append(d.disjuncts, disjunct)
	}
	d.disjunction = d.disjuncts[0]
	for _, dj := range d.disjuncts[1:] {
		d.disjunction = WrapTerm(d.disjunction).Or(dj).Core()
	}

	// Each stated rule must be what the analysis rebuilds from its
	// pieces: the statements the door signs are rebuilt, never the
	// author's text re-read, so an unfaithful analysis fails here.
	for j := range d.Rules {
		rebuilt := d.ruleAt(j, defVar, termsOf(params))
		if !rebuilt.AlphaEquals(d.RuleTerms[j]) {
			return nil, fmt.Errorf("define inductive: rule %d rebuilds as %s, not as stated (%s) — "+
				"report this shape", j, PrintTerm(rebuilt), PrintTerm(d.RuleTerms[j]))
		}
	}

	// The closure body: λp̄. λx̄. ∀R'. closed(R') ⇒ R'(x̄).
	xs := make([]VarTerm, len(d.IndexTypes))
	for i, t := range d.IndexTypes {
		v := Var(TermName(fmt.Sprintf("x%d", i)), t).Core().(VarTerm).RenameToAvoid(avoid...)
		xs[i] = v
		avoid = append(avoid, v)
	}
	body := WrapTerm(d.closedAt(d.rel)).Imply(Apply(d.rel, termsOf(xs)...).Core()).Core()
	body = ForAll(d.rel)(body).Core()
	body = ext.ReverseAbsVars(body, xs...)
	body = ext.ReverseAbsVars(body, params...)
	if !body.Type().Equals(defVar.Type()) {
		return nil, fmt.Errorf("define inductive: the closure body has type %s, not the declared %s",
			ext.FormatType(body.Type()), ext.FormatType(defVar.Type()))
	}
	d.Body = body
	return d, nil
}

// analyzeRule reads one rule: ∀v̄. [ant ⇒] R(p̄, t̄), the antecedent's
// conjuncts each a side condition or a positive premise.
func (d *InductiveDefinition) analyzeRule(t Term) (*InductiveRule, error) {
	binders, matrix := ext.DecomposesFORALL(t)
	rule := &InductiveRule{}
	for v := range binders.Iter() {
		rule.Vars = append(rule.Vars, v)
	}
	concl := matrix
	if ant, c, ok := ext.MatchesIMPLY(matrix); ok {
		tree, err := d.analyzeAnt(ant, rule.Vars)
		if err != nil {
			return nil, err
		}
		rule.Ant, concl = tree, c
	}
	args, err := d.relationArgs(concl)
	if err != nil {
		return nil, fmt.Errorf("conclusion %s: %v", PrintTerm(concl), err)
	}
	rule.Args = args

	// An index whose argument is a rule
	// variable — the first index that variable stands at — is
	// substituted away; every other index keeps its equation.
	rule.substituted = make([]VarTerm, len(args))
	taken := map[VarTerm]bool{}
	for i, a := range args {
		v, isVar := a.AsVar()
		if !isVar {
			continue
		}
		idx := slices.IndexFunc(rule.Vars, v.EqualsVar)
		if idx < 0 || taken[rule.Vars[idx]] {
			continue
		}
		taken[rule.Vars[idx]] = true
		rule.substituted[i] = rule.Vars[idx]
	}
	for _, v := range rule.Vars {
		if !taken[v] {
			rule.bound = append(rule.bound, v)
		}
	}
	if len(rule.bound) == 0 && rule.Ant == nil && !slices.ContainsFunc(rule.substituted, func(v VarTerm) bool { return v.IsZero() }) {
		return nil, fmt.Errorf("the rule has no content: every index is a bare variable and there is no premise")
	}
	return rule, nil
}

// analyzeAnt reads an antecedent's ∧-tree.
func (d *InductiveDefinition) analyzeAnt(t Term, ruleVars []VarTerm) (*inductiveAnt, error) {
	if l, r, ok := ext.MatchesAND(t); ok {
		left, err := d.analyzeAnt(l, ruleVars)
		if err != nil {
			return nil, err
		}
		right, err := d.analyzeAnt(r, ruleVars)
		if err != nil {
			return nil, err
		}
		return &inductiveAnt{left: left, right: right}, nil
	}
	pr, err := d.analyzePremise(t)
	if err != nil {
		return nil, err
	}
	return &inductiveAnt{leaf: pr}, nil
}

// analyzePremise classifies one conjunct: R-free, or ∀ū. [G ⇒] R(p̄, s̄).
func (d *InductiveDefinition) analyzePremise(t Term) (*InductivePremise, error) {
	if !t.HasFree(d.DefVar) {
		return &InductivePremise{Side: t}, nil
	}
	binders, matrix := ext.DecomposesFORALL(t)
	pr := &InductivePremise{}
	for v := range binders.Iter() {
		pr.Vars = append(pr.Vars, v)
	}
	head := matrix
	if g, c, ok := ext.MatchesIMPLY(matrix); ok {
		if g.HasFree(d.DefVar) {
			return nil, fmt.Errorf("premise %s: the guard mentions %s — a premise may only "+
				"mention the relation in its conclusion (∀ū. G ⇒ %s(…) with G free of it)",
				PrintTerm(t), d.DefVar.Name(), d.DefVar.Name())
		}
		pr.Guard, head = g, c
	}
	args, err := d.relationArgs(head)
	if err != nil {
		return nil, fmt.Errorf("premise %s: %v — the first charter takes a premise as a side "+
			"condition free of %s, or as ∀ū. G ⇒ %s(p̄, s̄) with G free of it; %s under ∃, ∨ or ¬ "+
			"is outside it", PrintTerm(t), err, d.DefVar.Name(), d.DefVar.Name(), d.DefVar.Name())
	}
	pr.Args = args
	return pr, nil
}

// relationArgs reads R(p̄, s̄) — the definiendum applied at exactly the
// declared parameters then the indices — and returns s̄.
func (d *InductiveDefinition) relationArgs(t Term) ([]Term, error) {
	head, args := ext.MatchesApply(t)
	hv, ok := head.AsVar()
	if !ok || !hv.EqualsVar(d.DefVar) {
		return nil, fmt.Errorf("not an application of %s", d.DefVar.Name())
	}
	if len(args) != len(d.Params)+len(d.IndexTypes) {
		return nil, fmt.Errorf("%s applied to %d argument(s), not %d", d.DefVar.Name(), len(args),
			len(d.Params)+len(d.IndexTypes))
	}
	for i, p := range d.Params {
		av, isVar := args[i].AsVar()
		if !isVar || !av.EqualsVar(p) {
			return nil, fmt.Errorf("argument %d of %s is %s, not the parameter %s — every occurrence "+
				"takes the declared parameters unchanged", i, d.DefVar.Name(), PrintTerm(args[i]), p.Name())
		}
	}
	for i, a := range args[len(d.Params):] {
		if a.HasFree(d.DefVar) {
			return nil, fmt.Errorf("index %d of %s mentions %s", i, d.DefVar.Name(), d.DefVar.Name())
		}
	}
	return args[len(d.Params):], nil
}

// ---------------------------------------------------------------------------
// The canonical pieces, at a subject and a relation
// ---------------------------------------------------------------------------

// relationApp applies a relation to index arguments: a variable (R',
// P) applied directly; the definiendum or the minted constant applied
// after the parameters.
func (d *InductiveDefinition) relationApp(rel Term, params []Term, args []Term) Term {
	if _, isVar := rel.AsVar(); isVar && len(params) == 0 {
		return Apply(rel, args...).Core()
	}
	all := append(slices.Clone(params), args...)
	return Apply(rel, all...).Core()
}

// premiseAt writes one premise at a relation (a variable or, with
// params, the definiendum / constant).
func (d *InductiveDefinition) premiseAt(pr *InductivePremise, rel Term, params []Term) Term {
	if !pr.Positive() {
		return pr.Side
	}
	body := d.relationApp(rel, params, pr.Args)
	if pr.Guard != nil {
		body = WrapTerm(pr.Guard).Imply(body).Core()
	}
	for i := len(pr.Vars) - 1; i >= 0; i-- {
		body = ForAll(pr.Vars[i])(body).Core()
	}
	return body
}

// premiseStrongAt writes one premise with its recursive occurrence
// STRENGTHENED — `∀ū. G ⇒ (c(p̄, s̄) ∧ P(s̄))`, the relation alongside
// the property — and a side condition verbatim.
func (d *InductiveDefinition) premiseStrongAt(pr *InductivePremise, c ConstTerm, params []Term, P VarTerm) Term {
	if !pr.Positive() {
		return pr.Side
	}
	body := WrapTerm(d.relationApp(c, params, pr.Args)).And(Apply(P, pr.Args...).Core()).Core()
	if pr.Guard != nil {
		body = WrapTerm(pr.Guard).Imply(body).Core()
	}
	for i := len(pr.Vars) - 1; i >= 0; i-- {
		body = ForAll(pr.Vars[i])(body).Core()
	}
	return body
}

// antStrongAt writes an antecedent tree with every premise strengthened.
func (d *InductiveDefinition) antStrongAt(a *inductiveAnt, c ConstTerm, params []Term, P VarTerm) Term {
	if a.leaf != nil {
		return d.premiseStrongAt(a.leaf, c, params, P)
	}
	return WrapTerm(d.antStrongAt(a.left, c, params, P)).And(d.antStrongAt(a.right, c, params, P)).Core()
}

// ruleStrongAt writes rule j's STRENGTHENED obligation: the premises
// carry the relation beside the property, the conclusion is the
// property alone.
func (d *InductiveDefinition) ruleStrongAt(j int, c ConstTerm, params []Term, P VarTerm) Term {
	r := &d.Rules[j]
	body := Apply(P, r.Args...).Core()
	if r.Ant != nil {
		body = WrapTerm(d.antStrongAt(r.Ant, c, params, P)).Imply(body).Core()
	}
	for i := len(r.Vars) - 1; i >= 0; i-- {
		body = ForAll(r.Vars[i])(body).Core()
	}
	return body
}

// rulesStrongAt writes the whole strengthened obligation set, left-nested.
func (d *InductiveDefinition) rulesStrongAt(c ConstTerm, params []Term, P VarTerm) Term {
	out := d.ruleStrongAt(0, c, params, P)
	for j := 1; j < len(d.Rules); j++ {
		out = WrapTerm(out).And(d.ruleStrongAt(j, c, params, P)).Core()
	}
	return out
}

// antAt writes an antecedent tree at a relation.
func (d *InductiveDefinition) antAt(a *inductiveAnt, rel Term, params []Term) Term {
	if a.leaf != nil {
		return d.premiseAt(a.leaf, rel, params)
	}
	return WrapTerm(d.antAt(a.left, rel, params)).And(d.antAt(a.right, rel, params)).Core()
}

// ruleAt writes rule j at a relation: ∀v̄. [ant ⇒] rel(p̄, t̄).
func (d *InductiveDefinition) ruleAt(j int, rel Term, params []Term) Term {
	r := &d.Rules[j]
	body := d.relationApp(rel, params, r.Args)
	if r.Ant != nil {
		body = WrapTerm(d.antAt(r.Ant, rel, params)).Imply(body).Core()
	}
	for i := len(r.Vars) - 1; i >= 0; i-- {
		body = ForAll(r.Vars[i])(body).Core()
	}
	return body
}

// rulesAt writes the whole rule set at a relation, left-nested.
func (d *InductiveDefinition) rulesAt(rel Term, params []Term) Term {
	out := d.ruleAt(0, rel, params)
	for j := 1; j < len(d.Rules); j++ {
		out = WrapTerm(out).And(d.ruleAt(j, rel, params)).Core()
	}
	return out
}

// disjunctOf builds rule j's canonical disjunct at a subject and the
// bound relation R': ∃w̄. (⋀ aᵢ = tᵢ) ∧ ant — left-nested, the
// equations of the non-substituted indices first, the antecedent (when
// there is one) as ONE trailing conjunct; the substituted variables
// replaced by their subject term throughout.
func (d *InductiveDefinition) disjunctOf(j int, subject []Term, rel VarTerm) (Term, error) {
	r := &d.Rules[j]
	var subst []core.TermSubst
	for i, v := range r.substituted {
		if !v.IsZero() {
			subst = append(subst, MakeTermSubst(v, subject[i]))
		}
	}
	at := func(t Term) Term {
		if len(subst) == 0 {
			return t
		}
		return t.Substitute(subst...)
	}
	var pieces []Term
	for i, v := range r.substituted {
		if v.IsZero() {
			pieces = append(pieces, WrapTerm(subject[i]).Eq(at(r.Args[i])).Core())
		}
	}
	if r.Ant != nil {
		pieces = append(pieces, at(d.antAt(r.Ant, rel, nil)))
	}
	if len(pieces) == 0 {
		return nil, fmt.Errorf("the canonical disjunct is empty")
	}
	body := pieces[0]
	for _, p := range pieces[1:] {
		body = WrapTerm(body).And(p).Core()
	}
	for i := len(r.bound) - 1; i >= 0; i-- {
		body = Exists(r.bound[i])(body).Core()
	}
	return body, nil
}

// closedAt is the closure condition at a relation variable:
// ∀ā. D(ā) ⇒ rel(ā).
func (d *InductiveDefinition) closedAt(rel VarTerm) Term {
	disj := d.disjunction.Substitute(MakeTermSubst(d.rel, rel))
	body := WrapTerm(disj).Imply(Apply(rel, termsOf(d.subject)...).Core()).Core()
	for i := len(d.subject) - 1; i >= 0; i-- {
		body = ForAll(d.subject[i])(body).Core()
	}
	return body
}

// instantiated rewrites a canonical term (built at ā and R') at a
// subject and a relation. The relation may be a variable (a plain
// substitution) or a λ (substituted, then its redexes reduced by the
// kernel's targeted β — the same reduction a proof's instantiation
// undergoes, so the two spellings agree exactly).
func (d *InductiveDefinition) instantiated(t Term, subject []Term, rel Term) Term {
	subst := make([]core.TermSubst, 0, len(subject)+1)
	for i, s := range subject {
		subst = append(subst, MakeTermSubst(d.subject[i], s))
	}
	subst = append(subst, MakeTermSubst(d.rel, rel))
	out := t.Substitute(subst...)
	if abs, isAbs := rel.AsAbsTerm(); isAbs {
		if w := chainBeta(abs, len(d.IndexTypes))(out); w != nil {
			out = prop.Rhs(w)
		}
	}
	return out
}

// ---------------------------------------------------------------------------
// Mint, statements, recovery
// ---------------------------------------------------------------------------

// MintInductiveDefinition performs the kernel mint — the closure body
// as R's definition (core.NewConstDef) under exclusive registration —
// and returns the minted constant.
func MintInductiveDefinition(env *ProverEnv, d *InductiveDefinition) (ConstTerm, error) {
	c, err := mintDefinedConst(env, d.DefVar.Name(), d.Body)
	if err != nil {
		return ConstTerm{}, err
	}
	if !c.Type().Equals(d.DefVar.Type()) {
		panic(fmt.Sprintf("MintInductiveDefinition(%s): minted at %s, declared %s",
			d.DefVar.Name(), ext.FormatType(c.Type()), ext.FormatType(d.DefVar.Type())))
	}
	return c, nil
}

// RecoverInductiveDefinition re-runs the analysis on the recorded rule
// set and checks the minted constant's body against it — what the
// composite's replay and emit run from the record (the constant, the
// parameter variables, the rules).
func RecoverInductiveDefinition(c ConstTerm, params []VarTerm, rules []Term) (*InductiveDefinition, error) {
	def := c.DefThm()
	if def.IsZero() {
		return nil, fmt.Errorf("%s has no definition", c.Name())
	}
	defVar := Var(c.Name(), c.Type()).Core().(VarTerm)
	props := make([]Prop, len(rules))
	for i, r := range rules {
		props[i] = core.MakeProp(r)
	}
	d, err := AnalyzeInductiveDefinition(defVar, params, props)
	if err != nil {
		return nil, err
	}
	if !prop.Rhs(WrapProp(def)).AlphaEquals(d.Body) {
		return nil, fmt.Errorf("%s's definition is not the closure of the recorded rules — record drift",
			c.Name())
	}
	return d, nil
}

// Stmt builds the derived theorem of one kind at the minted constant.
func (d *InductiveDefinition) Stmt(c ConstTerm, k InductiveTheoremKind) Prop {
	params := termsOf(d.Params)
	var body Term
	switch k {
	case InductiveRules:
		body = d.rulesAt(c, params)
	case InductiveInduct:
		P := d.motive()
		body = d.inductionAt(c, params, P, d.rulesAt(P, nil))
	case InductiveInductStrong:
		P := d.motive()
		body = d.inductionAt(c, params, P, d.rulesStrongAt(c, params, P))
	case InductiveCases:
		cRel := d.constantRelation(c)
		body = WrapTerm(d.relationApp(c, params, termsOf(d.subject))).Eq(d.instantiated(d.disjunction, termsOf(d.subject), cRel)).Core()
		for i := len(d.subject) - 1; i >= 0; i-- {
			body = ForAll(d.subject[i])(body).Core()
		}
	default:
		panic(fmt.Sprintf("InductiveDefinition.Stmt: unknown kind %v", k))
	}
	for i := len(d.Params) - 1; i >= 0; i-- {
		body = ForAll(d.Params[i])(body).Core()
	}
	return core.MakeProp(body)
}

// inductionAt is an induction's body below the parameters, in the
// standard form: ∀P x̄. rules ∧ c(p̄, x̄) ⇒ P(x̄), rules the rule set at P
// (left-nested, so each rule reads as its own hypothesis) and the guard
// the relation at the conclusion binders.
func (d *InductiveDefinition) inductionAt(c ConstTerm, params []Term, P VarTerm, rules Term) Term {
	xs := d.conclusionVars()
	guard := d.relationApp(c, params, termsOf(xs))
	body := WrapTerm(WrapTerm(rules).And(guard).Core()).Imply(Apply(P, termsOf(xs)...).Core()).Core()
	for i := len(xs) - 1; i >= 0; i-- {
		body = ForAll(xs[i])(body).Core()
	}
	return ForAll(P)(body).Core()
}

// motive is the induction predicate's variable, P over the indices,
// named clear of everything in the rules.
func (d *InductiveDefinition) motive() VarTerm {
	return Var("P", funTypeOf(d.IndexTypes, TypeBool)).Core().(VarTerm).RenameToAvoid(d.avoidTerms()...)
}

// conclusionVars are Induct's conclusion binders x̄.
func (d *InductiveDefinition) conclusionVars() []VarTerm {
	avoid := d.avoidTerms()
	out := make([]VarTerm, len(d.IndexTypes))
	for i, t := range d.IndexTypes {
		v := Var(TermName(fmt.Sprintf("x%d", i)), t).Core().(VarTerm).RenameToAvoid(avoid...)
		out[i] = v
		avoid = append(avoid, v)
	}
	return out
}

// constantRelation is λā. c(p̄, ā) — the minted relation over the
// indices alone, the form a canonical piece is instantiated at.
func (d *InductiveDefinition) constantRelation(c ConstTerm) Term {
	return ext.ReverseAbsVars(d.relationApp(c, termsOf(d.Params), termsOf(d.subject)), d.subject...)
}

// avoidTerms lists what fresh names must stay clear of: the rules,
// the parameters, the definiendum, the subject and the relation.
func (d *InductiveDefinition) avoidTerms() []Term {
	out := []Term{d.DefVar, d.rel}
	for _, p := range d.Params {
		out = append(out, p)
	}
	for _, s := range d.subject {
		out = append(out, s)
	}
	return append(out, d.RuleTerms...)
}

// ---------------------------------------------------------------------------
// The derivations
// ---------------------------------------------------------------------------
//
// Every derivation runs at relation VARIABLES and instantiates a λ only
// at its end, by the kernel's INST followed by the targeted β of that
// one abstraction: the rule set, the closure condition and the
// disjuncts are then one construction each, read at P, R' or the
// minted relation by substitution. A proof of `rules[R₁] ⊢ rules[R₂]`
// for two variables is the monotonicity recipe; both Rules and Cases
// spend it.

// inductiveDeriver bundles a definition with its minted constant.
type inductiveDeriver struct {
	d *InductiveDefinition
	c ConstTerm
	// params are the parameter variables as terms; cRel the constant
	// over the indices alone (λā. c(p̄, ā)).
	params []Term
	cRel   Term
}

func newInductiveDeriver(d *InductiveDefinition, c ConstTerm) *inductiveDeriver {
	return &inductiveDeriver{d: d, c: c, params: termsOf(d.Params), cRel: d.constantRelation(c)}
}

// DeriveInductiveTheorem derives the theorem of one kind at the
// constant — pure kernel derivation, panicking on internal drift (the
// derived statement must be the computed one).
func DeriveInductiveTheorem(d *InductiveDefinition, c ConstTerm, k InductiveTheoremKind) Prop {
	dv := newInductiveDeriver(d, c)
	stmt := d.Stmt(c, k)
	var derived *PropWrapper
	switch k {
	case InductiveRules:
		derived = dv.rules()
	case InductiveInduct:
		derived = dv.induct()
	case InductiveCases:
		derived = dv.cases()
	case InductiveInductStrong:
		derived = dv.inductStrong()
	default:
		panic(fmt.Sprintf("DeriveInductiveTheorem: unknown kind %v", k))
	}
	if derived.NumHyps() != 0 || !derived.AlphaEquals(stmt) {
		panic(fmt.Sprintf("DeriveInductiveTheorem(%s, %v): derived %s ≠ statement %s — kit drift",
			c.Name(), k, PrintProp(derived), PrintProp(stmt)))
	}
	return derived
}

// unfoldAt is ⊢ c(p̄, s̄) = (∀R'. closed(R') ⇒ R'(s̄)), β-collapsed.
func (dv *inductiveDeriver) unfoldAt(subject []Term) *PropWrapper {
	all := append(slices.Clone(dv.params), subject...)
	return prop.ExpandDef(dv.c, all...)
}

// closureAt is the closure condition at a relation variable, as a
// term: ∀ā. D_rel(ā) ⇒ rel(ā).
func (dv *inductiveDeriver) closureAt(rel VarTerm) Term { return dv.d.closedAt(rel) }

// disjunctionAt / disjunctsAt instantiate the canonical disjunction at
// a subject and a relation.
func (dv *inductiveDeriver) disjunctionAt(subject []Term, rel Term) Term {
	return dv.d.instantiated(dv.d.disjunction, subject, rel)
}

func (dv *inductiveDeriver) disjunctsAt(subject []Term, rel Term) []Term {
	out := make([]Term, len(dv.d.disjuncts))
	for j, dj := range dv.d.disjuncts {
		out[j] = dv.d.instantiated(dj, subject, rel)
	}
	return out
}

// openedDisjunct is one instantiated disjunct taken apart: its
// ∃-binders (as the instantiation left them), the equations aᵢ = tᵢ of
// the kept indices in index order, and the antecedent (nil when the
// rule is unconditional) — plus the body under the binders.
type openedDisjunct struct {
	bound []VarTerm
	body  Term
	eqs   []Term
	ant   Term
}

// open takes an instantiated disjunct apart along rule j's shape.
func (dv *inductiveDeriver) open(j int, disjunct Term) *openedDisjunct {
	r := &dv.d.Rules[j]
	binders, body := ext.DecomposesEXISTS(disjunct)
	od := &openedDisjunct{body: body}
	for v := range binders.Iter() {
		od.bound = append(od.bound, v)
	}
	Assert(len(od.bound) == len(r.bound))
	kept := 0
	for _, v := range r.substituted {
		if v.IsZero() {
			kept++
		}
	}
	n := kept
	if r.Ant != nil {
		n++
	}
	pieces := splitLeftNestedAnd(body, n)
	od.eqs = pieces[:kept]
	if r.Ant != nil {
		od.ant = pieces[kept]
	}
	return od
}

// splitLeftNestedAnd peels a left-nested conjunction of exactly n
// conjuncts into its pieces.
func splitLeftNestedAnd(t Term, n int) []Term {
	Assert(n >= 1)
	pieces := make([]Term, n)
	cur := t
	for k := n - 1; k >= 1; k-- {
		l, r, ok := ext.MatchesAND(cur)
		Assert(ok)
		pieces[k] = r
		cur = l
	}
	pieces[0] = cur
	return pieces
}

// projections proves each piece of an opened body from the body
// itself: body ⊢ eqᵢ, body ⊢ ant.
func (od *openedDisjunct) projections() []*PropWrapper {
	pieces := slices.Clone(od.eqs)
	if od.ant != nil {
		pieces = append(pieces, od.ant)
	}
	return prop.HypANDRecursive(pieces...)
}

// antProjections proves each leaf of an instantiated antecedent from
// the antecedent: ant ⊢ leafᵢ.
func antProjections(tree *inductiveAnt, t Term) []*PropWrapper {
	var walk func(tree *inductiveAnt, t Term, have *PropWrapper) []*PropWrapper
	walk = func(tree *inductiveAnt, t Term, have *PropWrapper) []*PropWrapper {
		if tree.leaf != nil {
			return []*PropWrapper{have}
		}
		l, r, ok := ext.MatchesAND(t)
		Assert(ok)
		left := prop.HypAND0(l, r).DeriveHypFrom(have)
		right := prop.HypAND1(l, r).DeriveHypFrom(have)
		return append(walk(tree.left, l, left), walk(tree.right, r, right)...)
	}
	return walk(tree, t, prop.Assume(t))
}

// congruence is ⊢ rel(t̄) = rel(ā) from the equations aᵢ = tᵢ of the
// kept indices (the substituted ones already ARE the subject): the
// relation reflexive, each argument equation reversed — targeted
// congruence, never a blanket rewrite, so nothing inside the relation
// is touched.
func (dv *inductiveDeriver) congruence(j int, rel Term, params []Term, subject []Term, od *openedDisjunct) *PropWrapper {
	r := &dv.d.Rules[j]
	w := prop.Refl(rel)
	for _, p := range params {
		w = w.Apply(prop.Refl(p))
	}
	k := 0
	for i, v := range r.substituted {
		if !v.IsZero() {
			w = w.Apply(prop.Refl(subject[i]))
			continue
		}
		w = w.Apply(prop.Assume(od.eqs[k]).EqSym()) // tᵢ = aᵢ
		k++
	}
	return w
}

// ruleInstances instantiates rule j at the opened disjunct's variables:
// the substituted indices at the subject, the bound ones at themselves.
func (dv *inductiveDeriver) ruleWitnesses(j int, subject []Term, od *openedDisjunct) []Term {
	r := &dv.d.Rules[j]
	out := make([]Term, len(r.Vars))
	k := 0
	for idx, v := range r.Vars {
		i := slices.Index(r.substituted, v)
		if i >= 0 {
			out[idx] = subject[i]
			continue
		}
		out[idx] = od.bound[k]
		k++
	}
	return out
}

// caseOf is the per-disjunct step shared by Induct and Cases-⇐: from
// rule j at a relation (⊢ ∀v̄. ant ⇒ rel(t̄), or rel(t̄)) and the opened
// disjunct at that relation, derive {ruleⱼ-hyp…}, disjunctⱼ ⊢ rel(ā).
// ruleThm carries whatever hypotheses it carries (rules[P] for Induct,
// none for Cases); the disjunct becomes a single hypothesis.
func (dv *inductiveDeriver) caseOf(j int, ruleThm *PropWrapper, rel Term, params []Term, subject []Term, disjunct Term) *PropWrapper {
	r := &dv.d.Rules[j]
	od := dv.open(j, disjunct)
	w := ruleThm.ConclForAllInsts(dv.ruleWitnesses(j, subject, od)...)
	if r.Ant != nil {
		w = w.DemoteHyp() // …, ant ⊢ rel(t̄)
	}
	w = dv.congruence(j, rel, params, subject, od).EqMP(w) // …, ant, eqs ⊢ rel(ā)
	for _, pr := range od.projections() {
		w = w.DeriveHypFrom(pr)
	}
	for i := len(od.bound) - 1; i >= 0; i-- {
		w = w.HypExists(od.bound[i], existsBodyFrom(disjunct, i))
	}
	return w
}

// existsBodyFrom returns the body under the first i+1 ∃-binders of a
// disjunct (the hypothesis HypExists expects at step i).
func existsBodyFrom(disjunct Term, i int) Term {
	t := disjunct
	for k := 0; k <= i; k++ {
		abs := ext.MatchesEXISTS(t)
		Assert(!abs.IsZero())
		t = abs.Body()
	}
	return t
}

// byCases assembles per-disjunct proofs `Γⱼ, Dⱼ ⊢ concl` into
// `⋃Γⱼ, D₁ ∨ … ∨ Dₘ ⊢ concl`.
func byCases(concl Term, disjuncts []Term, cases []*PropWrapper) *PropWrapper {
	if len(disjuncts) == 1 {
		return cases[0]
	}
	w := prop.ByCasesRecursive(concl, disjuncts...)
	for j, c := range cases {
		w = w.DeriveHypFrom(c.PromoteHyp(disjuncts[j]))
	}
	return w
}

// inductCurried is the weak rule induction derived in its curried
// shape, ⊢ ∀p̄. ∀P. rules[P] ⇒ ∀x̄. c(p̄, x̄) ⇒ P(x̄): induct closes it in
// the standard form, and inductStrong instantiates it at its predicate.
func (dv *inductiveDeriver) inductCurried() *PropWrapper {
	d := dv.d
	P := d.motive()
	xs := d.conclusionVars()
	rulesP := d.rulesAt(P, nil)
	ruleThms := prop.HypANDRecursive(ruleTermsAt(d, P)...) // rules[P] ⊢ ruleⱼ[P]

	// rules[P] ⊢ closed(P): the case analysis over the disjunction.
	subject := termsOf(d.subject)
	disjuncts := dv.disjunctsAt(subject, P)
	cases := make([]*PropWrapper, len(disjuncts))
	for j := range disjuncts {
		cases[j] = dv.caseOf(j, ruleThms[j], P, nil, subject, disjuncts[j])
	}
	concl := Apply(P, subject...).Core()
	closed := byCases(concl, disjuncts, cases).
		PromoteHyp(dv.disjunctionAt(subject, P)).
		ConclForAllList(d.subject...)
	Assert(closed.Conclusion().AlphaEquals(dv.closureAt(P)))

	// c(p̄, x̄) ⊢ closed(P) ⇒ P(x̄), and the modus ponens.
	xsT := termsOf(xs)
	atP := dv.unfoldAt(xsT).
		EqMP(prop.Assume(dv.d.relationApp(dv.c, dv.params, xsT))).
		ConclForAllInst(P).
		DemoteHyp().
		DeriveHypFrom(closed)
	return atP.
		PromoteHyp(dv.d.relationApp(dv.c, dv.params, xsT)).
		ConclForAllList(xs...).
		PromoteHyp(rulesP).
		ConclForAll(P).
		ConclForAllList(d.Params...)
}

// induct is the weak rule induction as the door states it: inductCurried
// opened at its own binders and closed again in the standard form.
func (dv *inductiveDeriver) induct() *PropWrapper {
	d := dv.d
	P := d.motive()
	xsT := termsOf(d.conclusionVars())
	open := dv.inductCurried().
		ConclForAllInsts(dv.params...).
		ConclForAllInst(P).
		DemoteHyp().
		ConclForAllInsts(xsT...).
		DemoteHyp() // rules[P], c(p̄, x̄) ⊢ P(x̄)
	return dv.closeStandard(open, P, d.rulesAt(P, nil))
}

// closeStandard closes an opened induction, rules, c(p̄, x̄) ⊢ P(x̄), in
// the standard form ⊢ ∀p̄ P x̄. rules ∧ c(p̄, x̄) ⇒ P(x̄): the two
// hypotheses become the conjuncts of one.
func (dv *inductiveDeriver) closeStandard(open *PropWrapper, P VarTerm, rules Term) *PropWrapper {
	d := dv.d
	xs := d.conclusionVars()
	guard := d.relationApp(dv.c, dv.params, termsOf(xs))
	if open.HasHyp(rules) {
		open = open.DeriveHypFrom(prop.HypAND0(rules, guard))
	}
	return open.
		DeriveHypFrom(prop.HypAND1(rules, guard)).
		PromoteHyp(WrapTerm(rules).And(guard).Core()).
		ConclForAllList(xs...).
		ConclForAll(P).
		ConclForAllList(d.Params...)
}

// ruleTermsAt lists the rules at a relation variable.
func ruleTermsAt(d *InductiveDefinition, rel VarTerm) []Term {
	out := make([]Term, len(d.Rules))
	for j := range d.Rules {
		out[j] = d.ruleAt(j, rel, nil)
	}
	return out
}

// monotone is the recipe: with R₁ and R₂ relation variables and the
// transport TR = ∀ā. R₁(ā) ⇒ R₂(ā) as a hypothesis, derive
// {leaves of ant[R₁]}, TR ⊢ ant[R₂] for rule j's antecedent, the
// leaves as separate hypotheses (the caller collapses them).
// r1 supplies R₁ when constructing the source premises; R₂ comes
// from transport's consequent and needs no separate parameter.
func (dv *inductiveDeriver) monotone(j int, r1 VarTerm, transport Term) *PropWrapper {
	d := dv.d
	tree := d.Rules[j].Ant
	var walk func(a *inductiveAnt) *PropWrapper
	walk = func(a *inductiveAnt) *PropWrapper {
		if a.leaf == nil {
			l, r := walk(a.left), walk(a.right)
			return prop.ConclAND(l.Conclusion(), r.Conclusion()).DeriveHypFrom(l).DeriveHypFrom(r)
		}
		pr := a.leaf
		src := d.premiseAt(pr, r1, nil)
		if !pr.Positive() {
			return prop.Assume(src)
		}
		w, us := prop.Assume(src).StripConclForAll()
		if pr.Guard != nil {
			w = w.DemoteHyp() // src, G ⊢ R₁(s̄)
		}
		_, args := ext.MatchesApply(w.Conclusion())
		carried := prop.Assume(transport).ConclForAllInsts(args...).DemoteHyp() // TR, R₁(s̄) ⊢ R₂(s̄)
		w = carried.DeriveHypFrom(w)                                            // src, G, TR ⊢ R₂(s̄)
		if pr.Guard != nil {
			w = w.PromoteHyp(pr.Guard.Substitute(varSubst(pr.Vars, us)...))
		}
		return w.ConclForAllList(us...)
	}
	return walk(tree)
}

// varSubst pairs binders with their fresh stand-ins.
func varSubst(from []VarTerm, to []VarTerm) []core.TermSubst {
	out := make([]core.TermSubst, len(from))
	for i := range from {
		out[i] = MakeTermSubst(from[i], to[i])
	}
	return out
}

// conjoin proves the left-nested conjunction of the pieces'
// conclusions from the pieces, each piece's own hypotheses carried
// through. Two pieces may state one formula — a rule whose conclusion
// repeats an index term (permutation's R(nil, nil)) contributes the
// reflexive equation nil = nil twice — and a theorem's hypotheses form
// a set, so a conclusion an earlier piece already stated is discharged
// once; any other piece is discharged unconditionally, and one whose
// conclusion is not a hypothesis still panics.
func conjoin(pieces []*PropWrapper) *PropWrapper {
	if len(pieces) == 1 {
		return pieces[0]
	}
	terms := make([]Term, len(pieces))
	for i, p := range pieces {
		terms[i] = p.Conclusion()
	}
	w := prop.ConclANDRecursive(terms...)
	for i, p := range pieces {
		if statedEarlier(terms, i) {
			continue
		}
		w = w.DeriveHypFrom(p)
	}
	return w
}

// statedEarlier says whether terms[i] repeats one of terms[:i].
func statedEarlier(terms []Term, i int) bool {
	for _, t := range terms[:i] {
		if t.AlphaEquals(terms[i]) {
			return true
		}
	}
	return false
}

// ruleFrom is the per-rule step shared by Rules and Cases-⇒: the
// disjunction at a subject and R₂, from rule j's own pieces at R₁ —
// the substituted indices at the subject, the equations reflexive, the
// antecedent carried across by monotonicity. Returns
// {leaves of ant[R₁]}, TR ⊢ D_R₂(subject), with the subject being the
// rule's conclusion arguments read at the disjunct's own variables.
//
// Concretely: open rule j's disjunct at the canonical subject and R₂,
// so its ∃-binders are the rule's bound variables; the witnesses are
// those variables themselves, and the subject is t̄ with the
// substituted indices replaced by ā — i.e. the disjunct's equations
// aᵢ = tᵢ hold by reflexivity once ā is instantiated at t̄.
func (dv *inductiveDeriver) ruleFrom(j int, r1, r2 VarTerm, transport Term) (*PropWrapper, []VarTerm, []Term) {
	d := dv.d
	r := &d.Rules[j]
	// The subject t̄ read at the rule's variables: substituted indices
	// are their variable, kept ones their argument term.
	subject := make([]Term, len(r.Args))
	for i, v := range r.substituted {
		if !v.IsZero() {
			subject[i] = v
		} else {
			subject[i] = r.Args[i]
		}
	}
	disjuncts := dv.disjunctsAt(subject, r2)
	od := dv.open(j, disjuncts[j])
	// The instantiation renamed nothing: the rule's own variables are
	// free in the subject, and the ∃-binders are those same variables
	// — the kernel keeps a binder whose name is free in the substituted
	// term only by renaming it, so witness the body at the binders it
	// chose and instantiate back.
	var pieces []*PropWrapper
	k := 0
	bodyAtRule := od.body.Substitute(varSubst(od.bound, r.bound)...)
	bodyPieces := splitLeftNestedAnd(bodyAtRule, len(od.eqs)+boolToInt(od.ant != nil))
	for _, v := range r.substituted {
		if !v.IsZero() {
			continue
		}
		l, rr, ok := ext.MatchesEQ(bodyPieces[k])
		Assert(ok && l.AlphaEquals(rr))
		pieces = append(pieces, prop.Refl(l))
		k++
	}
	if od.ant != nil {
		pieces = append(pieces, dv.monotone(j, r1, transport))
		Assert(pieces[len(pieces)-1].Conclusion().AlphaEquals(bodyPieces[k]))
	}
	w := conjoin(pieces)
	// ∃-intro at the rule's bound variables, then the disjunct's place
	// in the disjunction.
	target := disjuncts[j]
	w = existsIntroChain(target, termsOf(r.bound), w)
	w = orIntroAt(disjuncts, j, w)
	return w, r.Vars, subject
}

// funTypeParts splits A → B → … → C into its argument types and C.
func funTypeParts(t HolType) ([]HolType, HolType) {
	parts := ext.MatchesFun(t)
	return parts[:len(parts)-1], parts[len(parts)-1]
}

// funTypeOf builds args… → result.
func funTypeOf(args []HolType, result HolType) HolType {
	if len(args) == 0 {
		return result
	}
	if len(args) == 1 {
		return MakeFun(args[0], result)
	}
	rest := append(slices.Clone(args[2:]), result)
	return MakeFun(args[0], args[1], rest...)
}

// chainBeta is the targeted β for a relation written as a λ over the
// indices: at a term that is exactly that abstraction applied to
// `arity` arguments it returns ⊢ abs(s₁)…(sₙ) = body[ā := s̄], reducing
// the spine one redex at a time (the outer redex reduced first leaves
// an inner redex whose abstraction is no longer the given one, which
// is why the single-abstraction β cannot serve a multi-index
// relation). Deep, so every occurrence in a term reduces; nothing
// else does.
func chainBeta(abs core.AbsTerm, arity int) prop.Rewrite {
	step := func(t Term) *PropWrapper {
		head, args := ext.MatchesApply(t)
		if len(args) != arity || !head.AlphaEquals(abs) {
			return nil
		}
		var eq *PropWrapper
		cur := Term(head)
		for _, a := range args {
			fn, ok := cur.AsAbsTerm()
			Assert(ok)
			// ⊢ fn(a) = fn.body[x := a]
			red := prop.Beta(Apply(fn, fn.Var()).Core()).TermInst(MakeTermSubst(fn.Var(), a))
			if eq == nil {
				eq = red
			} else {
				eq = eq.RightApply(a).EqTrans(red)
			}
			cur = prop.Rhs(red)
		}
		return eq
	}
	return prop.DeepRewrite(step)
}

// hypFrom is DeriveHypFrom with a readable failure: the derivations
// are deterministic, so a missing hypothesis is kit drift and the
// message names the term and the sequent it was expected in.
func hypFrom(w, pr *PropWrapper, where string) *PropWrapper {
	if !w.HasHyp(pr.Conclusion()) {
		panic(fmt.Sprintf("define inductive (%s): %s is not a hypothesis of %s",
			where, PrintTerm(pr.Conclusion()), PrintProp(w)))
	}
	return w.DeriveHypFrom(pr)
}

func boolToInt(b bool) int {
	if b {
		return 1
	}
	return 0
}

// rules: ∀p̄. rule₁ ∧ … ∧ ruleₘ at the constant.
func (dv *inductiveDeriver) rules() *PropWrapper {
	d := dv.d
	R1 := Var("R1", d.rel.Type()).Core().(VarTerm).RenameToAvoid(d.avoidTerms()...)
	R2 := d.rel
	transport := WrapTerm(Apply(R1, termsOf(d.subject)...).Core()).
		Imply(Apply(R2, termsOf(d.subject)...).Core()).Core()
	for i := len(d.subject) - 1; i >= 0; i-- {
		transport = ForAll(d.subject[i])(transport).Core()
	}
	closure := dv.closureAt(R2)

	// closed(R') ⊢ ∀ā. c(p̄, ā) ⇒ R'(ā): the transport, from the unfold.
	subject := termsOf(d.subject)
	cApp := d.relationApp(dv.c, dv.params, subject)
	transportThm := dv.unfoldAt(subject).
		EqMP(prop.Assume(cApp)).
		ConclForAllInst(R2).
		DemoteHyp().                  // c(p̄, ā), closed(R') ⊢ R'(ā)
		PromoteHyp(cApp).             // closed(R') ⊢ c(p̄, ā) ⇒ R'(ā)
		ConclForAllList(d.subject...) // closed(R') ⊢ ∀ā. c(p̄, ā) ⇒ R'(ā)
	betaC := chainBeta(dv.cRel.(core.AbsTerm), len(d.IndexTypes))
	transportAtC := transport.Substitute(MakeTermSubst(R1, dv.cRel))
	if w := betaC(transportAtC); w != nil {
		transportAtC = prop.Rhs(w)
	}
	Assert(transportThm.Conclusion().AlphaEquals(transportAtC))

	ruleThms := make([]*PropWrapper, len(d.Rules))
	for j := range d.Rules {
		r := &d.Rules[j]
		w, vars, subj := dv.ruleFrom(j, R1, R2, transport) // {ant[R₁] leaves}, TR ⊢ D_R'(t̄)
		// closed(R') at t̄, fed the disjunction: …, TR, closed(R') ⊢ R'(t̄).
		w = hypFrom(prop.Assume(closure).ConclForAllInsts(subj...).DemoteHyp(), w, "rules: closure at t̄")
		// R₁ := λā. c(p̄, ā): the transport becomes the theorem above,
		// the antecedent leaves become the rule's own at the constant.
		// The transport is discharged BEFORE R' is generalized — it
		// mentions R' free.
		w = w.TermInst(MakeTermSubst(R1, dv.cRel)).Rewrite(betaC)
		// An unconditional rule never spent the transport; a rule with
		// premises did, and the hypothesis is there to discharge.
		if w.HasHyp(transportThm.Conclusion()) {
			w = w.DeriveHypFrom(transportThm) // {ant[c] leaves}, closed(R') ⊢ R'(t̄)
		}
		w = w.PromoteHyp(closure).ConclForAll(R2) // {ant[c] leaves} ⊢ ∀R'. closed(R') ⇒ R'(t̄)
		w = dv.unfoldAt(subj).EqSym().EqMP(w)     // {ant[c] leaves} ⊢ c(p̄, t̄)
		if r.Ant != nil {
			ant := d.antAt(r.Ant, dv.c, dv.params)
			for _, pr := range antProjections(r.Ant, ant) {
				w = hypFrom(w, pr, "rules: antecedent leaf")
			}
			w = w.PromoteHyp(ant)
		}
		ruleThms[j] = w.ConclForAllList(vars...)
	}
	return conjoin(ruleThms).ConclForAllList(d.Params...)
}

// cases: ∀p̄. ∀ā. c(p̄, ā) ⇔ D_c(ā).
func (dv *inductiveDeriver) cases() *PropWrapper {
	d := dv.d
	subject := termsOf(d.subject)
	cApp := d.relationApp(dv.c, dv.params, subject)
	cAbs := dv.cRel.(core.AbsTerm)
	rulesThm := dv.rules().ConclForAllInsts(dv.params...) // ⊢ rules[c]
	ruleThms := prop.HypANDRecursive(ruleTermsAtConst(d, dv.c, dv.params)...)
	for j := range ruleThms {
		ruleThms[j] = ruleThms[j].DeriveHypFrom(rulesThm) // ⊢ ruleⱼ[c]
	}

	// ⇐: D_c(ā) ⊢ c(p̄, ā), each disjunct the rule it came from.
	disjunctsC := dv.disjunctsAt(subject, dv.cRel)
	backCases := make([]*PropWrapper, len(disjunctsC))
	for j := range disjunctsC {
		backCases[j] = dv.caseOf(j, ruleThms[j], dv.c, dv.params, subject, disjunctsC[j])
	}
	backward := byCases(cApp, disjunctsC, backCases) // D_c(ā) ⊢ c(p̄, ā)
	backwardAll := backward.PromoteHyp(dv.disjunctionAt(subject, dv.cRel)).ConclForAllList(d.subject...)

	// ⇒: the closure at Q := λā. D_c(ā), proved at relation variables
	// R₁ (the disjunction) and R₂ (the constant) then instantiated.
	R1 := Var("R1", d.rel.Type()).Core().(VarTerm).RenameToAvoid(d.avoidTerms()...)
	R2 := Var("R2", d.rel.Type()).Core().(VarTerm).RenameToAvoid(append(d.avoidTerms(), R1)...)
	transport := WrapTerm(Apply(R1, subject...).Core()).Imply(Apply(R2, subject...).Core()).Core()
	for i := len(d.subject) - 1; i >= 0; i-- {
		transport = ForAll(d.subject[i])(transport).Core()
	}
	// For each rule: {ant[R₁] leaves}, TR ⊢ D_R₂(t̄) — but the closure
	// condition at Q wants, for each disjunct of D_{R₁}(b̄) opened, the
	// conclusion D_R₂(b̄) at the SUBJECT b̄ (the equations bᵢ = tᵢ
	// carried, not reflexive). So open the disjunct at b̄ and R₁,
	// transport its antecedent, and rebuild the disjunct at b̄ and R₂.
	disjunctsR1 := dv.disjunctsAt(subject, R1)
	disjunctsR2 := dv.disjunctsAt(subject, R2)
	fwdCases := make([]*PropWrapper, len(disjunctsR1))
	for j := range disjunctsR1 {
		od1 := dv.open(j, disjunctsR1[j])
		od2 := dv.open(j, disjunctsR2[j])
		Assert(len(od1.bound) == len(od2.bound))
		// Align the two openings' binders (the instantiation may have
		// renamed them differently): work at od1's, map od2's body.
		body2 := od2.body.Substitute(varSubst(od2.bound, od1.bound)...)
		pieces2 := splitLeftNestedAnd(body2, len(od2.eqs)+boolToInt(od2.ant != nil))
		var pieces []*PropWrapper
		for k := range od1.eqs {
			Assert(od1.eqs[k].AlphaEquals(pieces2[k]))
			pieces = append(pieces, prop.Assume(od1.eqs[k]))
		}
		if od1.ant != nil {
			// The monotone recipe runs at the canonical premise terms,
			// whose variables are the rule's own; the opened antecedent
			// is the same term at od1's binders.
			r := &d.Rules[j]
			m := dv.monotone(j, R1, transport)
			m = m.TermInst(varSubst(r.bound, od1.bound)...)
			// The substituted indices stand at the subject in the opened
			// premise; the canonical premise has them at the rule's
			// variables.
			var subst []core.TermSubst
			for i, v := range r.substituted {
				if !v.IsZero() {
					subst = append(subst, MakeTermSubst(v, subject[i]))
				}
			}
			if len(subst) > 0 {
				m = m.TermInst(subst...)
			}
			Assert(m.Conclusion().AlphaEquals(pieces2[len(pieces2)-1]))
			pieces = append(pieces, m)
		}
		w := conjoin(pieces)
		w = existsIntroChain(disjunctsR2[j], termsOf(od1.bound), w)
		w = orIntroAt(disjunctsR2, j, w) // {eqs, ant[R₁] leaves}, TR ⊢ D_R₂(ā)
		// The antecedent's leaves are separate hypotheses of the
		// monotone recipe: collapse them into the antecedent, then the
		// antecedent and the equations into the body.
		if od1.ant != nil {
			for _, pr := range antProjections(d.Rules[j].Ant, od1.ant) {
				if w.HasHyp(pr.Conclusion()) {
					w = w.DeriveHypFrom(pr)
				}
			}
		}
		for _, pr := range od1.projections() {
			w = w.DeriveHypFrom(pr)
		}
		for i := len(od1.bound) - 1; i >= 0; i-- {
			w = w.HypExists(od1.bound[i], existsBodyFrom(disjunctsR1[j], i))
		}
		fwdCases[j] = w
	}
	closedR2 := byCases(dv.disjunctionAt(subject, R2), disjunctsR1, fwdCases).
		PromoteHyp(dv.disjunctionAt(subject, R1)).
		ConclForAllList(d.subject...) // TR ⊢ ∀ā. D_R₁(ā) ⇒ D_R₂(ā)
	// R₁ := λā. D_c(ā), R₂ := λā. c(p̄, ā): TR becomes the ⇐ theorem.
	qAbs, ok := ext.ReverseAbsVars(dv.disjunctionAt(subject, dv.cRel), d.subject...).AsAbsTerm()
	Assert(ok)
	betaQ := chainBeta(qAbs, len(d.IndexTypes))
	betaC := chainBeta(cAbs, len(d.IndexTypes))
	closedQ := closedR2.
		TermInst(MakeTermSubst(R1, qAbs), MakeTermSubst(R2, dv.cRel)).
		Rewrite(betaQ).
		Rewrite(betaC).
		DeriveHypFrom(backwardAll) // ⊢ closed(Q)  (β-reduced)

	// c(p̄, ā) ⊢ closed(Q) ⇒ D_c(ā), then the modus ponens.
	forward := dv.unfoldAt(subject).
		EqMP(prop.Assume(cApp)).
		ConclForAllInst(qAbs).
		Rewrite(betaQ).
		DemoteHyp().
		DeriveHypFrom(closedQ) // c(p̄, ā) ⊢ D_c(ā)

	iff := backward.Deduct(forward) // ⊢ c(p̄, ā) ⇔ D_c(ā)
	return iff.ConclForAllList(d.subject...).ConclForAllList(d.Params...)
}

// inductStrong: ∀p̄ P x̄. rulesStrong[c, P] ∧ c(p̄, x̄) ⇒ P(x̄).
//
// Weak induction run on Q := λx̄. c(p̄, x̄) ∧ P(x̄) — the move three
// chapters were making by hand. What weak induction asks for at Q is
// each rule with Q in its premises AND its conclusion; a premise at Q
// IS a strengthened premise, Q's body being that conjunction, so the
// strengthened obligation supplies the conclusion's property half
// outright, and Rules supplies its relation half from the premises'
// own relation halves — the monotonicity recipe at the transport
// Q ⇒ c. Reading the conclusion back is one projection.
func (dv *inductiveDeriver) inductStrong() *PropWrapper {
	d := dv.d
	P := d.motive()
	xs := d.conclusionVars()
	subject := termsOf(d.subject)
	cAt := func(args []Term) Term { return d.relationApp(dv.c, dv.params, args) }

	// Q, as the λ the weak principle is instantiated at.
	qBody := WrapTerm(cAt(subject)).And(Apply(P, subject...).Core()).Core()
	qAbs, ok := ext.ReverseAbsVars(qBody, d.subject...).AsAbsTerm()
	Assert(ok)
	betaQ := chainBeta(qAbs, len(d.IndexTypes))
	betaC := chainBeta(dv.cRel.(core.AbsTerm), len(d.IndexTypes))

	// The monotonicity recipe runs at relation VARIABLES; the transport
	// it needs, once instantiated, is the conjunction's left projection.
	avoid := append(d.avoidTerms(), P)
	R1 := Var("R1", d.rel.Type()).Core().(VarTerm).RenameToAvoid(avoid...)
	R2 := Var("R2", d.rel.Type()).Core().(VarTerm).RenameToAvoid(append(avoid, R1)...)
	transport := WrapTerm(Apply(R1, subject...).Core()).Imply(Apply(R2, subject...).Core()).Core()
	for i := len(d.subject) - 1; i >= 0; i-- {
		transport = ForAll(d.subject[i])(transport).Core()
	}
	transportThm := prop.HypAND0(cAt(subject), Apply(P, subject...).Core()).
		PromoteHyp(qBody).
		ConclForAllList(d.subject...) // ⊢ ∀ā. (c(p̄, ā) ∧ P(ā)) ⇒ c(p̄, ā)

	// The two premise sets, each read conjunct by conjunct.
	rulesStrong := d.rulesStrongAt(dv.c, dv.params, P)
	strongThms := prop.HypANDRecursive(ruleStrongTerms(d, dv.c, dv.params, P)...)
	rulesThm := dv.rules().ConclForAllInsts(dv.params...)
	ruleThms := prop.HypANDRecursive(ruleTermsAtConst(d, dv.c, dv.params)...)
	for j := range ruleThms {
		ruleThms[j] = ruleThms[j].DeriveHypFrom(rulesThm) // ⊢ ruleⱼ[c]
	}

	atQ := make([]*PropWrapper, len(d.Rules))
	for j := range d.Rules {
		r := &d.Rules[j]
		witnesses := termsOf(r.Vars)
		// The property half: the strengthened obligation at this rule's
		// own variables, fed its antecedent.
		pHalf := strongThms[j].ConclForAllInsts(witnesses...)
		var antQ Term
		if r.Ant != nil {
			antQ = d.antStrongAt(r.Ant, dv.c, dv.params, P)
			pHalf = pHalf.DemoteHyp() // …, ant[c ∧ P] ⊢ P(t̄)
		}
		// The relation half: rule j at the constant, its antecedent
		// obtained from the strengthened one by monotonicity.
		rHalf := ruleThms[j].ConclForAllInsts(witnesses...)
		if r.Ant != nil {
			carried := dv.monotone(j, R1, transport).
				TermInst(MakeTermSubst(R1, qAbs), MakeTermSubst(R2, dv.cRel)).
				Rewrite(betaQ).
				Rewrite(betaC)
			// A rule whose premises are all side conditions never spent
			// the transport: its antecedent is R-free and carries across
			// unchanged.
			if carried.HasHyp(transportThm.Conclusion()) {
				carried = carried.DeriveHypFrom(transportThm) // {ant[c ∧ P] leaves} ⊢ ant[c]
			}
			rHalf = hypFrom(rHalf.DemoteHyp(), carried, "induct strong: the relation half")
			for _, pr := range antProjections(r.Ant, antQ) {
				if rHalf.HasHyp(pr.Conclusion()) {
					rHalf = rHalf.DeriveHypFrom(pr)
				}
			}
		}
		w := prop.ConclAND(rHalf.Conclusion(), pHalf.Conclusion()).
			DeriveHypFrom(rHalf).
			DeriveHypFrom(pHalf) // …, ant[c ∧ P] ⊢ c(p̄, t̄) ∧ P(t̄)
		if r.Ant != nil {
			w = w.PromoteHyp(antQ)
		}
		atQ[j] = w.ConclForAllList(r.Vars...)
	}

	// The weak principle at Q, fed those obligations.
	obligations := conjoin(atQ)
	xsT := termsOf(xs)
	carried := dv.inductCurried().
		ConclForAllInsts(dv.params...).
		ConclForAllInst(qAbs).
		Rewrite(betaQ).
		DemoteHyp().
		DeriveHypFrom(obligations). // rulesStrong ⊢ ∀x̄. c(p̄, x̄) ⇒ c(p̄, x̄) ∧ P(x̄)
		ConclForAllInsts(xsT...).
		DemoteHyp()
	open := prop.HypAND1(cAt(xsT), Apply(P, xsT...).Core()).
		DeriveHypFrom(carried) // rulesStrong, c(p̄, x̄) ⊢ P(x̄)
	return dv.closeStandard(open, P, rulesStrong)
}

// ruleStrongTerms lists the strengthened obligations.
func ruleStrongTerms(d *InductiveDefinition, c ConstTerm, params []Term, P VarTerm) []Term {
	out := make([]Term, len(d.Rules))
	for j := range d.Rules {
		out[j] = d.ruleStrongAt(j, c, params, P)
	}
	return out
}

// ruleTermsAtConst lists the rules at the constant.
func ruleTermsAtConst(d *InductiveDefinition, c ConstTerm, params []Term) []Term {
	out := make([]Term, len(d.Rules))
	for j := range d.Rules {
		out[j] = d.ruleAt(j, c, params)
	}
	return out
}

// InductiveUnfoldRefusal reports, for a constant whose definition is
// an inductive closure, the refusal every unfold surface raises: the
// closure form is not a proof surface — its three theorems are.
func InductiveUnfoldRefusal(c ConstTerm) error {
	if !IsInductiveConstDef(c) {
		return nil
	}
	return fmt.Errorf("%s is an inductively defined relation: its closure form is not a proof surface. "+
		"Cite instead one of the theorems its definition comes with — its introduction rules, its rule "+
		"induction, that induction strengthened, or its case analysis; the chapter registers them beside "+
		"the constant, named for it (a `retrieve` or the family's own file names them)", c.Name())
}

// IsInductiveConstDef recognizes the closure body shape on a defined
// constant: λp̄. λx̄. ∀R'. (∀ā. D ⇒ R'(ā)) ⇒ R'(x̄), R' a bound relation
// applied at the head of both consequents.
func IsInductiveConstDef(c ConstTerm) bool {
	def := c.DefThm()
	if def.IsZero() {
		return false
	}
	l, r, ok := ext.MatchesEQ(def.Conclusion())
	if !ok || !l.Equals(c) {
		return false
	}
	_, body := ext.MatchesAbs(r)
	relAbs := ext.MatchesFORALL(body)
	if relAbs.IsZero() {
		return false
	}
	rel := relAbs.Var()
	closed, concl, ok := ext.MatchesIMPLY(relAbs.Body())
	if !ok {
		return false
	}
	if head, _ := ext.MatchesApply(concl); !head.Equals(rel) {
		return false
	}
	_, matrix := ext.DecomposesFORALL(closed)
	_, ruleConcl, ok := ext.MatchesIMPLY(matrix)
	if !ok {
		return false
	}
	head, _ := ext.MatchesApply(ruleConcl)
	return head.Equals(rel)
}
