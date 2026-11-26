// define_wf.go: well-founded recursion:
//
//   - ONE total equation, COND-form: f(x̄) = <COND tree>, the LHS
//     arguments all plain distinct variables (no constructor pattern —
//     that absence is what routes here rather than to the primrec
//     compiler).
//   - `measure:` — a term over the RECURSION ARGUMENT alone
//     (carrier → num), its λ-binder matched BY NAME against the LHS
//     argument it measures. The binder name is also how the payload
//     names the recursion position: the WF shape has no constructor
//     pattern to mark it.
//
// The move's obligation stays with the author: analysis builds
// the TERMINATION statement — for every recursive call site, under
// the COND guards in force on its path, the measure strictly drops —
// and the define composite surfaces it as the section's one open
// child. The compiler (CompileWFExistence, §"The compiler") consumes
// the closed obligation: continuity from termination by the
// COND-congruence walker, wellfounded(measure_less(measure)) from the served
// wellfounded_measure_less, the existence from the served wellfounded_recursion, and the
// canonical→author transfer (the v1.1 machinery's single-equation
// sibling).
//
// The file runs the shape's whole pipeline, in the order the move
// executes it: analysis and mint here, then §"The compiler"
// (existence from the served schema rows), §"The kernel derivations" (the
// continuity walker and the existence transfer it calls), and §"The guarded
// readings" (the manual's R4 — the per-COND-leaf equations a
// `define` returns, which are what reaches the simp set).

package proof

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// WFCallSite is one recursive call occurrence in the equation's RHS:
// the guard literals in force on its COND path (outermost first, each
// the guard term or its negation as the branch took it), and the
// call's arguments in author order.
type WFCallSite struct {
	Guards []Term
	Args   []Term
}

// RecArg is the call's recursion-position argument.
func (s *WFCallSite) RecArg(recPos int) Term { return s.Args[recPos] }

// WFDefinition is the analyzed form of a well-founded recursive
// definition — the definiendum still a VARIABLE (the mint has not
// happened), exactly the RecursiveDefinition convention.
type WFDefinition struct {
	DefVar VarTerm
	// ArgVars are the LHS argument variables, author order.
	ArgVars []VarTerm
	// ArgTypes are their types; ArgTypes[RecArgPos] is the carrier.
	ArgTypes []HolType
	// ResultType is what remains of DefVar's type after the spelled
	// arity.
	ResultType HolType
	// RecArgPos is the recursion argument's position, named by the
	// measure's λ-binder.
	RecArgPos int
	// Measure is the parsed measure term, λ-formed: carrier → num.
	Measure Term
	// Rhs is the equation's right side — the COND tree.
	Rhs Term
	// CallSites are the recursive call occurrences in walk order
	// (guard tree depth-first, then-branch before else-branch) — the
	// order the obligation's conjuncts follow and the continuity
	// walker consumes.
	CallSites []WFCallSite

	// Property is P(f): the ∀-closed defining equation, DefVar free.
	Property Term
	// EpsTerm is εf. P(f) — the core.NewConstDef payload.
	EpsTerm Term
	// ExistsStmt is ∃f. P(f) — what the Hilbert bridge owes.
	ExistsStmt Prop
	// Obligation is the termination statement the author proves: for
	// each call site, ∀ArgVars. guards ⇒ measure(callRec) <
	// measure(recArg), conjoined in site order, β-normalized (the
	// author sees arithmetic, never the measure's λ).
	Obligation Prop
}

// AnalyzeWFDefinition validates a parsed definition equation plus a
// measure against the WF v1 shape and decomposes it. Strict: every
// deviation is an error naming its repair.
func AnalyzeWFDefinition(equation Prop, defVar VarTerm, measure Term) (*WFDefinition, error) {
	if equation == nil || defVar.IsZero() {
		return nil, fmt.Errorf("nil WF definition equation")
	}
	if measure == nil {
		return nil, fmt.Errorf("WF definition needs a measure")
	}
	if equation.NumHyps() != 0 {
		return nil, fmt.Errorf("definition equation must be hyp-free; got %d hyps",
			equation.NumHyps())
	}

	binders, matrix := DecomposesFORALL(equation.Conclusion())
	l, rhs, ok := MatchesEQ(matrix)
	if !ok {
		return nil, fmt.Errorf("equation body must be an equation (= / ⇔), got %q",
			PrintTerm(matrix))
	}
	head, lhsArgs := MatchesApply(l)
	headVar, ok := head.AsVar()
	if !ok || !headVar.EqualsVar(defVar) {
		return nil, fmt.Errorf(
			"the definiendum %q must head the LEFT side as %s(args…) = body",
			defVar.Name(), defVar.Name())
	}
	if len(lhsArgs) == 0 {
		return nil, fmt.Errorf(
			"a WF definition takes at least one argument (the recursion argument)")
	}
	argVars := make([]VarTerm, len(lhsArgs))
	for i, a := range lhsArgs {
		v, ok := a.AsVar()
		if !ok {
			return nil, fmt.Errorf(
				"WF LHS argument %d is %q — the WF shape takes plain variable "+
					"arguments (a constructor pattern routes to the structural "+
					"recursion compiler; drop the measure there)",
				i, PrintTerm(a))
		}
		for j := range i {
			if argVars[j].EqualsVar(v) {
				return nil, fmt.Errorf("LHS argument %q appears twice", v.Name())
			}
		}
		argVars[i] = v
	}
	// Binder hygiene: the ∀-prefix must close exactly the LHS
	// arguments (the defining-equation convention — the strict door
	// already refuses other frees; this refuses extra binders).
	if binders.Size() != len(argVars) {
		return nil, fmt.Errorf(
			"the equation's ∀-prefix closes %d variables but the LHS applies %d — "+
				"quantify exactly the arguments", binders.Size(), len(argVars))
	}

	// Peel the spelled arity off the definiendum's type.
	argTypes := make([]HolType, len(argVars))
	rest := defVar.Type()
	for i := range argVars {
		ct, ok := rest.(CompositeType)
		if !ok || !ext.IsFunType(ct) {
			return nil, fmt.Errorf(
				"the definiendum %q has type %s but the equation applies %d arguments",
				defVar.Name(), FormatType(defVar.Type()), len(argVars))
		}
		argTypes[i], rest = ct.SubType(0), ct.SubType(1)
	}

	// The measure names the recursion argument: a λ whose binder NAME
	// matches exactly one LHS argument (the ruling's convention), its
	// type the carrier, its body at num.
	mAbs, ok := measure.AsAbsTerm()
	if !ok {
		return nil, fmt.Errorf(
			"the measure must be a λ over the recursion argument (e.g. \"λn:num. n\"); "+
				"got %q", PrintTerm(measure))
	}
	recPos := -1
	for i, v := range argVars {
		if v.Name() == mAbs.Var().Name() {
			if recPos >= 0 {
				return nil, fmt.Errorf("internal: duplicate LHS argument name %q", v.Name())
			}
			recPos = i
		}
	}
	if recPos < 0 {
		names := make([]string, len(argVars))
		for i, v := range argVars {
			names[i] = string(v.Name())
		}
		return nil, fmt.Errorf(
			"the measure's binder %q names no LHS argument — spell it over the "+
				"argument the recursion descends on (the LHS arguments: %v)",
			mAbs.Var().Name(), names)
	}
	if !mAbs.Var().Type().Equals(argTypes[recPos]) {
		return nil, fmt.Errorf(
			"the measure's binder has type %s but the recursion argument %q has "+
				"type %s", FormatType(mAbs.Var().Type()),
			argVars[recPos].Name(), FormatType(argTypes[recPos]))
	}
	if !mAbs.Body().Type().Equals(NumType) {
		return nil, fmt.Errorf(
			"the measure must land in num (the ℕ-valued measure genre); its body "+
				"has type %s", FormatType(mAbs.Body().Type()))
	}

	// Walk the RHS: collect the recursive call sites with their guard
	// contexts; refuse every v1-excluded placement with the repair
	// named.
	var sites []WFCallSite
	if err := scanWFBody(rhs, defVar, argVars, nil, &sites); err != nil {
		return nil, err
	}
	if len(sites) == 0 {
		return nil, fmt.Errorf(
			"the RHS never calls %q — a definition with no recursion is the "+
				"direct shape; drop the measure", defVar.Name())
	}

	property := equation.Conclusion()
	eps := WrapTerm(defVar).SuchThat(WrapTerm(property)).Core()
	exists := core.MakeProp(Exists(WrapTerm(defVar))(WrapTerm(property)).Core())

	wfd := &WFDefinition{
		DefVar:     defVar,
		ArgVars:    argVars,
		ArgTypes:   argTypes,
		ResultType: rest,
		RecArgPos:  recPos,
		Measure:    measure,
		Rhs:        rhs,
		CallSites:  sites,
		Property:   property,
		EpsTerm:    eps,
		ExistsStmt: exists,
	}
	obligation, err := buildWFObligation(wfd)
	if err != nil {
		return nil, err
	}
	wfd.Obligation = obligation
	return wfd, nil
}

// scanWFBody walks a term of the defining equation's RHS collecting
// recursive call sites. guards carries the COND decisions in force on
// the path (outermost first; then-branch appends the guard, else-
// branch its negation). The v1 exclusions each error with the repair
// named:
//
//   - f in a COND guard (nested recursion in the test) — out of v1;
//   - f under a binder (recursion through a λ — the higher-order
//     genre) — out of v1;
//   - f partially applied or passed bare — the call must spell every
//     argument;
//   - f inside a recursive call's own arguments — out of v1.
func scanWFBody(t Term, defVar VarTerm, argVars []VarTerm, guards []Term, sites *[]WFCallSite) error {
	if !t.HasFree(defVar) {
		return nil
	}
	if v, ok := t.AsVar(); ok {
		if v.EqualsVar(defVar) {
			return fmt.Errorf(
				"%q occurs bare (unapplied) in the RHS — a v1 recursive call spells "+
					"every argument: %s(…)", defVar.Name(), defVar.Name())
		}
		return nil
	}
	if abs, ok := t.AsAbsTerm(); ok {
		// t has the definiendum free and is a binder: recursion through
		// a λ body.
		_ = abs
		return fmt.Errorf(
			"%q occurs under a binder in %q — recursion through a λ is out of the "+
				"WF v1 shape (the higher-order genre)", defVar.Name(), PrintTerm(t))
	}
	if g, th, el, ok := MatchesCond(t); ok {
		if g.HasFree(defVar) {
			return fmt.Errorf(
				"%q occurs in a COND guard %q — recursion in the test is out of the "+
					"WF v1 shape", defVar.Name(), PrintTerm(g))
		}
		if err := scanWFBody(th, defVar, argVars, append(guards, g), sites); err != nil {
			return err
		}
		return scanWFBody(el, defVar, argVars, append(guards, Not(WrapTerm(g)).Core()), sites)
	}
	head, args := MatchesApply(t)
	if hv, ok := head.AsVar(); ok && hv.EqualsVar(defVar) {
		if len(args) != len(argVars) {
			return fmt.Errorf(
				"recursive call %q applies %d arguments; the definition spells %d — "+
					"a v1 call carries the full argument list",
				PrintTerm(t), len(args), len(argVars))
		}
		for _, a := range args {
			if a.HasFree(defVar) {
				return fmt.Errorf(
					"recursive call %q nests %q inside its own arguments — nested "+
						"recursion is out of the WF v1 shape",
					PrintTerm(t), defVar.Name())
			}
		}
		*sites = append(*sites, WFCallSite{
			Guards: append([]Term(nil), guards...),
			Args:   args,
		})
		return nil
	}
	if err := scanWFBody(head, defVar, argVars, guards, sites); err != nil {
		return err
	}
	for _, a := range args {
		if err := scanWFBody(a, defVar, argVars, guards, sites); err != nil {
			return err
		}
	}
	return nil
}

// buildWFObligation builds the termination statement: one conjunct
// per call site — ∀ArgVars. g₁ ⇒ … ⇒ gₖ ⇒ measure(callRec) <
// measure(recArg) — in site order, β-normalized so the author reads
// arithmetic, never the measure's λ.
func buildWFObligation(wfd *WFDefinition) (Prop, error) {
	conjuncts := make([]Term, len(wfd.CallSites))
	for i := range wfd.CallSites {
		s := &wfd.CallSites[i]
		body := Apply(dsl.NatLtMeta.Term(),
			Apply(wfd.Measure, s.RecArg(wfd.RecArgPos)).Core(),
			Apply(wfd.Measure, wfd.ArgVars[wfd.RecArgPos]).Core()).Core()
		for j := len(s.Guards) - 1; j >= 0; j-- {
			body = WrapTerm(s.Guards[j]).Imply(WrapTerm(body)).Core()
		}
		for j := len(wfd.ArgVars) - 1; j >= 0; j-- {
			body = ForAll(wfd.ArgVars[j])(WrapTerm(body)).Core()
		}
		conjuncts[i] = body
	}
	stmt := conjuncts[len(conjuncts)-1]
	for i := len(conjuncts) - 2; i >= 0; i-- {
		stmt = ext.And(conjuncts[i], stmt).Core()
	}
	// β-normalize the measure applications (measure = λn.body applied
	// at the call arguments). DeepBeta returns nil when there is
	// nothing to reduce.
	if eq := DeepBeta(stmt); eq != nil {
		stmt = Rhs(eq)
	}
	return core.MakeProp(stmt), nil
}

// Extras are the LHS argument variables other than the recursion
// argument, author order — the canonical motive's curried parameters
// (the v1.1 convention).
func (wfd *WFDefinition) Extras() []VarTerm {
	out := make([]VarTerm, 0, len(wfd.ArgVars)-1)
	for i, v := range wfd.ArgVars {
		if i != wfd.RecArgPos {
			out = append(out, v)
		}
	}
	return out
}

// Motive is the canonical result type: the extra argument types
// folded onto the remaining result — what the WF schema's B
// instantiates at.
func (wfd *WFDefinition) Motive() HolType {
	motive := wfd.ResultType
	for i := len(wfd.ArgVars) - 1; i >= 0; i-- {
		if i == wfd.RecArgPos {
			continue
		}
		motive = MakeFun(wfd.ArgTypes[i], motive)
	}
	return motive
}

// Functional builds the WF schema's H — the equation's RHS abstracted
// into the recursion functional:
//
//	H := λφ. λ<recArg>. λ<extras…>. RHS[f(t̄) ↦ φ(t_rec)(t̄ ∖ rec)]
//
// φ at carrier → motive (the canonical function the schema's ∃f
// speaks), the value binders the author's own LHS variables (the RHS
// is free in exactly them, so no capture is possible; φ is renamed
// clear of everything in sight). Recursive calls canonicalize with
// the recursion argument hoisted — permuteRecCalls, the v1.1b
// machinery — or, when the recursion argument already comes first, by
// the plain definiendum→φ substitution (the author's spine is already
// canonical there).
func (wfd *WFDefinition) Functional() Term {
	phi := Var("φ", MakeFun(wfd.ArgTypes[wfd.RecArgPos], wfd.Motive())).Core().(VarTerm)
	avoid := make([]Term, 0, len(wfd.ArgVars)+2)
	avoid = append(avoid, wfd.Rhs, wfd.DefVar)
	for _, v := range wfd.ArgVars {
		avoid = append(avoid, v)
	}
	phi = phi.RenameToAvoid(avoid...)

	body := wfd.Rhs
	if wfd.RecArgPos == 0 {
		body = body.Substitute(MakeTermSubst(wfd.DefVar, phi))
	} else {
		body = permuteRecCalls(body, wfd.DefVar, phi, wfd.RecArgPos)
	}
	for _, v := range slices.Backward(wfd.Extras()) {
		body = Abs(v, body)
	}
	body = Abs(wfd.ArgVars[wfd.RecArgPos], body)
	return Abs(phi, body)
}

// AnalyzeWFExistence re-analyzes a WF definition from its existence
// obligation ∃f. P(f) plus the measure — the _DefineStep executor's
// entry: the ε-payload carries P(f), the proto carries the measure,
// and together they determine the termination obligation child.
func AnalyzeWFExistence(exists Prop, measure Term) (*WFDefinition, error) {
	if exists == nil || exists.NumHyps() != 0 {
		return nil, fmt.Errorf("existence obligation must be a hyp-free statement")
	}
	abs := MatchesEXISTS(exists.Conclusion())
	if abs.IsZero() {
		return nil, fmt.Errorf("existence obligation must be ∃-headed, got %q",
			PrintTerm(exists.Conclusion()))
	}
	return AnalyzeWFDefinition(core.MakeProp(abs.Body()), abs.Var(), measure)
}

// MintWFDefinition performs the kernel mint for an analyzed WF
// definition — c := εf. P(f), the MintRecursiveDefinition shape at the
// WF analysis. Returns the minted const and the characterizing
// statement P(c), UNPROVED: the definition section proves it through
// _DefineStep's WF branch, whose termination obligation the AUTHOR
// closes and whose existence the WF compiler then discharges.
func MintWFDefinition(env *ProverEnv, wfd *WFDefinition) (ConstTerm, Prop, error) {
	c, err := mintDefinedConst(env, wfd.DefVar.Name(), wfd.EpsTerm)
	if err != nil {
		return ConstTerm{}, nil, err
	}
	characterizing := core.MakeProp(
		wfd.Property.Substitute(MakeTermSubst(wfd.DefVar, c)))
	return c, characterizing, nil
}

// =======================================================================
// The compiler — existence from wellfounded_recursion
// =======================================================================
//
// The WF equation compiler: prove the existence obligation ∃f.P(f)
// of a COND-form well-founded definition from the served wellfounded_recursion
// schema, the served wellfounded_measure_less fact, and the AUTHOR-PROVED
// termination theorem. Pure statement-level derivation —
// deterministic, refuter-free, promise-transparent (the P4a
// compiler's discipline); every "internal:" error is an engine fault.
//
// The pipeline, in schema terms (A := the carrier, B := the motive):
//
//	wellfounded_recursion:      ∀H R. wellfounded(R) ⇒ continuity(H, R) ⇒ ∃f. ∀x. f(x) = H(f, x)
//	wellfounded_measure_less:  ∀m. wellfounded(measure_less(m))
//
//	H := the definition's functional (WFDefinition.Functional)
//	R := measure_less(measure)
//	WF premise   — wellfounded_measure_less at the measure;
//	continuity   — derived from the termination theorem by the
//	               COND-congruence walker (deriveWFContinuity): the
//	               only place the recursion's mathematics lives, and
//	               it consumes exactly the obligation the author
//	               closed;
//	existence    — MP, β-normalize, canonical→author transfer (the
//	               v1.1 choose dance at the WF single-equation shape),
//	               BridgeNormalize into the obligation's arrangement.
//
// Both arrangements of the schema rows are accepted — the sequent
// forms (wellfounded(R) a hyp, H and R free) and the wellfounded chapter's
// ∀-closed canonical statements, which are what the corpus serves.

// WFRecName / WFMeasureName are the library-theorem names the WF
// compiler resolves its schema pieces at — the conventional names
// the corpus serves (and the overlay re-serves).
const (
	WFRecName     = "wellfounded_recursion"
	WFMeasureName = "wellfounded_measure_less"
)

// CompileWFExistence proves the existence obligation of an analyzed WF
// definition from the served schema rows plus the author-proved
// termination theorem. Returns the proved obligation (in
// wfd.ExistsStmt's own arrangement) and the schema's name.
func CompileWFExistence(env *ProverEnv, wfd *WFDefinition, termination Prop) (Prop, string, error) {
	if env == nil {
		return nil, "", fmt.Errorf("compile WF definition: nil env")
	}
	if termination == nil || termination.NumHyps() != 0 {
		return nil, "", fmt.Errorf("compile WF definition: the termination theorem "+
			"must be a hyp-free proved statement; got %v", termination)
	}
	if !core.MakeProp(termination.Conclusion()).AlphaEquals(wfd.Obligation) {
		return nil, "", fmt.Errorf(
			"the closed obligation is not the definition's termination statement\n"+
				"  proved: %s\n  wanted: %s",
			PrintTerm(termination.Conclusion()), PrintProp(wfd.Obligation))
	}

	carrier := wfd.ArgTypes[wfd.RecArgPos]
	hTerm := wfd.Functional()

	// wellfounded(measure_less(measure)) — the WF premise, from the served
	// wellfounded_measure_less at the measure. The measure_less constant itself is read
	// off the instantiated statement, so no constant table is needed.
	wfMeasure, err := lookupWFRow(env, WFMeasureName)
	if err != nil {
		return nil, "", err
	}
	wfThm, err := instantiateWFMeasure(wfMeasure, carrier, wfd.Measure)
	if err != nil {
		return nil, "", fmt.Errorf("%s: %v", WFMeasureName, err)
	}
	_, wfArgs := MatchesApply(wfThm.Conclusion())
	if len(wfArgs) != 1 {
		return nil, "", fmt.Errorf("internal: instantiated %s is not wellfounded(R)-shaped: %s",
			WFMeasureName, PrintTerm(wfThm.Conclusion()))
	}
	rTerm := wfArgs[0]

	// The schema, instantiated at H and R, its two premises left as
	// hyps.
	wfRec, err := lookupWFRow(env, WFRecName)
	if err != nil {
		return nil, "", err
	}
	inst, err := instantiateWFRec(wfRec, hTerm, rTerm)
	if err != nil {
		return nil, "", fmt.Errorf("%s: %v", WFRecName, err)
	}

	// Discharge the premises: the WF-shaped hyp against the measure
	// fact, the other against the derived continuity.
	w := inst
	for _, h := range inst.Hyps() {
		if h.AlphaEquals(wfThm.Conclusion()) {
			w = WrapProp(w).DeriveHypFrom(wfThm)
			continue
		}
		cont, err := deriveWFContinuity(h, wfd, rTerm, termination)
		if err != nil {
			return nil, "", fmt.Errorf("continuity: %v", err)
		}
		w = WrapProp(w).DeriveHypFrom(cont)
	}
	if w.NumHyps() != 0 {
		return nil, "", fmt.Errorf("internal: schema premises not fully discharged: %s",
			PrintProp(w))
	}

	// β-normalize the canonical existence and transfer to the author's
	// spelling.
	proved := WrapProp(w).Rewrite(DeepBeta)
	transferred, err := transferWFExistence(wfd, proved)
	if err != nil {
		return nil, "", err
	}
	aligned := BridgeNormalize(wfd.ExistsStmt, transferred)
	if aligned == nil {
		return nil, "", fmt.Errorf(
			"internal: the transferred instance is not normalize-equivalent to the "+
				"equation's existence form\n  instance: %s\n  wanted:   %s",
			PrintProp(transferred), PrintProp(wfd.ExistsStmt))
	}
	return aligned, WFRecName, nil
}

// lookupWFRow resolves one schema row by name in the env's library
// theorems, with the repair named.
func lookupWFRow(env *ProverEnv, name string) (Prop, error) {
	thm, ok := env.LookupLibraryThm(name)
	if !ok || thm == nil {
		return nil, fmt.Errorf(
			"no library theorem named %q in scope — the WF compiler needs the "+
				"schema rows served (corpus LibraryThms, or the entry's declared deps)",
			name)
	}
	return thm, nil
}

// instantiateWFMeasure lands the served wellfounded_measure_less row at the
// definition's measure: ⊢ wellfounded(measure_less(measure)). Accepts both serving
// arrangements — ∀m-closed (chapter) and free-m (sequent).
func instantiateWFMeasure(row Prop, carrier HolType, measure Term) (Prop, error) {
	if row.NumHyps() != 0 {
		return nil, fmt.Errorf("unexpected hyps on the wellfounded_measure_less row: %s", PrintProp(row))
	}
	measureType := MakeFun(carrier, NumType)

	binders, matrix := DecomposesFORALL(row.Conclusion())
	var mVar VarTerm
	for v := range binders.Iter() {
		if _, ok := v.Type().(CompositeType); ok {
			mVar = v
		}
	}
	if binders.Size() == 0 {
		// Free-m arrangement: the measure variable is wellfounded's argument's
		// own head argument — wellfounded(measure_less(m)).
		_, args := MatchesApply(matrix)
		if len(args) == 1 {
			_, inner := MatchesApply(args[0])
			if len(inner) == 1 {
				if v, ok := inner[0].AsVar(); ok {
					mVar = v
				}
			}
		}
	}
	if mVar.IsZero() {
		return nil, fmt.Errorf("row has no measure slot: %s", PrintProp(row))
	}
	substs, ok := mVar.Type().Matches(measureType, func(VarType) bool { return true })
	if !ok {
		return nil, fmt.Errorf("measure slot type %s cannot instantiate at %s",
			FormatType(mVar.Type()), FormatType(measureType))
	}
	typed := core.PropTypeInst(row, substs...)
	if binders.Size() > 0 {
		return WrapProp(typed).ConclForAllInsts(measure), nil
	}
	typedVar := Var(mVar.Name(), measureType).Core().(VarTerm)
	return WrapProp(core.PropTermInst(WrapProp(typed),
		MakeTermSubst(typedVar, measure))), nil
}

// instantiateWFRec lands the served wellfounded_recursion row at the definition's
// functional and relation, with the two premises (wellfounded(R), continuity)
// left as HYPS of the returned prop. Accepts both serving
// arrangements:
//
//	chapter:   ⊢ ∀H R. wellfounded(R) ⇒ cont ⇒ ∃f. ∀x. f(x) = H(f, x)
//	sequent:   wellfounded(R) ⊢ cont ⇒ ∃f. ∀x. f(x) = H(f, x)   (H, R free)
func instantiateWFRec(row Prop, hTerm, rTerm Term) (Prop, error) {
	hType := hTerm.Type()
	rType := rTerm.Type()

	classify := func(vars []VarTerm) (h, r VarTerm, err error) {
		for _, v := range vars {
			switch {
			case typeShapeMatches(v.Type(), hType):
				if !h.IsZero() && !h.EqualsVar(v) {
					return VarTerm{}, VarTerm{}, fmt.Errorf("two functional-shaped slots (%s, %s)",
						h.Name(), v.Name())
				}
				h = v
			case typeShapeMatches(v.Type(), rType):
				if !r.IsZero() && !r.EqualsVar(v) {
					return VarTerm{}, VarTerm{}, fmt.Errorf("two relation-shaped slots (%s, %s)",
						r.Name(), v.Name())
				}
				r = v
			}
		}
		if h.IsZero() || r.IsZero() {
			return VarTerm{}, VarTerm{}, fmt.Errorf("could not locate the H and R slots")
		}
		return h, r, nil
	}

	binders, _ := DecomposesFORALL(row.Conclusion())
	if row.NumHyps() == 0 && binders.Size() >= 2 {
		// Closed arrangement.
		vars := make([]VarTerm, 0, binders.Size())
		for v := range binders.Iter() {
			vars = append(vars, v)
		}
		h, r, err := classify(vars)
		if err != nil {
			return nil, err
		}
		substs, ok := h.Type().Matches(hType, func(VarType) bool { return true })
		if !ok {
			return nil, fmt.Errorf("H slot type %s cannot instantiate at %s",
				FormatType(h.Type()), FormatType(hType))
		}
		if !r.Type().Substitute(substs...).Equals(rType) {
			return nil, fmt.Errorf("R slot type %s does not land at %s under the H "+
				"instantiation", FormatType(r.Type()), FormatType(rType))
		}
		typed := WrapProp(core.PropTypeInst(row, substs...))
		// Re-read the (now concrete) binder list and instantiate in
		// the row's own order.
		tBinders, _ := DecomposesFORALL(typed.Conclusion())
		args := make([]Term, 0, tBinders.Size())
		for v := range tBinders.Iter() {
			switch {
			case v.Type().Equals(hType):
				args = append(args, hTerm)
			case v.Type().Equals(rType):
				args = append(args, rTerm)
			default:
				return nil, fmt.Errorf("unexpected extra ∀-slot %q at %s",
					v.Name(), FormatType(v.Type()))
			}
		}
		w := typed.ConclForAllInsts(args...)
		return demoteWFPremises(w)
	}

	// Sequent arrangement: H and R free — located structurally: R off
	// the WF hyp, H off the ∃-body equation's right side.
	var slots []VarTerm
	for _, hyp := range row.Hyps() {
		if _, args := MatchesApply(hyp); len(args) == 1 {
			if v, ok := args[0].AsVar(); ok {
				slots = append(slots, v)
			}
		}
	}
	concl := row.Conclusion()
	if _, rSide, ok := MatchesIMPLY(concl); ok {
		concl = rSide
	}
	if abs := MatchesEXISTS(concl); !abs.IsZero() {
		_, matrix := DecomposesFORALL(abs.Body())
		if _, rhs, ok := MatchesEQ(matrix); ok {
			if head, _ := MatchesApply(rhs); head != nil {
				if v, ok := head.AsVar(); ok {
					slots = append(slots, v)
				}
			}
		}
	}
	h, r, err := classify(slots)
	if err != nil {
		return nil, err
	}
	substs, ok := h.Type().Matches(hType, func(VarType) bool { return true })
	if !ok {
		return nil, fmt.Errorf("H slot type %s cannot instantiate at %s",
			FormatType(h.Type()), FormatType(hType))
	}
	moreSubsts, ok := r.Type().Substitute(substs...).Matches(rType,
		func(VarType) bool { return true })
	if !ok {
		return nil, fmt.Errorf("R slot type %s cannot instantiate at %s",
			FormatType(r.Type()), FormatType(rType))
	}
	typed := core.PropTypeInst(row, append(substs, moreSubsts...)...)
	hTyped := Var(h.Name(), hType).Core().(VarTerm)
	rTyped := Var(r.Name(), rType).Core().(VarTerm)
	inst := core.PropTermInst(WrapProp(typed),
		MakeTermSubst(hTyped, hTerm), MakeTermSubst(rTyped, rTerm))
	return demoteWFPremises(WrapProp(inst))
}

// typeShapeMatches reports whether abstract (a slot's type) matches
// concrete under full type-variable instantiation.
func typeShapeMatches(abstract, concrete HolType) bool {
	_, ok := abstract.Matches(concrete, func(VarType) bool { return true })
	return ok
}

// demoteWFPremises moves implication antecedents into hyps until the
// conclusion is ∃-headed — at most the two schema premises, conjoined in
// one antecedent or curried, each its own hyp either way.
func demoteWFPremises(w *PropWrapper) (Prop, error) {
	for range 2 {
		if !MatchesEXISTS(w.Conclusion()).IsZero() {
			return w, nil
		}
		ante, _, ok := MatchesIMPLY(w.Conclusion())
		if !ok {
			break
		}
		w = w.DemoteHyp()
		if pieces := prop.LeftConjuncts(ante); len(pieces) > 1 {
			all := make([]int, len(pieces))
			for i := range all {
				all[i] = i
			}
			w = prop.ConjunctionFromPieces(pieces, all).DeriveTrans(w)
		}
	}
	if MatchesEXISTS(w.Conclusion()).IsZero() {
		return nil, fmt.Errorf("instantiated schema is not (premises ⇒) ∃-headed: %s",
			PrintProp(w))
	}
	return w, nil
}

// =======================================================================
// The kernel derivations — continuity and transfer
// =======================================================================
//
// The compiler's two kernel derivations: the continuity premise
// from the author's termination theorem (the COND-congruence
// walker), and the canonical→author existence transfer (the v1.1
// choose dance at the WF single-equation shape). Pure prop-layer
// forward derivation — deterministic, refuter-free; "internal:"
// errors are engine faults.

// deriveWFContinuity proves the schema's continuity premise — the
// exact hyp term the instantiated schema carries:
//
//	∀f g. ∀x. (∀z. R(z, x) ⇒ f(z) = g(z)) ⇒ H(f, x) = H(g, x)
//
// from the termination theorem. The structure mirrors the definition
// body: β-reduce both H-applications, peel the shared value-λs, and
// walk the two bodies in lockstep — identical away from the recursive
// calls, so reflexivity and PropApply carry everything except:
//
//   - a COND node, closed by case split on its guard (condCongruence:
//     the guard rewritten to ⊤/⊥ under its own assumption, the branch
//     reduced by the bootstrap COND clauses, ByCases over the excluded
//     middle);
//   - a recursive call f(a)(w̄) vs g(a)(w̄), closed from the agreement
//     antecedent at z := a, whose R(a, x) side is the termination
//     theorem's conjunct for THIS site — instantiated at the ambient
//     argument values, its guard antecedents left as hyps for the
//     enclosing COND splits to consume.
func deriveWFContinuity(target Term, wfd *WFDefinition, rTerm Term, termination Prop) (Prop, error) {
	// Decompose the target: ∀f g x. A ⇒ lhs = rhs.
	binders, matrix := DecomposesFORALL(target)
	if binders.Size() != 3 {
		return nil, fmt.Errorf("internal: continuity premise closes %d variables, want 3: %s",
			binders.Size(), PrintTerm(target))
	}
	vars := make([]VarTerm, 0, 3)
	for v := range binders.Iter() {
		vars = append(vars, v)
	}
	fVar, gVar, xVar := vars[0], vars[1], vars[2]
	aTerm, eqTerm, ok := MatchesIMPLY(matrix)
	if !ok {
		return nil, fmt.Errorf("internal: continuity matrix is not an implication: %s",
			PrintTerm(matrix))
	}
	lhs, rhs, ok := MatchesEQ(eqTerm)
	if !ok {
		return nil, fmt.Errorf("internal: continuity conclusion is not an equation: %s",
			PrintTerm(eqTerm))
	}

	// β-reduce both sides: H(f)(x) ↠ λv̄. body.
	eqF := DeepBeta(lhs)
	eqG := DeepBeta(rhs)
	if eqF == nil || eqG == nil {
		return nil, fmt.Errorf("internal: the H-applications carry no β-redex: %s",
			PrintTerm(eqTerm))
	}
	nfF, nfG := Rhs(eqF), Rhs(eqG)

	// The termination conjuncts, one per call site, instantiated
	// lazily at the ambient argument values once the value-λs are
	// peeled.
	conjuncts := conjProject(WrapProp(termination))
	if len(conjuncts) != len(wfd.CallSites) {
		return nil, fmt.Errorf("internal: termination has %d conjuncts for %d call sites",
			len(conjuncts), len(wfd.CallSites))
	}

	// Peel the shared value-λs, walk, and re-abstract.
	type peeled struct{ v VarTerm }
	var lam []peeled
	tF, tG := nfF, nfG
	for {
		aF, okF := tF.AsAbsTerm()
		aG, okG := tG.AsAbsTerm()
		if !okF || !okG {
			break
		}
		if !aF.Var().EqualsVar(aG.Var()) {
			return nil, fmt.Errorf("internal: β-normal binders diverge: %s vs %s",
				PrintTerm(tF), PrintTerm(tG))
		}
		lam = append(lam, peeled{aF.Var()})
		tF, tG = aF.Body(), aG.Body()
	}

	// The ambient argument values, author-position order: the target's
	// x at the recursion position, the peeled binders at the extras.
	values := make([]Term, len(wfd.ArgVars))
	values[wfd.RecArgPos] = xVar
	li := 0
	for i := range wfd.ArgVars {
		if i == wfd.RecArgPos {
			continue
		}
		if li >= len(lam) {
			return nil, fmt.Errorf("internal: %d value-λs for %d extra arguments",
				len(lam), len(wfd.ArgVars)-1)
		}
		values[i] = lam[li].v
		li++
	}

	wk := &wfWalker{
		wfd: wfd, fVar: fVar, gVar: gVar, xVar: xVar,
		aTerm: aTerm, rTerm: rTerm,
		values: values, conjuncts: conjuncts,
	}
	body, err := wk.walk(tF, tG)
	if err != nil {
		return nil, err
	}
	if wk.site != len(wfd.CallSites) {
		return nil, fmt.Errorf("internal: walked %d call sites, analysis found %d",
			wk.site, len(wfd.CallSites))
	}
	for i := len(lam) - 1; i >= 0; i-- {
		body = body.Abs(lam[i].v)
	}

	// Bridge the β-reduction back: lhs = nfF = nfG = rhs.
	w := WrapProp(eqF).EqTrans(body).EqTrans(WrapProp(eqG).EqSym())
	// Discharge the agreement assumption and ∀-close in target order.
	return w.PromoteHyp(aTerm).ConclForAllList(fVar, gVar, xVar), nil
}

// wfWalker carries the lockstep walk's fixed context.
type wfWalker struct {
	wfd        *WFDefinition
	fVar, gVar VarTerm
	xVar       VarTerm
	aTerm      Term // the agreement antecedent ∀z. R(z,x) ⇒ f(z) = g(z)
	rTerm      Term // R := measure_less(measure)
	values     []Term
	conjuncts  []*PropWrapper
	site       int // next call-site index (walk order = analysis order)
}

// walk derives ⊢ tF = tG (guard-literal hyps pending) for two terms
// that differ only at recursive-call heads (f vs g).
func (wk *wfWalker) walk(tF, tG Term) (*PropWrapper, error) {
	if tF.AlphaEquals(tG) {
		return prop.Refl(tF), nil
	}
	if gd, thF, elF, ok := MatchesCond(tF); ok {
		gdG, thG, elG, okG := MatchesCond(tG)
		if !okG || !gd.AlphaEquals(gdG) {
			return nil, fmt.Errorf("internal: COND nodes diverge: %s vs %s",
				PrintTerm(tF), PrintTerm(tG))
		}
		wThen, err := wk.walk(thF, thG)
		if err != nil {
			return nil, err
		}
		wElse, err := wk.walk(elF, elG)
		if err != nil {
			return nil, err
		}
		head, _ := MatchesApply(tF)
		return condCongruence(head, gd, thF, elF, thG, elG, wThen, wElse), nil
	}
	head, args := MatchesApply(tF)
	if hv, ok := head.AsVar(); ok && hv.EqualsVar(wk.fVar) {
		return wk.callSite(tF, tG, args)
	}
	headG, argsG := MatchesApply(tG)
	if len(args) == 0 || len(args) != len(argsG) {
		return nil, fmt.Errorf("internal: application spines diverge: %s vs %s",
			PrintTerm(tF), PrintTerm(tG))
	}
	w, err := wk.walk(head, headG)
	if err != nil {
		return nil, err
	}
	for i, a := range args {
		wa, err := wk.walk(a, argsG[i])
		if err != nil {
			return nil, err
		}
		w = w.Apply(wa)
	}
	return w, nil
}

// callSite closes one recursive-call divergence f(a)(w̄) = g(a)(w̄):
// the agreement antecedent at z := a, its R(a, x) side proved from
// the termination conjunct for this site through the measure_less unfold.
// The conjunct's guard antecedents stay as hyps — the enclosing COND
// splits consume them.
func (wk *wfWalker) callSite(tF, tG Term, args []Term) (*PropWrapper, error) {
	if wk.site >= len(wk.conjuncts) {
		return nil, fmt.Errorf("internal: more call sites than termination conjuncts")
	}
	siteIdx := wk.site
	wk.site++
	a := args[0]

	// {guards} ⊢ measure(a) < measure(x) — the conjunct at the ambient
	// values, its guard antecedents demoted to hyps.
	dec := wk.conjuncts[siteIdx].ConclForAllInsts(wk.values...)
	nGuards := len(wk.wfd.CallSites[siteIdx].Guards)
	for range nGuards {
		dec = dec.DemoteHyp()
	}

	// ⊢ R(a, x) = (measure(a) < measure(x)): unfold measure_less at the
	// site and β-collapse the measure applications.
	measureHead, rArgs := MatchesApply(wk.rTerm)
	measureConst, ok := measureHead.AsConst()
	if !ok || len(rArgs) != 1 {
		return nil, fmt.Errorf("internal: R is not measure_less(measure)-shaped: %s",
			PrintTerm(wk.rTerm))
	}
	unfold := prop.ExpandDef(measureConst, rArgs[0], a, wk.xVar)
	if bet := DeepBeta(Rhs(unfold)); bet != nil {
		unfold = unfold.EqTrans(bet)
	}

	// {guards} ⊢ R(a, x).
	rFact := WrapProp(unfold).EqSym().EqMP(dec)

	// {A} ⊢ R(a, x) ⇒ f(a) = g(a), then MP.
	agree := prop.Assume(wk.aTerm).ConclForAllInst(a).DemoteHyp().DeriveHypFrom(rFact)

	// Apply the call's remaining arguments (f-free by analysis).
	w := agree
	for _, extra := range args[1:] {
		w = w.RightApply(extra)
	}
	if !w.Conclusion().AlphaEquals(WrapTerm(tF).Eq(WrapTerm(tG)).Core()) {
		return nil, fmt.Errorf(
			"internal: call-site derivation landed on %s, wanted %s = %s",
			PrintTerm(w.Conclusion()), PrintTerm(tF), PrintTerm(tG))
	}
	return w, nil
}

// condCongruence combines two branch equations, each proved under its
// own guard literal, into the COND-node equation:
//
//	{…, gd} ⊢ thF = thG    {…, ¬gd} ⊢ elF = elG
//	--------------------------------------------
//	   {…} ⊢ COND(gd, thF, elF) = COND(gd, thG, elG)
//
// by rewriting the guard to ⊤ (resp. ⊥) under its assumption, reducing
// with the bootstrap COND clauses, and closing over the excluded
// middle. head is the COND constant at this node's type instance.
func condCongruence(head Term, gd, thF, elF, thG, elG Term, wThen, wElse *PropWrapper) *PropWrapper {
	eqTerm := Cond(gd, thF, elF).Eq(Cond(gd, thG, elG)).Core()

	// {gd} ⊢ gd = ⊤ and {¬gd} ⊢ gd = ⊥ (shared with the readings
	// derivation).
	gdTrue := guardTrueEq(gd)
	notGd := Not(WrapTerm(gd)).Core()
	gdFalse := guardFalseEq(gd)

	// {gd} ⊢ COND(gd, x, y) = x, at both sides' branch pairs.
	reduceT := func(x, y Term) *PropWrapper {
		return gdTrue.LeftApply(head).RightApply(x).RightApply(y).
			EqTrans(prop.CondClauseT(x, y))
	}
	reduceF := func(x, y Term) *PropWrapper {
		return gdFalse.LeftApply(head).RightApply(x).RightApply(y).
			EqTrans(prop.CondClauseF(x, y))
	}

	thenCase := reduceT(thF, elF).EqTrans(wThen).EqTrans(reduceT(thG, elG).EqSym()).
		PromoteHyp(gd)
	elseCase := reduceF(thF, elF).EqTrans(wElse).EqTrans(reduceF(thG, elG).EqSym()).
		PromoteHyp(notGd)

	return prop.ByCases(eqTerm, gd, notGd).
		DeriveHypFrom(prop.ExcludedMiddle(gd)).
		DeriveHypFrom(thenCase).
		DeriveHypFrom(elseCase)
}

// transferWFExistence turns the compiled CANONICAL existence
// ⊢ ∃fc. ∀x. fc(x) = λv̄.body — fc at carrier → motive — into the
// AUTHOR-form existence ⊢ ∃f. ∀x̄. f(x̄) = rhs the obligation states:
// the v1.1 transfer at the WF single-equation shape (no constructor
// matching; one clause, plain-variable recursion argument).
func transferWFExistence(wfd *WFDefinition, proved Prop) (Prop, error) {
	abs := MatchesEXISTS(proved.Conclusion())
	if abs.IsZero() {
		return nil, fmt.Errorf("internal: compiled WF instance is not ∃-headed: %s",
			PrintTerm(proved.Conclusion()))
	}
	avoid := make([]Term, 0, len(wfd.ArgVars)+2)
	avoid = append(avoid, wfd.Property, wfd.DefVar)
	for _, v := range wfd.ArgVars {
		avoid = append(avoid, v)
	}
	fnVar := abs.Var().RenameToAvoid(avoid...)
	body := abs.Body()
	if !fnVar.EqualsVar(abs.Var()) {
		body = body.Substitute(MakeTermSubst(abs.Var(), fnVar))
	}

	// The author-order witness: the chosen function itself when the
	// recursion argument comes first; the reshuffle wrapper otherwise.
	var witness Term = fnVar
	if wfd.RecArgPos > 0 {
		witness = wfArgOrderWrapper(wfd.ArgTypes, wfd.RecArgPos, fnVar)
	}

	w, stripped := prop.Assume(body).StripConclForAll()
	if len(stripped) != 1 {
		return nil, fmt.Errorf("internal: canonical equation strips %d binders, want 1",
			len(stripped))
	}
	recVar := wfd.ArgVars[wfd.RecArgPos]
	if !stripped[0].EqualsVar(recVar) {
		w = w.TermInst(MakeTermSubst(stripped[0], recVar))
	}
	// Uncurry: apply the extras and β-reduce.
	for _, v := range wfd.Extras() {
		w = w.RightApply(v)
	}
	w = w.RewriteConcl(DeepBeta)

	// Land on the author matrix at the witness; the reshuffle wrapper
	// carries β-redexes the derived side has reduced — expand back.
	_, matrix := DecomposesFORALL(wfd.Property)
	target := matrix.Substitute(MakeTermSubst(wfd.DefVar, witness))
	if !w.Conclusion().AlphaEquals(target) {
		eq := DeepBeta(target)
		if eq == nil || !Rhs(eq).AlphaEquals(w.Conclusion()) {
			return nil, fmt.Errorf(
				"internal: the WF equation did not land on its author form\n"+
					"  derived: %s\n  wanted:  %s",
				PrintTerm(w.Conclusion()), PrintTerm(target))
		}
		w = WrapProp(eq).EqSym().EqMP(w)
	}
	acc := w.ConclForAllList(wfd.ArgVars...)

	intro := prop.InstExists(wfd.ExistsStmt.Conclusion(), witness)
	return acc.DeriveTrans(intro).HypExists(fnVar, body).DeriveHypFrom(proved), nil
}

// wfArgOrderWrapper builds λx₀…xₖ. fn(x_p)(x₀,…,x̂_p,…,xₖ) — the
// author-argument-order face of the canonical function (the define_
// curry authorOrderWrapper at the WF shape's inputs).
func wfArgOrderWrapper(argTypes []HolType, recPos int, fnVar VarTerm) Term {
	xs := make([]VarTerm, len(argTypes))
	avoid := []Term{fnVar}
	for i, ty := range argTypes {
		x := Var(TermName(fmt.Sprintf("x%d", i)), ty).Core().(VarTerm).
			RenameToAvoid(avoid...)
		xs[i] = x
		avoid = append(avoid, x)
	}
	callArgs := make([]Term, 0, len(xs))
	callArgs = append(callArgs, xs[recPos])
	for i, x := range xs {
		if i == recPos {
			continue
		}
		callArgs = append(callArgs, x)
	}
	body := Apply(fnVar, callArgs...).Core()
	for i := len(xs) - 1; i >= 0; i-- {
		body = Abs(xs[i], body)
	}
	return body
}

// =======================================================================
// The guarded readings — the COND ruling's R4 half
// =======================================================================
//
// From a WF definition's characterizing COND equation, derive the
// equations a `define` returns — one per leaf of the RHS's
// top-level COND tree:
//
//	∀m n. gcd2(m, n) = COND(n = 0, m, gcd2(n, nat_mod(m, n)))
//	  ⇒  ∀m. gcd2(m, 0) = m                                (base)
//	  ⇒  ∀m n. ¬(n = 0) ⇒ gcd2(m, n) = gcd2(n, nat_mod(m, n))  (step)
//
// These are what R4 installs into the simp set (`simp_installed: 2`);
// the characterizing COND equation itself stays the entry's registered
// statement — an unconditional unfold rule would rewrite every
// occurrence on sight.
//
// Each leaf's reading carries its COND path as antecedents — except
// that a POSITIVE guard of the shape `binder = closed-term` is
// discharged by SUBSTITUTION instead (the binder instantiated at the
// term, the guard reduced by reflexivity), which is what turns the
// base case into the pattern-form equation the author would have
// written. Pure prop-layer derivation from the characterizing theorem.

// DeriveWFReadings derives the guarded readings of a characterizing
// COND equation (the minted-constant form). Returns one proved
// statement per top-level COND-tree leaf, in guard-tree order
// (then-branch before else-branch).
func DeriveWFReadings(characterizing Prop) ([]Prop, error) {
	if characterizing == nil || characterizing.NumHyps() != 0 {
		return nil, fmt.Errorf("characterizing theorem must be hyp-free")
	}
	binders, matrix := DecomposesFORALL(characterizing.Conclusion())
	if _, _, ok := MatchesEQ(matrix); !ok {
		return nil, fmt.Errorf("characterizing statement is not an equation: %s",
			PrintTerm(matrix))
	}
	vars := make([]VarTerm, 0, binders.Size())
	for v := range binders.Iter() {
		vars = append(vars, v)
	}

	var readings []Prop
	err := deriveReadingLeaves(characterizing, vars, nil, &readings)
	if err != nil {
		return nil, err
	}
	return readings, nil
}

// pathLit is one COND decision on the way to a leaf: the guard term
// and the branch taken.
type pathLit struct {
	guard Term
	then  bool
}

// deriveReadingLeaves recurses over the top-level COND spine of the
// equation's RHS, deriving one reading per leaf.
func deriveReadingLeaves(characterizing Prop, vars []VarTerm, path []pathLit, out *[]Prop) error {
	_, matrix := DecomposesFORALL(characterizing.Conclusion())
	_, rhs, _ := MatchesEQ(matrix)
	// Locate this path's node.
	node := rhs
	for _, lit := range path {
		_, th, el, ok := MatchesCond(node)
		if !ok {
			return fmt.Errorf("internal: reading path outran the COND spine")
		}
		if lit.then {
			node = th
		} else {
			node = el
		}
	}
	if _, _, _, ok := MatchesCond(node); ok {
		gd := guardAt(rhs, path)
		thenPath := append(append([]pathLit(nil), path...), pathLit{gd, true})
		elsePath := append(append([]pathLit(nil), path...), pathLit{gd, false})
		if err := deriveReadingLeaves(characterizing, vars, thenPath, out); err != nil {
			return err
		}
		return deriveReadingLeaves(characterizing, vars, elsePath, out)
	}

	reading, err := deriveOneReading(characterizing, vars, path)
	if err != nil {
		return err
	}
	*out = append(*out, reading)
	return nil
}

// guardAt reads the guard of the COND node at the given path.
func guardAt(rhs Term, path []pathLit) Term {
	node := rhs
	for _, lit := range path {
		_, th, el, _ := MatchesCond(node)
		if lit.then {
			node = th
		} else {
			node = el
		}
	}
	g, _, _, _ := MatchesCond(node)
	return g
}

// deriveOneReading derives the reading for one leaf: instantiate the
// substitutable positive guards, reduce the path's COND nodes under
// their (assumed or proved) guard values, and re-close.
func deriveOneReading(characterizing Prop, vars []VarTerm, path []pathLit) (Prop, error) {
	// Substitution pass: a positive guard `v = t` with v a binder and
	// t free of every binder pins v := t.
	values := make([]Term, len(vars))
	pinned := make(map[VarTerm]bool)
	for i, v := range vars {
		values[i] = v
	}
	for _, lit := range path {
		if !lit.then {
			continue
		}
		l, r, ok := MatchesEQ(lit.guard)
		if !ok {
			continue
		}
		v, ok := l.AsVar()
		if !ok {
			continue
		}
		clean := true
		for _, b := range vars {
			if r.HasFree(b) {
				clean = false
			}
		}
		if !clean {
			continue
		}
		for i, b := range vars {
			if b.EqualsVar(v) && !pinned[b] {
				values[i] = r
				pinned[b] = true
			}
		}
	}

	w := WrapProp(characterizing).ConclForAllInsts(values...)
	// Walk the path, reducing each COND node under its guard.
	var assumed []Term
	subst := func(t Term) Term {
		for i, v := range vars {
			if pinned[v] {
				t = t.Substitute(MakeTermSubst(v, values[i]))
			}
		}
		return t
	}
	_, matrix := DecomposesFORALL(characterizing.Conclusion())
	_, rhs, _ := MatchesEQ(matrix)
	node := subst(rhs)
	for _, lit := range path {
		head, _ := MatchesApply(node)
		gd, th, el, ok := MatchesCond(node)
		if !ok {
			return nil, fmt.Errorf("internal: reduced path outran the COND spine")
		}
		var gdEq *PropWrapper // ⊢/{…} gd = ⊤ (or ⊥)
		if lit.then {
			if l, r, isEq := MatchesEQ(gd); isEq && l.AlphaEquals(r) {
				// The substitution closed this guard: t = t.
				gdEq = prop.DerivesTrue.Deduct(prop.Refl(l)).EqSym()
			} else {
				gdEq = guardTrueEq(gd)
				assumed = append(assumed, gd)
			}
			w = w.EqTrans(gdEq.LeftApply(head).RightApply(th).RightApply(el).
				EqTrans(prop.CondClauseT(th, el)))
			node = th
		} else {
			notGd := Not(WrapTerm(gd)).Core()
			gdEq = guardFalseEq(gd)
			assumed = append(assumed, notGd)
			w = w.EqTrans(gdEq.LeftApply(head).RightApply(th).RightApply(el).
				EqTrans(prop.CondClauseF(th, el)))
			node = el
		}
	}
	// Discharge the assumed guards (innermost last) and ∀-close the
	// unpinned binders in author order.
	for i := len(assumed) - 1; i >= 0; i-- {
		w = w.PromoteHyp(assumed[i])
	}
	remaining := make([]VarTerm, 0, len(vars))
	for _, v := range vars {
		if !pinned[v] {
			remaining = append(remaining, v)
		}
	}
	// Unwrap: callers store the reading as a cert (core.Thm), so hand
	// back the derived value itself, not the derivation wrapper.
	return w.ConclForAllList(remaining...).Prop, nil
}

// guardTrueEq derives {gd} ⊢ gd = ⊤; guardFalseEq derives
// {¬gd} ⊢ gd = ⊥ — the guard-under-its-own-assumption rewrites the
// COND reductions ride on (shared with the continuity walker's
// condCongruence).
func guardTrueEq(gd Term) *PropWrapper {
	return prop.DerivesTrue.Deduct(prop.Assume(gd)).EqSym()
}

func guardFalseEq(gd Term) *PropWrapper {
	return prop.FalseDerives(gd).Deduct(prop.Contradict(gd))
}
