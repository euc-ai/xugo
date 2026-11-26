// define.go — the `define` RPC: the definition move (the manual's
// §"Statements and definitions — one elaborator"). One command, payload
// variants; a session `define` creates a definition SECTION — the mint
// happens here at the RPC boundary (outside the proof tree), the
// section's root is the characterizing theorem, and its body is the
// ONE composite _DefineStep (prover/proof/step_define.go).
//
// The `recursive:` payload serves both its shapes: a single
// non-recursive equation is the DIRECT case,
// and constructor-clause equations compile against the carrier's
// registered recursion schema (num_recursion / <T>_RECURSION — the P4a
// equation compiler), the existence obligation discharged engine-side
// with no refuter. `data:` is the datatype door, `spec:` the
// specification door, and `typedef:` the type-definition door (the
// one kernel principle besides constant
// definition), `quotient:` the quotient door (a typedef over the
// equivalence-class shape with its class map and the seven theorems
// Lean's Quot comes with; a function on the classes is the
// `recursive:` payload with class patterns — the LIFT shape, whose
// respectfulness obligation is the author's), and `inductive:` the
// inductive-definition door.
//
// Scope injection is free by architecture: constant identity is
// process-global (the ConstMetaManager behind the engine env's
// ProofService), and every session parse resolves through it, so the
// minted constant is visible to all later statements with no vocab
// plumbing. The registration is EXCLUSIVE (a collision errors, never
// shadows) and process-global — a serve restart is the experiment
// eraser.

package engine

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/emit"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// keepDefinitionText records the author's spelling of a definition for
// emit-section (Session.defineTexts).
func (s *Session) keepDefinitionText(constName string, text emit.DefinitionText) {
	if s.defineTexts == nil {
		s.defineTexts = map[string]emit.DefinitionText{}
	}
	s.defineTexts[constName] = text
}

// definitionText answers emit.EmitOptions.DefinitionText.
func (s *Session) definitionText(name core.TermName) (emit.DefinitionText, bool) {
	t, ok := s.defineTexts[string(name)]
	return t, ok
}

// DefineRecursive is the `recursive:` payload — the equation-shaped
// definition door (transcript A1's shape): one equation per
// constructor for a recursive definition, or a single
// definiendum-free equation for the direct case.
type DefineRecursive struct {
	// Name is the fresh constant's name.
	Name string `json:"name"`
	// Type is the constant's type in text form ("num → num → bool").
	Type string `json:"type"`
	// Equations are statement literals; each parses with the
	// definiendum declared at Type and both strict switches on.
	Equations []string `json:"equations"`
	// Measure routes the definition to the WF shape (transcript
	// D): a term over the RECURSION ARGUMENT alone (carrier → num),
	// its λ-binder matched BY NAME against the LHS argument it
	// measures — e.g. "λn:num. n". With a measure the equation must be
	// the ONE total COND form, and the move opens the TERMINATION
	// obligation for the author instead of closing engine-side.
	Measure string `json:"measure,omitempty"`
}

// DefineSpec is the `spec:` payload — the specification definition
// door (transcript E's shape): one or more constants introduced by
// CHOICE against a specification, with the
// POINTWISE existence obligation opened for the author — the WF
// discipline minus the termination walker. The session door is
// FRESH-only by ruling (de novo authoring is the session scenario);
// an imported constant group is CLAIMED through the door
// (family.DefineSpec), which serves both provenances.
type DefineSpec struct {
	// Consts declares the spec-defined constants in DEFINITION ORDER
	// (the specification's chain: each constant's existence claim may
	// nest the later ones).
	Consts []SpecConstDecl `json:"consts"`
	// Spec is the specification statement literal — the
	// characterizing statement at the constants, each applied at ONE
	// fixed argument form over the statement's ∀-binders. Parses with
	// every definiendum declared as a variable of its stated type,
	// both strict switches on.
	Spec string `json:"spec"`
}

// SpecConstDecl declares one spec constant: its name and its type in
// text form ("num → num").
type SpecConstDecl struct {
	Name string `json:"name"`
	Type string `json:"type"`
}

// DefineRequest is the `define` RPC envelope. Exactly one payload
// variant must be set.
type DefineRequest struct {
	SessionID string           `json:"session_id"`
	Recursive *DefineRecursive `json:"recursive,omitempty"`
	Data      *DefineData      `json:"data,omitempty"`
	Spec      *DefineSpec      `json:"spec,omitempty"`
	Typedef   *DefineTypedef   `json:"typedef,omitempty"`
	Inductive *DefineInductive `json:"inductive,omitempty"`
	Quotient  *DefineQuotient  `json:"quotient,omitempty"`
}

// DefineResult reports a completed definition move.
type DefineResult struct {
	// Defined is the minted constant's name (the type name for the
	// data shape; the joined name list for a multi-constant spec —
	// Consts carries the machine-readable list).
	Defined string `json:"defined"`
	// Shape names the served definition shape: "direct"
	// (one plain equation), "recursive" (schema-compiled), "lift" (a
	// function on a quotient's classes), "data", "spec"
	// (constants by choice), "typedef" (a type definition), "quotient"
	// or "inductive".
	Shape string `json:"shape"`
	// Schema names the recursion principle the compiler instantiated
	// (num_recursion, list_recursion, …). Empty for the direct shape.
	Schema string `json:"schema,omitempty"`
	// Characterizing is the registered characterizing theorem's
	// statement, printed (the round-trip printer's form).
	Characterizing string `json:"characterizing"`
	// Key is the characterizing statement's normalized key.
	Key string `json:"key"`
	// GoalID / Section locate the definition section in the session
	// (proved on return for the direct shape).
	GoalID  string `json:"goal_id"`
	Section int    `json:"section"`
	// SimpInstalled counts the characterizing equations installed into the
	// session's simp set (the manual's R4: installation is part of
	// definition — the bare `simp` tactic fires them with zero setup). The
	// theorem installs WHOLE (one rule, possibly a conjunction); the count
	// reports its clauses.
	SimpInstalled int `json:"simp_installed"`
	// Scope reports the constant's visibility. Constant identity is
	// process-global by architecture; this field reports, it does not
	// wire.
	Scope string `json:"scope"`

	// Obligation / ObligationGoalID report the WF shape's opened
	// termination obligation (transcript D1's response): the statement
	// printed, and the open goal to close it at (D2). Empty for the
	// shapes that close engine-side; the on-close completion (R4
	// installation, simp_installed) rides the closing apply's
	// StepResult.DefineCompleted.
	Obligation       string `json:"obligation,omitempty"`
	ObligationGoalID string `json:"obligation_goal_id,omitempty"`

	// --- data/spec/typedef-payload outputs (empty for the equation shapes) ---

	// TypeDefined is the minted type at its parameters ("btree(A)").
	// Data and typedef shapes.
	TypeDefined string `json:"type,omitempty"`
	// Consts lists the minted constants: the constructors (data), the
	// spec-defined group in definition order (spec), or the abs/rep
	// pair (typedef).
	Consts []string `json:"consts,omitempty"`
	// Derived lists the derived theorems' conventional names
	// (btree_induction, btree_recursion, btree_injective, btree_distinct — the
	// absent kinds omitted).
	Derived []string `json:"derived,omitempty"`
	// SimpInstalledNames names the rules the move installed into the
	// session simp set (INJ / DISTINCT).
	SimpInstalledNames []string `json:"simp_installed_names,omitempty"`
	// DerivedSections locates the derived-theorem sections: a
	// datatype's INDUCT / RECURSION / INJ / DISTINCT, a type
	// definition's Retraction / Membership.
	DerivedSections []DerivedSectionInfo `json:"derived_sections,omitempty"`
}

// envConstResolver adapts the session env's const-meta lookup into the
// ParseScope resolver shape — the same registry the mint's exclusivity
// check reads, so parse-time resolution and mint-time collision
// detection can never disagree. (In production this is the global
// ConstMetaManager; engine tests carry a mock service.)
// envTypeResolver is the env's type vocabulary (ProofService.TypeArity),
// nil when the env carries none.
func envTypeResolver(env *proof.ProverEnv) func(string) (int, bool) {
	if env == nil || env.ProofService == nil {
		return nil
	}
	return env.ProofService.TypeArity
}

func envConstResolver(env *proof.ProverEnv) func(string) core.ConstTermMeta {
	svc := env.ProofService
	if svc == nil || svc.LoadConstMeta == nil {
		return nil
	}
	return func(name string) core.ConstTermMeta {
		if meta, ok := svc.LoadConstMeta(core.TermName(name)); ok {
			return meta
		}
		return core.ConstTermMeta{}
	}
}

// Define executes the definition move in a session. On success the
// session has one new PROVED section — the characterizing theorem —
// and the constant is registered for every later parse.
func (e *Engine) Define(req *DefineRequest) (*DefineResult, error) {
	if err := checkDefinePayload(req); err != nil {
		return nil, err
	}
	s, err := e.getSession(req.SessionID)
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if err := s.faultRefusal(); err != nil {
		return nil, err
	}
	return e.defineMoveLocked(s, req)
}

// checkDefinePayload refuses a define request that does not carry
// exactly one payload.
func checkDefinePayload(req *DefineRequest) error {
	if req == nil {
		return fmt.Errorf("define: nil request")
	}
	set := 0
	for _, p := range []bool{req.Recursive != nil, req.Data != nil, req.Spec != nil, req.Typedef != nil, req.Inductive != nil, req.Quotient != nil} {
		if p {
			set++
		}
	}
	if set == 0 {
		return fmt.Errorf("define requires a payload: `recursive:` " +
			"{name, type, equations}, `data:` {name, params, constructors}, " +
			"`spec:` {consts, spec}, `typedef:` {type, abs, rep, pred, witness?}, " +
			"`quotient:` {type, mk, abs, rep, relation} or " +
			"`inductive:` {name, type, params?, rules}")
	}
	if set > 1 {
		return fmt.Errorf("define takes exactly one payload variant")
	}
	return nil
}

// defineMoveLocked is Define under the session lock, for a request
// checkDefinePayload passed.
func (e *Engine) defineMoveLocked(s *Session, req *DefineRequest) (*DefineResult, error) {
	// The define records itself as ONE event; the sections it adds
	// must not record as goals of their own (a resume re-mints first,
	// then their statements decode).
	s.recordingSuppressed++
	res, err := e.defineLocked(s, req)
	s.recordingSuppressed--
	if err != nil {
		return nil, err
	}
	// The move is in the lineage (lineage.go): a resume re-mints by
	// replaying it, and the sections it proved outright are recorded.
	s.recordDefine(req)
	s.recordProvedSections()
	return res, nil
}

// defineLocked serves one define payload; s.mu is held.
func (e *Engine) defineLocked(s *Session, req *DefineRequest) (*DefineResult, error) {
	if req.Data != nil {
		return e.defineData(s, req.Data)
	}
	if req.Spec != nil {
		return e.defineSpec(s, req.Spec)
	}
	if req.Typedef != nil {
		return e.defineTypedef(s, req.Typedef)
	}
	if req.Inductive != nil {
		return e.defineInductive(s, req.Inductive)
	}
	if req.Quotient != nil {
		return e.defineQuotient(s, req.Quotient)
	}

	r := req.Recursive
	if r.Name == "" || r.Type == "" {
		return nil, fmt.Errorf("define recursive: both `name` and `type` are required")
	}
	if len(r.Equations) == 0 {
		return nil, fmt.Errorf("define recursive: at least one equation is required")
	}

	base := &dsl.ParseScope{ConstResolver: envConstResolver(s.env), TypeResolver: envTypeResolver(s.env), Syntax: constSyntax(), CoerceDomain: s.CoerceDomain()}
	equations := make([]core.Prop, len(r.Equations))
	var defVar core.VarTerm
	for i, text := range r.Equations {
		eq, dv, err := proof.ParseDefinitionEquation(text, r.Name, r.Type, base)
		if err != nil {
			return nil, err
		}
		equations[i], defVar = eq, dv
	}

	// WF shape (measure set): one total COND equation, the termination
	// obligation opened for the author.
	if r.Measure != "" {
		return e.defineWF(s, r, equations, defVar)
	}
	// LIFT shape (a class pattern among the arguments): one equation at
	// the classes, the respectfulness obligation opened for the author.
	if len(equations) == 1 && proof.IsQuotientLiftEquation(equations[0], defVar) {
		return e.defineLift(s, r, equations, defVar)
	}

	// Route: a single non-recursive equation is the direct shape;
	// anything else compiles against the carrier's
	// recursion schema.
	var (
		c              core.ConstTerm
		characterizing core.Prop
		shape, schema  string
		served         proof.DefinitionShape
	)
	if len(equations) == 1 && !proof.IsCompiledDefinitionEquation(equations[0], defVar) {
		dd, err := proof.AnalyzeDirectDefinition(equations[0], defVar)
		if err != nil {
			return nil, err
		}
		c, characterizing, err = proof.MintDirectDefinition(s.env, dd)
		if err != nil {
			return nil, err
		}
		shape, served = "direct", proof.DefinitionDirect
	} else {
		rd, err := proof.AnalyzeRecursiveDefinition(equations, defVar)
		if err != nil {
			return nil, err
		}
		// Compile BEFORE minting: a definition whose existence the
		// schema cannot discharge must not register a constant. The
		// step's apply re-runs the same deterministic compilation.
		if _, schema, err = proof.CompileRecursiveExistence(s.env, rd); err != nil {
			return nil, err
		}
		c, characterizing, err = proof.MintRecursiveDefinition(s.env, rd)
		if err != nil {
			return nil, err
		}
		shape, served = "recursive", proof.DefinitionRecursive
	}

	// The definition section: root = the characterizing theorem, body
	// = the one composite; both served shapes close outright (the
	// recursive obligation is discharged engine-side by the compiler).
	goalID := s.addGoalNode(proof.CreateGoalStack(characterizing), nil)
	node := s.goalIndex[goalID].node
	if !proof.ApplyDefineStep(node, s.env, c) || !node.Proved() {
		// The mint stands (process-global by ruling); the session stays
		// clean. This is an engine-side derivation gap, not an
		// authoring error — the analyze/mint/compile layer accepted the
		// input.
		s.sections = s.sections[:len(s.sections)-1]
		s.rebuildGoalIndex()
		return nil, fmt.Errorf(
			"define: the characterizing derivation did not close for %q — the "+
				"constant IS minted (process-global); report this shape", r.Name)
	}
	s.rebuildGoalIndex()

	// R4 — installation is part of definition: the shape's default
	// rules (proof.DefinitionSimpRules — for both equation shapes the
	// characterizing theorem whole, a conjunction being a valid rule)
	// join the session's simp set, backed by the definition section's
	// own promise.
	s.installDefinitionRules(r.Name, served, node.PromisedThm(), nil)
	s.keepDefinitionText(r.Name, emit.DefinitionText{Type: r.Type, Equations: append([]string(nil), r.Equations...)})

	normalized, _ := prop.Normalize(characterizing)
	return &DefineResult{
		Defined:        r.Name,
		Shape:          shape,
		Schema:         schema,
		Characterizing: ext.PrintTerm(characterizing.Conclusion()),
		Key:            string(normalized.AlphaKey()),
		GoalID:         goalID,
		Section:        len(s.sections) - 1,
		SimpInstalled:  len(ext.DecomposesAND(characterizing.Conclusion())),
		Scope:          "process",
	}, nil
}

// defineWF executes the WF definition move: analyze at the
// strict door, check the schema rows are served, mint, open the
// definition section with the ONE composite — whose child is the
// TERMINATION obligation, left open for the author (transcript D's
// D1). The section completes on the apply that closes the obligation
// (Session.sweepPendingDefines — R4 installation and the completion
// report both ride that response).
func (e *Engine) defineWF(s *Session, r *DefineRecursive, equations []core.Prop, defVar core.VarTerm) (*DefineResult, error) {
	if len(equations) != 1 {
		return nil, fmt.Errorf(
			"define recursive with measure: the WF v1 shape is ONE total COND "+
				"equation (got %d equations) — spell the guards as COND branches",
			len(equations))
	}
	mRes := dsl.ParseTermTextInScope(r.Measure, nil, &dsl.ParseScope{
		ConstResolver:      envConstResolver(s.env),
		TypeResolver:       envTypeResolver(s.env),
		StrictResolution:   true,
		StrictMint:         true,
		FreshenMetaLetters: true,
	}, nil)
	if len(mRes.Errors) > 0 {
		return nil, fmt.Errorf("parse measure %q: %s", r.Measure, mRes.Errors[0].Message)
	}
	wfd, err := proof.AnalyzeWFDefinition(equations[0], defVar, mRes.Term)
	if err != nil {
		return nil, err
	}
	// Serving precheck (the compile-before-mint discipline's WF
	// analogue — the full compile needs the author's termination
	// theorem, but a missing schema row must refuse BEFORE minting).
	for _, name := range []string{proof.WFRecName, proof.WFMeasureName} {
		if thm, ok := s.env.LookupLibraryThm(name); !ok || thm == nil {
			return nil, fmt.Errorf(
				"define recursive with measure: no library theorem named %q in "+
					"scope — the WF compiler needs the schema rows served", name)
		}
	}
	c, characterizing, err := proof.MintWFDefinition(s.env, wfd)
	if err != nil {
		return nil, err
	}

	goalID := s.addGoalNode(proof.CreateGoalStack(characterizing), nil)
	node := s.goalIndex[goalID].node
	if !proof.ApplyDefineWFStep(node, s.env, c, wfd.Measure) {
		// The mint stands (process-global by ruling); the session stays
		// clean. Engine-side gap — the analyze/mint layer accepted the
		// input.
		s.sections = s.sections[:len(s.sections)-1]
		s.rebuildGoalIndex()
		return nil, fmt.Errorf(
			"define: the WF composite did not apply for %q — the constant IS "+
				"minted (process-global); report this shape", r.Name)
	}
	s.rebuildGoalIndex()
	section := len(s.sections) - 1

	leaves := node.UnsolvedLeaves()
	if len(leaves) != 1 {
		return nil, fmt.Errorf(
			"define: the WF composite opened %d children, want 1 (the termination "+
				"obligation) — report this shape", len(leaves))
	}
	normalized, _ := prop.Normalize(characterizing)
	key := string(normalized.AlphaKey())
	s.pendingDefines = append(s.pendingDefines, pendingDefine{
		name:    r.Name,
		shape:   proof.DefinitionWF,
		section: section,
		node:    node,
		key:     key,
	})
	s.keepDefinitionText(r.Name, emit.DefinitionText{
		Type: r.Type, Equations: append([]string(nil), r.Equations...), Measure: r.Measure,
	})

	return &DefineResult{
		Defined:          r.Name,
		Shape:            "recursive",
		Schema:           "wellfounded_recursion (measure)",
		Characterizing:   ext.PrintTerm(characterizing.Conclusion()),
		Key:              key,
		GoalID:           goalID,
		Section:          section,
		Scope:            "process",
		Obligation:       ext.PrintTerm(leaves[0].Goal.Conclusion()),
		ObligationGoalID: s.openLeafID(leaves[0], section),
	}, nil
}

// defineSpec executes the spec definition move (the `spec:` shape —
// the specification as a composite, the WF branch's degenerate form):
// parse the specification with the definienda as typed variables at
// the strict door, mint the nested tag-free ε chain, open the
// definition section with the ONE composite — whose child is the
// POINTWISE existence obligation, left open for the author. The
// section completes on the apply that closes the obligation
// (Session.sweepPendingDefines); by ruling the completion installs
// NOTHING into the simp set — a specification is not a directed
// rewrite (divmod's `m = nat_div(m, n) * n + nat_mod(m, n)` has a bare-variable
// LHS), so the author cites the characterizing theorem instead.
func (e *Engine) defineSpec(s *Session, d *DefineSpec) (*DefineResult, error) {
	if len(d.Consts) == 0 || d.Spec == "" {
		return nil, fmt.Errorf("define spec: both `consts` and `spec` are required")
	}
	names := make([]string, len(d.Consts))
	types := make([]string, len(d.Consts))
	for i, sc := range d.Consts {
		if sc.Name == "" || sc.Type == "" {
			return nil, fmt.Errorf("define spec: consts[%d] needs both `name` and `type`", i)
		}
		names[i], types[i] = sc.Name, sc.Type
	}
	base := &dsl.ParseScope{ConstResolver: envConstResolver(s.env), TypeResolver: envTypeResolver(s.env), CoerceDomain: s.CoerceDomain()}
	// FRESH-only by ruling. ParseSpecStatement refuses a name already
	// in scope as its own invariant; this door's message adds where
	// the claim provenance lives.
	for _, n := range names {
		if base.ConstResolver != nil && !base.ConstResolver(n).IsZero() {
			return nil, fmt.Errorf(
				"define spec: %q already names a constant — the session door is "+
					"FRESH-only (de novo); an imported constant group is claimed "+
					"through the definition door (family.DefineSpec)", n)
		}
	}
	stmt, defVars, err := proof.ParseSpecStatement(d.Spec, names, types, base)
	if err != nil {
		return nil, err
	}
	consts, characterizing, err := proof.MintSpecDefinition(s.env, stmt, defVars)
	if err != nil {
		return nil, err
	}
	constTerms := make([]core.Term, len(consts))
	for i, c := range consts {
		constTerms[i] = c
	}

	goalID := s.addGoalNode(proof.CreateGoalStack(characterizing), nil)
	node := s.goalIndex[goalID].node
	if !proof.ApplyDefineSpecStep(node, s.env, constTerms) {
		// The mint stands (process-global by ruling); the session stays
		// clean. Engine-side gap — the parse/mint layer accepted the
		// input.
		s.sections = s.sections[:len(s.sections)-1]
		s.rebuildGoalIndex()
		return nil, fmt.Errorf(
			"define: the spec composite did not apply for %s — the constants ARE "+
				"minted (process-global); report this shape", strings.Join(names, ", "))
	}
	s.rebuildGoalIndex()
	section := len(s.sections) - 1

	leaves := node.UnsolvedLeaves()
	if len(leaves) != 1 {
		return nil, fmt.Errorf(
			"define: the spec composite opened %d children, want 1 (the pointwise "+
				"existence obligation) — report this shape", len(leaves))
	}
	normalized, _ := prop.Normalize(characterizing)
	key := string(normalized.AlphaKey())
	defined := strings.Join(names, ", ")
	s.pendingDefines = append(s.pendingDefines, pendingDefine{
		name:    defined,
		shape:   proof.DefinitionSpec,
		section: section,
		node:    node,
		key:     key,
		consts:  names,
	})
	for i, n := range names {
		s.keepDefinitionText(n, emit.DefinitionText{Type: types[i], Spec: d.Spec})
	}

	return &DefineResult{
		Defined:          defined,
		Shape:            "spec",
		Schema:           "specification",
		Consts:           names,
		Characterizing:   ext.PrintTerm(characterizing.Conclusion()),
		Key:              key,
		GoalID:           goalID,
		Section:          section,
		Scope:            "process",
		Obligation:       ext.PrintTerm(leaves[0].Goal.Conclusion()),
		ObligationGoalID: s.openLeafID(leaves[0], section),
	}, nil
}

// DefineData is the `data:` payload — the datatype definition door
// (transcript B1's shape): the type name, its parameters, and
// the constructors.
type DefineData struct {
	Name         string                      `json:"name"`
	Params       []string                    `json:"params,omitempty"`
	Constructors []proof.DataConstructorSpec `json:"constructors"`
}

// DerivedSectionInfo locates one derived-theorem section of a datatype
// or type definition in the session.
type DerivedSectionInfo struct {
	// Kind is INDUCT / RECURSION / INJ / DISTINCT for a datatype,
	// Retraction / Membership for a type definition.
	Kind string `json:"kind"`
	// Principle is a datatype theorem's conventional library name
	// (btree_induction, …) — the induction/recursion dispatch key. Empty
	// for a type definition's theorems.
	Principle string `json:"principle,omitempty"`
	GoalID    string `json:"goal_id"`
	Section   int    `json:"section"`
}

// defineData executes the `data:` definition move: analyze at the
// strict door, mint (type + constructors, exclusive, process-global),
// then one PROVED section per derived-theorem family — each closed by
// the define-data composite, close-or-fail — with the INDUCT and
// RECURSION theorems installed into the env's library overlay under
// their conventional names (the induction tactic and the recursion
// compile dispatch on them) and INJ/DISTINCT installed into the
// session simp set (R4).
func (e *Engine) defineData(s *Session, d *DefineData) (*DefineResult, error) {
	if d.Name == "" {
		return nil, fmt.Errorf("define data: `name` is required")
	}
	svc := s.env.ProofService
	var lookup func(core.TermName) core.ConstTermMeta
	if svc != nil && svc.LoadConstMeta != nil {
		lookup = func(name core.TermName) core.ConstTermMeta {
			if meta, ok := svc.LoadConstMeta(name); ok {
				return meta
			}
			return core.ConstTermMeta{}
		}
	}
	var typeInUse func(core.TypeName) bool
	if svc != nil && svc.RangeConstMeta != nil {
		typeInUse = proof.TypeNameInUseProbe(svc.RangeConstMeta)
	}
	dd, err := proof.AnalyzeDataDefinition(d.Name, d.Params, d.Constructors, lookup, typeInUse)
	if err != nil {
		return nil, err
	}
	md, err := proof.MintDataDefinition(s.env, dd)
	if err != nil {
		return nil, err
	}

	ctorTerms := make([]core.Term, len(md.Ctors))
	consts := make([]string, len(md.Ctors))
	for i, c := range md.Ctors {
		ctorTerms[i] = c
		consts[i] = string(c.Name())
	}

	kinds := md.Kinds()
	added := 0
	rollback := func() {
		s.sections = s.sections[:len(s.sections)-added]
		s.rebuildGoalIndex()
	}
	var sections []DerivedSectionInfo
	var derived []string
	nodeByKind := map[proof.DataTheoremKind]*proof.GoalStackNode{}
	for _, k := range kinds {
		stmt := md.Stmt(k)
		goalID := s.addGoalNode(proof.CreateGoalStack(stmt), nil)
		added++
		node := s.goalIndex[goalID].node
		if !proof.ApplyDefineDataStep(node, s.env, md.Mk, ctorTerms) || !node.Proved() {
			// The mint stands (process-global by ruling); the session
			// stays clean. Engine-side derivation gap — the analyze/mint
			// layer accepted the input.
			rollback()
			return nil, fmt.Errorf(
				"define data: the %v derivation did not close for %q — the datatype IS "+
					"minted (process-global); report this shape", k, d.Name)
		}
		nodeByKind[k] = node
		derived = append(derived, md.PrincipleName(k))
		sections = append(sections, DerivedSectionInfo{
			Kind:      k.String(),
			Principle: md.PrincipleName(k),
			GoalID:    goalID,
			Section:   len(s.sections) - 1,
		})
	}

	// Principle installation: the induction tactic reads <T>_INDUCT,
	// the recursion-schema compile <T>_RECURSION — both through the
	// env's library overlay (LookupLibraryThm), which carries its own
	// lock (the session-mint ruling's "LibraryThms writes under the
	// engine lock"). The mint's exclusivity makes a name collision here
	// an engine fault, not an authoring error.
	for _, k := range []proof.DataTheoremKind{proof.DataInduct, proof.DataRecursion} {
		if err := s.env.InstallLibraryThm(md.PrincipleName(k), nodeByKind[k].PromisedThm()); err != nil {
			rollback()
			return nil, fmt.Errorf("define data: %v — report this shape", err)
		}
	}

	// R4: each derived theorem installs what its shape says
	// (proof.DefinitionSimpRules — INJ and DISTINCT are rules, the
	// principles are not), backed by its own section's promise.
	var simpInstalled []string
	record := sessionDataDefine{typeName: d.Name}
	for _, k := range kinds {
		rules := s.installDefinitionRules(d.Name, proof.DataDefinitionShape(k), nodeByKind[k].PromisedThm(), nil)
		if len(rules) == 0 {
			continue
		}
		simpInstalled = append(simpInstalled, md.PrincipleName(k))
		switch k {
		case proof.DataInj:
			record.inj = md.Stmt(k)
		case proof.DataDistinct:
			record.distinct = md.Stmt(k)
		}
	}
	s.dataDefines = append(s.dataDefines, record)

	typeText := d.Name
	if len(d.Params) > 0 {
		typeText += "(" + strings.Join(d.Params, ", ") + ")"
	}
	return &DefineResult{
		Defined:            d.Name,
		Shape:              "data",
		TypeDefined:        typeText,
		Consts:             consts,
		Derived:            derived,
		SimpInstalledNames: simpInstalled,
		SimpInstalled:      len(simpInstalled),
		DerivedSections:    sections,
		Scope:              "process",
	}, nil
}

// DefineTypedef is the `typedef:` payload — the type-definition door:
// a type carved out of a representation
// type ρ by a predicate, with abs : ρ → T and rep : T → ρ its
// bijection. The inhabitation is the author's mathematics, proved
// BEFORE the define as an ordinary session goal — `∃x:ρ. Pred(x)`,
// or, with Witness, the membership `Pred(w)` at a closed point of ρ
// (a λ-predicate's redex reduced: `0 < 1`, not `(λn. 0 < n)(1)`) —
// and the door finds that proved section by its statement. A
// predicate the normalizer decides (`∃x. Pred(x)` normalizes to ⊤)
// needs none. On return the session has two PROVED sections, the
// type's Retraction (`∀a:T. abs(rep(a)) = a`) and Membership
// (`∀r:ρ. Pred(r) ⇔ rep(abs(r)) = r`) theorems, and the type resolves
// in every later statement. Nothing installs into the simp set: the
// chapter door registers the two theorems as plain entries, and a
// session and an import must agree on what a definition installs.
type DefineTypedef struct {
	// Type is the minted type's name; its parameters are Pred's type
	// variables in first-occurrence order.
	Type string `json:"type"`
	// Abs and Rep name the bijection's constants.
	Abs string `json:"abs"`
	Rep string `json:"rep"`
	// Pred is the representing predicate — a closed λ over ρ in text,
	// parsed with both strict switches on ("λn:num. 0 < n").
	Pred string `json:"pred"`
	// Witness, when set, is the closed point of ρ the proved
	// inhabitation states the membership at.
	Witness string `json:"witness,omitempty"`
}

// sessionTypedefDefine is one type-definition move's session record:
// the type name, the inhabitation statement the author proved (nil
// when the normalizer decided it) and the two theorems' statements —
// what the emit layer needs to name the future entries
// (`<fam>.<Type>Inhabited` / `…Retraction` / `…Membership`).
type sessionTypedefDefine struct {
	typeName               string
	existence              core.Prop
	retraction, membership core.Prop
}

// defineTypedef executes the `typedef:` definition move: parse the
// predicate (and witness) at the strict door, analyze, locate the
// proved inhabitation section, mint (type + abs/rep, exclusive,
// process-global), then one PROVED section per theorem — each closed
// by the define-type composite, its inhabitation child closed by
// citing the proved section's theorem (the KnownThm leaf emit
// resolves to the future entry).
func (e *Engine) defineTypedef(s *Session, d *DefineTypedef) (*DefineResult, error) {
	if d.Type == "" || d.Abs == "" || d.Rep == "" || d.Pred == "" {
		return nil, fmt.Errorf("define typedef: `type`, `abs`, `rep` and `pred` are all required")
	}
	if err := proof.CheckMintedTypeName(d.Type); err != nil {
		return nil, fmt.Errorf("define typedef: %v", err)
	}
	scope := &dsl.ParseScope{
		ConstResolver:      envConstResolver(s.env),
		TypeResolver:       envTypeResolver(s.env),
		StrictResolution:   true,
		StrictMint:         true,
		FreshenMetaLetters: true,
	}
	pres := dsl.ParseTermTextInScope(d.Pred, nil, scope, nil)
	if len(pres.Errors) > 0 {
		return nil, fmt.Errorf("define typedef: parse pred %q: %s", d.Pred, pres.Errors[0].Message)
	}
	pred := pres.Term.Core()
	td, err := proof.AnalyzeTypeDefinition(pred, nil)
	if err != nil {
		return nil, fmt.Errorf("define typedef: %v", err)
	}
	if d.Witness != "" {
		if td.Trivial {
			return nil, fmt.Errorf("define typedef: %s holds by normalization — drop `witness`",
				ext.PrintTerm(td.Exists.Conclusion()))
		}
		wres := dsl.ParseTermTextInScope(d.Witness, nil, scope, td.Rho)
		if len(wres.Errors) > 0 {
			return nil, fmt.Errorf("define typedef: parse witness %q: %s", d.Witness, wres.Errors[0].Message)
		}
		if td, err = proof.AnalyzeTypeDefinition(pred, wres.Term.Core()); err != nil {
			return nil, fmt.Errorf("define typedef: %v", err)
		}
	}

	// The inhabitation: the normalizer's certificate, or the proved
	// section stating the obligation — found by statement, so a resume
	// finds it again with no id on the wire.
	var source core.Prop
	var existenceRoot *proof.GoalStackNode
	if td.Trivial {
		source = td.TrivialSource()
	} else {
		for _, sec := range s.sections {
			root := sec.root
			if !root.Proved() || len(sec.deferred) > 0 || root.Goal.NumHyps() != 0 {
				continue
			}
			if root.Goal.Conclusion().AlphaEquals(td.Obligation.Conclusion()) {
				existenceRoot = root
				break
			}
		}
		if existenceRoot == nil {
			hint := "add it as a goal and prove it first"
			if d.Witness == "" {
				hint += ", or give `witness` and prove the membership at it"
			}
			return nil, fmt.Errorf("define typedef: the inhabitation %s is not a proved section — %s",
				ext.PrintTerm(td.Obligation.Conclusion()), hint)
		}
		inhabitation := existenceRoot.PromisedThm()
		source = core.Promise(td.Applied, func(f core.Forcer) core.ThmCert {
			return f.Force(core.AsThm(td.SourceFromObligation(inhabitation)))
		})
	}

	md, err := proof.MintTypeDefinition(s.env, td, core.TypeName(d.Type), core.TermName(d.Abs), core.TermName(d.Rep), source)
	if err != nil {
		return nil, err
	}

	added := 0
	rollback := func() {
		s.sections = s.sections[:len(s.sections)-added]
		s.rebuildGoalIndex()
	}
	var sections []DerivedSectionInfo
	for _, k := range proof.TypeDefTheoremKinds {
		goalID := s.addGoalNode(proof.CreateGoalStack(md.Stmt(k)), nil)
		added++
		node := s.goalIndex[goalID].node
		if !proof.ApplyDefineTypeStep(node, md.Abs) {
			// The mint stands (process-global by ruling); the session
			// stays clean. Engine-side derivation gap — the analyze/mint
			// layer accepted the input.
			rollback()
			return nil, fmt.Errorf(
				"define typedef: the %v derivation did not apply for %q — the type IS "+
					"minted (process-global); report this shape", k, d.Type)
		}
		if existenceRoot != nil {
			leaves := node.UnsolvedLeaves()
			if len(leaves) != 1 || !proof.ApplyCiteKnown(leaves[0], existenceRoot.PromisedThm()) {
				rollback()
				return nil, fmt.Errorf(
					"define typedef: the %v composite's inhabitation child did not close from the "+
						"proved section for %q — the type IS minted (process-global); report this shape", k, d.Type)
			}
		}
		if !node.Proved() {
			rollback()
			return nil, fmt.Errorf(
				"define typedef: the %v section did not close for %q — the type IS minted "+
					"(process-global); report this shape", k, d.Type)
		}
		sections = append(sections, DerivedSectionInfo{
			Kind:    k.String(),
			GoalID:  goalID,
			Section: len(s.sections) - 1,
		})
	}
	s.rebuildGoalIndex()
	s.typedefDefines = append(s.typedefDefines, sessionTypedefDefine{
		typeName:   d.Type,
		existence:  td.Obligation,
		retraction: md.Retraction,
		membership: md.Membership,
	})

	return &DefineResult{
		Defined:         d.Type,
		Shape:           "typedef",
		Schema:          "type_definition",
		TypeDefined:     md.TypeText(),
		Consts:          []string{d.Abs, d.Rep},
		DerivedSections: sections,
		Scope:           "process",
	}, nil
}

// DefineInductive is the `inductive:` payload — the inductive-definition
// door: a relation minted as the
// SMALLEST one closed under the stated rules, with its Rules / Induct /
// Cases theorems derived by kernel rules alone (prover/proof
// define_inductive.go states the fragment the first charter serves).
type DefineInductive struct {
	Name string `json:"name"`
	// Type is the relation's type, ending in bool with at least one
	// index beyond the parameters.
	Type string `json:"type"`
	// Params names the leading arguments every occurrence takes
	// unchanged (the R of TC(R, x, y)), typed off their slots of Type.
	Params []string `json:"params,omitempty"`
	// Rules are the introduction rules as text, the relation applied
	// at the parameters then its indices.
	Rules []string `json:"rules"`
}

// sessionInductiveDefine records one inductive definition move: the
// constant's name and the three theorems' statements — what the emit
// layer needs to name the future entries (`<fam>.<Const>Rules` /
// `…Induct` / `…Cases`).
type sessionInductiveDefine struct {
	constName            string
	rules, induct, cases core.Prop
}

// defineInductive executes the `inductive:` definition move: parse the
// rules at the strict door with the definiendum and the parameters as
// variables, analyze against the fragment, mint (exclusive,
// process-global), then one PROVED section per theorem — each closed
// by the define-inductive composite, close-or-fail. Nothing installs
// into the simp set: the rules are not rewrite rules and the Cases
// theorem would rewrite the relation into itself.
func (e *Engine) defineInductive(s *Session, d *DefineInductive) (*DefineResult, error) {
	if d.Name == "" || d.Type == "" {
		return nil, fmt.Errorf("define inductive: both `name` and `type` are required")
	}
	if len(d.Rules) == 0 {
		return nil, fmt.Errorf("define inductive: at least one rule is required")
	}
	base := &dsl.ParseScope{ConstResolver: envConstResolver(s.env), TypeResolver: envTypeResolver(s.env), CoerceDomain: s.CoerceDomain()}
	rules := make([]core.Prop, len(d.Rules))
	var defVar core.VarTerm
	var params []core.VarTerm
	for i, text := range d.Rules {
		r, dv, pv, err := proof.ParseInductiveRule(text, d.Name, d.Type, d.Params, base)
		if err != nil {
			return nil, err
		}
		rules[i], defVar, params = r, dv, pv
	}
	idef, err := proof.AnalyzeInductiveDefinition(defVar, params, rules)
	if err != nil {
		return nil, err
	}
	c, err := proof.MintInductiveDefinition(s.env, idef)
	if err != nil {
		return nil, err
	}
	paramTerms := make([]core.Term, len(idef.Params))
	for i, p := range idef.Params {
		paramTerms[i] = p
	}

	added := 0
	rollback := func() {
		s.sections = s.sections[:len(s.sections)-added]
		s.rebuildGoalIndex()
	}
	var sections []DerivedSectionInfo
	var derived []string
	stmts := map[proof.InductiveTheoremKind]core.Prop{}
	var rulesGoalID string
	for _, k := range idef.Kinds() {
		stmt := idef.Stmt(c, k)
		stmts[k] = stmt
		goalID := s.addGoalNode(proof.CreateGoalStack(stmt), nil)
		added++
		node := s.goalIndex[goalID].node
		if !proof.ApplyDefineInductiveStep(node, c, paramTerms, idef.RuleTerms) || !node.Proved() {
			// The mint stands (process-global by ruling); the session
			// stays clean. Engine-side derivation gap — the analyze/mint
			// layer accepted the input.
			rollback()
			return nil, fmt.Errorf(
				"define inductive: the %v derivation did not close for %q — the relation IS "+
					"minted (process-global); report this shape", k, d.Name)
		}
		if k == proof.InductiveRules {
			rulesGoalID = goalID
		}
		derived = append(derived, idef.PrincipleName(k))
		sections = append(sections, DerivedSectionInfo{
			Kind:      k.String(),
			Principle: idef.PrincipleName(k),
			GoalID:    goalID,
			Section:   len(s.sections) - 1,
		})
	}
	s.rebuildGoalIndex()
	s.inductiveDefines = append(s.inductiveDefines, sessionInductiveDefine{
		constName: d.Name,
		rules:     stmts[proof.InductiveRules],
		induct:    stmts[proof.InductiveInduct],
		cases:     stmts[proof.InductiveCases],
	})
	// The author's spelling, for emit-section: the type and the rules
	// as written (DefinitionText.Equations carries the rules).
	s.keepDefinitionText(d.Name, emit.DefinitionText{Type: d.Type, Equations: d.Rules})

	normalized, _ := prop.Normalize(stmts[proof.InductiveRules])
	return &DefineResult{
		Defined:         d.Name,
		Shape:           "inductive",
		Schema:          "inductive_definition",
		Characterizing:  ext.PrintTerm(stmts[proof.InductiveRules].Conclusion()),
		Key:             string(normalized.AlphaKey()),
		GoalID:          rulesGoalID,
		Section:         sections[0].Section,
		Consts:          []string{d.Name},
		Derived:         derived,
		DerivedSections: sections,
		Scope:           "process",
	}, nil
}

// DefineQuotient is the `quotient:` payload — the quotient door: a type
// carved out of the equivalence classes of a relation the session (or
// a chapter) already defined, with its class map `mk` (spelled ⁅x⁆ and
// by the word `class`) and the seven theorems a quotient comes with
// (prover/proof/define_quotient.go). The one input is the author's
// mathematics, proved BEFORE the define as an ordinary session goal —
// `equivalence(R)`, the relations chapter's predicate — and the door
// finds that proved section by its statement. On return the session
// has seven PROVED sections; the induction principle, Sound and Exact
// are installed into the env's library overlay under their
// conventional names (so `induction` dispatches on a class-typed goal
// variable and a lift's compile finds its laws), and Eq — `mk(x) = mk(y)
// ⇔ R(x, y)` — joins the session simp set (R4).
type DefineQuotient struct {
	// Type is the minted type's name; its parameters are the type
	// variables of the relation's carrier, in first-occurrence order.
	Type string `json:"type"`
	// Mk names the class map; Abs and Rep the typedef pair under it.
	Mk  string `json:"mk"`
	Abs string `json:"abs"`
	Rep string `json:"rep"`
	// Relation is the equivalence relation in text — a constant,
	// possibly applied to its parameters ("nadd_eq"), of type
	// ρ → ρ → bool; parsed with both strict switches on.
	Relation string `json:"relation"`
}

// sessionQuotientDefine is one quotient definition move's session
// record: the type's name, the relation, the equivalence statement the
// author proved and the seven theorems' statements — what the emit
// layer needs to name the future entries (`<fam>.<ExportedType>
// Surjectivity` … and `<fam>.<ExportedRelation>Equivalence`).
type sessionQuotientDefine struct {
	typeName    string
	relation    core.Term
	equivalence core.Prop
	stmts       map[proof.QuotientTheoremKind]core.Prop
}

// defineQuotient executes the `quotient:` definition move: parse the
// relation at the strict door, analyze, locate the proved equivalence
// section, mint (type + abs/rep + class map, exclusive,
// process-global), register the class notation, then one PROVED
// section per theorem — each closed by the define-quotient composite,
// its equivalence child closed by citing the proved section's theorem.
func (e *Engine) defineQuotient(s *Session, d *DefineQuotient) (*DefineResult, error) {
	if d.Type == "" || d.Mk == "" || d.Abs == "" || d.Rep == "" || d.Relation == "" {
		return nil, fmt.Errorf("define quotient: `type`, `mk`, `abs`, `rep` and `relation` are all required")
	}
	if err := proof.CheckMintedTypeName(d.Type); err != nil {
		return nil, fmt.Errorf("define quotient: %v", err)
	}
	base := &dsl.ParseScope{
		ConstResolver: envConstResolver(s.env),
		TypeResolver:  envTypeResolver(s.env),
		Syntax:        constSyntax(),
		CoerceDomain:  s.CoerceDomain(),
	}
	rel, err := proof.ParseQuotientRelation(d.Relation, base)
	if err != nil {
		return nil, fmt.Errorf("define quotient: %v", err)
	}
	resolve := func(name core.TermName) core.ConstTermMeta {
		if base.ConstResolver == nil {
			return core.ConstTermMeta{}
		}
		return base.ConstResolver(string(name))
	}
	qd, err := proof.AnalyzeQuotientDefinition(rel, resolve)
	if err != nil {
		return nil, fmt.Errorf("define quotient: %v", err)
	}

	// The equivalence: the proved section stating it — found by
	// statement, so a resume finds it again with no id on the wire.
	var equivalenceRoot *proof.GoalStackNode
	for _, sec := range s.sections {
		root := sec.root
		if !root.Proved() || len(sec.deferred) > 0 || root.Goal.NumHyps() != 0 {
			continue
		}
		if root.Goal.Conclusion().AlphaEquals(qd.Equivalence.Conclusion()) {
			equivalenceRoot = root
			break
		}
	}
	if equivalenceRoot == nil {
		return nil, fmt.Errorf("define quotient: the equivalence %s is not a proved section — add it as a goal and prove it first "+
			"(a chapter's theorem closes it in one `lemma`; the relations chapter's Reflexive / Symmetric / Transitive laws read it off the three)",
			ext.PrintTerm(qd.Equivalence.Conclusion()))
	}

	mq, err := proof.MintQuotientDefinition(s.env, qd, core.TypeName(d.Type), core.TermName(d.Abs), core.TermName(d.Rep), core.TermName(d.Mk))
	if err != nil {
		return nil, err
	}
	registry.RegisterClassNotation(mq)

	added := 0
	rollback := func() {
		s.sections = s.sections[:len(s.sections)-added]
		s.rebuildGoalIndex()
	}
	record := sessionQuotientDefine{typeName: d.Type, relation: rel, equivalence: qd.Equivalence, stmts: map[proof.QuotientTheoremKind]core.Prop{}}
	nodeByKind := map[proof.QuotientTheoremKind]*proof.GoalStackNode{}
	var sections []DerivedSectionInfo
	var derived []string
	for _, k := range proof.QuotientTheoremKinds {
		stmt := mq.Stmt(k)
		record.stmts[k] = stmt
		goalID := s.addGoalNode(proof.CreateGoalStack(stmt), nil)
		added++
		node := s.goalIndex[goalID].node
		if !proof.ApplyDefineQuotientStep(node, s.env, mq.Mk) {
			rollback()
			return nil, fmt.Errorf(
				"define quotient: the %v derivation did not apply for %q — the type IS "+
					"minted (process-global); report this shape", k, d.Type)
		}
		leaves := node.UnsolvedLeaves()
		if len(leaves) != 1 || !proof.ApplyCiteKnown(leaves[0], equivalenceRoot.PromisedThm()) {
			rollback()
			return nil, fmt.Errorf(
				"define quotient: the %v composite's equivalence child did not close from the "+
					"proved section for %q — the type IS minted (process-global); report this shape", k, d.Type)
		}
		if !node.Proved() {
			rollback()
			return nil, fmt.Errorf(
				"define quotient: the %v section did not close for %q — the type IS minted "+
					"(process-global); report this shape", k, d.Type)
		}
		nodeByKind[k] = node
		if name := mq.PrincipleName(k); name != "" {
			derived = append(derived, name)
		}
		sections = append(sections, DerivedSectionInfo{
			Kind:      k.String(),
			Principle: mq.PrincipleName(k),
			GoalID:    goalID,
			Section:   len(s.sections) - 1,
		})
	}
	s.rebuildGoalIndex()

	// The by-name bindings: the induction tactic reads <Q>_induction,
	// the lift compiler <Q>_sound / <Q>_exact — all through the env's
	// library overlay.
	for _, k := range []proof.QuotientTheoremKind{proof.QuotientInduct, proof.QuotientSound, proof.QuotientExact} {
		if err := s.env.InstallLibraryThm(mq.PrincipleName(k), nodeByKind[k].PromisedThm()); err != nil {
			rollback()
			return nil, fmt.Errorf("define quotient: %v — report this shape", err)
		}
	}
	// R4: Eq is the one rule among the seven.
	var simpInstalled []string
	for _, k := range proof.QuotientTheoremKinds {
		rules := s.installDefinitionRules(d.Type, proof.QuotientDefinitionShape(k), nodeByKind[k].PromisedThm(), nil)
		if len(rules) > 0 {
			simpInstalled = append(simpInstalled, k.String())
		}
	}
	s.quotientDefines = append(s.quotientDefines, record)
	s.keepDefinitionText(d.Mk, emit.DefinitionText{Type: mq.TypeText(), Equations: []string{d.Relation}})

	normalized, _ := prop.Normalize(mq.Stmt(proof.QuotientEq))
	return &DefineResult{
		Defined:            d.Type,
		Shape:              "quotient",
		Schema:             "quotient (typedef over the equivalence classes)",
		TypeDefined:        mq.TypeText(),
		Characterizing:     ext.PrintTerm(mq.Stmt(proof.QuotientEq).Conclusion()),
		Key:                string(normalized.AlphaKey()),
		GoalID:             sections[4].GoalID,
		Section:            sections[4].Section,
		Consts:             []string{d.Mk, d.Abs, d.Rep},
		Derived:            derived,
		SimpInstalled:      len(simpInstalled),
		SimpInstalledNames: simpInstalled,
		DerivedSections:    sections,
		Scope:              "process",
	}, nil
}

// defineLift executes the LIFT definition move (the `recursive:`
// payload with a class pattern among its arguments): analyze at the
// strict door, check the quotients' laws are served, mint, open the
// definition section with the ONE composite — whose child is the
// RESPECTFULNESS obligation, left open for the author. The section
// completes on the apply that closes the obligation
// (Session.sweepPendingDefines — R4 installs the computation rule and
// the completion report rides that response).
func (e *Engine) defineLift(s *Session, r *DefineRecursive, equations []core.Prop, defVar core.VarTerm) (*DefineResult, error) {
	ld, err := proof.AnalyzeLiftDefinition(equations, defVar, func(name core.TermName) core.ConstTermMeta {
		if resolver := envConstResolver(s.env); resolver != nil {
			return resolver(string(name))
		}
		return core.ConstTermMeta{}
	})
	if err != nil {
		return nil, fmt.Errorf("define: %v", err)
	}
	// Serving precheck (the compile-before-mint discipline's lift
	// analogue — the full compile needs the author's respectfulness,
	// but a quotient whose laws are not served must refuse BEFORE
	// minting).
	for _, mq := range ld.LiftQuotients() {
		for _, k := range []proof.QuotientTheoremKind{proof.QuotientSound, proof.QuotientExact} {
			name := mq.PrincipleName(k)
			if thm, ok := s.env.LookupLibraryThm(name); !ok || thm == nil {
				return nil, fmt.Errorf(
					"define: no library theorem named %q in scope — the lift compiler needs the "+
						"quotient's laws served (a session `define quotient:` installs them; a chapter's "+
						"quotient serves them through its entries)", name)
			}
		}
	}
	c, characterizing, err := proof.MintLiftDefinition(s.env, ld)
	if err != nil {
		return nil, err
	}

	goalID := s.addGoalNode(proof.CreateGoalStack(characterizing), nil)
	node := s.goalIndex[goalID].node
	if !proof.ApplyDefineStep(node, s.env, c) {
		s.sections = s.sections[:len(s.sections)-1]
		s.rebuildGoalIndex()
		return nil, fmt.Errorf(
			"define: the lift composite did not apply for %q — the constant IS "+
				"minted (process-global); report this shape", r.Name)
	}
	s.rebuildGoalIndex()
	section := len(s.sections) - 1

	leaves := node.UnsolvedLeaves()
	if len(leaves) != 1 {
		return nil, fmt.Errorf(
			"define: the lift composite opened %d children, want 1 (the respectfulness "+
				"obligation) — report this shape", len(leaves))
	}
	normalized, _ := prop.Normalize(characterizing)
	key := string(normalized.AlphaKey())
	s.pendingDefines = append(s.pendingDefines, pendingDefine{
		name:    r.Name,
		shape:   proof.DefinitionLift,
		section: section,
		node:    node,
		key:     key,
	})
	s.keepDefinitionText(r.Name, emit.DefinitionText{Type: r.Type, Equations: append([]string(nil), r.Equations...)})

	return &DefineResult{
		Defined:          r.Name,
		Shape:            "lift",
		Schema:           "quotient_lift",
		Characterizing:   ext.PrintTerm(characterizing.Conclusion()),
		Key:              key,
		GoalID:           goalID,
		Section:          section,
		Scope:            "process",
		Obligation:       ext.PrintTerm(leaves[0].Goal.Conclusion()),
		ObligationGoalID: s.openLeafID(leaves[0], section),
	}, nil
}
