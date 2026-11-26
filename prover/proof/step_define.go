// step_define.go — the definition move's composite ministeps:
// `define` below, and §"DefineData" for the `data:` payload's sibling.
// Same design in both — one proto tag, payload the minted identity
// alone, `apply` the shared executor — so they read as one file, the
// way the recurring composites share step_composite.go.
//
// ONE proto tag (StepProto_Define, tag 57) whose payload is the MINTED
// CONST alone; the characterizing form is the recorded goal, and the
// definition body lives on the const's meta, so nothing else rides the
// wire and there is no second copy to drift. `apply` IS the shared
// executor: the engine `define` RPC (session side), a family.Define
// Build (replay), and emit-time verification all run this same
// function — the record/emit/replay code-reuse principle
// (step_composite.go), sibling of set_tac / simp_with / def_expand /
// by.
//
// The MINT itself (core.NewConstDef + exclusive registration — see
// define.go) happens OUTSIDE the proof tree at the RPC/Build boundary:
// apply runs on probe clones, so a kernel-definitional act must not
// live inside a step. By the time this step runs, the const exists and
// carries its definition; the step's whole job is deriving the
// characterizing theorem from it.
//
// Dispatch is on the def shape (prop.IsHilbertConstDef — the same
// discriminator AxiomDef / ExistentialConstDef route on):
//
//   - DIRECT (⊢ c = λx̄.body — the non-recursive `define`): zero
//     children. apply derives ⊢ ∀x̄. c(x̄) = body at the goal's own
//     binders (deriveDirectCharacterizing) and closes the goal
//     outright.
//   - HILBERT (⊢ c = εf.P(f) — the recursive shapes): one child,
//     [⊢ ∃f. P(f)] — the existence obligation, surfaced for its
//     closer (the compiled schema instance engine-side for primrec;
//     the author's termination for the WF shape, the author's
//     respectfulness for the LIFT shape). Reconstruction is the
//     ExistentialConstDef bridge with the residual FOLDED — the goal
//     IS P(c), so unlike _ExistentialConstDefStep (whose child(1)
//     carries P(c) as a hyp toward an arbitrary G) no residual child
//     exists. BridgeNormalize absorbs the raw-vs-goal arrangement
//     drift.

package proof

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
)

type _DefineStep struct {
	constTerm ConstTerm
	// measure is the WF shape's measure term (λ over the recursion
	// argument) — nil for the direct and primrec shapes. It rides the
	// proto (DefineProto.measure): the ε-payload β-reduces it away, and
	// the executor needs it to recompute the termination obligation
	// child deterministically.
	measure Term
	cases   []Case
	// env is RUNTIME-ONLY (never serialized), injected by Script.Do /
	// passed by ApplyDefineStep. The HILBERT branch's engine-side
	// obligation close reads the carrier's recursion schema from
	// env.LibraryThms (primrec), and the WF reconstruct reads the
	// served wellfounded_recursion/wellfounded_measure_less rows; nil env skips the primrec close
	// and declines the WF shape.
	env *ProverEnv
}

// DefineStep is the ministep constructor: the body of a definition
// section. c must resolve to the MINTED const (via .Core()). Variadic
// Case args populate the embedded cases slice for Script.Do dispatch —
// the Hilbert shape's one existence obligation; the direct shape takes
// none. Nil-env by construction (the CnfRefute convention): Script.Do
// injects the running Script's env.
func DefineStep(c Term, cases ...Case) Step {
	return _DefineStep{constTerm: c.Core().(ConstTerm), cases: cases}
}

// DefineWFStep is the WF shape's ministep constructor: the measure
// marks the definition well-founded, so the composite's one child is
// the TERMINATION obligation (author-closed — the variadic Case) and
// the reconstruct runs the WF equation compiler on it.
func DefineWFStep(c Term, measure Term, cases ...Case) Step {
	return _DefineStep{constTerm: c.Core().(ConstTerm), measure: measure.Core(), cases: cases}
}

// DefineWFStep — method sugar, the DefineStep convention.
func (s *Script) DefineWFStep(c Term, measure Term, cases ...Case) Step {
	return DefineWFStep(c, measure, cases...)
}

// DefineStep — pure struct-literal sugar; method delegates to the bare
// form (the AxiomDefStep convention, for emitted bodies).
func (s *Script) DefineStep(c Term, cases ...Case) Step { return DefineStep(c, cases...) }

func (step _DefineStep) caseBodies() []Case { return step.cases }

func (step _DefineStep) String() string {
	return fmt.Sprintf("Define: %s", PrintTerm(step.constTerm))
}

func (step _DefineStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	Assert(!step.constTerm.IsZero())
	dp := &DefineProto{Const: b.TermRef(step.constTerm)}
	if step.measure != nil {
		m := b.TermRef(step.measure)
		dp.Measure = &m
	}
	return &StepProto_Define{Define: dp}
}

func (step _DefineStep) apply(p Prop) *SubGoals {
	Assert(!step.constTerm.IsZero())
	if p.NumHyps() != 0 {
		// A definition section's root is a closed statement.
		return nil
	}

	if !prop.IsHilbertConstDef(step.constTerm) {
		// DIRECT: the characterizing theorem follows from the stored
		// definition outright.
		derived := deriveDirectCharacterizing(step.constTerm, p)
		if derived == nil {
			return nil
		}
		return tactic.MakeEmptySubGoals(p, derived)
	}
	// A Hilbert-shape definition stated as ITSELF — a direct definition
	// whose body is a choice (`ind_suc = εf. …`), the goal exactly the
	// definition's own equation — is read as that equation, with no
	// obligation: only an exact match takes this route, so a
	// specification's characterizing form P(c) (an equation only by
	// accident, `c = ⊤` for `c = εx. x ⇔ ⊤`) still surfaces its
	// existence obligation below.
	if derived := deriveDirectExact(step.constTerm, p); derived != nil {
		return tactic.MakeEmptySubGoals(p, derived)
	}

	// HILBERT: the existence obligation.
	bridge := prop.ExistentialConstDef(step.constTerm)
	if bridge.IsZero() || bridge.NumHyps() != 1 {
		return nil
	}
	existsProp := core.MakeProp(bridge.Hyps()[0])
	goalStmt := core.MakeProp(p.Conclusion())
	// Statement-level pre-check: the goal must be the characterizing
	// form P(c) up to normalize arrangement — checked here so a
	// mismatched goal fails the APPLY (agent-visible), never the
	// reconstruct (a panic mid-force).
	if BridgeNormalize(goalStmt, core.MakeProp(bridge.Conclusion())) == nil {
		return nil
	}
	dischargeGoal := func(existsThm Prop) Prop {
		weakened := prop.WeakenTo(existsThm, existsProp)
		raw := WrapProp(bridge).DeriveHypFrom(weakened)
		out := BridgeNormalize(goalStmt, raw)
		if out == nil {
			// The statement-level pre-check passed at apply; the proved
			// side runs the identical pipeline, so divergence here is an
			// engine bug, not an authoring error.
			panic(fmt.Sprintf("_DefineStep: characterizing form diverged between "+
				"apply and reconstruct for %s", PrintTerm(step.constTerm)))
		}
		return out
	}

	// WF shape (measure set): the one child is the TERMINATION
	// obligation — the author's mathematics — and the reconstruct runs
	// the WF equation compiler on the closed obligation (transcript D's
	// D1/D2 as a composite). The obligation statement is recomputed
	// from the ε-payload plus the measure, so replay is deterministic.
	if step.measure != nil {
		if step.env == nil {
			return nil
		}
		wfd, err := AnalyzeWFExistence(existsProp, step.measure)
		if err != nil {
			return nil
		}
		reconstruct := func(thms ...Prop) Prop {
			existsThm, _, err := CompileWFExistence(step.env, wfd, thms[0])
			if err != nil {
				// The obligation child matched and closed; a compile
				// failure past that point is an engine fault, not an
				// authoring error.
				panic(fmt.Sprintf("_DefineStep: WF compile failed for %s: %v",
					PrintTerm(step.constTerm), err))
			}
			return dischargeGoal(existsThm)
		}
		return tactic.MakeSubGoals(p, reconstruct, wfd.Obligation)
	}

	// LIFT shape (a class pattern among the equation's arguments —
	// define_lift.go): the one child is the RESPECTFULNESS obligation,
	// the author's mathematics, and the reconstruct runs the lift
	// compiler on the closed obligation. The obligation statement is
	// recomputed from the ε-payload, so replay is deterministic.
	if step.env != nil {
		if ld, err := AnalyzeLiftExistence(existsProp, envConstMetaResolver(step.env)); err == nil {
			reconstruct := func(thms ...Prop) Prop {
				existsThm, err := CompileLiftExistence(step.env, ld, thms[0])
				if err != nil {
					// The obligation child matched and closed; a compile
					// failure past that point is an engine fault or a
					// missing dep (the quotient's Sound / Exact) — surface
					// it loudly, never as a silent non-close.
					panic(fmt.Sprintf("_DefineStep: lift compile failed for %s: %v",
						PrintTerm(step.constTerm), err))
				}
				return dischargeGoal(existsThm)
			}
			return tactic.MakeSubGoals(p, reconstruct, ld.Obligation)
		}
	}

	// Engine-side obligation close — the equation compiler (primrec).
	// Deterministic and refuter-free: analyze the obligation's own
	// statement, instantiate the carrier's registered recursion schema,
	// ∃!→∃, bridge. Zero children when it lands (the charter's
	// close-or-fail); an obligation the compiler does not serve (an env
	// with no schemas) surfaces as the open child below.
	if step.env != nil {
		if rd, err := AnalyzeRecursiveExistence(existsProp); err == nil {
			if existsThm, _, err := CompileRecursiveExistence(step.env, rd); err == nil {
				return tactic.MakeEmptySubGoals(p, dischargeGoal(existsThm))
			}
		}
	}

	reconstruct := func(thms ...Prop) Prop { return dischargeGoal(thms[0]) }
	return tactic.MakeSubGoals(p, reconstruct, existsProp)
}

func (step _DefineStep) applyAction(s *Script, root *GoalStackNode) { s.Do(root, step) }

// ApplyDefineStep runs the define composite on n's goal, recording ONE
// _DefineStep ministep when it applies. The engine's `define` RPC
// entry: bool-returning (the ApplySetTac convention) so a goal that is
// not the minted const's characterizing shape surfaces as an
// agent-visible error instead of a panic. env feeds the HILBERT
// branch's engine-side obligation close (the equation compiler); the
// direct shape ignores it.
func ApplyDefineStep(n *GoalStackNode, env *ProverEnv, c Term) bool {
	return n.runStep(_DefineStep{constTerm: c.Core().(ConstTerm), env: env})
}

// ApplyDefineWFStep is ApplyDefineStep for the WF shape: the measure
// routes the composite's HILBERT branch to the termination-obligation
// child (left OPEN for the author — the RPC returns with the section
// unproved; D2 closes it).
func ApplyDefineWFStep(n *GoalStackNode, env *ProverEnv, c Term, measure Term) bool {
	return n.runStep(_DefineStep{constTerm: c.Core().(ConstTerm),
		measure: measure.Core(), env: env})
}

// =======================================================================
// DefineData — the datatype move's ministep
// =======================================================================
//
// ONE proto tag (StepProto_DefineData, tag 58) whose payload is the
// minted identity alone — the mk const plus the ordered constructor
// consts (DefineDataProto); the recspace encoding, the shape
// predicate, and the typedef source all live on those consts' metas,
// so nothing else rides the wire to drift. `apply` IS the shared
// executor: the engine `define` RPC's `data:` payload (session side),
// a family.DefineData Build (replay), and emit-time
// verification all run this same function — the record/emit/replay
// code-reuse principle (step_composite.go), sibling of define / by /
// set_tac / simp_with.
//
// The MINT itself (core.NewTypeDef + one core.NewConstDef per
// constructor + exclusive registration — define_data.go) happens
// OUTSIDE the proof tree at the RPC/registration boundary, exactly as
// for `define`: apply runs on probe clones, so a kernel-definitional
// act must not live inside a step. By the time this step runs the
// datatype exists; the step's whole job is deriving ONE of its four
// derived-theorem families.
//
// Dispatch is by GOAL SHAPE: apply recovers the datatype from the
// metas, recomputes the four statements (INDUCT's sequent form,
// RECURSION, INJ, DISTINCT), α-matches the recorded goal against
// them, and re-derives the matched one — pure kernel derivation over
// the recspace rows, deterministic and refuter-free, zero children
// (close-or-fail). A goal matching none of the four fails the apply
// (agent-visible), never a panic mid-force.

type _DefineDataStep struct {
	mk    ConstTerm
	ctors []ConstTerm
	// env is RUNTIME-ONLY (never serialized — proto() carries the
	// consts alone), injected by Script.Do / passed by
	// ApplyDefineDataStep. The derivations read the recspace rows
	// (recspace_recursion, family_cons, …) through it; the INDUCT branch needs no
	// rows but keeps the same plumbing.
	env *ProverEnv
}

// DefineDataStep is the ministep constructor: the body of one of a
// data definition's derived-theorem sections. mk must resolve to the
// minted typedef abs const, ctors to the constructor consts in
// declaration order (via .Core()). Nil-env by construction (the
// CnfRefute convention): Script.Do injects the running Script's env.
func DefineDataStep(mk Term, ctors ...Term) Step {
	cs := make([]ConstTerm, len(ctors))
	for i, c := range ctors {
		cs[i] = c.Core().(ConstTerm)
	}
	return _DefineDataStep{mk: mk.Core().(ConstTerm), ctors: cs}
}

// DefineDataStep — pure struct-literal sugar; method delegates to the
// bare form (the DefineStep convention, for emitted bodies).
func (s *Script) DefineDataStep(mk Term, ctors ...Term) Step {
	return DefineDataStep(mk, ctors...)
}

func (step _DefineDataStep) String() string {
	return fmt.Sprintf("DefineData: %s", PrintTerm(step.mk))
}

func (step _DefineDataStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	Assert(!step.mk.IsZero() && len(step.ctors) > 0)
	p := &DefineDataProto{Mk: b.TermRef(step.mk)}
	for _, c := range step.ctors {
		p.Ctors = append(p.Ctors, b.TermRef(c))
	}
	return &StepProto_DefineData{DefineData: p}
}

func (step _DefineDataStep) apply(p Prop) *SubGoals {
	Assert(!step.mk.IsZero())
	md, err := RecoverMintedDatatype(step.mk, step.ctors)
	if err != nil {
		return nil
	}
	goalStmt := core.MakeProp(p.Conclusion(), p.Hyps()...)
	for _, k := range md.Kinds() {
		stmt := md.Stmt(k)
		if stmt == nil || !stmt.AlphaEquals(goalStmt) {
			continue
		}
		// The goal IS this datatype's derived statement; from here the
		// derivation must close (close-or-fail). A failure is an env
		// fault (a recspace row missing from LibraryThms) or a kit
		// fault — either way a defect to surface loudly, never a
		// silent does-not-apply.
		derived, derr := DeriveDataTheorem(step.env, md, k)
		if derr != nil || derived == nil {
			panic(fmt.Sprintf("_DefineDataStep: goal matches %s's %v statement but the "+
				"derivation failed: %v", md.Def.TypeName, k, derr))
		}
		return tactic.MakeEmptySubGoals(p, derived)
	}
	return nil
}

func (step _DefineDataStep) applyAction(s *Script, root *GoalStackNode) { s.Do(root, step) }

// ApplyDefineDataStep runs the define-data composite on n's goal,
// recording ONE _DefineDataStep ministep when it applies. The engine's
// `define data:` RPC entry — bool-returning (the ApplyDefineStep
// convention) so a goal that is not one of the datatype's derived
// statements surfaces as an agent-visible error instead of a panic.
func ApplyDefineDataStep(n *GoalStackNode, env *ProverEnv, mk Term, ctors []Term) bool {
	cs := make([]ConstTerm, len(ctors))
	for i, c := range ctors {
		cs[i] = c.Core().(ConstTerm)
	}
	return n.runStep(_DefineDataStep{mk: mk.Core().(ConstTerm), ctors: cs, env: env})
}

// =======================================================================
// DefineSpec — the specification move's ministep
// =======================================================================
//
// The `spec:` shape (define_spec.go is the analysis and compiler spine).
//
// ONE proto tag (StepProto_DefineSpec, tag 59) whose payload is the
// ordered spec-defined const list ALONE: the characterizing form is
// the recorded goal, each definition body lives on its const's meta,
// and the obligation statement is recomputed from the goal — nothing
// else rides the wire to drift. apply IS the shared executor (the
// record/emit/replay code-reuse principle): a family.DefineSpec Build
// (replay) and the engine session path run this same function.
//
// One child, always: the POINTWISE existence obligation
// (SpecDefinition.Obligation) — the author's mathematics, per the
// obligations-surfaced ruling. Reconstruction runs the spec compiler
// (CompileSpecExistence) on the closed obligation — Skolemization by
// ε-witnesses, the stored claims' shape conditioning, the
// ExistentialConstDef bridge chain — and BridgeNormalizes the last
// bridge's conclusion onto the recorded goal.

type _DefineSpecStep struct {
	consts []ConstTerm
	cases  []Case
	// env is RUNTIME-ONLY (never serialized), injected by Script.Do /
	// ApplyDefineSpecStep. The compiler reads the served fst/snd rows
	// from env.LibraryThms when a claim applies a constant at a pair
	// literal; nil env declines those shapes.
	env *ProverEnv
}

// DefineSpecStep is the ministep constructor: the body of a spec
// definition section. Each element of consts must resolve to a minted
// (or claimed) const via .Core(). The variadic Case closes the one
// obligation child.
func DefineSpecStep(consts []Term, cases ...Case) Step {
	cs := make([]ConstTerm, len(consts))
	for i, c := range consts {
		cs[i] = c.Core().(ConstTerm)
	}
	return _DefineSpecStep{consts: cs, cases: cases}
}

// DefineSpecStep — method sugar, the DefineStep convention (for
// emitted bodies).
func (s *Script) DefineSpecStep(consts []Term, cases ...Case) Step {
	return DefineSpecStep(consts, cases...)
}

func (step _DefineSpecStep) caseBodies() []Case { return step.cases }

func (step _DefineSpecStep) String() string {
	names := make([]string, len(step.consts))
	for i, c := range step.consts {
		names[i] = string(c.Name())
	}
	return fmt.Sprintf("DefineSpec: %s", strings.Join(names, ", "))
}

func (step _DefineSpecStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	Assert(len(step.consts) > 0)
	p := &DefineSpecProto{Consts: make([]uint32, len(step.consts))}
	for i, c := range step.consts {
		p.Consts[i] = b.TermRef(c)
	}
	return &StepProto_DefineSpec{DefineSpec: p}
}

func (step _DefineSpecStep) apply(p Prop) *SubGoals {
	if len(step.consts) == 0 {
		return nil
	}
	if p.NumHyps() != 0 {
		// A definition section's root is a closed statement.
		return nil
	}
	for _, c := range step.consts {
		if !prop.IsHilbertConstDef(c) {
			return nil
		}
	}
	goal := core.MakeProp(p.Conclusion())
	sd, err := AnalyzeSpecGoal(goal, step.consts)
	if err != nil {
		return nil
	}
	env := step.env
	reconstruct := func(thms ...Prop) Prop {
		derived, err := CompileSpecExistence(env, sd, thms[0])
		if err != nil {
			// The obligation child matched and closed; a compile failure
			// past that point is an engine fault or a missing dep —
			// surface it loudly, never as a silent non-close.
			panic(fmt.Sprintf("_DefineSpecStep: spec compile failed for %s: %v",
				step.String(), err))
		}
		out := BridgeNormalize(goal, derived)
		if out == nil {
			panic(fmt.Sprintf(
				"_DefineSpecStep: derived property is not normalize-equivalent to "+
					"the goal for %s\n  derived: %s\n  goal:    %s",
				step.String(), PrintProp(derived), PrintProp(goal)))
		}
		return out
	}
	return tactic.MakeSubGoals(p, reconstruct, sd.Obligation)
}

func (step _DefineSpecStep) applyAction(s *Script, root *GoalStackNode) { s.Do(root, step) }

// ApplyDefineSpecStep runs the spec define composite on n's goal,
// recording ONE _DefineSpecStep ministep when it applies —
// bool-returning (the ApplySetTac convention) so a goal that is not
// the constants' characterizing shape surfaces as an agent-visible
// error instead of a panic.
func ApplyDefineSpecStep(n *GoalStackNode, env *ProverEnv, consts []Term) bool {
	cs := make([]ConstTerm, len(consts))
	for i, c := range consts {
		cs[i] = c.Core().(ConstTerm)
	}
	return n.runStep(_DefineSpecStep{consts: cs, env: env})
}

// =======================================================================
// DefineType — the type-definition move's ministep
// =======================================================================
//
// The type definition as a composite (define_type.go is the
// analysis and mint spine). ONE proto tag (StepProto_DefineType) whose
// payload is the minted ABS const alone: the predicate, the
// representation type and the recorded inhabitation source all live
// on its meta, so nothing else rides the wire to drift. `apply` IS the
// shared executor: the engine `define` RPC's `typedef:` payload
// (session side), a family.DefineType Build (replay) and emit-time
// verification all run this same function.
//
// The MINT itself (core.NewTypeDef + exclusive registration —
// MintTypeDefinition) happens OUTSIDE the proof tree at the
// RPC/registration boundary, as for every define shape. By the time
// this step runs the type exists; the step's whole job is deriving ONE
// of its two theorems.
//
// Dispatch is by GOAL SHAPE: apply recovers the type definition from
// the abs meta, recomputes the two statements (Retraction /
// Membership), α-matches the recorded goal against them, and
// re-derives the matched one through the kernel's TypeDefExpand. A
// trivial inhabitation (the normalizer decides ∃x. Pred(x)) closes
// outright from the recorded certificate — zero children. Otherwise
// the one child is the inhabitation statement — `∃x. Pred(x)`, or
// `Pred(w)` reduced at the witness — the author's mathematics, closed
// by a cite of the proved section (session) or of the Existence dep
// (chapter); the reconstruct bridges the proved child to the source
// and expands. A goal matching neither statement fails the apply
// (agent-visible), never a panic mid-force.

type _DefineTypeStep struct {
	abs   ConstTerm
	cases []Case
}

// DefineTypeStep is the ministep constructor: the body of one of a
// type definition's two sections. abs must resolve to the minted abs
// const (via .Core()). The variadic Case closes the inhabitation child
// when there is one.
func DefineTypeStep(abs Term, cases ...Case) Step {
	return _DefineTypeStep{abs: abs.Core().(ConstTerm), cases: cases}
}

// DefineTypeStep — method sugar, the DefineStep convention (for
// emitted bodies).
func (s *Script) DefineTypeStep(abs Term, cases ...Case) Step {
	return DefineTypeStep(abs, cases...)
}

func (step _DefineTypeStep) caseBodies() []Case { return step.cases }

func (step _DefineTypeStep) String() string {
	return fmt.Sprintf("DefineType: %s", PrintTerm(step.abs))
}

func (step _DefineTypeStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	Assert(!step.abs.IsZero())
	return &StepProto_DefineType{DefineType: &DefineTypeProto{Abs: b.TermRef(step.abs)}}
}

func (step _DefineTypeStep) apply(p Prop) *SubGoals {
	Assert(!step.abs.IsZero())
	if p.NumHyps() != 0 {
		// A definition section's root is a closed statement.
		return nil
	}
	md, err := RecoverMintedTypedef(step.abs)
	if err != nil {
		return nil
	}
	goal := core.MakeProp(p.Conclusion())
	kind, ok := md.KindOf(goal)
	if !ok {
		return nil
	}
	if md.Def.Trivial {
		// The recorded source is the normalizer's certificate.
		return tactic.MakeEmptySubGoals(p, md.Derive(kind, step.abs.Meta().DefSource()))
	}
	reconstruct := func(thms ...Prop) Prop {
		return md.Derive(kind, md.Def.SourceFromObligation(thms[0]))
	}
	return tactic.MakeSubGoals(p, reconstruct, md.Def.Obligation)
}

func (step _DefineTypeStep) applyAction(s *Script, root *GoalStackNode) { s.Do(root, step) }

// ApplyDefineTypeStep runs the define-type composite on n's goal,
// recording ONE _DefineTypeStep ministep when it applies — the engine's
// `define typedef:` RPC entry, bool-returning (the ApplyDefineStep
// convention) so a goal that is not one of the type's two statements
// surfaces as an agent-visible error instead of a panic. The
// inhabitation child, when there is one, is left for the caller to
// close.
func ApplyDefineTypeStep(n *GoalStackNode, abs Term) bool {
	return n.runStep(_DefineTypeStep{abs: abs.Core().(ConstTerm)})
}

// =======================================================================
// DefineInductive — the inductive-definition move's ministep
// =======================================================================
//
// The inductive definition as a composite (define_inductive.go
// is the analysis, mint and derivation spine). ONE proto tag
// (StepProto_DefineInductive, 63) whose payload is the minted constant,
// the parameter variables and the rules AS STATED: the rules are the
// definition's identity — the closure body on the constant's meta does
// not determine them, a substituted index equation and a premise
// equation reading alike — so they ride the record the way the WF
// measure does, and nothing else does. `apply` IS the shared executor:
// the engine `define` RPC's `inductive:` payload (session side), a
// family.DefineInductive Build (replay) and emit-time verification all
// run this same function.
//
// The MINT (core.NewConstDef of the closure body + exclusive
// registration — MintInductiveDefinition) happens OUTSIDE the proof
// tree at the RPC/registration boundary, as for every define shape.
// By the time this step runs the constant exists; the step's whole job
// is deriving ONE of its three theorems.
//
// Dispatch is by GOAL SHAPE: apply re-runs the analysis on the
// recorded rules, checks the constant's body is their closure,
// recomputes the three statements (Rules / Induct / Cases), α-matches
// the recorded goal against them, and re-derives the matched one —
// pure kernel derivation, deterministic and refuter-free, zero
// children (close-or-fail). A goal matching none of the three fails
// the apply (agent-visible), never a panic mid-force.

type _DefineInductiveStep struct {
	constTerm ConstTerm
	params    []VarTerm
	rules     []Term
}

// DefineInductiveStep is the ministep constructor: the body of one of
// an inductive definition's three sections. c must resolve to the
// minted constant (via .Core()); params are the parameter variables in
// declaration order; rules the rules as stated, with the definiendum
// as a variable of the constant's name and type.
func DefineInductiveStep(c Term, params []Term, rules []Term) Step {
	pv := make([]VarTerm, len(params))
	for i, p := range params {
		pv[i] = p.Core().(VarTerm)
	}
	rs := make([]Term, len(rules))
	for i, r := range rules {
		rs[i] = r.Core()
	}
	return _DefineInductiveStep{constTerm: c.Core().(ConstTerm), params: pv, rules: rs}
}

// DefineInductiveStep — method sugar, the DefineStep convention (for
// emitted bodies).
func (s *Script) DefineInductiveStep(c Term, params []Term, rules []Term) Step {
	return DefineInductiveStep(c, params, rules)
}

func (step _DefineInductiveStep) String() string {
	return fmt.Sprintf("DefineInductive: %s", PrintTerm(step.constTerm))
}

func (step _DefineInductiveStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	Assert(!step.constTerm.IsZero() && len(step.rules) > 0)
	p := &DefineInductiveProto{Const: b.TermRef(step.constTerm)}
	for _, v := range step.params {
		p.Params = append(p.Params, b.TermRef(v))
	}
	for _, r := range step.rules {
		p.Rules = append(p.Rules, b.TermRef(r))
	}
	return &StepProto_DefineInductive{DefineInductive: p}
}

func (step _DefineInductiveStep) apply(p Prop) *SubGoals {
	Assert(!step.constTerm.IsZero())
	if p.NumHyps() != 0 {
		// A definition section's root is a closed statement.
		return nil
	}
	d, err := RecoverInductiveDefinition(step.constTerm, step.params, step.rules)
	if err != nil {
		return nil
	}
	goal := core.MakeProp(p.Conclusion())
	for _, k := range d.Kinds() {
		if !d.Stmt(step.constTerm, k).AlphaEquals(goal) {
			continue
		}
		// The goal IS this definition's derived statement; from here the
		// derivation must close (close-or-fail) — a failure is kit
		// drift, surfaced loudly, never a silent does-not-apply.
		return tactic.MakeEmptySubGoals(p, DeriveInductiveTheorem(d, step.constTerm, k))
	}
	return nil
}

func (step _DefineInductiveStep) applyAction(s *Script, root *GoalStackNode) { s.Do(root, step) }

// ApplyDefineInductiveStep runs the define-inductive composite on n's
// goal, recording ONE _DefineInductiveStep ministep when it applies —
// the engine's `define inductive:` RPC entry, bool-returning (the
// ApplyDefineStep convention) so a goal that is not one of the
// definition's three statements surfaces as an agent-visible error
// instead of a panic.
func ApplyDefineInductiveStep(n *GoalStackNode, c Term, params []Term, rules []Term) bool {
	return n.runStep(DefineInductiveStep(c, params, rules).(_DefineInductiveStep))
}

// =======================================================================
// DefineQuotient — the quotient definition move's ministep
// =======================================================================
//
// A quotient as a composite (define_quotient.go is the analysis, mint
// and derivation spine). ONE proto tag (StepProto_DefineQuotient, 64)
// whose payload is the minted CLASS MAP alone: its definition
// λx. abs(R(x)) names the relation and the typedef abs, whose meta
// names the rep and carries the inhabitation, so nothing else rides the
// wire to drift. `apply` IS the shared executor: the engine `define`
// RPC's `quotient:` payload (session side), a family.DefineQuotient
// Build (replay) and emit-time verification all run this same
// function.
//
// The MINT (core.NewTypeDef + the class map's core.NewConstDef +
// exclusive registration — MintQuotientDefinition) happens OUTSIDE the
// proof tree at the RPC/registration boundary, as for every define
// shape. By the time this step runs the type exists; the step's whole
// job is deriving ONE of its seven theorems.
//
// Dispatch is by GOAL SHAPE: apply recovers the quotient from the class
// map, recomputes the seven statements, α-matches the recorded goal
// against them, and re-derives the matched one — pure kernel
// derivation, deterministic and refuter-free. The one child, in every
// section, is equivalence(R) — the author's mathematics, closed by a
// cite of the proved section (session) or of the Equivalence dep
// (chapter); the sections whose derivation reads no law carry it all
// the same, so that every section declares the one dep and emit renders
// any of them as the one door call. A goal matching none of the seven
// fails the apply (agent-visible), never a panic mid-force.

type _DefineQuotientStep struct {
	mk    ConstTerm
	cases []Case
	// env is RUNTIME-ONLY (never serialized), injected by Script.Do /
	// ApplyDefineQuotientStep: the recovery resolves the relations
	// chapter's `equivalence` constant through its registry.
	env *ProverEnv
}

// DefineQuotientStep is the ministep constructor: the body of one of a
// quotient definition's seven sections. mk must resolve to the minted
// class map (via .Core()). The variadic Case closes the equivalence
// child.
func DefineQuotientStep(mk Term, cases ...Case) Step {
	return _DefineQuotientStep{mk: mk.Core().(ConstTerm), cases: cases}
}

// DefineQuotientStep — method sugar, the DefineStep convention (for
// emitted bodies).
func (s *Script) DefineQuotientStep(mk Term, cases ...Case) Step {
	return DefineQuotientStep(mk, cases...)
}

func (step _DefineQuotientStep) caseBodies() []Case { return step.cases }

func (step _DefineQuotientStep) String() string {
	return fmt.Sprintf("DefineQuotient: %s", PrintTerm(step.mk))
}

func (step _DefineQuotientStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	Assert(!step.mk.IsZero())
	return &StepProto_DefineQuotient{DefineQuotient: &DefineQuotientProto{Mk: b.TermRef(step.mk)}}
}

func (step _DefineQuotientStep) apply(p Prop) *SubGoals {
	Assert(!step.mk.IsZero())
	if step.env == nil {
		return nil
	}
	mq, err := RecoverMintedQuotient(step.mk, envConstMetaResolver(step.env))
	if err != nil {
		return nil
	}
	goal := core.MakeProp(p.Conclusion(), p.Hyps()...)
	kind, ok := mq.KindOf(goal)
	if !ok {
		return nil
	}
	reconstruct := func(thms ...Prop) Prop { return mq.Derive(kind, thms[0]) }
	return tactic.MakeSubGoals(p, reconstruct, mq.Def.Equivalence)
}

func (step _DefineQuotientStep) applyAction(s *Script, root *GoalStackNode) { s.Do(root, step) }

// ApplyDefineQuotientStep runs the define-quotient composite on n's
// goal, recording ONE _DefineQuotientStep ministep when it applies —
// the engine's `define quotient:` RPC entry, bool-returning (the
// ApplyDefineStep convention) so a goal that is not one of the
// quotient's seven statements surfaces as an agent-visible error
// instead of a panic. The equivalence child is left for the caller to
// close.
func ApplyDefineQuotientStep(n *GoalStackNode, env *ProverEnv, mk Term) bool {
	return n.runStep(_DefineQuotientStep{mk: mk.Core().(ConstTerm), env: env})
}

// envConstMetaResolver adapts an env's const-meta lookup to the
// resolver shape the quotient spine reads constants through.
func envConstMetaResolver(env *ProverEnv) func(TermName) ConstTermMeta {
	if env == nil || env.ProofService == nil || env.ProofService.LoadConstMeta == nil {
		return nil
	}
	return func(name TermName) ConstTermMeta {
		if meta, ok := env.ProofService.LoadConstMeta(name); ok {
			return meta
		}
		return ConstTermMeta{}
	}
}

// IsDefinitionSection reports whether n's recorded step is one of the
// definition composites (define / define_data / define_spec /
// define_type / define_inductive / define_quotient) — the root of a
// definition section. Its theorem is an ENTRY at landing, cited by
// key: nothing may inline its derivation (ApplyCiteNode) and nothing
// re-runs it (VerifyStepsReplay).
func (n *GoalStackNode) IsDefinitionSection() bool {
	switch n.miniStep.(type) {
	case _DefineStep, _DefineDataStep, _DefineSpecStep, _DefineTypeStep, _DefineInductiveStep, _DefineQuotientStep:
		return true
	}
	return false
}
