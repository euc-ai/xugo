// define_type.go — the type-definition move's analysis and mint spine:
// what the session `define` RPC's
// `typedef:` payload, the chapter door family.DefineType and the
// _DefineTypeStep composite (step_define.go) share, the way
// define_data.go serves the datatype move. The mint is core.NewTypeDef
// over a SOURCE ⊢ Pred(_) — the inhabitation — and the two theorems a
// type definition comes with are derived from that source by the
// kernel's TypeDefExpand and closed to their stated form:
//
//	Retraction   ∀a:T. abs(rep(a)) = a
//	Membership   ∀r:ρ. Pred(r) ⇔ rep(abs(r)) = r     (Pred(r) β-reduced)
//
// The inhabitation comes one of two ways. TRIVIAL — `∃x. Pred(x)`
// holds by normalization alone (the pair shape is inhabited by any
// pair, an equivalence-class shape by any class) — is proved at
// analysis by the normalizer and recorded as a certificate: pure
// logic, no obligation. Otherwise it is the author's mathematics,
// stated one of two ways: `∃x. Pred(x)` (the existence form), or
// `Pred(w)` at a closed witness w (the applied form the basic type
// definition takes — `is_num(ind_zero)`), written with the redex reduced
// when Pred is a λ. That statement is the composite's one child; the
// session closes it by citing the proved section, the chapter by
// citing its Existence dep, and the reconstruct bridges the proved
// child to the recorded source (∃ unfolded at Pred, or the β-equation
// read backwards) — kernel rules throughout, so no path trusts the
// inhabitation.
//
// A trivial inhabitation is never an obligation: a statement the
// normalizer decides has the key of ⊤, which no entry may carry.

package proof

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

// TypeDefinition is the analyzed form of one type definition: the
// representing predicate, its representation type, and the
// inhabitation's shape.
type TypeDefinition struct {
	// Pred is the closed representing predicate, ρ → bool.
	Pred Term
	// PredAbs is Pred as a λ; nil for a constant predicate (is_num),
	// whose membership stands unreduced.
	PredAbs core.AbsTerm
	// Rho is the representation type.
	Rho HolType
	// Witness is the closed point of ρ the applied form states the
	// membership at; nil for the existence form.
	Witness Term
	// Exists is `∃x:ρ. Pred(x)` — ∃ applied to Pred.
	Exists Prop
	// Trivial reports that Exists holds by normalization alone; then
	// there is no obligation and TrivialSource is the certificate.
	Trivial bool
	// Applied is the recorded source's statement: `Pred(w)` for the
	// applied form, `Pred(εPred)` — what `∃(Pred)` unfolds to under the
	// kernel's definition of ∃ — otherwise.
	Applied Prop
	// Obligation is the statement the author proves — `Pred(w)` with a
	// λ-predicate's redex reduced, or Exists — and the composite's one
	// child. Nil when Trivial.
	Obligation Prop

	trivialSource Prop
	// betaAtWitness is `⊢ Pred(w) = reduced` for a λ-predicate's applied
	// form: the bridge from the reduced obligation to the recorded
	// source. Nil otherwise.
	betaAtWitness *prop.PropWrapper
}

// AnalyzeTypeDefinition checks the predicate (closed, ρ → bool) and
// the witness (closed, of type ρ; nil for the existence form) and
// decides the inhabitation's shape. A witness that is literally the
// selected point εPred is refused: the applied form at that point IS
// the existence form, and the recorded source would not tell them
// apart.
func AnalyzeTypeDefinition(pred Term, witness Term) (*TypeDefinition, error) {
	if pred == nil {
		return nil, fmt.Errorf("type definition: a representing predicate is required")
	}
	predType, isComposite := pred.Type().(CompositeType)
	if !isComposite || !ext.IsFunType(pred.Type()) || !predType.SubType(1).Equals(core.TypeBool()) {
		return nil, fmt.Errorf("type definition: Pred must be a predicate ρ → bool, got %s : %s",
			PrintTerm(pred), ext.FormatType(pred.Type()))
	}
	if frees := pred.Frees(nil); len(frees) > 0 {
		return nil, fmt.Errorf("type definition: Pred must be closed — free %s", PrintTerm(frees[0]))
	}
	td := &TypeDefinition{Pred: pred, Rho: predType.SubType(0)}
	td.PredAbs, _ = pred.AsAbsTerm()
	td.Exists = core.MakeProp(core.Apply(existsAt(td.Rho), pred))

	normalized, reconstruct := prop.Normalize(td.Exists)
	td.Trivial = normalized.Conclusion().Equals(ext.T) && normalized.NumHyps() == 0

	if witness != nil {
		if frees := witness.Frees(nil); len(frees) > 0 {
			return nil, fmt.Errorf("type definition: Witness must be closed — free %s", PrintTerm(frees[0]))
		}
		if !witness.Type().Equals(td.Rho) {
			return nil, fmt.Errorf("type definition: Witness %s : %s is not of the representation type %s",
				PrintTerm(witness), ext.FormatType(witness.Type()), ext.FormatType(td.Rho))
		}
		if witness.AlphaEquals(selectedPoint(pred)) {
			return nil, fmt.Errorf("type definition: the witness is the selected point εPred — state the existence form instead")
		}
		td.Witness = witness
		td.Applied = core.MakeProp(core.Apply(pred, witness))
		td.Obligation = td.Applied
		if !td.PredAbs.IsZero() {
			td.betaAtWitness = prop.DeepBetaAbs(td.PredAbs)(td.Applied.Conclusion())
			_, reduced, ok := core.MatchesEQ(td.betaAtWitness.Conclusion())
			utils.Assert(ok)
			td.Obligation = core.MakeProp(reduced)
		}
	} else {
		td.Applied = core.MakeProp(selectedWitness(pred))
		td.Obligation = td.Exists
	}
	if td.Trivial {
		td.Obligation = nil
		td.trivialSource = selectFromExists(reconstruct(prop.DerivesTrue), pred).AsThmCert()
	}
	return td, nil
}

// TrivialSource is the certificate ⊢ Pred(εPred) a trivial
// inhabitation records as the mint's source. Nil unless Trivial.
func (td *TypeDefinition) TrivialSource() Prop { return td.trivialSource }

// SourceFromObligation bridges the proved obligation to the recorded
// source ⊢ Pred(_): the existence form unfolds ∃ at Pred (kernel
// rules: the definition of ∃ instantiated at ρ, applied to Pred, the
// redex reduced, EqMP); the applied form reads the β-equation
// backwards when the obligation was stated reduced, and is the source
// verbatim otherwise. The proved statement must be the obligation —
// the composite's agreement check; a mismatch panics, which is the
// door's own contract at replay.
func (td *TypeDefinition) SourceFromObligation(proved Prop) Prop {
	if td.Trivial {
		panic("type definition: a trivial inhabitation has no obligation to bridge from")
	}
	if td.Witness == nil {
		return selectFromExists(proved, td.Pred)
	}
	if proved.AlphaEquals(td.Applied) {
		return proved
	}
	if td.betaAtWitness != nil && proved.NumHyps() == 0 &&
		proved.Conclusion().AlphaEquals(td.Obligation.Conclusion()) {
		return td.betaAtWitness.EqSym().EqMP(proved)
	}
	panic(fmt.Sprintf("type definition: the inhabitation proves %s, not the recorded membership %s",
		PrintTerm(proved.Conclusion()), PrintTerm(td.Applied.Conclusion())))
}

// TypeDefTheoremKind names one of the two theorems a type definition
// comes with.
type TypeDefTheoremKind int

const (
	TypeDefRetraction TypeDefTheoremKind = iota
	TypeDefMembership
)

// TypeDefTheoremKinds lists the two kinds in registration order.
var TypeDefTheoremKinds = []TypeDefTheoremKind{TypeDefRetraction, TypeDefMembership}

func (k TypeDefTheoremKind) String() string {
	switch k {
	case TypeDefRetraction:
		return "Retraction"
	case TypeDefMembership:
		return "Membership"
	}
	return fmt.Sprintf("TypeDefTheoremKind(%d)", int(k))
}

// MintedTypedef is a type definition after its mint: the analysis, the
// minted identity, and the two theorems' statements.
type MintedTypedef struct {
	Def      *TypeDefinition
	Meta     core.MetaType
	Abs, Rep ConstTerm
	// Retraction and Membership are the two statements, computed from
	// the recorded source without forcing it.
	Retraction, Membership Prop
}

// Stmt returns the statement of one kind.
func (md *MintedTypedef) Stmt(k TypeDefTheoremKind) Prop {
	switch k {
	case TypeDefRetraction:
		return md.Retraction
	case TypeDefMembership:
		return md.Membership
	}
	return nil
}

// KindOf reports which of the two statements goal is, α-equal.
func (md *MintedTypedef) KindOf(goal Prop) (TypeDefTheoremKind, bool) {
	for _, k := range TypeDefTheoremKinds {
		if md.Stmt(k).AlphaEquals(goal) {
			return k, true
		}
	}
	return 0, false
}

// Derive derives one theorem from a source ⊢ Pred(_): the kernel's
// TypeDefExpand on the abs meta, the output closed to the stated form
// (the membership's redex reduced, the free variable ∀-bound).
// Provedness flows from the source: a certificate yields a theorem,
// a promise a promise-backed one, a bare statement the statement.
func (md *MintedTypedef) Derive(k TypeDefTheoremKind, source Prop) Prop {
	raw1, raw2 := md.Abs.Meta().TypeDefExpand(source)
	switch k {
	case TypeDefRetraction:
		return closeTypeDefAxiom(raw1, core.AbsTerm{})
	case TypeDefMembership:
		return closeTypeDefAxiom(raw2, md.Def.PredAbs)
	}
	panic(fmt.Sprintf("type definition: unknown theorem kind %v", k))
}

// TypeParams lists the minted type's parameters — Pred's type
// variables in first-occurrence order — as the parser spells them.
func (md *MintedTypedef) TypeParams() []string {
	vars := md.Def.Rho.TypeVars()
	out := make([]string, len(vars))
	for i, v := range vars {
		out[i] = string(v.Name())
	}
	return out
}

// TypeText is the minted type at its parameters, in author form
// ("int", "prod(A, B)").
func (md *MintedTypedef) TypeText() string {
	text := string(md.Meta.Name())
	if params := md.TypeParams(); len(params) > 0 {
		text += "("
		for i, p := range params {
			if i > 0 {
				text += ", "
			}
			text += p
		}
		text += ")"
	}
	return text
}

// MintTypeDefinition mints the type on source (⊢ Pred(_): the trivial
// certificate, or a promise that forces the inhabitation's proof) and
// registers the abs/rep pair under the definition move's EXCLUSIVE
// discipline — a name already registered errors, never shadows — after
// refusing a type name already in use: the kernel's bool and fun, or a
// type any registered constant mentions, at any arity. MetaType
// identity is by name and arity, so a second NewTypeDef under a name in
// use would mint a second bijection for the SAME type — two subsets, of
// any sizes, each in bijection with one type. The kernel panics on a
// name a definition has introduced; this mint is where every typedef
// door (the chapter's, the session's, the quotient's) refuses first,
// with an error, and refuses more: a type made by hand that a
// registered constant mentions, which a definition under its name would
// give a meaning. Every name is checked before anything registers.
func MintTypeDefinition(env *ProverEnv, td *TypeDefinition, typeName TypeName, absName, repName TermName, source Prop) (*MintedTypedef, error) {
	if env == nil || env.ProofService == nil || env.ProofService.LoadOrStoreConstMeta == nil {
		return nil, fmt.Errorf("define typedef: env carries no const-meta registry")
	}
	if _, alias := dsl.TypeAliasArity(string(typeName)); alias {
		return nil, fmt.Errorf("define typedef: %q is the text DSL's spelling of τ → bool, not a name a type may take", typeName)
	}
	if source == nil || source.NumHyps() != 0 || !source.Conclusion().AlphaEquals(td.Applied.Conclusion()) {
		panic(fmt.Sprintf("define typedef: the mint's source must state %s", PrintTerm(td.Applied.Conclusion())))
	}
	svc := env.ProofService
	for _, n := range []TermName{absName, repName} {
		if svc.LoadConstMeta != nil {
			if _, taken := svc.LoadConstMeta(n); taken {
				return nil, fmt.Errorf(
					"define typedef: constant %q is already registered — a second mint, or a "+
						"collision with an imported constant; pick a fresh name", n)
			}
		}
	}
	if svc.RangeConstMeta != nil && TypeNameInUseProbe(svc.RangeConstMeta)(typeName) {
		return nil, fmt.Errorf("define typedef: type %q is already in use — pick a fresh name", typeName)
	}
	metaType, abs, rep := core.NewTypeDef(source, typeName, absName, repName)
	for _, c := range []ConstTerm{abs, rep} {
		if _, existed := svc.LoadOrStoreConstMeta(c.Meta()); existed {
			return nil, fmt.Errorf("define typedef: %q was registered concurrently — pick a fresh name", c.Name())
		}
	}
	md := &MintedTypedef{Def: td, Meta: metaType, Abs: abs, Rep: rep}
	md.Retraction = core.MakeProp(md.Derive(TypeDefRetraction, source).Conclusion())
	md.Membership = core.MakeProp(md.Derive(TypeDefMembership, source).Conclusion())
	return md, nil
}

// RecoverMintedTypedef reads a type definition back off its abs
// const's meta — the composite's replay and emit's rendering both run
// this, so the recorded section and the rendered door call cannot
// drift. The recorded source `Pred(_)` gives the predicate and the
// inhabitation's form: an argument that is the selected point εPred
// is the existence form, anything else the witness.
func RecoverMintedTypedef(abs ConstTerm) (*MintedTypedef, error) {
	if abs.IsZero() {
		return nil, fmt.Errorf("type definition: nil abs const")
	}
	meta := abs.Meta()
	if !meta.IsTypeDefAbs() {
		return nil, fmt.Errorf("type definition: %s is not a type definition's abs constant", abs.Name())
	}
	source := meta.DefSource()
	app, ok := source.Conclusion().AsAppliedTerm()
	if !ok {
		return nil, fmt.Errorf("type definition: %s's recorded source is not an application: %s",
			abs.Name(), PrintTerm(source.Conclusion()))
	}
	pred := app.Fun()
	var witness Term
	if !app.Arg().AlphaEquals(selectedPoint(pred)) {
		witness = app.Arg()
	}
	td, err := AnalyzeTypeDefinition(pred, witness)
	if err != nil {
		return nil, err
	}
	absType, ok := abs.Type().(CompositeType)
	if !ok {
		return nil, fmt.Errorf("type definition: %s's type is not a function type", abs.Name())
	}
	minted, ok := absType.SubType(1).(CompositeType)
	if !ok {
		return nil, fmt.Errorf("type definition: %s does not abstract into a composite type", abs.Name())
	}
	rep := core.MakeConstTerm(meta.TypeDefCounterpart(), meta.TypeDefCounterpart().AbsType())
	md := &MintedTypedef{Def: td, Meta: minted.Meta(), Abs: abs, Rep: rep}
	md.Retraction = core.MakeProp(md.Derive(TypeDefRetraction, source).Conclusion())
	md.Membership = core.MakeProp(md.Derive(TypeDefMembership, source).Conclusion())
	return md, nil
}

// selectedPoint is εPred — the point ∃(Pred) selects.
func selectedPoint(pred Term) Term {
	rho := pred.Type().(CompositeType).SubType(0)
	eps := core.MakeConstTerm(core.MetaHilbert(), core.MakeFun(core.MakeFun(rho, core.TypeBool()), rho))
	return core.Apply(eps, pred)
}

// selectedWitness is Pred(εPred): the applied form ∃(Pred) unfolds to
// under the kernel's definition of ∃, which is the ⊢ P(_) shape a
// type definition is stamped against.
func selectedWitness(pred Term) Term {
	return core.Apply(pred, selectedPoint(pred))
}

// existsAt is the ∃ constant at the representation type ρ.
func existsAt(rho HolType) Term {
	return ext.Const(ext.EXISTS.Meta(), core.MakeFun(core.MakeFun(rho, core.TypeBool()), core.TypeBool())).Core()
}

// selectFromExists derives ⊢ Pred(εPred) from ⊢ ∃x. Pred(x): the
// kernel defines ∃ as λP. P(εP), so the existence theorem IS the
// selected form once the definition is unfolded and β-reduced at
// Pred. Pure kernel rules: the definition instantiated at ρ, applied
// to Pred (PropRightApply), the β-redex reduced, EqMP with the existence
// theorem. The existence theorem's predicate must be α-equal to pred
// or EqMP panics.
func selectFromExists(exists Prop, pred Term) Prop {
	app, ok := exists.Conclusion().AsAppliedTerm()
	if !ok {
		panic(fmt.Sprintf("type definition: the existence theorem is not an application: %s", PrintTerm(exists.Conclusion())))
	}
	existsConst, ok := app.Fun().AsConst()
	if !ok || existsConst.Name() != ext.EXISTS.Name() {
		panic(fmt.Sprintf("type definition: the existence theorem is not ∃-headed: %s", PrintTerm(exists.Conclusion())))
	}
	if !app.Arg().AlphaEquals(pred) {
		panic(fmt.Sprintf("type definition: the existence theorem's predicate differs from Pred:\n  proved: %s\n  Pred:   %s",
			PrintTerm(app.Arg()), PrintTerm(pred)))
	}
	unfolded := prop.WrapProp(existsConst.DefThm()).RightApply(pred)
	_, rhs, ok := core.MatchesEQ(unfolded.Conclusion())
	utils.Assert(ok)
	redex, ok := rhs.AsAppliedTerm()
	utils.Assert(ok)
	lam, ok := redex.Fun().AsAbsTerm()
	utils.Assert(ok)
	reduced := unfolded.Rewrite(prop.DeepBetaAbs(lam))
	return core.EqMP(reduced, exists)
}

// closeTypeDefAxiom turns a raw TypeDefExpand output — free in its one
// variable, the membership's left side a β-redex Pred(r) — into the
// stated form: the redex reduced (reduce = Pred; nil for the
// retraction) and the variable ∀-closed.
func closeTypeDefAxiom(raw Prop, reduce core.AbsTerm) Prop {
	w := prop.WrapProp(raw)
	if !reduce.IsZero() {
		w = w.Rewrite(prop.DeepBetaAbs(reduce))
	}
	frees := w.Conclusion().Frees(nil)
	if len(frees) != 1 {
		panic(fmt.Sprintf("type definition: an axiom with %d free variables: %s", len(frees), PrintTerm(w.Conclusion())))
	}
	return w.ConclForAll(frees[0])
}

// CheckMintedTypeName is the spelling rule for a minted type name: a
// plain identifier, not a lone capital (a type VARIABLE).
func CheckMintedTypeName(name string) error {
	for i, r := range name {
		ok := r == '_' || (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z') || (i > 0 && r >= '0' && r <= '9')
		if !ok {
			return fmt.Errorf("type name %q is not a plain identifier", name)
		}
	}
	if len(name) == 1 && name[0] >= 'A' && name[0] <= 'Z' {
		return fmt.Errorf("%q would parse as a type variable, not a type name", name)
	}
	return nil
}
