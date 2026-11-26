// define_lift.go — a function on a quotient, defined at its classes:
// the LIFT shape of the `recursive:` definition door (Lean's
// Quotient.lift / lift₂, Isabelle's lift_definition), served by the
// `define` composite's HILBERT branch with the author's obligation as
// its one child, the way the WF shape serves its termination.
//
// The author states the computation rule, with the quotient's class
// map as a constructor pattern wherever an argument is a class:
//
//	∀a b:ρ. op(⁅a⁆, ⁅b⁆) = ⁅a + b⁆            (a class-valued operation)
//	∀a b:ρ. le(⁅a⁆, ⁅b⁆) ⇔ a ≤ b              (a relation on classes)
//	∀x:A. ∀p:ρ. mem(x, ⁅p⁆) ⇔ x = fst(p) ∨ …   (an external argument beside a class)
//
// An argument is either a class pattern mk(a) — mk some quotient's
// class map (define_quotient.go), a one of the equation's binders — or
// a plain binder; at least one argument is a class. The value is a
// class ⁅body⁆ when it is written as one, else any term (a value of a
// quotient type not written as a class is held to equality, which is
// what it says). Nothing recurs. The one obligation is RESPECTFULNESS,
// in the shape the corpus states its well-definedness laws:
//
//	∀a a' b b'. R(a, a') ∧ R(b, b') ⇒ R'(body, body')     (R' the codomain's relation)
//	                                  ⇒ body = body'          (an external value)
//
// each class binder followed by its primed twin, an external binder
// held fixed. The constant mints as εf. ∀…. f(patterns) = value — the
// recursive shape's payload — and the existence compiler
// (CompileLiftExistence) derives ∃f from the proved obligation by
// kernel rules alone: the witness takes each class to a representative
// by choice, the class of that representative is the class given
// (Exact), respectfulness carries the body across, and Sound returns
// to classes. The quotient's Sound and Exact are read from
// env.LibraryThms under their conventional names (`<Q>_sound`,
// `<Q>_exact`), which the quotient door binds.

package proof

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// LiftArg is one argument of a lifted function: its binder, and the
// quotient whose class pattern it is (nil for an external argument).
type LiftArg struct {
	Var      VarTerm
	Quotient *MintedQuotient
}

// LiftDefinition is the analyzed form of one lift.
type LiftDefinition struct {
	DefVar   VarTerm
	Equation Prop
	// Binders are the equation's ∀-binders in order; every one is an
	// argument's.
	Binders []VarTerm
	Args    []LiftArg
	// Codomain is the value's quotient when the value is written as a
	// class, nil otherwise; Body is the value with its class map
	// peeled (the value itself otherwise).
	Codomain *MintedQuotient
	Body     Term
	// Obligation is the respectfulness statement — the composite's
	// child, the author's mathematics.
	Obligation Prop
	// Property is P(f), the equation's conclusion with the definiendum
	// free; EpsTerm εf. P(f) — the mint's payload; ExistsStmt ∃f. P(f).
	Property   Term
	EpsTerm    Term
	ExistsStmt Prop
}

// IsQuotientLiftEquation reports whether a parsed definition equation
// is a lift — some argument on its left is a quotient's class map
// applied — the classifier the doors route on before the recursive
// shape (a class map is a constructor of no datatype).
func IsQuotientLiftEquation(equation Prop, defVar VarTerm) bool {
	if equation == nil {
		return false
	}
	_, matrix := DecomposesFORALL(equation.Conclusion())
	l, _, ok := MatchesEQ(matrix)
	if !ok {
		return false
	}
	head, args := MatchesApply(l)
	if hv, isVar := head.AsVar(); !isVar || !hv.EqualsVar(defVar) {
		return false
	}
	for _, a := range args {
		if c, _, ok := classPattern(a); ok && !c.IsZero() {
			return true
		}
	}
	return false
}

// classPattern reads mk(t) for a class map mk: the map, its argument
// and whether t is such a pattern.
func classPattern(t Term) (ConstTerm, Term, bool) {
	h, args := MatchesApply(t)
	if h == nil || len(args) != 1 {
		return ConstTerm{}, nil, false
	}
	c, isConst := h.AsConst()
	if !isConst || !IsQuotientClassMap(c) {
		return ConstTerm{}, nil, false
	}
	return c, args[0], true
}

// AnalyzeLiftDefinition validates parsed equations against the lift
// shape and decomposes them. Strict, repair-naming errors. resolve is
// the ambient constant registry the quotients recover through.
func AnalyzeLiftDefinition(equations []Prop, defVar VarTerm, resolve func(TermName) ConstTermMeta) (*LiftDefinition, error) {
	if len(equations) != 1 {
		return nil, fmt.Errorf("lift: a function on classes is ONE equation, its arguments the class patterns (got %d equations)", len(equations))
	}
	equation := equations[0]
	if equation.NumHyps() != 0 {
		return nil, fmt.Errorf("lift: the equation must be a hyp-free statement")
	}
	binderList, matrix := DecomposesFORALL(equation.Conclusion())
	binders := make([]VarTerm, 0, binderList.Size())
	for v := range binderList.Iter() {
		binders = append(binders, v)
	}
	l, r, ok := MatchesEQ(matrix)
	if !ok {
		return nil, fmt.Errorf("lift: the equation's matrix must be an equation (⇔ at bool), got %s", PrintTerm(matrix))
	}
	head, argTerms := MatchesApply(l)
	if hv, isVar := head.AsVar(); !isVar || !hv.EqualsVar(defVar) {
		return nil, fmt.Errorf("lift: the left side must apply %s, got %s", defVar.Name(), PrintTerm(l))
	}
	if r.HasFree(defVar) {
		return nil, fmt.Errorf("lift: %s recurs on the right — a function on classes is stated by its value at the classes, nothing recurs", defVar.Name())
	}
	ld := &LiftDefinition{DefVar: defVar, Equation: equation, Binders: binders}
	seen := map[string]bool{}
	classes := 0
	for i, at := range argTerms {
		var arg LiftArg
		if v, isVar := at.AsVar(); isVar {
			arg.Var = v
		} else {
			c, inner, isClass := classPattern(at)
			if !isClass {
				return nil, fmt.Errorf("lift: argument %d is %s — an argument is a plain binder or a class pattern mk(a) of a quotient's class map",
					i, PrintTerm(at))
			}
			v, isVar := inner.AsVar()
			if !isVar {
				return nil, fmt.Errorf("lift: the class pattern %s must be the class of a binder, not of %s", PrintTerm(at), PrintTerm(inner))
			}
			mq, err := RecoverMintedQuotient(c, resolve)
			if err != nil {
				return nil, fmt.Errorf("lift: argument %d: %v", i, err)
			}
			arg = LiftArg{Var: v, Quotient: mq}
			classes++
		}
		if slices.IndexFunc(binders, arg.Var.EqualsVar) < 0 {
			return nil, fmt.Errorf("lift: %s is not ∀-bound by the equation", PrintTerm(arg.Var))
		}
		if seen[string(arg.Var.Name())] {
			return nil, fmt.Errorf("lift: the left side's variables must be distinct; %s repeats", PrintTerm(arg.Var))
		}
		seen[string(arg.Var.Name())] = true
		ld.Args = append(ld.Args, arg)
	}
	if classes == 0 {
		return nil, fmt.Errorf("lift: no argument is a class pattern — this is a direct definition")
	}
	for _, b := range binders {
		if !seen[string(b.Name())] {
			return nil, fmt.Errorf("lift: ∀-bound variable %s is not an argument of %s(…) — every bound variable of a defining equation must appear on the left",
				PrintTerm(b), defVar.Name())
		}
	}
	for _, v := range r.Frees(nil) {
		if !seen[string(v.Name())] {
			return nil, fmt.Errorf("lift: the right side mentions %s, which is not bound by the equation", PrintTerm(v))
		}
	}

	// The value: a class when written as one.
	if c, body, isClass := classPattern(r); isClass {
		mq, err := RecoverMintedQuotient(c, resolve)
		if err != nil {
			return nil, fmt.Errorf("lift: the value: %v", err)
		}
		ld.Codomain, ld.Body = mq, body
	} else {
		ld.Body = r
	}

	ld.Obligation = ld.obligation()
	ld.Property = equation.Conclusion()
	ld.EpsTerm = WrapTerm(defVar).SuchThat(WrapTerm(ld.Property)).Core()
	ld.ExistsStmt = core.MakeProp(Exists(WrapTerm(defVar))(WrapTerm(ld.Property)).Core())
	return ld, nil
}

// obligation builds the respectfulness statement (see the file
// comment): the obligation's binders are the equation's, each class
// binder followed by its primed twin.
func (ld *LiftDefinition) obligation() Prop {
	var binders []VarTerm
	var antecedents []Term
	substs := make([]TermSubst, 0, len(ld.Args))
	for _, a := range ld.Args {
		binders = append(binders, a.Var)
		if a.Quotient == nil {
			continue
		}
		primed := primedVariant(a.Var, ld.Binders)
		binders = append(binders, primed)
		antecedents = append(antecedents, Apply(a.Quotient.Def.Rel, a.Var, primed).Core())
		substs = append(substs, MakeTermSubst(a.Var, primed))
	}
	primedBody := ld.Body.Substitute(substs...)
	var consequent Term
	if ld.Codomain != nil {
		consequent = Apply(ld.Codomain.Def.Rel, ld.Body, primedBody).Core()
	} else {
		consequent = ext.Eq(ld.Body, primedBody)
	}
	antecedent := antecedents[0]
	for _, t := range antecedents[1:] {
		antecedent = WrapTerm(antecedent).And(t).Core()
	}
	body := WrapTerm(antecedent).Imply(consequent).Core()
	for i := len(binders) - 1; i >= 0; i-- {
		body = ForAll(binders[i])(body).Core()
	}
	return core.MakeProp(body)
}

// primedVariant is v's primed twin, primed further while the name is
// taken by another binder.
func primedVariant(v VarTerm, taken []VarTerm) VarTerm {
	name := string(v.Name()) + "'"
	for slices.ContainsFunc(taken, func(b VarTerm) bool { return string(b.Name()) == name }) {
		name += "'"
	}
	return Var(TermName(name), v.Type()).Core().(VarTerm)
}

// MintLiftDefinition performs the kernel mint for an analyzed lift —
// c := εf. P(f) via core.NewConstDef, the recursive shape's payload —
// under the exclusive registration every mint shares. Returns the
// minted const and the characterizing statement P(c), UNPROVED: the
// definition section proves it through _DefineStep's HILBERT branch,
// whose child is the respectfulness obligation.
func MintLiftDefinition(env *ProverEnv, ld *LiftDefinition) (ConstTerm, Prop, error) {
	return MintLiftDefinitionAs(env, ld, ld.DefVar.Name())
}

// MintLiftDefinitionAs is MintLiftDefinition minting under name rather
// than the definiendum variable's own (the stand-in spelling case).
func MintLiftDefinitionAs(env *ProverEnv, ld *LiftDefinition, name TermName) (ConstTerm, Prop, error) {
	c, err := mintDefinedConst(env, name, ld.EpsTerm)
	if err != nil {
		return ConstTerm{}, nil, err
	}
	characterizing := core.MakeProp(ld.Property.Substitute(MakeTermSubst(ld.DefVar, c)))
	return c, characterizing, nil
}

// AnalyzeLiftExistence reads a lift back off its existence obligation
// ∃f. P(f) — the composite's replay entry — refusing by name any
// property that is not one lift equation.
func AnalyzeLiftExistence(exists Prop, resolve func(TermName) ConstTermMeta) (*LiftDefinition, error) {
	if exists == nil || exists.NumHyps() != 0 {
		return nil, fmt.Errorf("lift: the existence obligation must be a hyp-free statement")
	}
	abs := MatchesEXISTS(exists.Conclusion())
	if abs.IsZero() {
		return nil, fmt.Errorf("lift: the existence obligation must be ∃-headed, got %s", PrintTerm(exists.Conclusion()))
	}
	if conjuncts := DecomposesAND(abs.Body()); len(conjuncts) != 1 {
		return nil, fmt.Errorf("lift: one equation, got %d", len(conjuncts))
	}
	equation := core.MakeProp(abs.Body())
	if !IsQuotientLiftEquation(equation, abs.Var()) {
		return nil, fmt.Errorf("lift: no argument is a class pattern")
	}
	return AnalyzeLiftDefinition([]Prop{equation}, abs.Var(), resolve)
}

// IsQuotientLiftConst reports whether c is a lift's constant — a
// Hilbert-shaped definition whose property is one lift equation.
func IsQuotientLiftConst(c ConstTerm, resolve func(TermName) ConstTermMeta) bool {
	if !prop.IsHilbertConstDef(c) {
		return false
	}
	bridge := prop.ExistentialConstDef(c)
	if bridge.IsZero() || bridge.NumHyps() != 1 {
		return false
	}
	_, err := AnalyzeLiftExistence(core.MakeProp(bridge.Hyps()[0]), resolve)
	return err == nil
}

// LiftQuotients lists the quotients a lift reads — its class
// arguments' and its codomain's — each once, in argument order.
func (ld *LiftDefinition) LiftQuotients() []*MintedQuotient {
	var out []*MintedQuotient
	add := func(mq *MintedQuotient) {
		if mq == nil {
			return
		}
		for _, have := range out {
			if have.Meta.Equals(mq.Meta) {
				return
			}
		}
		out = append(out, mq)
	}
	for _, a := range ld.Args {
		add(a.Quotient)
	}
	add(ld.Codomain)
	return out
}

// quotientLaw serves a quotient's Sound or Exact from env.LibraryThms
// under its conventional name, type-instantiated at the quotient's
// instance in the lift.
func quotientLaw(env *ProverEnv, mq *MintedQuotient, k QuotientTheoremKind) (*PropWrapper, error) {
	name := mq.PrincipleName(k)
	if env == nil {
		return nil, fmt.Errorf("lift: no env to resolve %s from", name)
	}
	thm, ok := env.LookupLibraryThm(name)
	if !ok || thm == nil {
		return nil, fmt.Errorf("lift: library theorem %s is not loaded — the quotient's %v entry must serve it (a dep in Go; a session installs it at the quotient's define)",
			name, k)
	}
	stated := mq.Stmt(k)
	if thm.NumHyps() == 0 && thm.Conclusion().AlphaEquals(stated.Conclusion()) {
		return WrapProp(thm), nil
	}
	// A polymorphic quotient's law, served at its type variables,
	// instantiated at this lift's instance.
	served := MatchesFORALL(thm.Conclusion())
	want := MatchesFORALL(stated.Conclusion())
	if thm.NumHyps() != 0 || served.IsZero() || want.IsZero() {
		return nil, fmt.Errorf("lift: %s does not state the quotient's %v", name, k)
	}
	typeSubsts, ok := served.Var().Type().Matches(want.Var().Type(), func(VarType) bool { return true })
	if !ok {
		return nil, fmt.Errorf("lift: %s is stated at %s, not an instance of %s", name, FormatType(served.Var().Type()), FormatType(want.Var().Type()))
	}
	instantiated := WrapProp(core.PropTypeInst(thm, typeSubsts...))
	if !instantiated.Conclusion().AlphaEquals(stated.Conclusion()) {
		return nil, fmt.Errorf("lift: %s instantiates to %s, not the quotient's %v %s",
			name, PrintTerm(instantiated.Conclusion()), k, PrintTerm(stated.Conclusion()))
	}
	return instantiated, nil
}

// representativeVar is the bound variable the choice of a
// representative of a class argument's binder ranges over.
func representativeVar(a LiftArg) VarTerm {
	return Var(TermName("r_"+string(a.Var.Name())), a.Var.Type()).Core().(VarTerm)
}

// CompileLiftExistence derives ⊢ ∃f. P(f) from the proved
// respectfulness obligation — pure kernel derivation (see the file
// comment). respects must state ld.Obligation α-equally; its binders
// are read positionally.
func CompileLiftExistence(env *ProverEnv, ld *LiftDefinition, respects Prop) (Prop, error) {
	if respects == nil || respects.NumHyps() != 0 || !respects.Conclusion().AlphaEquals(ld.Obligation.Conclusion()) {
		return nil, fmt.Errorf("lift: the respectfulness proof must state %s", PrintTerm(ld.Obligation.Conclusion()))
	}
	// The witness: each class argument to a representative by choice.
	lamVars := make([]VarTerm, len(ld.Args))
	valueSubsts := make([]TermSubst, 0, len(ld.Args))
	for i, a := range ld.Args {
		if a.Quotient == nil {
			lamVars[i] = a.Var
			continue
		}
		q := Var(TermName("q_"+string(a.Var.Name())), a.Quotient.QType).Core().(VarTerm)
		lamVars[i] = q
		b := representativeVar(a)
		representative := WrapTerm(b).SuchThat(WrapTerm(ext.Eq(q, a.Quotient.class(b)))).Core()
		valueSubsts = append(valueSubsts, MakeTermSubst(a.Var, representative))
	}
	value := ld.Body.Substitute(valueSubsts...)
	if ld.Codomain != nil {
		value = ld.Codomain.class(value)
	}
	witness := value
	for i := len(lamVars) - 1; i >= 0; i-- {
		witness = Abs(lamVars[i], witness)
	}

	// At the patterns: w(mk a₁, …) β-reduces to the value at the chosen
	// representatives sᵢ := εb. mk(aᵢ) = mk(b).
	patterns := make([]Term, len(ld.Args))
	for i, a := range ld.Args {
		if a.Quotient == nil {
			patterns[i] = a.Var
		} else {
			patterns[i] = a.Quotient.class(a.Var)
		}
	}
	applied := Apply(witness, patterns...)
	betaEq := WrapProp(core.Refl(applied)).RewriteConclRhs(DeepBeta)

	// Each chosen representative is in the argument's class: the
	// choice gives mk(aᵢ) = mk(sᵢ), Exact turns it into R(aᵢ, sᵢ). The
	// respectfulness instantiates at (aᵢ, sᵢ), external binders at
	// themselves, in the obligation's binder order.
	var related []*PropWrapper
	var instantiation []Term
	for _, a := range ld.Args {
		instantiation = append(instantiation, a.Var)
		if a.Quotient == nil {
			continue
		}
		b := representativeVar(a)
		classA := a.Quotient.class(a.Var)
		chooser := Abs(b, ext.Eq(classA, a.Quotient.class(b)))
		chosen := WrapTerm(b).SuchThat(WrapTerm(ext.Eq(classA, a.Quotient.class(b)))).Core()
		existsClass := Exists(b)(ext.Eq(classA, a.Quotient.class(b))).Core()
		witnessed := WrapProp(core.Refl(classA)).DeriveTrans(prop.InstExists(existsClass, a.Var))
		classEq := witnessed.DeriveTrans(prop.SelectExists(chooser))
		exact, err := quotientLaw(env, a.Quotient, QuotientExact)
		if err != nil {
			return nil, err
		}
		related = append(related, exact.ConclForAllInsts(a.Var, chosen).DemoteHyp().DeriveHypFrom(classEq))
		instantiation = append(instantiation, chosen)
	}
	carried := WrapProp(respects).ConclForAllInsts(instantiation...).DemoteHyp()
	antecedent := related[0]
	for _, r := range related[1:] {
		antecedent = prop.ConclAND(antecedent.Conclusion(), r.Conclusion()).DeriveHypFrom(antecedent).DeriveHypFrom(r)
	}
	carried = carried.DeriveHypFrom(antecedent)
	// Back to the stated value: Sound at the codomain's classes, or the
	// bare equation externally.
	var valueEq *PropWrapper
	if ld.Codomain != nil {
		sound, err := quotientLaw(env, ld.Codomain, QuotientSound)
		if err != nil {
			return nil, err
		}
		_, args := MatchesApply(carried.Conclusion())
		if len(args) != 2 {
			return nil, fmt.Errorf("lift: respectfulness carried to %s, not a relation instance", PrintTerm(carried.Conclusion()))
		}
		valueEq = sound.ConclForAllInsts(args[0], args[1]).DemoteHyp().DeriveHypFrom(carried).EqSym()
	} else {
		valueEq = carried.EqSym()
	}
	equation := betaEq.EqTrans(valueEq)
	for i := len(ld.Binders) - 1; i >= 0; i-- {
		equation = equation.ConclForAll(ld.Binders[i])
	}
	return equation.DeriveTrans(prop.InstExists(ld.ExistsStmt.Conclusion(), witness)), nil
}
