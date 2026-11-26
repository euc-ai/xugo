/**
 * File: primitives.go
 *
 * Primitive inference rules to prove theorems.
 * These are the only rules that can be used to establish theorems.
 * All proofs must be built using these rules.
 * The rules are similar to the ones in HOL Light.
 *
 * Every rule reads a Prop input through Prop.kernel() and a Term input
 * through Term.kernel() first, so what a rule checks and what deriveProp
 * stamps is the kernel value an input stands on, never a wrapper's own
 * account of itself.
 *
 * The list of rules are:
 * - Reflexivity Rule
 * - Assumption Rule
 * - Beta-Reduction Rule
 * - Eta-Reduction Rule
 * - Axiom of ε-calculus
 * - Proposition Application Rule
 * - Deduction Rule
 * - Type Instantiation Rule
 * - Term Instantiation Rule
 *
 * The following rules are axiomatic rules for creating axioms and
 * associated const terms and meta types.
 * - Axiom Rule
 * - Constant Definition Rule
 * - Type Definition Rule
 *
 * The following rules can be derived from the primitives above.
 * They are not really primitives, but included here for convenience.
 * - Derivation Transitivity Rule
 * - Equality Transitivity Rule
 * - Equality Symmetry Rule
 */

package core

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/utils"
)

// Reflexivity Rule:
// t --> ⊢ t = t
func Refl(t Term) ThmCert {
	return makeThm(Eq(t, t))
}

// Assumption Rule: Takes a boolean expression t as an assumption and proves it
// t: bool --> t ⊢ t
func Assume(t Term) ThmCert {
	t = t.kernel()
	utils.Assert(isBool(t))
	return makeThm(t, t)
}

// Beta-Reduction Rule: Proves that applying a lambda expression to
// its bound variable is equivalent to its body
// (λx.t)(x) --> ⊢ (λx.t)(x) = t
func Beta(t AppliedTerm) ThmCert {
	abs, ok := t.Fun().AsAbsTerm()
	utils.Assert(ok && abs.Var().Equals(t.Arg()))
	return makeThm(Eq(t, abs.Body()))
}

// Eta-Reduction Rule: Proves that a lambda expression that receives
// parameter x and applies it to function t is equivalent to t itself
// t(x) --> ⊢ λx.(t(x)) = t
// provided x is not free in t
func Eta(t AppliedTerm) ThmCert {
	v, ok := t.arg.AsVar()
	utils.Assert(ok && !t.fun.HasFree(v))
	return makeThm(Eq(Abs(v, t), t.fun))
}

// Axiom of ε-calculus
// For a predicate P, if P(x) is true for some x, then P(εP) is true,
// where εP (Hilbert's ε operator) represents "choose x for which P(x) holds"
// P(x): bool --> P(x) ⊢ P(εP)
func Select(t AppliedTerm) ThmCert {
	utils.Assert(isBool(t))
	hilbert := MakeConstTerm(
		metaHilbert,
		MakeFun(t.fun.Type(), t.arg.Type()))
	return makeThm(apply(t.fun, apply(hilbert, t.fun)), t)
}

// Γ ⊢ f = g
// Δ ⊢ a = b
// -------------------------
// Γ ∪ Δ ⊢ f(a) = g(b)
func PropApply(t0, t1 Prop) Prop {
	t0, t1 = t0.kernel(), t1.kernel()
	f, g, ok0 := MatchesEQ(t0.Conclusion())
	a, b, ok1 := MatchesEQ(t1.Conclusion())
	utils.Assert(ok0 && ok1)

	p := makeStatementFromOrderedHyps(
		Eq(Apply(f, a), Apply(g, b)),
		utils.OrderedSlicesUnion(t0.Hyps(), t1.Hyps(), Term.AlphaEquals, Term.Compare))
	return deriveProp(p, t0, t1)
}

// Γ ⊢ a = b
// -------------------------
// Γ ⊢ f(a) = f(b)
// Special case of PropApply for convenience.
func PropLeftApply(t0 Term, t1 Prop) Prop {
	t0, t1 = t0.kernel(), t1.kernel()
	a, b, ok := MatchesEQ(t1.Conclusion())
	utils.Assert(ok)
	p := makeStatementFromOrderedHyps(Eq(Apply(t0, a), Apply(t0, b)), t1.Hyps())
	return deriveProp(p, t1)
}

// Γ ⊢ f = g
// -------------------------
// Γ ⊢ f(a) = g(a)
// Special case of PropApply for convenience.
func PropRightApply(t0 Prop, t1 Term) Prop {
	t0, t1 = t0.kernel(), t1.kernel()
	f, g, ok := MatchesEQ(t0.Conclusion())
	utils.Assert(ok)
	p := makeStatementFromOrderedHyps(Eq(Apply(f, t1), Apply(g, t1)), t0.Hyps())
	return deriveProp(p, t0)
}

// Γ ⊢ l = r
// ------------------
// Γ ⊢ λx.l = λx.r
// provided x is not free in the hyps
func PropAbs(v VarTerm, t Prop) Prop {
	t = t.kernel()
	l, r, ok := MatchesEQ(t.Conclusion())
	utils.Assert(ok && !t.AnyHyp(utils.Curry(Term.HasFree, v)))
	p := makeStatementFromOrderedHyps(Eq(Abs(v, l), Abs(v, r)), t.Hyps())
	return deriveProp(p, t)
}

// Equality Modus Ponens: Combines an equation and a proposition
// matching its left side to derive the right side
// Γ ⊢ l = r
// Δ ⊢ l
// ------------------
// Γ ∪ Δ ⊢ r
func EqMP(t0, t1 Prop) Prop {
	t0, t1 = t0.kernel(), t1.kernel()
	l, r, ok := MatchesEQ(t0.Conclusion())
	utils.Assert(ok && l.AlphaEquals(t1.Conclusion()))
	p := makeStatementFromOrderedHyps(
		r,
		utils.OrderedSlicesUnion(t0.Hyps(), t1.Hyps(), Term.AlphaEquals, Term.Compare))
	return deriveProp(p, t0, t1)
}

// Deduction Rule: Derives the equivalence of two propositions from their mutual implication
// Γ, r ⊢ l
// Δ, l ⊢ r
// ---------------------
// Γ ∪ Δ ⊢ l = r
func Deduct(t0, t1 Prop) Prop {
	t0, t1 = t0.kernel(), t1.kernel()
	hyps0, hyps1 := t0.Hyps(), t1.Hyps()

	if i, found := slices.BinarySearchFunc(
		hyps0, t1.Conclusion(), Term.Compare); found {
		hyps0 = slices.Delete(hyps0, i, i+1)
	}
	if i, found := slices.BinarySearchFunc(
		hyps1, t0.Conclusion(), Term.Compare); found {
		hyps1 = slices.Delete(hyps1, i, i+1)
	}
	p := makeStatementFromOrderedHyps(
		Eq(t0.Conclusion(), t1.Conclusion()),
		utils.OrderedSlicesUnion(hyps0, hyps1, Term.AlphaEquals, Term.Compare))
	return deriveProp(p, t0, t1)
}

// Type instantiation
func PropTypeInst(t Prop, subst ...TypeSubst) Prop {
	t = t.kernel()
	own := make([]TypeSubst, 0, len(subst))
	for _, s := range subst {
		if k := (TypeSubst{s.VarType, s.HolType.core()}); !uselessTypeSubst(k) {
			own = append(own, k)
		}
	}
	if len(own) == 0 {
		return t
	}
	concl := t.Conclusion().TypeSubstitute(own...)
	hyps := make([]Term, t.NumHyps())
	for i := range t.NumHyps() {
		hyps[i] = t.Hyp(i).TypeSubstitute(own...)
	}
	return deriveProp(makeStatement(concl, hyps), t)
}

func uselessTermSubst(s TermSubst) bool { return s.Term.Equals(s.VarTerm) }

// Term instantiation
func PropTermInst(t Prop, subst ...TermSubst) Prop {
	t = t.kernel()
	subst = slices.DeleteFunc(utils.Clone(kernelTermSubsts(subst)), uselessTermSubst)
	if len(subst) == 0 {
		return t
	}
	concl := t.Conclusion().Substitute(subst...)
	hyps := make([]Term, t.NumHyps())
	for i := range t.NumHyps() {
		hyps[i] = t.Hyp(i).Substitute(subst...)
	}
	return deriveProp(makeStatement(concl, hyps), t)
}

// t: bool --> ⊢ t
func NewAxiom(t Term) ThmCert {
	t = t.kernel()
	utils.Assert(isBool(t))
	s := makeStatementFromOrderedHyps(t, nil)
	return certify(s, assumed(s, AxiomDoor))
}

// t --> ⊢ c = t
// provided t has no free variables and
// no extra type vars in the def term other than the vars in the type of t.
//
// A name is defined once in a process. Defining it again as an α-equal
// term returns the constant the first definition made, with the same
// definition; as any other term it panics, and so does a definition
// under the name of a constant the kernel has of its own or one a type
// definition introduced.
//
// Definitions form no cycle. A constant is made by hand under any name,
// so t may mention a constant named name, or one whose definition leads
// back to name: the definition then panics. A name t mentions that no
// definition has introduced is left as it is, and may be defined later.
func NewConstDef(t Term, name TermName) ConstTerm {
	t = t.kernel()
	utils.Assert(t.AllFree(utils.EmptyPredicate) &&
		slices.EqualFunc(
			t.Type().TypeVars(), t.typeVars(), (VarType).equalsVar))
	definitions.mu.Lock()
	defer definitions.mu.Unlock()
	if defined, ok := definitions.consts[name]; ok && defined.definedAs(t) {
		return MakeConstTerm(defined, defined.absType)
	}
	refuseDefinedConst("NewConstDef", name)
	mentions := mentionsOf(t)
	refuseDefinitionCycle("NewConstDef", mentions, constantNamed(name))
	meta := MakeConstMeta(name, t.Type())
	c := MakeConstTerm(meta, meta.absType)
	meta.def = makeThm(Eq(c, t))
	definitions.consts[name] = meta
	recordDefinition(mentions, constantNamed(name))
	return c
}

// NewTypeDef establishes a new abstract type and its abs/rep const pair.
//
// Input: a statement ⊢ P(_) witnessing that the subset {x | P x} is
// non-empty — a realized certificate, or a PROMISE of one; a plain
// statement is refused (panics). The mint records the statement, and
// the two type-def axioms take their
// provedness from whatever TypeDefExpand is later handed (a proved
// α-equal source yields proved axioms; the recorded promise itself is
// forced only when its recorded source is forced). So a type may be minted at
// package init on the promise that a chapter's entry proves its
// inhabitation, and nothing proved exists until that entry is built.
// Output: a fresh meta type and the abs/rep const terms. The two def
// theorems that characterize the type (⊢ abs(rep a) = a and
// ⊢ P(r) = (rep(abs r) = r)) are NOT returned here — they are produced on
// demand by calling the `TypeDefExpand` method on either const meta.
//
// A type name is defined once in a process, and so is each of the two
// constant names. Defining the type again from an α-equal source under
// the same two constant names returns what the first definition made,
// the source it recorded included; any other definition under a type
// name or a constant name in use panics, the kernel's own types and
// constants among them.
//
// Definitions form no cycle. The predicate P may not mention the type
// or either constant, nor a name whose definition leads back to one of
// them: the definition then panics, as NewConstDef's does.
//
// The rationale for this split: unlike NewConstDef (whose def is a plain
// theorem), the two type-def "defs" are consequences of the input theorem
// P. Encoding that dependency explicitly lets the library model the
// abs/rep axioms as theorems depending on the source theorem.
//
// Each meta records:
//   - `defSource`: the Prop form of the input ⊢ P(_) (for both abs and rep)
//   - `repMeta` (on abs-const) / `absMeta` (on rep-const): pointer to the
//     paired counterpart; these are kept asymmetric so abs↔rep orientation
//     is unambiguous at use sites
func NewTypeDef(
	t Prop,
	metaTypeName TypeName, absConstName, repConstName TermName) (
	MetaType, ConstTerm, ConstTerm) {
	t = t.kernel()
	utils.Assert(t.NumHyps() == 0)
	switch t.(type) {
	case ThmCert, ThmPromise:
	default:
		panic("NewTypeDef: the source ⊢ P(_) must be a certificate or a promise of one, " +
			"never a plain statement — a type minted on an unproved inhabitation would " +
			"make its abs/rep axioms theorems of nothing")
	}

	s, ok := t.Conclusion().(AppliedTerm)
	utils.Assert(ok && s.fun.AllFree(utils.EmptyPredicate))

	definitions.mu.Lock()
	defer definitions.mu.Unlock()
	if defined, ok := definitions.types[metaTypeName]; ok {
		if !defined.definedOn(t, absConstName, repConstName) {
			panic(fmt.Sprintf(
				"NewTypeDef: type %q is already defined — a type is identified by its name and arity, "+
					"so a second definition would be a second pair of axioms about it", metaTypeName))
		}
		return defined.metaType, defined.abs, defined.rep
	}
	refuseDefinedConst("NewTypeDef", absConstName)
	refuseDefinedConst("NewTypeDef", repConstName)
	if absConstName == repConstName {
		panic(fmt.Sprintf("NewTypeDef: %q names both constants of type %q", absConstName, metaTypeName))
	}
	introduced := []_DefinedName{typeNamed(metaTypeName), constantNamed(absConstName), constantNamed(repConstName)}
	mentions := mentionsOf(s.fun)
	refuseDefinitionCycle("NewTypeDef", mentions, introduced...)

	typeVars := s.fun.typeVars()
	arity := len(typeVars)
	metaType := MakeMetaType(metaTypeName, arity)
	absVarType := MakeCompositeType(metaType,
		utils.MapSlice(typeVars, (VarType).core)...)
	repVarType := s.arg.Type()

	absConstMeta := MakeConstMeta(absConstName, MakeFun(repVarType, absVarType))
	absConst := MakeConstTerm(absConstMeta, absConstMeta.absType)
	repConstMeta := MakeConstMeta(repConstName, MakeFun(absVarType, repVarType))
	repConst := MakeConstTerm(repConstMeta, repConstMeta.absType)

	// Record the source as the kernel value — typed as Prop but the concrete
	// value is the certificate or the promise itself, so TypeDefExpand(meta.
	// DefSource()) propagates its provedness to the two axioms — the
	// Deduct-style "Provedness propagates through operators when inputs
	// carry it" pattern.
	source := t
	absConstMeta.defSource = source
	repConstMeta.defSource = source

	// Wire pair pointers asymmetrically.
	absConstMeta.repMeta = repConstMeta
	repConstMeta.absMeta = absConstMeta

	definitions.types[metaTypeName] = _TypeDefinition{metaType: metaType, abs: absConst, rep: repConst}
	definitions.consts[absConstName] = absConstMeta
	definitions.consts[repConstName] = repConstMeta
	recordDefinition(mentions, introduced...)
	return metaType, absConst, repConst
}

// The following inference rules can be derived from the primitives above.
// They are not really primitives, but included here for convenience.

// Derivation Transitivity Rule: Links two propositions to form a derivation chain
// Γ ⊢ l
// Δ, l ⊢ r
// --------------------
// Γ ∪ Δ ⊢ r
// This is equivalent to the shorthand for EqMP(Deduct(t0, t1), t0)
func DeriveTrans(t0, t1 Prop) Prop {
	t0, t1 = t0.kernel(), t1.kernel()
	hyps1 := t1.Hyps()
	if i, found := slices.BinarySearchFunc(
		hyps1, t0.Conclusion(), Term.Compare); found {
		hyps1 = slices.Delete(hyps1, i, i+1)
	}
	p := makeStatementFromOrderedHyps(
		t1.Conclusion(),
		utils.OrderedSlicesUnion(t0.Hyps(), hyps1, Term.AlphaEquals, Term.Compare))
	return deriveProp(p, t0, t1)
}

// Equality Transitivity Rule: Links two equalities to form an equality chain
// Γ ⊢ l = m
// Δ ⊢ m = r
// ---------------------
// Γ ∪ Δ ⊢ l = r
// panic when not matching.
// This is equivalent to the shorthand for EqMP(PropLeftApply("l = ", t1), t0)
func EqTrans(t0, t1 Prop) Prop {
	t0, t1 = t0.kernel(), t1.kernel()
	l0, r0, ok0 := MatchesEQ(t0.Conclusion())
	l1, r1, ok1 := MatchesEQ(t1.Conclusion())
	utils.Assert(ok0 && ok1 && l1.AlphaEquals(r0))
	p := makeStatementFromOrderedHyps(
		Eq(l0, r1),
		utils.OrderedSlicesUnion(t0.Hyps(), t1.Hyps(), Term.AlphaEquals, Term.Compare))
	return deriveProp(p, t0, t1)
}

// Equality Symmetry Rule: Swaps the sides of an equality
// Γ ⊢ l = r
// -------------
// Γ ⊢ r = l
// panic if not an equality.
// This is equivalent to the shorthand for EqMP(PropRightApply(PropLeftApply("=", t), l), Refl(l))
func EqSym(t Prop) Prop {
	t = t.kernel()
	l, r, ok := MatchesEQ(t.Conclusion())
	utils.Assert(ok)
	p := makeStatementFromOrderedHyps(Eq(r, l), t.Hyps())
	return deriveProp(p, t)
}
