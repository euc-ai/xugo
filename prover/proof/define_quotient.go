// define_quotient.go — the quotient definition move's analysis, mint
// and derivation spine: what the session `define` RPC's `quotient:`
// payload, the chapter door family.DefineQuotient and the
// _DefineQuotientStep composite (step_define.go) share, the way
// define_type.go serves the type-definition move.
//
// A quotient Q = ρ / R is a type definition over the equivalence-class
// shape — the kernel's one type principle, nothing new is trusted —
// with ONE constant on top, the class map, and the interface Lean's
// Quot and Isabelle's quotient_type give:
//
//	typedef    abs : set(ρ) → Q,  rep : Q → set(ρ)
//	           over  λs:set(ρ). ∃x:ρ. s = R(x)      (inhabited by any class)
//	mk         mk : ρ → Q := λx. abs(R(x))          ("the class of x", ⁅x⁆)
//
// and the seven theorems the move comes with, each a PURE KERNEL
// DERIVATION over the two typedef axioms, the class map's definition
// and ONE input the author proves: equivalence(R), the relations
// chapter's structure predicate (reflexive ∧ symmetric ∧ transitive).
//
//	Surjectivity   ∀q:Q. ∃x:ρ. q = mk(x)
//	Induct         ∀P. ∀q. (∀x:ρ. P(mk(x))) ⇒ P(q)     (the standard form, which the induction tactic reads)
//	Sound          ∀x y:ρ. R(x, y) ⇒ mk(x) = mk(y)
//	Exact          ∀x y:ρ. mk(x) = mk(y) ⇒ R(x, y)
//	Eq             ∀x y:ρ. mk(x) = mk(y) ⇔ R(x, y)
//	ForallOnImage  ∀P:(Q → bool). (∀q:Q. P(q)) ⇔ (∀x:ρ. P(mk(x)))
//	ExistsOnImage  ∀P:(Q → bool). (∃q:Q. P(q)) ⇔ (∃x:ρ. P(mk(x)))
//
// Surjectivity, Induct and the two image bridges read nothing but the
// typedef; Exact reads reflexivity, Sound symmetry and transitivity, Eq
// both. The equivalence fact is the composite's one child in every
// section regardless, so that each section cites the same dep and emit
// renders either as the one door call.
//
// The induction principle registers under the conventional name
// `<Q>_induction`, so the `induction` tactic dispatches on a
// quotient-typed goal variable exactly as on a datatype's — the one
// case `∀x:ρ. P(mk(x))` is Lean's Quotient.inductionOn. Sound and Exact
// register under `<Q>_sound` and `<Q>_exact`, which the lift compiler
// (define_lift.go) reads for a function defined on classes.

package proof

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// EquivalenceConstName is the relations chapter's structure predicate
// the quotient move takes its one input in: equivalence(R). The
// chapter's definition reads reflexive(R) ∧ symmetric(R) ∧
// transitive(R), each of those a direct definition the derivations
// unfold by kernel rules — the three constants named below.
const (
	EquivalenceConstName = "equivalence"
	reflexiveConstName   = "reflexive"
	symmetricConstName   = "symmetric"
	transitiveConstName  = "transitive"
)

// QuotientDefinition is the analyzed form of one quotient: the
// relation, its carrier, the typedef the quotient rests on, and the
// equivalence statement the author proves.
type QuotientDefinition struct {
	// Rel is the closed equivalence relation R : ρ → ρ → bool.
	Rel Term
	// Rho is the representative type ρ.
	Rho HolType
	// Pred is the equivalence-class shape λs:(ρ → bool). ∃x:ρ. s = R(x)
	// — the predicate the type is carved out by.
	Pred Term
	// Typedef is Pred's analysis; its inhabitation is trivial.
	Typedef *TypeDefinition
	// Equivalence is `equivalence(R)` — the composite's one child, the
	// author's mathematics.
	Equivalence Prop

	equivalenceConst ConstTerm
}

// AnalyzeQuotientDefinition checks the relation (closed, ρ → ρ → bool,
// not a λ — a defined constant, possibly applied to its parameters),
// builds the class shape and the equivalence statement, and refuses a
// relation whose class shape the normalizer does not see inhabited or
// an `equivalence` constant that is not the relations chapter's.
// resolve is the ambient constant registry (the session env's or the
// manager's).
func AnalyzeQuotientDefinition(rel Term, resolve func(TermName) ConstTermMeta) (*QuotientDefinition, error) {
	if rel == nil {
		return nil, fmt.Errorf("quotient definition: a relation is required")
	}
	if frees := rel.Frees(nil); len(frees) > 0 {
		return nil, fmt.Errorf("quotient definition: the relation must be closed — free %s", PrintTerm(frees[0]))
	}
	if _, isAbs := rel.AsAbsTerm(); isAbs {
		return nil, fmt.Errorf("quotient definition: the relation %s is a λ — define it as a constant first (every statement about the quotient spells the relation by name)",
			PrintTerm(rel))
	}
	spine := MatchesFun(rel.Type())
	if len(spine) != 3 || !spine[0].Equals(spine[1]) || !spine[2].Equals(TypeBool) {
		return nil, fmt.Errorf("quotient definition: the relation must be a binary relation ρ → ρ → bool, got %s : %s",
			PrintTerm(rel), FormatType(rel.Type()))
	}
	rho := spine[0]
	s := Var("s", MakeFun(rho, TypeBool)).Core().(VarTerm)
	x := Var("x", rho).Core().(VarTerm)
	classShape := Exists(x)(ext.Eq(s, Apply(rel, x))).Core()
	pred := Abs(s, classShape)
	td, err := AnalyzeTypeDefinition(pred, nil)
	if err != nil {
		return nil, fmt.Errorf("quotient definition: %v", err)
	}
	if !td.Trivial {
		return nil, fmt.Errorf("quotient definition: the class shape %s is not seen inhabited by normalization — report this shape",
			PrintTerm(td.Exists.Conclusion()))
	}
	if resolve == nil {
		return nil, fmt.Errorf("quotient definition: no constant registry to resolve %s in", EquivalenceConstName)
	}
	eqv, err := equivalenceConstAt(rho, resolve)
	if err != nil {
		return nil, err
	}
	return &QuotientDefinition{
		Rel:              rel,
		Rho:              rho,
		Pred:             pred,
		Typedef:          td,
		Equivalence:      core.MakeProp(Apply(eqv, rel).Core()),
		equivalenceConst: eqv,
	}, nil
}

// equivalenceConstAt resolves the relations chapter's `equivalence`
// at the carrier ρ and checks its definition is the one the
// derivations unfold: λR. reflexive(R) ∧ symmetric(R) ∧ transitive(R),
// each of the three a direct definition over a relation variable.
func equivalenceConstAt(rho HolType, resolve func(TermName) ConstTermMeta) (ConstTerm, error) {
	meta := resolve(TermName(EquivalenceConstName))
	if meta.IsZero() {
		return ConstTerm{}, fmt.Errorf("quotient definition: no constant named %q is registered — the quotient's one input is the relations chapter's equivalence(R); import relations/equivalence",
			EquivalenceConstName)
	}
	relType := MakeFun(rho, MakeFun(rho, TypeBool))
	want := MakeFun(relType, TypeBool)
	substs, ok := meta.AbsType().Matches(want, func(VarType) bool { return true })
	if !ok {
		return ConstTerm{}, fmt.Errorf("quotient definition: the constant %q has type %s, not a predicate on relations",
			EquivalenceConstName, FormatType(meta.AbsType()))
	}
	eqv := MakeConstTerm(meta, meta.AbsType().Substitute(substs...))
	if !eqv.Type().Equals(want) {
		return ConstTerm{}, fmt.Errorf("quotient definition: %q instantiates to %s at %s, not %s",
			EquivalenceConstName, FormatType(eqv.Type()), FormatType(rho), FormatType(want))
	}
	if _, _, _, err := equivalenceLawConsts(eqv); err != nil {
		return ConstTerm{}, err
	}
	return eqv, nil
}

// equivalenceLawConsts reads the three law constants off the
// definition of equivalence at its instance — the shape the
// derivations unfold — and checks each against its own definition.
func equivalenceLawConsts(eqv ConstTerm) (refl, sym, trans ConstTerm, err error) {
	def := getDefThm(eqv)
	if def.IsZero() {
		return ConstTerm{}, ConstTerm{}, ConstTerm{}, fmt.Errorf("quotient definition: %q carries no definition", EquivalenceConstName)
	}
	_, body, ok := MatchesEQ(def.Conclusion())
	if !ok {
		return ConstTerm{}, ConstTerm{}, ConstTerm{}, fmt.Errorf("quotient definition: %q's definition is not an equation", EquivalenceConstName)
	}
	lam, ok := body.AsAbsTerm()
	if !ok {
		return ConstTerm{}, ConstTerm{}, ConstTerm{}, fmt.Errorf("quotient definition: %q is not a direct definition over the relation", EquivalenceConstName)
	}
	conjuncts := DecomposesAND(lam.Body())
	if len(conjuncts) != 3 {
		return ConstTerm{}, ConstTerm{}, ConstTerm{}, fmt.Errorf("quotient definition: %q must read reflexive(R) ∧ symmetric(R) ∧ transitive(R), got %s",
			EquivalenceConstName, PrintTerm(lam.Body()))
	}
	consts := make([]ConstTerm, 3)
	for i, name := range []string{reflexiveConstName, symmetricConstName, transitiveConstName} {
		head, args := MatchesApply(conjuncts[i])
		c, isConst := head.AsConst()
		if !isConst || string(c.Name()) != name || len(args) != 1 || !args[0].AlphaEquals(lam.Var()) {
			return ConstTerm{}, ConstTerm{}, ConstTerm{}, fmt.Errorf("quotient definition: conjunct %d of %q's definition must be %s(R), got %s",
				i+1, EquivalenceConstName, name, PrintTerm(conjuncts[i]))
		}
		if getDefThm(c).IsZero() {
			return ConstTerm{}, ConstTerm{}, ConstTerm{}, fmt.Errorf("quotient definition: %q carries no definition", name)
		}
		consts[i] = c
	}
	return consts[0], consts[1], consts[2], nil
}

// QuotientTheoremKind names one of the seven theorems a quotient
// definition comes with.
type QuotientTheoremKind int

const (
	QuotientSurjectivity QuotientTheoremKind = iota
	QuotientInduct
	QuotientSound
	QuotientExact
	QuotientEq
	QuotientForallOnImage
	QuotientExistsOnImage
)

// QuotientTheoremKinds lists the seven kinds in registration order.
var QuotientTheoremKinds = []QuotientTheoremKind{
	QuotientSurjectivity, QuotientInduct, QuotientSound, QuotientExact, QuotientEq,
	QuotientForallOnImage, QuotientExistsOnImage,
}

func (k QuotientTheoremKind) String() string {
	switch k {
	case QuotientSurjectivity:
		return "Surjectivity"
	case QuotientInduct:
		return "Induct"
	case QuotientSound:
		return "Sound"
	case QuotientExact:
		return "Exact"
	case QuotientEq:
		return "Eq"
	case QuotientForallOnImage:
		return "ForallOnImage"
	case QuotientExistsOnImage:
		return "ExistsOnImage"
	}
	return fmt.Sprintf("QuotientTheoremKind(%d)", int(k))
}

// MintedQuotient is a quotient definition after its mint: the
// analysis, the minted identity and the seven statements.
type MintedQuotient struct {
	Def *QuotientDefinition
	// Meta is the minted type; QType the type at its parameters.
	Meta  core.MetaType
	QType HolType
	// Abs and Rep are the typedef pair, Mk the class map.
	Abs, Rep, Mk ConstTerm

	typedef *MintedTypedef
	stmts   map[QuotientTheoremKind]Prop
}

// Stmt returns the statement of one kind.
func (mq *MintedQuotient) Stmt(k QuotientTheoremKind) Prop { return mq.stmts[k] }

// KindOf reports which of the seven statements goal is, α-equal.
func (mq *MintedQuotient) KindOf(goal Prop) (QuotientTheoremKind, bool) {
	for _, k := range QuotientTheoremKinds {
		if mq.stmts[k].AlphaEquals(goal) {
			return k, true
		}
	}
	return 0, false
}

// PrincipleName is the conventional library name a kind's theorem
// binds in a consumer's env — the induction tactic's `<Q>_induction`,
// the lift compiler's `<Q>_sound` / `<Q>_exact` — and "" for the kinds
// no compiler reads by name.
func (mq *MintedQuotient) PrincipleName(k QuotientTheoremKind) string {
	switch k {
	case QuotientInduct:
		return string(mq.Meta.Name()) + "_induction"
	case QuotientSound:
		return string(mq.Meta.Name()) + "_sound"
	case QuotientExact:
		return string(mq.Meta.Name()) + "_exact"
	}
	return ""
}

// TypeParams lists the minted type's parameters as the parser spells
// them, TypeText the type at them ("free_group(A)").
func (mq *MintedQuotient) TypeParams() []string { return mq.typedef.TypeParams() }
func (mq *MintedQuotient) TypeText() string     { return mq.typedef.TypeText() }

// MintQuotientDefinition mints the type on the trivial inhabitation,
// registers the typedef pair, then mints the class map — all under the
// definition move's EXCLUSIVE discipline (a name already registered
// errors, never shadows), every name checked before anything
// registers.
func MintQuotientDefinition(env *ProverEnv, qd *QuotientDefinition, typeName TypeName, absName, repName, mkName TermName) (*MintedQuotient, error) {
	if env == nil || env.ProofService == nil || env.ProofService.LoadOrStoreConstMeta == nil {
		return nil, fmt.Errorf("define quotient: env carries no const-meta registry")
	}
	if env.ProofService.LoadConstMeta != nil {
		if _, taken := env.ProofService.LoadConstMeta(mkName); taken {
			return nil, fmt.Errorf("define quotient: constant %q is already registered — pick a fresh name for the class map", mkName)
		}
	}
	md, err := MintTypeDefinition(env, qd.Typedef, typeName, absName, repName, qd.Typedef.TrivialSource())
	if err != nil {
		return nil, fmt.Errorf("define quotient: %v", err)
	}
	x := Var("x", qd.Rho).Core().(VarTerm)
	lam := Abs(x, Apply(md.Abs, Apply(qd.Rel, x)).Core())
	mk, err := mintDefinedConst(env, mkName, lam)
	if err != nil {
		return nil, fmt.Errorf("define quotient: %v", err)
	}
	return newMintedQuotient(qd, md, mk), nil
}

func newMintedQuotient(qd *QuotientDefinition, md *MintedTypedef, mk ConstTerm) *MintedQuotient {
	mq := &MintedQuotient{
		Def:     qd,
		Meta:    md.Meta,
		QType:   mkAbsType(md.Abs),
		Abs:     md.Abs,
		Rep:     md.Rep,
		Mk:      mk,
		typedef: md,
		stmts:   map[QuotientTheoremKind]Prop{},
	}
	for _, k := range QuotientTheoremKinds {
		mq.stmts[k] = mq.statement(k)
	}
	return mq
}

// RecoverMintedQuotient reads a quotient back off its class map's
// meta — the composite's replay and emit's rendering both run this, so
// the recorded section and the rendered door call cannot drift. The
// class map's definition λx. abs(R(x)) names the relation and the
// typedef abs, whose meta names the rep and carries the inhabitation.
func RecoverMintedQuotient(mk ConstTerm, resolve func(TermName) ConstTermMeta) (*MintedQuotient, error) {
	if mk.IsZero() {
		return nil, fmt.Errorf("quotient definition: nil class map")
	}
	abs, rel, err := quotientClassMapParts(mk)
	if err != nil {
		return nil, err
	}
	md, err := RecoverMintedTypedef(abs)
	if err != nil {
		return nil, fmt.Errorf("quotient definition: %v", err)
	}
	qd, err := AnalyzeQuotientDefinition(rel, resolve)
	if err != nil {
		return nil, err
	}
	if !qd.Pred.AlphaEquals(md.Def.Pred) {
		return nil, fmt.Errorf("quotient definition: %s is carved out by %s, not the class shape of %s",
			abs.Name(), PrintTerm(md.Def.Pred), PrintTerm(rel))
	}
	return newMintedQuotient(qd, md, mk), nil
}

// quotientClassMapParts reads abs and R off a class map's definition
// mk = λx. abs(R(x)), refusing any other shape by name.
func quotientClassMapParts(mk ConstTerm) (abs ConstTerm, rel Term, err error) {
	def := getDefThm(mk)
	if def.IsZero() {
		return ConstTerm{}, nil, fmt.Errorf("quotient definition: %s carries no definition", mk.Name())
	}
	_, body, ok := MatchesEQ(def.Conclusion())
	if !ok {
		return ConstTerm{}, nil, fmt.Errorf("quotient definition: %s's definition is not an equation", mk.Name())
	}
	lam, ok := body.AsAbsTerm()
	if !ok {
		return ConstTerm{}, nil, fmt.Errorf("quotient definition: %s is not a class map — its definition is not λx. abs(R(x))", mk.Name())
	}
	head, args := MatchesApply(lam.Body())
	absConst, isConst := head.AsConst()
	if !isConst || len(args) != 1 || !absConst.Meta().IsTypeDefAbs() {
		return ConstTerm{}, nil, fmt.Errorf("quotient definition: %s is not a class map — its body %s is not abs(R(x)) for a typedef abs",
			mk.Name(), PrintTerm(lam.Body()))
	}
	relHead, relArgs := MatchesApply(args[0])
	if len(relArgs) != 1 || !relArgs[0].AlphaEquals(lam.Var()) || relHead.HasFree(lam.Var()) {
		return ConstTerm{}, nil, fmt.Errorf("quotient definition: %s is not a class map — abs is applied to %s, not to R(x)",
			mk.Name(), PrintTerm(args[0]))
	}
	return absConst, relHead, nil
}

// IsQuotientClassMap reports whether c is a quotient's class map — the
// constructor pattern the lift compiler reads an equation's argument
// as.
func IsQuotientClassMap(c ConstTerm) bool {
	_, _, err := quotientClassMapParts(c)
	return err == nil
}

// ---------------------------------------------------------------------------
// The statements
// ---------------------------------------------------------------------------

func (mq *MintedQuotient) vars() (q, x, y VarTerm, P VarTerm) {
	q = Var("q", mq.QType).Core().(VarTerm)
	x = Var("x", mq.Def.Rho).Core().(VarTerm)
	y = Var("y", mq.Def.Rho).Core().(VarTerm)
	P = Var("P", MakeFun(mq.QType, TypeBool)).Core().(VarTerm)
	return
}

func (mq *MintedQuotient) class(t Term) Term { return Apply(mq.Mk, t).Core() }

func (mq *MintedQuotient) related(a, b Term) Term { return Apply(mq.Def.Rel, a, b).Core() }

func (mq *MintedQuotient) statement(k QuotientTheoremKind) Prop {
	q, x, y, P := mq.vars()
	switch k {
	case QuotientSurjectivity:
		return core.MakeProp(ForAll(q)(Exists(x)(ext.Eq(q, mq.class(x)))).Core())
	case QuotientInduct:
		case_ := ForAll(x)(Apply(P, mq.class(x))).Core()
		return core.MakeProp(ForAll(P)(ForAll(q)(WrapTerm(case_).Imply(Apply(P, q)))).Core())
	case QuotientSound:
		return core.MakeProp(ForAll(x, y)(WrapTerm(mq.related(x, y)).Imply(ext.Eq(mq.class(x), mq.class(y)))).Core())
	case QuotientExact:
		return core.MakeProp(ForAll(x, y)(WrapTerm(ext.Eq(mq.class(x), mq.class(y))).Imply(mq.related(x, y))).Core())
	case QuotientEq:
		return core.MakeProp(ForAll(x, y)(ext.Eq(ext.Eq(mq.class(x), mq.class(y)), mq.related(x, y))).Core())
	case QuotientForallOnImage:
		lhs := ForAll(q)(Apply(P, q))
		rhs := ForAll(x)(Apply(P, mq.class(x)))
		return core.MakeProp(ForAll(P)(ext.Eq(lhs, rhs)).Core())
	case QuotientExistsOnImage:
		lhs := Exists(q)(Apply(P, q))
		rhs := Exists(x)(Apply(P, mq.class(x)))
		return core.MakeProp(ForAll(P)(ext.Eq(lhs, rhs)).Core())
	}
	panic(fmt.Sprintf("quotient definition: unknown theorem kind %v", k))
}

// ---------------------------------------------------------------------------
// The derivations
// ---------------------------------------------------------------------------

// quotientDeriver bundles the minted quotient with its typedef axioms
// and the class map's equation, read once per derivation.
type quotientDeriver struct {
	mq *MintedQuotient
	// retraction: ⊢ abs(rep a) = a, free a : Q.
	retraction *PropWrapper
	aVar       VarTerm
	// membership: ⊢ (∃x. r = R(x)) ⇔ rep(abs r) = r, free r : set(ρ).
	membership *PropWrapper
	rVar       VarTerm
	// mkDef: ⊢ mk = λx. abs(R(x)).
	mkDef *PropWrapper
	mkLam core.AbsTerm
}

func newQuotientDeriver(mq *MintedQuotient) *quotientDeriver {
	source := mq.Abs.Meta().DefSource()
	Assert(source != nil)
	raw1, raw2 := mq.Abs.Meta().TypeDefExpand(source)
	d := &quotientDeriver{mq: mq, retraction: WrapProp(raw1)}
	frees1 := raw1.Conclusion().Frees(nil)
	Assert(len(frees1) == 1)
	d.aVar = frees1[0]
	d.membership = WrapProp(raw2).Rewrite(DeepBetaAbs(mq.Def.Typedef.PredAbs))
	frees2 := d.membership.Conclusion().Frees(nil)
	Assert(len(frees2) == 1)
	d.rVar = frees2[0]
	def := getDefThm(mq.Mk)
	Assert(!def.IsZero())
	d.mkDef = WrapProp(def)
	_, body, ok := MatchesEQ(def.Conclusion())
	Assert(ok)
	d.mkLam, ok = body.AsAbsTerm()
	Assert(ok)
	return d
}

// mkEq: ⊢ mk(t) = abs(R(t)).
func (d *quotientDeriver) mkEq(t Term) *PropWrapper {
	return d.mkDef.RightApply(t).Rewrite(DeepBetaAbs(d.mkLam))
}

// retractionAt: ⊢ abs(rep q) = q.
func (d *quotientDeriver) retractionAt(q Term) *PropWrapper {
	return d.retraction.TermInst(MakeTermSubst(d.aVar, q))
}

// membershipAt: ⊢ (∃x. s = R(x)) ⇔ rep(abs s) = s.
func (d *quotientDeriver) membershipAt(s Term) *PropWrapper {
	return d.membership.TermInst(MakeTermSubst(d.rVar, s))
}

// classRep: ⊢ rep(mk t) = R(t) — the class of t is R(t): the
// membership at s := R(t), its left side witnessed by t itself.
func (d *quotientDeriver) classRep(t Term) *PropWrapper {
	rt := Apply(d.mq.Def.Rel, t).Core()
	at := d.membershipAt(rt)
	exists, _, ok := core.MatchesEQ(at.Conclusion())
	Assert(ok)
	witnessed := WrapProp(core.Refl(rt)).DeriveTrans(prop.InstExists(exists, t))
	repAbs := at.EqMP(witnessed)
	return d.mkEq(t).LeftApply(d.mq.Rep).EqTrans(repAbs)
}

// surjectivity: ⊢ ∀q. ∃x. q = mk(x).
func (d *quotientDeriver) surjectivity() *PropWrapper {
	q, x, _, _ := d.mq.vars()
	repQ := Apply(d.mq.Rep, q).Core()
	retr := d.retractionAt(q)
	// (∃x. rep q = R(x)) holds: rep(abs(rep q)) = rep q by the retraction.
	exRep := d.membershipAt(repQ).EqSym().EqMP(retr.LeftApply(d.mq.Rep))
	// Under rep q = R(x): q = abs(rep q) = abs(R(x)) = mk(x).
	h := ext.Eq(repQ, Apply(d.mq.Def.Rel, x)).Core()
	qMk := retr.EqSym().EqTrans(prop.Assume(h).LeftApply(d.mq.Abs)).EqTrans(d.mkEq(x).EqSym())
	return qMk.ConclExistsInst(x).HypExists(x, h).DeriveHypFrom(exRep).ConclForAll(q)
}

// induct: ⊢ ∀P. ∀q. (∀x. P(mk(x))) ⇒ P(q). Every class is the class of
// some representative (surjectivity), at which the case holds.
func (d *quotientDeriver) induct(surj *PropWrapper) *PropWrapper {
	q, x, _, P := d.mq.vars()
	case_ := ForAll(x)(Apply(P, d.mq.class(x))).Core()
	atX := prop.Assume(case_).ConclForAllInst(x)
	h := ext.Eq(q, d.mq.class(x)).Core()
	pq := prop.Assume(h).LeftApply(P).EqSym().EqMP(atX)
	return pq.HypExists(x, h).DeriveHypFrom(surj.ConclForAllInst(q)).PromoteHyp(case_).ConclForAll(q).ConclForAll(P)
}

// forallOnImage: ⊢ ∀P. (∀q. P(q)) ⇔ (∀x. P(mk(x))).
func (d *quotientDeriver) forallOnImage(induct *PropWrapper) *PropWrapper {
	q, x, _, P := d.mq.vars()
	allQ := ForAll(q)(Apply(P, q)).Core()
	// ⇒: instantiate at the class.
	fwd := prop.Assume(allQ).ConclForAllInst(d.mq.class(x)).ConclForAll(x)
	// ⇐: the induction principle at P and q, its case assumed,
	// generalized over q.
	bwd := induct.ConclForAllInsts(P, q).DemoteHyp().ConclForAll(q)
	return bwd.Deduct(fwd).ConclForAll(P)
}

// existsOnImage: ⊢ ∀P. (∃q. P(q)) ⇔ (∃x. P(mk(x))).
func (d *quotientDeriver) existsOnImage(surj *PropWrapper) *PropWrapper {
	q, x, _, P := d.mq.vars()
	pq := Apply(P, q).Core()
	pmk := Apply(P, d.mq.class(x)).Core()
	exQ := Exists(q)(pq).Core()
	exX := Exists(x)(pmk).Core()
	// ⇐: the class is a witness.
	bwd := prop.Assume(pmk).DeriveTrans(prop.InstExists(exQ, d.mq.class(x))).HypExists(x, pmk)
	// ⇒: q is some class; P carries over.
	h := ext.Eq(q, d.mq.class(x)).Core()
	atClass := prop.Assume(h).LeftApply(P).EqMP(prop.Assume(pq))
	fwd := atClass.DeriveTrans(prop.InstExists(exX, x)).HypExists(x, h).DeriveHypFrom(surj.ConclForAllInst(q)).HypExists(q, pq)
	return bwd.Deduct(fwd).ConclForAll(P)
}

// laws reads the three laws off the proved equivalence(R): the
// structure's definition unfolded, each conjunct's definition
// unfolded — ∀x. R(x, x); ∀x y. R(x, y) ⇒ R(y, x); ∀x y z. R(x, y) ∧
// R(y, z) ⇒ R(x, z).
func (d *quotientDeriver) laws(equivalence Prop) (refl, sym, trans *PropWrapper) {
	eqv := d.mq.Def.equivalenceConst
	reflC, symC, transC, err := equivalenceLawConsts(eqv)
	if err != nil {
		panic(err)
	}
	rel := d.mq.Def.Rel
	unfold := func(c ConstTerm, fact Prop) *PropWrapper {
		def := WrapProp(getDefThm(c))
		_, body, ok := MatchesEQ(def.Conclusion())
		Assert(ok)
		lam, ok := body.AsAbsTerm()
		Assert(ok)
		return def.RightApply(rel).Rewrite(DeepBetaAbs(lam)).EqMP(fact)
	}
	conj := unfold(eqv, equivalence)
	return unfold(reflC, conjLeaf(conj, 0)), unfold(symC, conjLeaf(conj, 1)), unfold(transC, conjLeaf(conj, 2))
}

// sound: ⊢ ∀x y. R(x, y) ⇒ mk(x) = mk(y). Under R(x, y) the classes
// R(x) and R(y) agree pointwise by symmetry and transitivity, hence as
// functions by extensionality, hence under abs.
func (d *quotientDeriver) sound(sym, trans *PropWrapper) *PropWrapper {
	_, x, y, _ := d.mq.vars()
	z := Var("z", d.mq.Def.Rho).Core().(VarTerm)
	rel := d.mq.related
	rxy, rxz, ryz, ryx := rel(x, y), rel(x, z), rel(y, z), rel(y, x)
	// {R x y} ⊢ R y x
	yx := sym.ConclForAllInsts(x, y).DemoteHyp()
	// {R x y, R x z} ⊢ R y z: transitivity at (y, x, z) through R y x.
	fwd := trans.ConclForAllInsts(y, x, z).DemoteHyp().DeriveHypFrom(prop.ConclAND(ryx, rxz)).DeriveHypFrom(yx)
	// {R x y, R y z} ⊢ R x z: transitivity at (x, y, z).
	bwd := trans.ConclForAllInsts(x, y, z).DemoteHyp().DeriveHypFrom(prop.ConclAND(rxy, ryz))
	pointwise := bwd.Deduct(fwd).ConclForAll(z)
	// λz. R x z = λz. R y z, then η on both sides: R x = R y.
	lamX := Abs(z, rxz)
	lamY := Abs(z, ryz)
	lamEq := prop.FunEq(lamX, lamY).EqSym().EqMP(pointwise)
	etaX := WrapProp(core.Eta(Apply(Apply(d.mq.Def.Rel, x), z)))
	etaY := WrapProp(core.Eta(Apply(Apply(d.mq.Def.Rel, y), z)))
	classes := etaX.EqSym().EqTrans(lamEq).EqTrans(etaY)
	mkEq := d.mkEq(x).EqTrans(classes.LeftApply(d.mq.Abs)).EqTrans(d.mkEq(y).EqSym())
	return mkEq.PromoteHyp(rxy).ConclForAll(y).ConclForAll(x)
}

// exact: ⊢ ∀x y. mk(x) = mk(y) ⇒ R(x, y). Equal classes have equal
// representations R(x) = R(y); at y the right side is R(y, y), which
// reflexivity gives.
func (d *quotientDeriver) exact(refl *PropWrapper) *PropWrapper {
	_, x, y, _ := d.mq.vars()
	h := ext.Eq(d.mq.class(x), d.mq.class(y)).Core()
	reps := d.classRep(x).EqSym().EqTrans(prop.Assume(h).LeftApply(d.mq.Rep)).EqTrans(d.classRep(y))
	atY := reps.RightApply(y)
	rxy := atY.EqSym().EqMP(refl.ConclForAllInst(y))
	return rxy.PromoteHyp(h).ConclForAll(y).ConclForAll(x)
}

// eq: ⊢ ∀x y. mk(x) = mk(y) ⇔ R(x, y), from Sound and Exact.
func (d *quotientDeriver) eq(sound, exact *PropWrapper) *PropWrapper {
	_, x, y, _ := d.mq.vars()
	fromRel := sound.ConclForAllInsts(x, y).DemoteHyp()
	toRel := exact.ConclForAllInsts(x, y).DemoteHyp()
	return fromRel.Deduct(toRel).ConclForAll(y).ConclForAll(x)
}

// Derive derives one theorem from the proved equivalence(R) — pure
// kernel rules over the typedef axioms, the class map's definition and
// the relations chapter's definitions. equivalence must state
// Def.Equivalence (α-equal) and may be a promise; the kinds that read
// no law never force it. The derived theorem is α-checked against the
// statement — a mismatch is kit drift and panics.
func (mq *MintedQuotient) Derive(k QuotientTheoremKind, equivalence Prop) Prop {
	if equivalence == nil || equivalence.NumHyps() != 0 || !equivalence.Conclusion().AlphaEquals(mq.Def.Equivalence.Conclusion()) {
		panic(fmt.Sprintf("quotient definition: the equivalence input must state %s", PrintTerm(mq.Def.Equivalence.Conclusion())))
	}
	d := newQuotientDeriver(mq)
	var out *PropWrapper
	switch k {
	case QuotientSurjectivity:
		out = d.surjectivity()
	case QuotientInduct:
		out = d.induct(d.surjectivity())
	case QuotientForallOnImage:
		out = d.forallOnImage(d.induct(d.surjectivity()))
	case QuotientExistsOnImage:
		out = d.existsOnImage(d.surjectivity())
	case QuotientSound:
		_, sym, trans := d.laws(equivalence)
		out = d.sound(sym, trans)
	case QuotientExact:
		refl, _, _ := d.laws(equivalence)
		out = d.exact(refl)
	case QuotientEq:
		refl, sym, trans := d.laws(equivalence)
		out = d.eq(d.sound(sym, trans), d.exact(refl))
	default:
		panic(fmt.Sprintf("quotient definition: unknown theorem kind %v", k))
	}
	if !out.AlphaEquals(mq.stmts[k]) {
		panic(fmt.Sprintf("quotient definition: derived %v as %s, not the statement %s — kit drift",
			k, PrintProp(out), PrintProp(mq.stmts[k])))
	}
	return out
}

// ParseQuotientRelation reads the relation text at the strict door —
// a closed term, every name resolved, type letters tied — the way the
// typedef door reads its predicate.
func ParseQuotientRelation(text string, base *dsl.ParseScope) (Term, error) {
	scope := dsl.ParseScope{}
	if base != nil {
		scope = *base
	}
	scope.StrictResolution = true
	scope.StrictMint = true
	scope.FreshenMetaLetters = true
	res := dsl.ParseTermTextInScope(text, nil, &scope, nil)
	if len(res.Errors) > 0 {
		return nil, fmt.Errorf("parse relation %q: %s", text, res.Errors[0].Message)
	}
	// The text names no binder, so a constant's type letters come out
	// of the parse at their occurrence-local stand-ins; the quotient's
	// parameters are the letters themselves (free_group(A) over
	// word_equiv's A), read back by name.
	rel, err := dsl.ReadBackMetaLetters(res.Term.Core())
	if err != nil {
		return nil, fmt.Errorf("parse relation %q: %v", text, err)
	}
	return rel, nil
}
