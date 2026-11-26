package bridge

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/reify"
	"github.com/euc-ai/xugo/utils"
)

// Library is what the builder reads. Theorem is a library theorem by
// its registered name, the proof's cite, so the proof's recorded
// dependencies hold it; Constant is a constant of the corpus by name,
// nil for a name it does not know; Arith proves a statement of natural
// number arithmetic, its hypotheses kept as hypotheses, nil where the
// closer does not prove it.
type Library interface {
	Theorem(name string) core.Prop
	Constant(name core.TermName) core.ConstTermMeta
	Arith(goal core.Prop) core.Prop
	// Stating is the corpus entry whose statement is fact, read as
	// Theorem reads it; nil when no entry states it.
	Stating(fact core.Term) core.Prop
}

// The corpus lemmas the builder cites besides the plan's, as
// family.Member.
const (
	lemmaFieldRing          = "field.RingOn"
	lemmaZeroIn             = "comm_ring.ZeroIn"
	lemmaInUniv             = "set_basic.InUniv"
	lemmaSubsetUniv         = "set_order.SubsetUniv"
	lemmaEnvOKDef           = "first_order.EnvOKDef"
	lemmaEnvOKSubset        = "first_order.EnvOKSubset"
	lemmaRingFormulaEvalDef = "ring_formula.RingFormulaEvalDef"
	lemmaRingTruthDef       = "ring_formula.RingFormulaTruthDef"
	lemmaVariableSupport    = "polynomial_formula.PolynomialVariableSupport"
	lemmaCodeSupport        = "polynomial_encoding.PolynomialCodeSupport"
	lemmaDecodeTupleCong    = "polynomial_encoding.DecodeTupleCongruence"
	lemmaDecodeCongruence   = "polynomial_encoding.DecodeCongruence"
	lemmaDecodeFamilyCong   = "polynomial_encoding.DecodePolynomialsCongruence"
)

// Build proves a sentence's bridge, field_on(F) ⊢ Φ ⇔
// ring_formula_truth(F, φ) — ordered_field_on(F, lt) ⊢ Φ ⇔
// ordered_ring_formula_truth(F, lt, φ) in the ordered theory: the formula
// read at the zero environment λv. F.zero. A reification with
// parameters panics, as does a plan node the builder has no proof for.
func Build(in reify.Input, res *reify.Result, lib Library) core.Prop {
	if len(in.Parameters) > 0 {
		panic("bridge: Build proves a sentence's bridge; this reification names parameters")
	}
	b := newBuilder(in, res, lib)
	return b.root().Core()
}

// BuildWithParameters proves the bridge of a formula with parameters at
// a fresh environment ρ, returned beside it: Φ ⇔ ring_formula_eval(F, ρ,
// φ), or the ordered theory's eval, under the structure's obligation,
// fo_env_ok(F.carrier, 𝕌, ρ), each parameter's representation in ρ
// and the parameters' obligations.
func BuildWithParameters(in reify.Input, res *reify.Result, lib Library) (core.Prop, core.VarTerm) {
	b := newBuilder(in, res, lib)
	t, rho := b.parameterized()
	return t.Core(), rho
}

type _Builder struct {
	lib      Library
	in       reify.Input
	res      *reify.Result
	F        core.Term
	ring     core.Term
	carrier  core.Term
	atom     core.Term
	records  prop.Rewrite
	field    *prop.PropWrapper
	commRing *prop.PropWrapper
	// lt and ordered are the order and ordered_field_on(F, lt), in the
	// ordered theory; nil in the ring theory.
	lt      core.Term
	ordered *prop.PropWrapper
	avoid   []core.Term
}

func newBuilder(in reify.Input, res *reify.Result, lib Library) *_Builder {
	b := &_Builder{lib: lib, in: in, res: res, F: in.Structure.Field}
	b.ring = b.call("field_ring", b.F)
	b.carrier = b.call("field_carrier", b.F)
	b.records = b.fieldRingProjections()
	b.avoid = []core.Term{in.Proposition, res.Formula}
	if in.Structure.Ordered() {
		b.lt = in.Structure.Order
		b.atom = b.call("ordered_ring_formula_atom", b.F, b.lt)
		b.ordered = assume(b.call("ordered_field_on", b.F, b.lt))
		b.field = b.use(lemmaOrderedFieldOn, nil, b.F, b.lt)
	} else {
		b.atom = b.call("ring_formula_atom", b.F)
		b.field = assume(b.call("field_on", b.F))
	}
	b.commRing = b.use(lemmaFieldRing, nil, b.F)
	return b
}

// The theory's own lemmas: the evaluation and truth definitions, the
// true formula's, and the comparisons'.
const (
	lemmaOrderedFieldOn      = "ordered_field.FieldOn"
	lemmaOrderedEvalDef      = "ordered_ring_formula.OrderedRingFormulaEvalDef"
	lemmaOrderedTruthDef     = "ordered_ring_formula.OrderedRingFormulaTruthDef"
	lemmaOrderedTrueHolds    = "ordered_ring_formula_combinators.OrderedTrueFormulaHolds"
	lemmaOrderedTrueSupport  = "ordered_ring_formula_combinators.OrderedTrueFormulaSupport"
	lemmaComparisonBridge    = "ordered_ring_formula_combinators.ComparisonBridge"
	lemmaStrictComparison    = "ordered_ring_formula_combinators.StrictComparisonBridge"
	lemmaWeakSupport         = "ordered_ring_formula_combinators.WeakInequalityFormulaSupport"
	lemmaOrderedEqualSupport = "ordered_ring_formula_combinators.OrderedEqualityFormulaSupport"
	lemmaWeakFormulaDef      = "ordered_ring_formula_combinators.LeFormulaDef"
)

// structureArgs is F, and the order after it in the ordered theory: the
// leading witnesses of the theory's lemmas.
func (b *_Builder) structureArgs(rest ...core.Term) []core.Term {
	if b.lt != nil {
		return append([]core.Term{b.F, b.lt}, rest...)
	}
	return append([]core.Term{b.F}, rest...)
}

// evalDef is ⊢ theory_eval(σ, φ) ⇔ fo_eval(F.carrier, e, σ, φ).
func (b *_Builder) evalDef(sigma, phi core.Term) *prop.PropWrapper {
	if b.lt != nil {
		return b.instance(lemmaOrderedEvalDef, b.structureArgs(sigma, phi)...)
	}
	return b.instance(lemmaRingFormulaEvalDef, b.structureArgs(sigma, phi)...)
}

// truthDef is ⊢ theory_truth(φ) ⇔ theory_eval(λv. F.zero, φ).
func (b *_Builder) truthDef(phi core.Term) *prop.PropWrapper {
	if b.lt != nil {
		return b.instance(lemmaOrderedTruthDef, b.structureArgs(phi)...)
	}
	return b.instance(lemmaRingTruthDef, b.structureArgs(phi)...)
}

// call is the corpus constant name applied to the arguments, at the
// type instance the arguments fit.
func (b *_Builder) call(name core.TermName, args ...core.Term) core.Term {
	return constantCall(b.lib, name, args...)
}

// constantCall is the library constant applied to the arguments, its
// type instantiated to fit them.
func constantCall(lib Library, name core.TermName, args ...core.Term) core.Term {
	meta := lib.Constant(name)
	if meta.IsZero() {
		panic(fmt.Sprintf("bridge: the corpus has no constant %s", name))
	}
	abstract := meta.AbsType()
	parts := ext.MatchesFun(abstract)
	if len(parts) <= len(args) {
		panic(fmt.Sprintf("bridge: %s applied to %d arguments", name, len(args)))
	}
	var env []core.TypeSubst
	for i, a := range args {
		if !core.MatchTypeInto(parts[i], a.Type(), utils.FullPredicate, &env) {
			panic(fmt.Sprintf("bridge: %s's argument %d, %s, does not fit %s", name, i, ext.PrintTerm(a), ext.FormatType(parts[i])))
		}
	}
	substs := slices.DeleteFunc(env, func(s core.TypeSubst) bool { return s.HolType.Equals(s.VarType) })
	c := core.MakeConstTerm(meta, abstract.Substitute(substs...))
	if len(args) == 0 {
		return c
	}
	return ext.Apply(c, args...)
}

func (b *_Builder) fresh(name string, t core.HolType) core.VarTerm {
	v := core.Var(name, t).RenameToAvoid(b.avoid...)
	b.avoid = append(b.avoid, v)
	return v
}

// normal is a library instance as the builder reads it: β-normal, and
// each projection of a field's ring read as the field's own
// (field_ring(X).carrier is X.carrier), X itself never read through.
func (b *_Builder) normal(t *prop.PropWrapper) *prop.PropWrapper {
	t = t.RewriteConcl(prop.DeepBeta)
	if b.records != nil {
		t = t.RewriteConcl(b.records)
	}
	return t
}

// instance is the library theorem at the witnesses, in the builder's
// normal form, its antecedents left in place.
func (b *_Builder) instance(name string, witnesses ...core.Term) *prop.PropWrapper {
	return b.normal(instantiate(wrap(b.lib.Theorem(name)), witnesses...))
}

// use is the library theorem at the witnesses with every antecedent
// discharged in the context (nil for none but the structure's).
func (b *_Builder) use(name string, c *_Context, witnesses ...core.Term) *prop.PropWrapper {
	t := b.instance(name, witnesses...)
	for {
		h, _, ok := ext.MatchesIMPLY(t.Conclusion())
		if !ok {
			return t
		}
		t = modusPonens(t, b.prove(h, c, name))
	}
}

// _Context is what a node is proved under: the environment, the facts
// that hold of it — carrier-valued everywhere, the agreement with the
// enclosing environment below the current block — and the binders, each
// with its guard and representation fact, and the index bounds.
type _Context struct {
	sigma   core.Term
	envOK   *prop.PropWrapper
	facts   []*prop.PropWrapper
	binders []*_Binder
	agree   []*_Agreement
}

// _Binder is a binder above a node: its block, the HOL term it stands
// for, and its representation fact at the context's environment.
type _Binder struct {
	block *reify.Block
	value core.Term
	rep   *prop.PropWrapper
}

// _Agreement is ⊢ ∀v. v < s ⇒ τ(v) = σ(v) with its parts.
type _Agreement struct {
	fact     *prop.PropWrapper
	tau, sig core.Term
	start    core.Term
}

func (c *_Context) with(facts ...*prop.PropWrapper) *_Context {
	next := *c
	next.facts = append(slices.Clone(c.facts), facts...)
	return &next
}

func (c *_Context) find(h core.Term) *prop.PropWrapper {
	if c == nil {
		return nil
	}
	for _, f := range slices.Backward(c.facts) {
		if f.Conclusion().AlphaEquals(h) {
			return f
		}
	}
	if c.envOK != nil && c.envOK.Conclusion().AlphaEquals(h) {
		return c.envOK
	}
	for _, bd := range c.binders {
		if bd.rep != nil && bd.rep.Conclusion().AlphaEquals(h) {
			return bd.rep
		}
	}
	return nil
}

// prove proves an antecedent of a lemma instance in the context: a
// fact, a conjunction of provable parts, a membership in the universe,
// a subset of it, the environment carrier-valued on a support or at a
// name, an agreement of two environments on a range, or a statement of
// arithmetic.
func (b *_Builder) prove(h core.Term, c *_Context, lemma string) *prop.PropWrapper {
	for _, f := range []*prop.PropWrapper{b.field, b.commRing, b.ordered} {
		if f != nil && f.Conclusion().AlphaEquals(h) {
			return f
		}
	}
	if f := c.find(h); f != nil {
		return f
	}
	if h.Equals(ext.T) {
		return wrap(prop.DerivesTrue)
	}
	if l, r, ok := ext.MatchesAND(h); ok {
		return conjoin(b.prove(l, c, lemma), b.prove(r, c, lemma))
	}
	head, args := ext.MatchesApply(h)
	name := core.TermName("")
	if k, ok := head.AsConst(); ok {
		name = k.Name()
	}
	switch {
	case name == "set_member" && len(args) == 2 && b.isUniverse(args[1]):
		return b.instance(lemmaInUniv, args[0])
	case name == "subset" && len(args) == 2 && b.isUniverse(args[1]):
		return b.instance(lemmaSubsetUniv, args[0])
	case name == "fo_env_ok" && len(args) == 3 && c != nil && c.envOK != nil:
		return b.envOn(c, args[1], args[2], lemma)
	case name == "set_member" && len(args) == 2 && args[1].AlphaEquals(b.carrier) && c != nil && c.envOK != nil:
		if app, ok := args[0].AsAppliedTerm(); ok && app.Fun().AlphaEquals(c.sigma) {
			return b.valueIn(c, app.Arg())
		}
	}
	if abs := ext.MatchesFORALL(h); !abs.IsZero() && c != nil {
		if t := b.agreementOn(h, c); t != nil {
			return t
		}
	}
	if isArithmetic(h) {
		return b.arith(h, c)
	}
	panic(fmt.Sprintf("bridge: %s needs %s, which the context does not give", lemma, ext.PrintTerm(h)))
}

func (b *_Builder) isUniverse(t core.Term) bool {
	k, ok := t.AsConst()
	return ok && k.Name() == "universe"
}

// envOn is ⊢ fo_env_ok(F.carrier, U, τ) from the context's
// carrier-valued environment τ, U ⊆ 𝕌.
func (b *_Builder) envOn(c *_Context, U, tau core.Term, lemma string) *prop.PropWrapper {
	_, args := ext.MatchesApply(c.envOK.Conclusion())
	if !tau.AlphaEquals(c.sigma) {
		panic(fmt.Sprintf("bridge: %s needs the environment %s carrier-valued; the context's is %s", lemma, ext.PrintTerm(tau), ext.PrintTerm(c.sigma)))
	}
	return b.use(lemmaEnvOKSubset, c, b.carrier, U, args[1], tau)
}

// valueIn is ⊢ σ(v) ∈ F.carrier from the context's carrier-valued σ.
func (b *_Builder) valueIn(c *_Context, v core.Term) *prop.PropWrapper {
	_, args := ext.MatchesApply(c.envOK.Conclusion())
	def := b.instance(lemmaEnvOKDef, b.carrier, args[1], c.sigma)
	everywhere := def.EqMP(c.envOK).ConclForAllInst(v)
	return modusPonens(everywhere, b.instance(lemmaInUniv, v))
}

// agreementOn proves ∀v. lo ≤ v ∧ v < hi ⇒ τ(v) = σ(v) from the
// context's agreement of τ with σ below s, hi ≤ s by arithmetic; nil
// when h is not such a range or no agreement of τ with σ is known.
func (b *_Builder) agreementOn(h core.Term, c *_Context) *prop.PropWrapper {
	abs := ext.MatchesFORALL(h)
	v := abs.Var()
	rng, eq, ok := ext.MatchesIMPLY(abs.Body())
	if !ok {
		return nil
	}
	l, r, ok := core.MatchesEQ(eq)
	if !ok {
		return nil
	}
	la, lok := l.AsAppliedTerm()
	ra, rok := r.AsAppliedTerm()
	if !lok || !rok || !la.Arg().Equals(v) || !ra.Arg().Equals(v) {
		return nil
	}
	for _, a := range c.agree {
		if !a.tau.AlphaEquals(la.Fun()) || !a.sig.AlphaEquals(ra.Fun()) {
			continue
		}
		below := b.arith(b.call("<", v, a.start), c.with(conjunctionPieces(rng)...))
		at := modusPonens(a.fact.ConclForAllInst(v), below)
		return discharge(at, rng).ConclForAll(v)
	}
	return nil
}

func isArithmetic(h core.Term) bool {
	head, args := ext.MatchesApply(h)
	k, ok := head.AsConst()
	if !ok || len(args) != 2 || !args[0].Type().Equals(ext.NumType) {
		return false
	}
	switch k.Name() {
	case "<", "<=", "=":
		return true
	}
	return false
}

// arith proves a statement of arithmetic from the context's arithmetic
// facts and, for an inequality, the products its monomials read of the
// context's index bounds (products).
func (b *_Builder) arith(h core.Term, c *_Context) *prop.PropWrapper {
	var hyps []*prop.PropWrapper
	var bounds []_Bound
	if c != nil {
		for _, f := range c.facts {
			if isArithmetic(f.Conclusion()) {
				hyps = append(hyps, f)
			}
			if bd, ok := boundOf(f.Conclusion()); ok {
				bd.fact = f
				bounds = append(bounds, bd)
			}
		}
	}
	for _, p := range products(b.lib, h, bounds) {
		statement := p.statement(b.lib)
		if !slices.ContainsFunc(hyps, func(f *prop.PropWrapper) bool { return f.Conclusion().AlphaEquals(statement) }) {
			hyps = append(hyps, b.productFact(p))
		}
	}
	return b.closer(h, hyps)
}

// closer proves a statement of arithmetic from the facts by the
// library's closer, the facts' hypotheses in place of their conclusions;
// a statement the closer does not prove is a defect of the plan that
// asked for it.
func (b *_Builder) closer(h core.Term, facts []*prop.PropWrapper) *prop.PropWrapper {
	return derivedArith(b.lib, h, facts)
}

// derivedArith is closer over a library: ⊢ h from the facts, or a panic
// naming h.
func derivedArith(lib Library, h core.Term, facts []*prop.PropWrapper) *prop.PropWrapper {
	terms := make([]core.Term, len(facts))
	for i, f := range facts {
		terms[i] = f.Conclusion()
	}
	proved := lib.Arith(core.MakeProp(h, terms...))
	if proved == nil {
		panic(fmt.Sprintf("bridge: the arithmetic closer does not prove %s from %d facts", ext.PrintTerm(h), len(facts)))
	}
	t := wrap(proved)
	sameConclusion(t, h, "the arithmetic closer")
	for _, f := range facts {
		t = wrap(f.MaybeDeriveTrans(t))
	}
	return t
}

// The ring projections a field's ring answers with the field's own
// part, with the equation that computes each on the constructor.
var ringProjections = map[core.TermName]string{
	"ring_carrier": "module_record.RingCarrierDef",
	"ring_zero":    "module_record.RingZeroDef",
	"ring_one":     "module_record.RingOneDef",
	"ring_add":     "module_record.RingAddDef",
	"ring_mul":     "module_record.RingMulDef",
	"ring_neg":     "module_record.RingNegDef",
	"ring_sub":     "module_record.RingSubDef",
}

const (
	lemmaFieldRingDef    = "field.FieldRingDef"
	lemmaRestrictRingDef = "module_record.RestrictRingDef"
)

// fieldRingProjections rewrites ring_p(field_ring(X)) to X's own part,
// and ring_p(restrict_ring(R, T)) to R's part (T for the carrier): the
// ring unfolded to the ring constructor at its parts, and the
// projection computed on the constructor. It reads nothing of X or R,
// so a concrete structure keeps its spelling.
func (b *_Builder) fieldRingProjections() prop.Rewrite { return fieldRingProjections(b.lib) }

// fieldRingProjections reads each projection of a field's ring as the
// field's own, field_ring(X).zero as X.zero, through lib's equations.
func fieldRingProjections(lib Library) prop.Rewrite {
	return prop.DeepRewrite(func(t core.Term) *prop.PropWrapper {
		app, ok := t.AsAppliedTerm()
		if !ok {
			return nil
		}
		k, ok := app.Fun().AsConst()
		if !ok {
			return nil
		}
		lemma, ok := ringProjections[k.Name()]
		if !ok {
			return nil
		}
		head, ringArgs := ext.MatchesApply(app.Arg())
		fr, ok := head.AsConst()
		if !ok {
			return nil
		}
		var unfold *prop.PropWrapper
		switch {
		case fr.Name() == "field_ring" && len(ringArgs) == 1:
			unfold = instantiate(wrap(lib.Theorem(lemmaFieldRingDef)), ringArgs...)
		case fr.Name() == "restrict_ring" && len(ringArgs) == 2:
			unfold = instantiate(wrap(lib.Theorem(lemmaRestrictRingDef)), ringArgs...)
		default:
			return nil
		}
		_, constructor, _ := core.MatchesEQ(unfold.Conclusion())
		_, parts := ext.MatchesApply(constructor)
		at := unary(t, unfold)
		project := instantiate(wrap(lib.Theorem(lemma)), parts...)
		return at.EqTrans(project)
	})
}
