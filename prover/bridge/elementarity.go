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

// The transfer theorems the executor cites, as family.Member.
const (
	lemmaClosedOnDef     = "algebraic_closure.AlgebraicallyClosedFieldOnIff"
	lemmaRingSentence    = "algebraically_closed_field_transfer.SentenceTransfer"
	lemmaOrderedSentence = "real_closed_field_transfer.SentenceTransfer"
	lemmaRealClosedDef   = "real_closed_field.RealClosedField"
	lemmaPrimeFamily     = "lefschetz.PrimeFamilyTransfer"
)

// Mode is how the step reaches its goal: by elementary equivalence with
// a source where the sentence is true, or along an elementary embedding.
type Mode int

const (
	EquivalenceMode Mode = iota
	EmbeddingMode
)

// Theory is the first-order theory the step runs in.
type Theory int

const (
	RealClosedTheory Theory = iota
	AlgebraicallyClosedTheory
)

// Source is what the equivalence mode reads the sentence's truth from: a
// library entry stating the property at a concrete structure, by its
// registered name; or a resident fact giving, for every prime p, an
// algebraically closed field of characteristic p where the property
// holds.
type Source struct {
	Entry  string
	Family core.Prop
}

// Call is one call of the step: the goal, the facts it is proved from (each a
// theorem whose hypotheses the goal's context holds, a conjunction read
// as its conjuncts), its source, and
// the parameters of the fixed-parameter form .At, none in a sentence
// transfer.
type Call struct {
	Goal   core.Term
	Facts  []core.Prop
	Source Source
	Params []core.Term
}

// Outcome is a proved call: the theorem, its hypotheses among the
// facts', and what the executor derived — recorded beside the call, so
// a replay that derives otherwise refuses.
type Outcome struct {
	Theorem core.Prop
	Mode    Mode
	Theory  Theory
}

// Refusal is a call the executor cannot carry out: a goal outside the
// grammar, a structure no fact names, a source of the wrong shape, a
// source whose sentence is another formula. It is the one error the
// executor returns, since the call is the author's.
type Refusal struct{ Detail string }

func (r *Refusal) Error() string { return "ByElementarity: " + r.Detail }

func refuse(format string, args ...any) error {
	return &Refusal{Detail: fmt.Sprintf(format, args...)}
}

// Elementarity carries out a call.
func Elementarity(call Call, vocabulary *reify.Vocabulary, lib Library) (Outcome, error) {
	x := &_Executor{call: call, vocabulary: vocabulary, lib: lib}
	return x.run()
}

type _Executor struct {
	call       Call
	vocabulary *reify.Vocabulary
	lib        Library
	facts      []*prop.PropWrapper
	// bounded is the degree bounds the embedding mode took from
	// membership facts, each discharged by its ∃ at the end
	// (boundFromMembership).
	bounded []_Witness
}

func (x *_Executor) run() (Outcome, error) {
	x.readFacts()
	if x.call.Source.Entry == "" && x.call.Source.Family == nil {
		if len(x.call.Params) > 0 {
			return Outcome{}, refuse("the fixed-parameter form .At transfers from an entry or a family of models by prime; the call names no source")
		}
		t, theory, err := x.embed()
		return Outcome{Theorem: t, Mode: EmbeddingMode, Theory: theory}, err
	}
	target, theory, err := x.structure()
	if err != nil {
		return Outcome{}, err
	}
	switch {
	case x.call.Source.Family != nil:
		if theory != AlgebraicallyClosedTheory {
			return Outcome{}, refuse("a family of models by prime transfers in the theory of algebraically closed fields; the goal's structure is a real closed field")
		}
		if len(x.call.Params) > 0 {
			t, err := x.fixed(target)
			return Outcome{Theorem: t, Mode: EquivalenceMode, Theory: theory}, err
		}
		t, err := x.family(target.F, wrap(x.call.Source.Family), x.call.Goal)
		return Outcome{Theorem: t, Mode: EquivalenceMode, Theory: theory}, err
	case x.call.Source.Entry != "":
		if len(x.call.Params) > 0 {
			t, err := x.fixed(target)
			return Outcome{Theorem: t, Mode: EquivalenceMode, Theory: theory}, err
		}
		t, err := x.entry(target, x.call.Goal)
		return Outcome{Theorem: t, Mode: EquivalenceMode, Theory: theory}, err
	}
	return Outcome{}, refuse("the equivalence mode names its source: an entry, or a family of models by prime")
}

// readFacts reads the call's facts, a conjunction as its conjuncts.
func (x *_Executor) readFacts() {
	for _, f := range x.call.Facts {
		w := wrap(f)
		if _, _, ok := ext.MatchesAND(w.Conclusion()); !ok {
			x.facts = append(x.facts, w)
			continue
		}
		for _, piece := range conjunctionPieces(w.Conclusion()) {
			x.facts = append(x.facts, w.DeriveTrans(piece))
		}
	}
}

// _Structure is a field record and, in the ordered theory, its order.
type _Structure struct {
	F, lt core.Term
}

// structure reads the target structure and the theory off the facts: an
// algebraically_closed_field_on fact makes the ring theory, a
// real_closed_field fact the ordered one; both, or neither, is refused.
func (x *_Executor) structure() (_Structure, Theory, error) {
	var ring, ordered []_Structure
	for _, f := range x.facts {
		head, args := ext.MatchesApply(f.Conclusion())
		c, ok := head.AsConst()
		if !ok {
			continue
		}
		switch {
		case c.Name() == "algebraically_closed_field_on" && len(args) == 1 && freeIn(args[0], x.call.Goal):
			ring = append(ring, _Structure{F: args[0]})
		case c.Name() == "real_closed_field" && len(args) == 2 && freeIn(args[0], x.call.Goal):
			ordered = append(ordered, _Structure{F: args[0], lt: args[1]})
		}
	}
	switch {
	case len(ring) == 1 && len(ordered) == 0:
		return ring[0], AlgebraicallyClosedTheory, nil
	case len(ordered) == 1 && len(ring) == 0:
		return ordered[0], RealClosedTheory, nil
	case len(ring)+len(ordered) == 0:
		return _Structure{}, 0, refuse("no fact names the goal's structure as an algebraically closed or a real closed field")
	}
	return _Structure{}, 0, refuse("the facts name more than one structure of the goal as a closed field")
}

// freeIn tells whether v is a variable free in t.
func freeIn(v, t core.Term) bool {
	x, ok := v.AsVar()
	return ok && t.HasFree(x)
}

func (x *_Executor) fact(h core.Term) *prop.PropWrapper {
	for _, f := range x.facts {
		if f.Conclusion().AlphaEquals(h) {
			return f
		}
	}
	return nil
}

// reify reads a sentence about a structure.
func (x *_Executor) reify(st _Structure, phi core.Term) (reify.Input, *reify.Result, error) {
	in := reify.Input{Structure: reify.Structure{Field: st.F, Order: st.lt}, Proposition: phi, Unfold: DefinitionUnfolder(), Arithmetic: _Arithmetic{x.lib}, Vocabulary: x.vocabulary}
	res, err := reify.Reify(in)
	return in, res, err
}

// sentence is the bridge at a structure with its obligation discharged
// from the structure's closed-field fact — ⊢ Φ ⇔ ring_formula_truth(F, φ),
// or the ordered truth — and the formula's closedness, the given one
// when it was proved already.
func (x *_Executor) sentence(st _Structure, in reify.Input, res *reify.Result, closed *prop.PropWrapper) (*prop.PropWrapper, *prop.PropWrapper) {
	b := newBuilder(in, res, x.lib)
	bridge := b.root()
	if closed == nil {
		closed = b.closed()
	}
	return x.structureFrom(b, st).DeriveTrans(bridge), closed
}

// structureFrom is the builder's structure obligation, field_on(F) or
// ordered_field_on(F, lt), from the closed-field fact; from its
// assumption when the fact is a hypothesis to come.
func (x *_Executor) structureFrom(b *_Builder, st _Structure) *prop.PropWrapper {
	closedOn, lemma := b.call("algebraically_closed_field_on", st.F), lemmaClosedOnDef
	witnesses := []core.Term{st.F}
	if st.lt != nil {
		closedOn, lemma = b.call("real_closed_field", st.F, st.lt), lemmaRealClosedDef
		witnesses = append(witnesses, st.lt)
	}
	def := b.instance(lemma, witnesses...)
	fact := x.fact(closedOn)
	if fact == nil {
		fact = assume(closedOn)
	}
	return def.EqMP(fact).DeriveTrans(prop.HypAND0(conjuncts(def)))
}

func (x *_Executor) closedFact(b *_Builder, st _Structure) *prop.PropWrapper {
	if st.lt != nil {
		return x.fact(b.call("real_closed_field", st.F, st.lt))
	}
	return x.fact(b.call("algebraically_closed_field_on", st.F))
}

// instance is the corpus entry stating that the source structure, a
// concrete one, is a closed field of the goal's theory —
// real_closed_field(S, lt) or algebraically_closed_field_on(S) — where
// no fact names it: the structure's instance, which the call need not
// pass, taken among the facts. Nil when no entry states it.
func (x *_Executor) instance(b *_Builder, S _Structure) *prop.PropWrapper {
	fact := b.call("algebraically_closed_field_on", S.F)
	if S.lt != nil {
		fact = b.call("real_closed_field", S.F, S.lt)
	}
	t := x.lib.Stating(fact)
	if t == nil {
		return nil
	}
	instance := wrap(t)
	x.facts = append(x.facts, instance)
	return instance
}

// family transfers goal, a proposition about F, from source, a family
// of models by prime: the property at each model is the sentence's
// truth there, so every prime characteristic has an algebraically
// closed field where the sentence is true, and the sentence is true in
// F (lefschetz.PrimeFamilyTransfer).
func (x *_Executor) family(F core.Term, source *prop.PropWrapper, goal core.Term) (*prop.PropWrapper, error) {
	p, prime, G, closedG, characteristic, property, ok := familyShape(source.Conclusion())
	if !ok {
		return nil, refuse("the source is not a family of models by prime, ∀p. nat_prime(p) ⇒ ∃G. algebraically_closed_field_on(G) ∧ field_characteristic(G, p) ∧ Φ(G): %s", ext.PrintTerm(source.Conclusion()))
	}
	inT, resT, err := x.reify(_Structure{F: F}, goal)
	if err != nil {
		return nil, err
	}
	inS, resS, err := x.reify(_Structure{F: G}, property)
	if err != nil {
		return nil, err
	}
	if !resS.Formula.AlphaEquals(resT.Formula) {
		return nil, refuse("the family's models and the goal read as two sentences:\n  goal:   %s\n  source: %s", ext.PrintTerm(resT.Formula), ext.PrintTerm(resS.Formula))
	}
	target, closed := x.sentence(_Structure{F: F}, inT, resT, nil)
	model, _ := x.sentence(_Structure{F: G}, inS, resS, closed)
	b := newBuilder(inT, resT, x.lib)
	_ = inS

	// at a prime p, the model the family gives satisfies the sentence
	head := ext.WrapTerm(closedG).And(characteristic).Core()
	body := ext.WrapTerm(head).And(property).Core()
	given := assume(body)
	both := given.DeriveTrans(prop.HypAND0(head, property))
	closedPiece := both.DeriveTrans(prop.HypAND0(closedG, characteristic))
	characteristicPiece := both.DeriveTrans(prop.HypAND1(closedG, characteristic))
	truth := closedPiece.DeriveTrans(model.EqMP(given.DeriveTrans(prop.HypAND1(head, property))))
	_, truthTerm, _ := core.MatchesEQ(model.Conclusion())
	satisfied := ext.Exists(G)(ext.WrapTerm(head).And(truthTerm).Core()).Core()
	witnessed := construct(satisfied, []*prop.PropWrapper{closedPiece, characteristicPiece, truth}).HypExists(G, body)
	atPrime := modusPonens(source.ConclForAllInst(p), assume(prime)).DeriveTrans(witnessed)
	every := atPrime.PromoteHyp(prime).ConclForAll(p)

	closedF := x.fact(b.call("algebraically_closed_field_on", F))
	lemma := instantiate(wrap(b.lib.Theorem(lemmaPrimeFamily)), F, resT.Formula)
	lemma = b.normal(atModels(lemma, G.Type()))
	sentenceTrue := modusPonens(lemma, conjoin(conjoin(closedF, closed), every))
	return target.EqSym().EqMP(sentenceTrue), nil
}

// atModels instantiates the type of a two-host lemma's models, the
// field ∃-bound in its antecedent, at the family's field type.
func atModels(t *prop.PropWrapper, field core.HolType) *prop.PropWrapper {
	h, _, ok := ext.MatchesIMPLY(t.Conclusion())
	if !ok {
		panic("bridge: the family transfer has no antecedent")
	}
	var models core.AbsTerm
	for _, piece := range conjunctionPieces(h) {
		if all := ext.MatchesFORALL(piece.Conclusion()); !all.IsZero() {
			_, exists, _ := ext.MatchesIMPLY(all.Body())
			models = ext.MatchesEXISTS(exists)
		}
	}
	if models.IsZero() {
		panic("bridge: the family transfer's antecedent names no family of models")
	}
	var env []core.TypeSubst
	if !core.MatchTypeInto(models.Var().Type(), field, utils.FullPredicate, &env) {
		panic("bridge: the family's models are not fields of the lemma's kind")
	}
	substs := slices.DeleteFunc(env, func(s core.TypeSubst) bool { return s.HolType.Equals(s.VarType) })
	if len(substs) == 0 {
		return t
	}
	return t.TypeInst(substs...)
}

// familyData reads a family of models with the property's data bound
// ahead of the prime, ∀data. ∀p. nat_prime(p) ⇒ ∃G. … ∧ Φ(G, data), and
// returns the data's binders and Φ(G, data).
func familyData(t core.Term) (ext.VarList, core.Term, bool) {
	var data ext.VarList
	for {
		if _, _, _, _, _, property, ok := familyShape(t); ok {
			return data, property, true
		}
		all := ext.MatchesFORALL(t)
		if all.IsZero() {
			return ext.VarList{}, nil, false
		}
		data.Add(all.Var())
		t = all.Body()
	}
}

// familyShape reads ∀p. nat_prime(p) ⇒ ∃G. algebraically_closed_field_on(G) ∧
// field_characteristic(G, p) ∧ Φ(G).
func familyShape(t core.Term) (p core.VarTerm, prime core.Term, G core.VarTerm, closedG, characteristic, property core.Term, ok bool) {
	outer := ext.MatchesFORALL(t)
	if outer.IsZero() {
		return
	}
	p = outer.Var()
	prime, exists, isImply := ext.MatchesIMPLY(outer.Body())
	if !isImply || !isApplicationOf(prime, "nat_prime") {
		return
	}
	model := ext.MatchesEXISTS(exists)
	if model.IsZero() {
		return
	}
	G = model.Var()
	head, rest, isAnd := ext.MatchesAND(model.Body())
	if !isAnd {
		return
	}
	closedG, characteristic, isAnd = ext.MatchesAND(head)
	if !isAnd || !isApplicationOf(closedG, "algebraically_closed_field_on") || !isApplicationOf(characteristic, "field_characteristic") {
		return
	}
	return p, prime, G, closedG, characteristic, rest, true
}

func isApplicationOf(t core.Term, name core.TermName) bool {
	head, _ := ext.MatchesApply(t)
	c, ok := head.AsConst()
	return ok && c.Name() == name
}

// entry transfers from a library entry stating the property at a
// concrete structure S: the target's sentence is the source's, true in
// S, and closed fields of one theory agree on a closed sentence —
// algebraically closed fields of one characteristic, or any two real
// closed fields.
func (x *_Executor) entry(target _Structure, goal core.Term) (*prop.PropWrapper, error) {
	inT, resT, err := x.reify(target, goal)
	if err != nil {
		return nil, err
	}
	source := wrap(x.lib.Theorem(x.call.Source.Entry))
	instance, S, err := matchSource(source, goal, target)
	if err != nil {
		return nil, err
	}
	inS, resS, err := x.reify(S, instance.Conclusion())
	if err != nil {
		return nil, err
	}
	if !resS.Formula.AlphaEquals(resT.Formula) {
		return nil, refuse("the source and the goal read as two sentences:\n  goal:   %s\n  source: %s", ext.PrintTerm(resT.Formula), ext.PrintTerm(resS.Formula))
	}
	bridge, closed := x.sentence(target, inT, resT, nil)
	b := newBuilder(inT, resT, x.lib)
	closedS := x.closedFact(b, S)
	if closedS == nil {
		closedS = x.instance(b, S)
	}
	if closedS == nil {
		return nil, refuse("no fact names the source structure %s as a closed field of the goal's theory, and no corpus entry states it", ext.PrintTerm(S.F))
	}
	model, _ := x.sentence(S, inS, resS, closed)
	var agree *prop.PropWrapper
	if target.lt != nil {
		transfer := b.normal(instantiate(wrap(b.lib.Theorem(lemmaOrderedSentence)), target.F, target.lt, S.F, S.lt, resT.Formula))
		agree = modusPonens(transfer, conjoin(conjoin(x.closedFact(b, target), closedS), closed))
	} else {
		same := x.fact(b.call("same_characteristic", target.F, S.F))
		if same == nil {
			return nil, refuse("no fact gives same_characteristic(%s, %s)", ext.PrintTerm(target.F), ext.PrintTerm(S.F))
		}
		transfer := b.normal(instantiate(wrap(b.lib.Theorem(lemmaRingSentence)), target.F, S.F, resT.Formula))
		agree = modusPonens(transfer, conjoin(conjoin(conjoin(x.closedFact(b, target), closedS), same), closed))
	}
	truthS := model.EqMP(instance)
	return bridge.EqSym().EqMP(agree.EqSym().EqMP(truthS)), nil
}

// matchSource instantiates the source entry's leading binders so its
// statement is the goal at the source's structure: the goal and the
// source apply one predicate, the arguments where the goal has the
// field and the order are the source's, and every other argument of
// the source is a binder the goal's argument instantiates.
func matchSource(source *prop.PropWrapper, goal core.Term, target _Structure) (*prop.PropWrapper, _Structure, error) {
	list, body := ext.DecomposesFORALL(source.Conclusion())
	gHead, gArgs := ext.MatchesApply(goal)
	sHead, sArgs := ext.MatchesApply(body)
	gc, gok := gHead.AsConst()
	sc, sok := sHead.AsConst()
	if !gok || !sok || gc.Name() != sc.Name() || len(gArgs) != len(sArgs) {
		return nil, _Structure{}, refuse("the source states another property than the goal:\n  goal:   %s\n  source: %s", ext.PrintTerm(goal), ext.PrintTerm(body))
	}
	var S _Structure
	witnesses := map[core.TermName]core.Term{}
	for i, a := range gArgs {
		switch {
		case a.AlphaEquals(target.F):
			S.F = sArgs[i]
			continue
		case target.lt != nil && a.AlphaEquals(target.lt):
			S.lt = sArgs[i]
			continue
		}
		v, isVar := sArgs[i].AsVar()
		if !isVar || !list.Has(v) {
			return nil, _Structure{}, refuse("the source fixes argument %d of the property, %s, where the goal has %s", i, ext.PrintTerm(sArgs[i]), ext.PrintTerm(a))
		}
		witnesses[v.Name()] = a
	}
	if S.F == nil || (target.lt != nil && S.lt == nil) {
		return nil, _Structure{}, refuse("the goal does not apply the property to its structure %s", ext.PrintTerm(target.F))
	}
	var ordered []core.Term
	for v := range list.Iter() {
		w, ok := witnesses[v.Name()]
		if !ok {
			return nil, _Structure{}, refuse("the source's binder %s is not an argument of the property", v.Name())
		}
		ordered = append(ordered, w)
	}
	return instantiate(source, ordered...), S, nil
}
