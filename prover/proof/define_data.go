// define_data.go — the datatype kit's data model: the `data:` payload
// of the definition move.
//
//   - Every datatype T(σ) is carved out of recspace(P), where P — the
//     PAYLOAD type — is the right-nested product over the multiset
//     union of the constructors' external (non-recursive) argument
//     types (bool when there are none). A constructor
//     Cⱼ(e₁,…,r₁,…) encodes as recspace_node(sucʲ(0), payloadⱼ, subtreesⱼ):
//     the j-th index numeral, its external args injected into their
//     payload slots (unused slots filled with εv.⊤), and its
//     recursive args as an family_cons list of recspace subtrees closed by
//     λn.recspace_bottom.
//   - The SHAPE PREDICATE is the rules' impredicative closure —
//     pred = λa. ∀T'. (∀a. rule(a,T') ⇒ T'(a)) ⇒ T'(a) — exactly the
//     form an inductive-definitions package derives, written
//     directly.
//   - The TYPEDEF (core.NewTypeDef) consumes ⊢ pred(witness) — the
//     witness is the first basal constructor's encoding at ε-filled
//     arguments, and its derivation is env-free pure logic — and
//     mints T with its mk_T/dest_T pair. Constructors are direct
//     core.NewConstDef mints over mk∘enc∘dest.
//   - INDUCT / RECURSION / INJ / DISTINCT are then derived from the
//     typedef axioms plus the recspace corpus rows (recspace_recursion,
//     recspace_node_injective, family_cons, suc_not_zero, suc_injective, pair_injective, fst, snd) —
//     deterministic, refuter-free kernel derivation, the equation
//     compiler's discipline (§"The derivations").
//
// The file's first half is the shared data model: the strict-door
// analysis (AnalyzeDataDefinition), the encoding and statement
// builders, the mint (MintDataDefinition — RPC/registration boundary,
// outside the proof tree, like every definition mint), and the
// meta-recovery the composite step replays from
// (RecoverMintedDatatype: the payload on the wire is the minted consts
// alone; everything else lives on their metas). §"The derivations" is
// the second half — the four derived-theorem families, built on the
// model's own encoding and closure builders so a statement and its
// proof cannot drift apart.
//
// v1 shape (the data twin of the primrec v1 ruling): a single
// non-mutual datatype; each constructor argument is either exactly
// T(σ) (recursive) or an external type not mentioning T (no nested or
// function-typed recursion); at least one constructor has no
// recursive argument (the typedef witness — a datatype without one is
// empty and its nonemptiness underivable); type parameters are
// distinct single uppercase letters in ascending order (the kernel's
// type-slot order is the sorted order of the predicate's type
// variables, so ascending spelling makes author order and slot order
// one thing), each used by some constructor.

package proof

import (
	"fmt"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// DataConstructorSpec is one constructor of a `data:` payload as
// spelled by the author: the constructor's name and its argument
// types in text form ("A", "btree(A)").
type DataConstructorSpec struct {
	Name string   `json:"name"`
	Args []string `json:"args"`
}

// DataCtor is one analyzed constructor.
type DataCtor struct {
	Name TermName
	// ArgTypes are the argument types in author order (the recursive
	// ones spelled at the abstract instance T(σ)).
	ArgTypes []HolType
	// IsRec marks the recursive (T-typed) argument positions.
	IsRec []bool
	// PayloadSlot maps each argument position to its payload slot
	// index (-1 for recursive args). External args claim the FIRST
	// unconsumed slot of their type, in argument order.
	PayloadSlot []int
}

// Arity returns the constructor's argument count.
func (c *DataCtor) Arity() int { return len(c.ArgTypes) }

// RecPositions returns the recursive argument positions in order.
func (c *DataCtor) RecPositions() []int {
	var out []int
	for i, r := range c.IsRec {
		if r {
			out = append(out, i)
		}
	}
	return out
}

// DataDefinition is the analyzed form of a `data:` payload — pure
// description, no kernel objects yet.
type DataDefinition struct {
	TypeName TypeName
	// Params in author order — enforced ascending, so this is also the
	// kernel's type-slot order (core.NewTypeDef sorts the predicate's
	// type variables by name).
	Params []VarType
	Ctors  []DataCtor
	// PayloadSlots is the payload tuple's slot list: the multiset
	// union over constructors of their external argument types, each
	// distinct type appearing max-multiplicity times, ordered by first
	// occurrence. Empty means the payload type is bool.
	PayloadSlots []HolType
}

// PayloadType returns the recspace payload type: the right-nested
// product over PayloadSlots, or bool for none.
func (dd *DataDefinition) PayloadType() HolType {
	if len(dd.PayloadSlots) == 0 {
		return TypeBool
	}
	p := dd.PayloadSlots[len(dd.PayloadSlots)-1]
	for i := len(dd.PayloadSlots) - 2; i >= 0; i-- {
		p = MakeProdType(dd.PayloadSlots[i], p)
	}
	return p
}

// AbsTypePattern returns T(σ) — the datatype at its own parameter
// letters.
func (dd *DataDefinition) AbsTypePattern() CompositeType {
	args := make([]HolType, len(dd.Params))
	for i, p := range dd.Params {
		args[i] = p
	}
	return MakeCompositeType(
		MakeMetaType(dd.TypeName, len(dd.Params)), args...)
}

var recspaceMetaType = MakeMetaType("recspace", 1)

// RecspaceType returns recspace(P) — the representation type.
func (dd *DataDefinition) RecspaceType() HolType {
	return MakeCompositeType(recspaceMetaType, dd.PayloadType())
}

// checkTypeNameSpelling validates the new type's name as a spellable
// type identifier: letters/digits/underscores starting with a letter
// or underscore, NOT a single uppercase letter (the DSL parses that as
// a type VARIABLE), and not one of the logic's type names.
func checkTypeNameSpelling(name string) error {
	for i, r := range name {
		ok := r == '_' || (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z') ||
			(i > 0 && r >= '0' && r <= '9')
		if !ok {
			return fmt.Errorf(
				"define data: type name %q is not a plain identifier (letters, digits, "+
					"underscores; no leading digit)", name)
		}
	}
	if len(name) == 1 && name[0] >= 'A' && name[0] <= 'Z' {
		return fmt.Errorf(
			"define data: %q would parse as a type VARIABLE, not a type name — "+
				"use a longer or lowercase name", name)
	}
	switch name {
	case "bool", "fun":
		return fmt.Errorf("define data: %q is a builtin type name — pick a fresh name", name)
	}
	return nil
}

// typeMentionsMeta walks t for any composite node whose meta has the
// given name (any arity).
func typeMentionsMeta(t HolType, name TypeName) bool {
	ct, ok := t.(CompositeType)
	if !ok {
		return false
	}
	if ct.Meta().Name() == name {
		return true
	}
	for i := 0; i < ct.Meta().Arity(); i++ {
		if typeMentionsMeta(ct.SubType(i), name) {
			return true
		}
	}
	return false
}

// AnalyzeDataDefinition validates a `data:` payload against the v1
// shape (see the file comment) and decomposes it. Strict, repair-
// naming errors — a rejection names its repair. lookupConst probes
// constant-name freshness (nil skips the probe — test envs);
// typeInUse, when non-nil, probes the TYPE name against every type any
// registered constant mentions — the guard core.NewTypeDef does not
// provide for a type made by hand: the kernel refuses the name of a
// type a definition introduced and knows no other.
func AnalyzeDataDefinition(
	typeName string, params []string, ctors []DataConstructorSpec,
	lookupConst func(TermName) ConstTermMeta,
	typeInUse func(TypeName) bool,
) (*DataDefinition, error) {
	if typeName == "" {
		return nil, fmt.Errorf("define data: `name` is required")
	}
	if err := checkTypeNameSpelling(typeName); err != nil {
		return nil, err
	}
	if len(ctors) == 0 {
		return nil, fmt.Errorf("define data: at least one constructor is required")
	}

	// Type-name freshness. Type identity is by name and arity, so a
	// definition under the name of a type made by hand SILENTLY gives
	// that type a meaning: every statement that spells it, a card's or
	// the postulate's among them, then says something else. The kernel
	// refuses only the name of a type a definition introduced, so every
	// available probe runs. The text DSL's own alias (set) is refused
	// first: a type minted under it could never be spelled.
	if _, alias := dsl.TypeAliasArity(typeName); alias {
		return nil, fmt.Errorf("define data: %q is the text DSL's spelling of τ → bool, not a name a type may take", typeName)
	}
	for _, half := range []string{"mk_", "dest_"} {
		if lookupConst != nil && !lookupConst(TermName(half+typeName)).IsZero() {
			return nil, fmt.Errorf(
				"define data: type %q already exists (its %s%s constant is registered) — pick a fresh name",
				typeName, half, typeName)
		}
	}
	if typeInUse != nil && typeInUse(TypeName(typeName)) {
		return nil, fmt.Errorf(
			"define data: type name %q is already in use by a registered constant's type — pick a fresh name",
			typeName)
	}

	// Params: distinct single uppercase letters, ascending, so author
	// order IS the kernel's sorted-slot order.
	paramVars := make([]VarType, len(params))
	for i, p := range params {
		if len(p) != 1 || p[0] < 'A' || p[0] > 'Z' {
			return nil, fmt.Errorf(
				"define data: param %q must be a single uppercase type letter (the DSL's type-variable spelling)", p)
		}
		if i > 0 && params[i-1] >= p {
			return nil, fmt.Errorf(
				"define data: params must be distinct and in ascending order (got %q after %q) — "+
					"the kernel's type-slot order is the sorted letter order, so ascending spelling keeps the two identical",
				p, params[i-1])
		}
		paramVars[i] = MakeVarType(p)
	}

	patternArgs := make([]HolType, len(paramVars))
	for i, p := range paramVars {
		patternArgs[i] = p
	}
	absPattern := MakeCompositeType(
		MakeMetaType(TypeName(typeName), len(params)), patternArgs...)

	paramUsed := make([]bool, len(params))
	analyzed := make([]DataCtor, 0, len(ctors))
	hasBasal := false
	for _, spec := range ctors {
		if spec.Name == "" {
			return nil, fmt.Errorf("define data: every constructor needs a name")
		}
		for i, r := range spec.Name {
			ok := r == '_' || (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z') ||
				(i > 0 && r >= '0' && r <= '9')
			if !ok {
				return nil, fmt.Errorf(
					"define data: constructor name %q is not a plain identifier (letters, "+
						"digits, underscores; no leading digit)", spec.Name)
			}
		}
		for _, prev := range analyzed {
			if string(prev.Name) == spec.Name {
				return nil, fmt.Errorf("define data: constructor %q is declared twice", spec.Name)
			}
		}
		if lookupConst != nil && !lookupConst(TermName(spec.Name)).IsZero() {
			return nil, fmt.Errorf(
				"define data: constructor %q already names a constant — pick a fresh name", spec.Name)
		}
		c := DataCtor{Name: TermName(spec.Name)}
		recCount := 0
		for _, argText := range spec.Args {
			t, err := dsl.ParseTypeText(argText)
			if err != nil {
				return nil, fmt.Errorf("define data: constructor %s argument type %q: %v",
					spec.Name, argText, err)
			}
			isRec := t.Equals(absPattern)
			if !isRec && typeMentionsMeta(t, TypeName(typeName)) {
				return nil, fmt.Errorf(
					"define data: constructor %s argument %q mentions %s other than as the bare "+
						"recursive occurrence %s — nested and function-typed recursion are out of the data v1 shape",
					spec.Name, argText, typeName, FormatType(absPattern))
			}
			if !isRec {
				for _, v := range t.TypeVars() {
					idx := slices.IndexFunc(paramVars, func(pv VarType) bool { return v.Equals(pv) })
					if idx < 0 {
						return nil, fmt.Errorf(
							"define data: constructor %s argument %q mentions type variable %s, which is "+
								"not a declared param — add it to `params` or fix the spelling",
							spec.Name, argText, v.Name())
					}
					paramUsed[idx] = true
				}
			} else {
				recCount++
				for i := range paramUsed {
					paramUsed[i] = true
				}
			}
			c.ArgTypes = append(c.ArgTypes, t)
			c.IsRec = append(c.IsRec, isRec)
		}
		if recCount == 0 {
			hasBasal = true
		}
		analyzed = append(analyzed, c)
	}
	if !hasBasal {
		return nil, fmt.Errorf(
			"define data: every constructor of %s has a recursive argument — the type would be "+
				"empty; add a base constructor with no %s-typed arguments", typeName, typeName)
	}
	for i, used := range paramUsed {
		if !used {
			return nil, fmt.Errorf(
				"define data: param %s is not used by any constructor argument — drop it "+
					"(phantom type parameters are out of the data v1 shape)", params[i])
		}
	}

	// Payload slots: multiset union of external argument types, max
	// multiplicity per type, first-occurrence order.
	var slots []HolType
	slotCount := func(t HolType) int {
		n := 0
		for _, s := range slots {
			if s.Equals(t) {
				n++
			}
		}
		return n
	}
	for _, c := range analyzed {
		counts := map[string]int{}
		for i, t := range c.ArgTypes {
			if c.IsRec[i] {
				continue
			}
			key := string(t.Key())
			counts[key]++
			have := slotCount(t)
			if counts[key] > have {
				slots = append(slots, t)
			}
		}
	}

	dd := &DataDefinition{
		TypeName:     TypeName(typeName),
		Params:       paramVars,
		Ctors:        analyzed,
		PayloadSlots: slots,
	}
	// Slot assignment per constructor: first unconsumed slot of the
	// argument's type, in argument order.
	for ci := range dd.Ctors {
		c := &dd.Ctors[ci]
		c.PayloadSlot = make([]int, c.Arity())
		taken := make([]bool, len(slots))
		for i, t := range c.ArgTypes {
			if c.IsRec[i] {
				c.PayloadSlot[i] = -1
				continue
			}
			found := -1
			for si, s := range slots {
				if !taken[si] && s.Equals(t) {
					found = si
					break
				}
			}
			Assert(found >= 0) // by construction of slots
			taken[found] = true
			c.PayloadSlot[i] = found
		}
	}
	return dd, nil
}

// recspaceVocab bundles the recspace-layer constants the encodings
// are built from, at the instances one datatype needs. All fetched
// from the caller's const-meta resolver so the encodings carry the
// registry's own meta identities.
type recspaceVocab struct {
	constr ConstTerm // num → P → (num → R) → R
	bottom ConstTerm // R
	fcons  ConstTerm // R → (num → R) → num → R
	suc    ConstTerm // num → num
	zero   ConstTerm // num
}

func fetchRecspaceVocab(dd *DataDefinition, lookup func(TermName) ConstTermMeta) (*recspaceVocab, error) {
	if lookup == nil {
		return nil, fmt.Errorf("define data: no const-meta resolver — the recspace vocabulary is unreachable")
	}
	get := func(name string) (ConstTermMeta, error) {
		if meta := lookup(TermName(name)); !meta.IsZero() {
			return meta, nil
		}
		return ConstTermMeta{}, fmt.Errorf(
			"define data: constant %q is not registered — the recspace layer (the datatypes/datatype_universe family) must be linked", name)
	}
	constrMeta, err := get("recspace_node")
	if err != nil {
		return nil, err
	}
	bottomMeta, err := get("recspace_bottom")
	if err != nil {
		return nil, err
	}
	fconsMeta, err := get("family_cons")
	if err != nil {
		return nil, err
	}
	sucMeta, err := get("suc")
	if err != nil {
		return nil, err
	}
	zeroMeta, err := get("_0")
	if err != nil {
		return nil, err
	}
	p, r := dd.PayloadType(), dd.RecspaceType()
	numToR := MakeFun(NumType, r)
	return &recspaceVocab{
		constr: MakeConstTerm(constrMeta,
			MakeFun(NumType, MakeFun(p, MakeFun(numToR, r)))),
		bottom: MakeConstTerm(bottomMeta, r),
		fcons: MakeConstTerm(fconsMeta,
			MakeFun(r, MakeFun(numToR, numToR))),
		suc:  MakeConstTerm(sucMeta, MakeFun(NumType, NumType)),
		zero: MakeConstTerm(zeroMeta, NumType),
	}, nil
}

// index returns the j-th constructor index term sucʲ(_0).
func (v *recspaceVocab) index(j int) Term {
	t := Term(v.zero)
	for range j {
		t = Apply(v.suc, t).Core()
	}
	return t
}

// bottomTail returns λn:num. recspace_bottom — the empty subtree function.
func (v *recspaceVocab) bottomTail() Term {
	n := Var("n", NumType)
	return n.To(v.bottom).Core()
}

// payloadTuple builds the payload term for one constructor: the
// right-nested pair over the slot list with the constructor's own
// external arguments at their assigned slots and εv.⊤ everywhere
// else; εv:bool.⊤ for the empty slot list.
func (dd *DataDefinition) payloadTuple(c *DataCtor, args []Term) Term {
	slotTerms := make([]Term, len(dd.PayloadSlots))
	for i, t := range dd.PayloadSlots {
		slotTerms[i] = Var("v", t).SuchThat(T).Core()
	}
	for i, slot := range c.PayloadSlot {
		if slot >= 0 {
			slotTerms[slot] = args[i]
		}
	}
	if len(slotTerms) == 0 {
		return Var("v", TypeBool).SuchThat(T).Core()
	}
	out := slotTerms[len(slotTerms)-1]
	for i := len(slotTerms) - 2; i >= 0; i-- {
		out = makePair(slotTerms[i], out)
	}
	return out
}

// makePair builds (a, b) with the shared comma meta at the operands'
// instance. ConstTerm identity hashes (name, type), so the ext-owned
// meta agrees with the registry's own "," terms.
func makePair(a, b Term) Term {
	comma := MakeConstTerm(ext.CommaConstMeta,
		MakeFun(a.Type(), MakeFun(b.Type(), MakeProdType(a.Type(), b.Type()))))
	return Apply(comma, a, b).Core()
}

// subtreeList builds the family_cons list of the constructor's recursive
// subtrees (already at recspace type), closed by λn.recspace_bottom.
func (v *recspaceVocab) subtreeList(recs []Term) Term {
	out := v.bottomTail()
	for i := len(recs) - 1; i >= 0; i-- {
		out = Apply(v.fcons, recs[i], out).Core()
	}
	return out
}

// encode builds recspace_node(sucʲ(0), payload, subtrees) for constructor j:
// args are the constructor's arguments with the RECURSIVE positions
// already at recspace type (the caller passes dest(aᵢ) or a rep
// variable, per use).
func (dd *DataDefinition) encode(v *recspaceVocab, j int, args []Term) Term {
	c := &dd.Ctors[j]
	Assert(len(args) == c.Arity())
	var recs []Term
	for i := range args {
		if c.IsRec[i] {
			recs = append(recs, args[i])
		}
	}
	return Apply(v.constr, v.index(j), dd.payloadTuple(c, args), v.subtreeList(recs)).Core()
}

// predicateName returns the shape predicate's bound-variable name —
// the type name primed (list', option').
func (dd *DataDefinition) predicateName() TermName {
	return TermName(string(dd.TypeName) + "'")
}

// shapePredicate builds the impredicative shape predicate:
//
//	λa. ∀T'. (∀a. rule(a,T') ⇒ T'(a)) ⇒ T'(a)
//
// (the rules' closure builder lives in §"The derivations" —
// closureTermAt — so statements and derivations share one
// construction).
func (dd *DataDefinition) shapePredicate(v *recspaceVocab) Term {
	r := dd.RecspaceType()
	q := Var(dd.predicateName(), MakeFun(r, TypeBool)).Core().(VarTerm)
	a := Var("a", r).Core().(VarTerm)
	applyQ := func(t Term) Term { return Apply(q, t).Core() }
	body := ForAll(q)(
		WrapTerm(dd.closureTermAt(v, applyQ)).Imply(applyQ(a)))
	return Abs(a, body.Core())
}

// witnessIndex returns the first basal constructor's index (no
// recursive args) — the typedef witness. Analysis guarantees one.
func (dd *DataDefinition) witnessIndex() int {
	for j := range dd.Ctors {
		if len(dd.Ctors[j].RecPositions()) == 0 {
			return j
		}
	}
	panic("unreachable: AnalyzeDataDefinition guarantees a basal constructor")
}

// witnessTerm builds the typedef witness: the first basal
// constructor's encoding at ε-filled arguments.
func (dd *DataDefinition) witnessTerm(v *recspaceVocab) Term {
	j := dd.witnessIndex()
	c := &dd.Ctors[j]
	args := make([]Term, c.Arity())
	for i, t := range c.ArgTypes {
		args[i] = Var("v", t).SuchThat(T).Core()
	}
	return dd.encode(v, j, args)
}

// MintedDatatype is a minted datatype's live identity: the analyzed
// definition plus the kernel objects. Recoverable from the minted
// consts alone (RecoverMintedDatatype) — the composite's replay
// contract.
type MintedDatatype struct {
	Def     *DataDefinition
	Vocab   *recspaceVocab
	Meta    core.MetaType
	AbsType HolType // T(σ)
	Mk      ConstTerm
	Dest    ConstTerm
	Ctors   []ConstTerm
	// Pred is the shape predicate (closed λ over recspace(P)).
	Pred Term
}

// MkName / DestName spell the typedef pair's conventional names.
func MkName(typeName TypeName) TermName {
	return TermName("mk_" + string(typeName))
}
func DestName(typeName TypeName) TermName {
	return TermName("dest_" + string(typeName))
}

// MintDataDefinition performs the kernel mint for an analyzed
// datatype: derive ⊢ pred(witness) (env-free pure logic —
// deriveWitnessNonemptiness), core.NewTypeDef, then one
// core.NewConstDef per constructor (Cⱼ := λargs. mk(encⱼ(ext-args,
// dest(rec-args)))), all under the EXCLUSIVE registration discipline
// of the definition move (a collision errors, never shadows). Names
// are checked before anything registers, so a late collision cannot
// leave a half-minted datatype behind.
func MintDataDefinition(env *ProverEnv, dd *DataDefinition) (*MintedDatatype, error) {
	if env == nil || env.ProofService == nil || env.ProofService.LoadOrStoreConstMeta == nil {
		return nil, fmt.Errorf("define data: env carries no const-meta registry")
	}
	lookup := func(name TermName) ConstTermMeta {
		if env.ProofService.LoadConstMeta == nil {
			return ConstTermMeta{}
		}
		if meta, ok := env.ProofService.LoadConstMeta(name); ok {
			return meta
		}
		return ConstTermMeta{}
	}
	names := []TermName{MkName(dd.TypeName), DestName(dd.TypeName)}
	for _, c := range dd.Ctors {
		names = append(names, c.Name)
	}
	for _, n := range names {
		if !lookup(n).IsZero() {
			return nil, fmt.Errorf(
				"define data: constant %q is already registered — a second mint, or a "+
					"collision with an imported constant; pick a fresh name", n)
		}
	}

	v, err := fetchRecspaceVocab(dd, lookup)
	if err != nil {
		return nil, err
	}
	pred := dd.shapePredicate(v)
	witness := dd.witnessTerm(v)
	nonempty := deriveWitnessNonemptiness(dd, v, pred, witness)

	metaType, mk, dest := core.NewTypeDef(
		nonempty, dd.TypeName, MkName(dd.TypeName), DestName(dd.TypeName))
	if _, existed := env.ProofService.LoadOrStoreConstMeta(mk.Meta()); existed {
		return nil, fmt.Errorf("define data: %q was registered concurrently — pick a fresh name", mk.Name())
	}
	if _, existed := env.ProofService.LoadOrStoreConstMeta(dest.Meta()); existed {
		return nil, fmt.Errorf("define data: %q was registered concurrently — pick a fresh name", dest.Name())
	}

	md := &MintedDatatype{
		Def:     dd,
		Vocab:   v,
		Meta:    metaType,
		AbsType: mkAbsType(mk),
		Mk:      mk,
		Dest:    dest,
		Pred:    pred,
	}
	for j := range dd.Ctors {
		c, err := mintDefinedConst(env, dd.Ctors[j].Name, md.ctorLambda(j))
		if err != nil {
			return nil, err
		}
		md.Ctors = append(md.Ctors, c)
	}
	return md, nil
}

// mkAbsType reads T(σ) off the mk const's type (recspace(P) → T(σ)).
func mkAbsType(mk ConstTerm) HolType {
	fn := mk.Type().(CompositeType)
	return fn.SubType(1)
}

// ctorLambda builds constructor j's definition body:
// λa₀…aₘ. mk(encⱼ(…)) with recursive args passed through dest.
func (md *MintedDatatype) ctorLambda(j int) Term {
	c := &md.Def.Ctors[j]
	argVars := make([]VarTerm, c.Arity())
	encArgs := make([]Term, c.Arity())
	for i, t := range c.ArgTypes {
		av := Var(TermName(fmt.Sprintf("a%d", i)), md.authorArgType(t)).Core().(VarTerm)
		argVars[i] = av
		if c.IsRec[i] {
			encArgs[i] = Apply(md.Dest, av).Core()
		} else {
			encArgs[i] = av
		}
	}
	body := Apply(md.Mk, md.Def.encode(md.Vocab, j, encArgs)).Core()
	for i := len(argVars) - 1; i >= 0; i-- {
		body = Abs(argVars[i], body)
	}
	return body
}

// authorArgType maps an analyzed argument type to the minted world:
// the recursive pattern T(σ) is the same type by structural identity,
// so this is the identity — kept as a seam for clarity.
func (md *MintedDatatype) authorArgType(t HolType) HolType { return t }

// CtorTerm returns constructor j's const at its abs (pattern-letter)
// instance.
func (md *MintedDatatype) CtorTerm(j int) ConstTerm { return md.Ctors[j] }

// ---------------------------------------------------------------------------
// Derived-theorem statements
// ---------------------------------------------------------------------------

// DataTheoremKind names the four derived-theorem families of a data
// definition, in their canonical order.
type DataTheoremKind int

const (
	DataInduct DataTheoremKind = iota
	DataRecursion
	DataInj
	DataDistinct
)

func (k DataTheoremKind) String() string {
	switch k {
	case DataInduct:
		return "induction"
	case DataRecursion:
		return "recursion"
	case DataInj:
		return "injective"
	case DataDistinct:
		return "distinct"
	}
	return fmt.Sprintf("DataTheoremKind(%d)", int(k))
}

// PrincipleName returns the theorem's library name (btree_induction,
// btree_recursion, …) — the induction/recursion
// dispatch convention (tactic.PrincipleNameCandidates /
// RecursionPrincipleNameCandidates).
func (md *MintedDatatype) PrincipleName(k DataTheoremKind) string {
	return string(md.Def.TypeName) + "_" + k.String()
}

// ctorArgVars builds constructor j's author-typed argument variables,
// named a₀… (with the given suffix appended — INJ's primed copy).
func (md *MintedDatatype) ctorArgVars(j int, suffix string) []VarTerm {
	c := &md.Def.Ctors[j]
	out := make([]VarTerm, c.Arity())
	for i, t := range c.ArgTypes {
		out[i] = Var(TermName(fmt.Sprintf("a%d%s", i, suffix)), t).Core().(VarTerm)
	}
	return out
}

// ctorApp builds Cⱼ(args…).
func (md *MintedDatatype) ctorApp(j int, args []VarTerm) Term {
	if len(args) == 0 {
		return md.Ctors[j]
	}
	terms := make([]Term, len(args))
	for i, a := range args {
		terms[i] = a
	}
	return Apply(md.Ctors[j], terms...).Core()
}

// InductStmt builds the induction principle in the standard form every
// member statement is written in — the form the induction tactic reads
// (tactic.AnalyzeInductionPrinciple) and ByInduction cites:
//
//	∀P. ∀x. case₁ ∧ … ∧ caseₙ ⇒ P(x)
//
// one case per constructor, in constructor order along the left
// ∧-spine, caseⱼ being `∀a…. P(r₁) ⇒ … ⇒ P(Cⱼ(a…))` with one premise per
// recursive argument.
func (md *MintedDatatype) InductStmt() Prop {
	P, x := md.inductVars()
	body := WrapTerm(ext.And(md.inductCases(P)...)).Imply(Apply(P, x)).Core()
	return core.MakeProp(ForAll(P)(ForAll(x)(body)).Core())
}

// inductVars is the principle's predicate and index: P : T → bool and
// x : T, the two binders of its prefix.
func (md *MintedDatatype) inductVars() (P, x VarTerm) {
	P = Var("P", MakeFun(md.AbsType, TypeBool)).Core().(VarTerm)
	x = Var("x", md.AbsType).Core().(VarTerm)
	return P, x
}

// inductCases builds the principle's cases at predicate variable P, one
// per constructor in constructor order.
func (md *MintedDatatype) inductCases(P VarTerm) []Term {
	cases := make([]Term, len(md.Def.Ctors))
	for j := range md.Def.Ctors {
		cases[j] = md.inductCase(P, j)
	}
	return cases
}

// inductCase builds constructor j's case at predicate variable P.
func (md *MintedDatatype) inductCase(P VarTerm, j int) Term {
	args := md.ctorArgVars(j, "")
	body := Apply(P, md.ctorApp(j, args)).Core()
	for i := len(args) - 1; i >= 0; i-- {
		if md.Def.Ctors[j].IsRec[i] {
			body = WrapTerm(Apply(P, args[i]).Core()).Imply(body).Core()
		}
	}
	for i := len(args) - 1; i >= 0; i-- {
		body = ForAll(args[i])(body).Core()
	}
	return body
}

// motiveLetter picks the recursion motive's type letter: the first of
// Z, Y, X, … not used as a param.
func (md *MintedDatatype) motiveLetter() VarType {
	for l := 'Z'; l >= 'A'; l-- {
		candidate := MakeVarType(string(l))
		taken := slices.ContainsFunc(md.Def.Params, func(p VarType) bool {
			return candidate.Equals(p)
		})
		if !taken {
			return candidate
		}
	}
	panic("unreachable: 26 letters, fewer params")
}

// recParamVar builds the j-th recursion parameter fⱼ (named Cⱼ' — the
// list_recursion convention): its type takes the constructor's
// arguments at author types, then one motive-typed slot per recursive
// argument.
func (md *MintedDatatype) recParamVar(j int, motive HolType) VarTerm {
	c := &md.Def.Ctors[j]
	t := motive
	for range c.RecPositions() {
		t = MakeFun(motive, t)
	}
	for i := c.Arity() - 1; i >= 0; i-- {
		t = MakeFun(c.ArgTypes[i], t)
	}
	return Var(TermName(string(c.Name)+"'"), t).Core().(VarTerm)
}

// recClause builds constructor j's recursion clause at fn and fⱼ:
//
//	∀a…. fn(Cⱼ(a…)) = fⱼ(a…, fn(r₁), …)
func (md *MintedDatatype) recClause(j int, fn, fj VarTerm) Term {
	args := md.ctorArgVars(j, "")
	rhsArgs := make([]Term, 0, len(args)+2)
	for _, a := range args {
		rhsArgs = append(rhsArgs, a)
	}
	for _, i := range md.Def.Ctors[j].RecPositions() {
		rhsArgs = append(rhsArgs, Apply(fn, args[i]).Core())
	}
	lhs := Apply(fn, md.ctorApp(j, args)).Core()
	var rhs Term = fj
	if len(rhsArgs) > 0 {
		rhs = Apply(fj, rhsArgs...).Core()
	}
	body := WrapTerm(lhs).Eq(rhs).Core()
	for i := len(args) - 1; i >= 0; i-- {
		body = ForAll(args[i])(body).Core()
	}
	return body
}

// RecursionStmt builds the recursion principle in list_recursion's
// arrangement — parameters ∀-bound, one clause per constructor:
//
//	∀f₀…f_{k-1}. ∃fn : T(σ) → Z. clause₀ ∧ … ∧ clause_{k-1}
func (md *MintedDatatype) RecursionStmt() Prop {
	motive := md.motiveLetter()
	fn := Var("fn", MakeFun(md.AbsType, motive)).Core().(VarTerm)
	params := make([]VarTerm, len(md.Def.Ctors))
	var body Term
	for j := range md.Def.Ctors {
		params[j] = md.recParamVar(j, motive)
		clause := md.recClause(j, fn, params[j])
		if body == nil {
			body = clause
		} else {
			body = WrapTerm(body).And(clause).Core()
		}
	}
	out := Exists(fn)(body).Core()
	for j := len(params) - 1; j >= 0; j-- {
		out = ForAll(params[j])(out).Core()
	}
	return core.MakeProp(out)
}

// InjStmt builds the constructors-injective theorem — one ∀-closed ⇔
// per constructor WITH arguments, conjoined:
//
//	∀a… a…'. (Cⱼ(a…) = Cⱼ(a…')) ⇔ (a₀ = a₀' ∧ …)
//
// nil when no constructor has arguments.
func (md *MintedDatatype) InjStmt() Prop {
	var body Term
	for j := range md.Def.Ctors {
		if md.Def.Ctors[j].Arity() == 0 {
			continue
		}
		l := md.ctorArgVars(j, "")
		r := md.ctorArgVars(j, "'")
		var eqs Term
		for i := range l {
			eq := WrapTerm(Term(l[i])).Eq(r[i]).Core()
			if eqs == nil {
				eqs = eq
			} else {
				eqs = WrapTerm(eqs).And(eq).Core()
			}
		}
		clause := WrapTerm(
			WrapTerm(md.ctorApp(j, l)).Eq(md.ctorApp(j, r)).Core()).
			Eq(eqs).Core()
		for i := len(r) - 1; i >= 0; i-- {
			clause = ForAll(r[i])(clause).Core()
		}
		for i := len(l) - 1; i >= 0; i-- {
			clause = ForAll(l[i])(clause).Core()
		}
		if body == nil {
			body = clause
		} else {
			body = WrapTerm(body).And(clause).Core()
		}
	}
	if body == nil {
		return nil
	}
	return core.MakeProp(body)
}

// DistinctStmt builds the constructors-distinct theorem — one
// ∀-closed inequation per constructor pair j < j', conjoined:
//
//	∀a… b…. ¬(Cⱼ(a…) = Cⱼ'(b…))
//
// nil for a single-constructor type.
func (md *MintedDatatype) DistinctStmt() Prop {
	var body Term
	for j := range md.Def.Ctors {
		for j2 := j + 1; j2 < len(md.Def.Ctors); j2++ {
			l := md.ctorArgVars(j, "")
			r := md.ctorArgVars(j2, "'")
			clause := Not(
				WrapTerm(md.ctorApp(j, l)).Eq(md.ctorApp(j2, r)).Core()).Core()
			for i := len(r) - 1; i >= 0; i-- {
				clause = ForAll(r[i])(clause).Core()
			}
			for i := len(l) - 1; i >= 0; i-- {
				clause = ForAll(l[i])(clause).Core()
			}
			if body == nil {
				body = clause
			} else {
				body = WrapTerm(body).And(clause).Core()
			}
		}
	}
	if body == nil {
		return nil
	}
	return core.MakeProp(body)
}

// Stmt returns the statement for one derived-theorem kind (nil when
// the kind is empty for this datatype: INJ with no argumented
// constructor, DISTINCT with one constructor).
func (md *MintedDatatype) Stmt(k DataTheoremKind) Prop {
	switch k {
	case DataInduct:
		return md.InductStmt()
	case DataRecursion:
		return md.RecursionStmt()
	case DataInj:
		return md.InjStmt()
	case DataDistinct:
		return md.DistinctStmt()
	}
	return nil
}

// Kinds returns the datatype's non-empty derived-theorem kinds in
// canonical order.
func (md *MintedDatatype) Kinds() []DataTheoremKind {
	out := []DataTheoremKind{DataInduct, DataRecursion}
	if md.InjStmt() != nil {
		out = append(out, DataInj)
	}
	if md.DistinctStmt() != nil {
		out = append(out, DataDistinct)
	}
	return out
}

// ---------------------------------------------------------------------------
// Recovery from the minted consts (the composite's replay entry)
// ---------------------------------------------------------------------------

// RecoverMintedDatatype rebuilds the MintedDatatype from the minted
// consts alone — the composite step's payload contract: mk plus the
// ordered constructor consts. The definition is read back off the
// metas: T(σ) and the params off mk's type, each constructor's
// argument types and recursive positions off its stored definition
// lambda (a recursive argument is one the body passes through dest).
func RecoverMintedDatatype(mk ConstTerm, ctors []ConstTerm) (*MintedDatatype, error) {
	if mk.IsZero() || len(ctors) == 0 {
		return nil, fmt.Errorf("define data step: empty payload")
	}
	meta := mk.Meta()
	if !meta.IsTypeDefAbs() {
		return nil, fmt.Errorf("define data step: %q is not a typedef abs const", mk.Name())
	}
	absType, ok := mkAbsType(mk).(CompositeType)
	if !ok {
		return nil, fmt.Errorf("define data step: %q's codomain is not a composite type", mk.Name())
	}
	typeName := absType.Meta().Name()
	params := make([]VarType, absType.Meta().Arity())
	for i := range params {
		v, ok := absType.SubType(i).(VarType)
		if !ok {
			return nil, fmt.Errorf(
				"define data step: %q must be recorded at its pattern instance (parameter %d is %s)",
				typeName, i, FormatType(absType.SubType(i)))
		}
		params[i] = v
	}

	dd := &DataDefinition{TypeName: typeName, Params: params}
	for _, c := range ctors {
		lam := ctorDefLambda(c)
		if lam == nil {
			return nil, fmt.Errorf("define data step: constructor %q carries no definition", c.Name())
		}
		ctor := DataCtor{Name: c.Name()}
		body := lam
		for abs, isAbs := body.AsAbsTerm(); isAbs; abs, isAbs = body.AsAbsTerm() {
			t := abs.Var().Type()
			ctor.ArgTypes = append(ctor.ArgTypes, t)
			ctor.IsRec = append(ctor.IsRec, t.Equals(absType))
			body = abs.Body()
		}
		dd.Ctors = append(dd.Ctors, ctor)
	}
	// Payload slots and slot assignment re-derive exactly as at
	// analysis (deterministic in the ctor list).
	var slots []HolType
	slotCount := func(t HolType) int {
		n := 0
		for _, s := range slots {
			if s.Equals(t) {
				n++
			}
		}
		return n
	}
	for ci := range dd.Ctors {
		counts := map[string]int{}
		c := &dd.Ctors[ci]
		for i, t := range c.ArgTypes {
			if c.IsRec[i] {
				continue
			}
			key := string(t.Key())
			counts[key]++
			if counts[key] > slotCount(t) {
				slots = append(slots, t)
			}
		}
	}
	dd.PayloadSlots = slots
	for ci := range dd.Ctors {
		c := &dd.Ctors[ci]
		c.PayloadSlot = make([]int, c.Arity())
		taken := make([]bool, len(slots))
		for i, t := range c.ArgTypes {
			if c.IsRec[i] {
				c.PayloadSlot[i] = -1
				continue
			}
			found := -1
			for si, s := range slots {
				if !taken[si] && s.Equals(t) {
					found = si
					break
				}
			}
			if found < 0 {
				return nil, fmt.Errorf("define data step: constructor %q slot recovery diverged", c.Name)
			}
			taken[found] = true
			c.PayloadSlot[i] = found
		}
	}

	// Rebuild the vocab off the recorded consts' own metas (the
	// encodings inside the ctor defs carry them).
	v, err := recoverVocab(dd, ctors)
	if err != nil {
		return nil, err
	}
	md := &MintedDatatype{
		Def:     dd,
		Vocab:   v,
		Meta:    absType.Meta(),
		AbsType: absType,
		Mk:      mk,
		Dest:    destFromMk(mk),
		Ctors:   ctors,
		Pred:    dd.shapePredicate(v),
	}
	// Consistency tripwire: every recorded ctor def must equal the
	// re-derived encoding lambda — a drifted recording cannot close.
	for j, c := range ctors {
		if !ctorDefLambda(c).AlphaEquals(md.ctorLambda(j)) {
			return nil, fmt.Errorf(
				"define data step: constructor %q's stored definition does not match its "+
					"re-derived encoding — recording and kit have drifted", c.Name())
		}
	}
	// And the recorded pred must be the defSource's own predicate.
	src := meta.DefSource()
	if src == nil {
		return nil, fmt.Errorf("define data step: %q carries no typedef source", mk.Name())
	}
	app, ok := src.Conclusion().(core.AppliedTerm)
	if !ok || !app.Fun().AlphaEquals(md.Pred) {
		return nil, fmt.Errorf(
			"define data step: %q's typedef predicate does not match the re-derived shape "+
				"predicate — recording and kit have drifted", mk.Name())
	}
	return md, nil
}

// destFromMk returns the paired rep const at its abs instance.
func destFromMk(mk ConstTerm) ConstTerm {
	rep := mk.Meta().TypeDefCounterpart()
	return MakeConstTerm(rep, rep.AbsType())
}

// ctorDefLambda reads a constructor's stored definition body (the λ
// of ⊢ c = λ…) off its meta. nil for a def-less const.
func ctorDefLambda(c ConstTerm) Term {
	def := c.DefThm()
	if def.IsZero() {
		return nil
	}
	_, r, ok := MatchesEQ(def.Conclusion())
	if !ok {
		return nil
	}
	return r
}

// recoverVocab rebuilds the recspaceVocab by scanning the constructor
// definitions for the recspace-layer const occurrences (they are
// guaranteed present: every encoding head is recspace_node, every encoding
// carries λn.recspace_bottom, indices carry suc/_0 from the second constructor
// on, family_cons from the first recursive argument on). Metas found this
// way are the exact metas the mint used — no resolver needed at
// replay.
func recoverVocab(dd *DataDefinition, ctors []ConstTerm) (*recspaceVocab, error) {
	metas := map[string]ConstTermMeta{}
	var scan func(t Term)
	scan = func(t Term) {
		if c, ok := t.AsConst(); ok {
			name := string(c.Name())
			if _, seen := metas[name]; !seen {
				metas[name] = c.Meta()
			}
			return
		}
		if app, ok := t.AsAppliedTerm(); ok {
			scan(app.Fun())
			scan(app.Arg())
			return
		}
		if abs, ok := t.AsAbsTerm(); ok {
			scan(abs.Body())
		}
	}
	for _, c := range ctors {
		scan(ctorDefLambda(c))
	}
	lookup := func(name TermName) ConstTermMeta { return metas[string(name)] }
	// suc/_0/family_cons may be absent from a minimal datatype's encodings
	// (single basal constructor); fall back to the shared ext metas,
	// which agree by (name, type) identity.
	if _, ok := metas["suc"]; !ok {
		metas["suc"] = MakeConstMeta("suc", MakeFun(NumType, NumType))
	}
	if _, ok := metas["_0"]; !ok {
		metas["_0"] = ext.ZeroMeta
	}
	if _, ok := metas["family_cons"]; !ok {
		metas["family_cons"] = MakeConstMeta("family_cons",
			MakeFun(MakeVarType("A"),
				MakeFun(MakeFun(NumType, MakeVarType("A")),
					MakeFun(NumType, MakeVarType("A")))))
	}
	return fetchRecspaceVocab(dd, lookup)
}

// TypeNameInUseProbe builds AnalyzeDataDefinition's typeInUse probe
// from a const-meta enumeration: a type name is IN USE when any
// registered constant's type mentions a composite meta of that name.
// The logic's alphabet (bool and the function arrow) is always in use. rangeMetas yields every registered meta; nil disables the probe.
func TypeNameInUseProbe(rangeMetas func(yield func(ConstTermMeta) bool)) func(TypeName) bool {
	if rangeMetas == nil {
		return nil
	}
	return func(name TypeName) bool {
		switch strings.TrimSpace(string(name)) {
		case "bool", "fun":
			return true
		}
		found := false
		rangeMetas(func(meta ConstTermMeta) bool {
			if typeMentionsMeta(meta.AbsType(), name) {
				found = true
				return false
			}
			return true
		})
		return found
	}
}

// =======================================================================
// The derivations — witness / INDUCT / RECURSION / INJ / DISTINCT
// =======================================================================
//
// The derivations: the four derived-theorem families of a data
// definition, each a PURE KERNEL DERIVATION over the prop layer —
// deterministic, refuter-free, close-or-fail — the equation
// compiler's discipline (CompileRecursiveExistence) extended to the
// recspace pipeline.
//
// Raw material (env.LibraryThms rows, resolved by name exactly as the
// recursion schemas are): recspace_recursion, recspace_node_injective, family_cons, suc_not_zero,
// suc_injective, and — for multi-slot payloads — pair_injective / fst / snd. The
// typedef's two axioms come off the minted metas (TypeDefExpand,
// provedness carried from the live NewTypeDef source), and INDUCT plus
// the typedef witness need no library rows at all: they are pure logic
// over the impredicative shape predicate.
//
// Derivation map:
//
//	witness    ⊢ pred(witness)               — the closure hypothesis
//	           instantiated at the witness, the basal rule disjunct
//	           introduced by reflexivity, ∃/∨-intro chains.
//	INDUCT     hyps ⊢ P(x): instantiate pred(dest x) at the predicate
//	           λr. pred r ∧ P(mk r), prove that predicate rule-closed
//	           from the goal's own case hypotheses (the per-case
//	           ∃/∧-elimination + the constructor unfolds), project.
//	RECURSION  instantiate recspace_recursion at the family_cons case-selector of
//	           per-constructor case functions; the witness λx.fn(dest x)
//	           satisfies each clause by the constructor unfold, the
//	           typedef bijections, and family_cons/fst/snd computation.
//	INJ        dest both sides, recspace_node_injective, then payload projection
//	           (pair_injective) and subtree-list application at each index
//	           (family_cons computation) back through mk.
//	DISTINCT   dest both sides, recspace_node_injective's index component, and a
//	           suc_injective/suc_not_zero chain on the two index numerals.

// dataDeriver bundles a minted datatype with its typedef axioms and
// the env whose LibraryThms serve the recspace rows.
type dataDeriver struct {
	md  *MintedDatatype
	env *ProverEnv

	// mkDest: ⊢ mk(dest a) = a, free a : T(σ).
	mkDest *PropWrapper
	aVar   VarTerm
	// predIff: ⊢ pred·r ⇔ (dest(mk r) = r), free r : recspace(P) —
	// the predicate side stays an unreduced application, which is
	// exactly the instantiation handle the derivations want.
	predIff *PropWrapper
	rVar    VarTerm
}

func newDataDeriver(env *ProverEnv, md *MintedDatatype) *dataDeriver {
	src := md.Mk.Meta().DefSource()
	Assert(src != nil)
	out1, out2 := md.Mk.Meta().TypeDefExpand(src)
	d := &dataDeriver{
		md:      md,
		env:     env,
		mkDest:  WrapProp(out1),
		predIff: WrapProp(out2),
	}
	frees1 := out1.Conclusion().Frees(nil)
	Assert(len(frees1) == 1)
	d.aVar = frees1[0]
	frees2 := out2.Conclusion().Frees(nil)
	Assert(len(frees2) == 1)
	d.rVar = frees2[0]
	return d
}

// libRow resolves a named recspace row from the env (LibraryThms plus
// the dynamic overlay), with the repair named.
func (d *dataDeriver) libRow(name string) (*PropWrapper, error) {
	if d.env == nil {
		return nil, fmt.Errorf("define data: no env to resolve %s from", name)
	}
	thm, ok := d.env.LookupLibraryThm(name)
	if !ok || thm == nil {
		return nil, fmt.Errorf(
			"define data: library theorem %s is not loaded — the corpus "+
				"(serve.InductionPrinciples) or the entry's Deps must serve it", name)
	}
	return WrapProp(thm), nil
}

// conjLeaf derives the k-th leaf of w's conclusion read as a FLATTENED
// conjunction, walking the term's actual association rather than
// assuming one. The corpus's arrangement freedom reaches here the same
// way orientIff absorbs orientation: the emitted recspace_node_injective row
// right-associated its three component equations, the one
// left-associates them (the DSL's ∧ is left-associative), and both say
// the same thing.
func conjLeaf(w *PropWrapper, k int) *PropWrapper {
	for {
		l, r, ok := MatchesAND(w.Conclusion())
		if !ok {
			Assert(k == 0)
			return w
		}
		if n := len(DecomposesAND(l)); k < n {
			w = w.DeriveTrans(HypAND0(l, r))
		} else {
			k -= n
			w = w.DeriveTrans(HypAND1(l, r))
		}
	}
}

// stripRow strips a row's leading ∀-binders, freeing them — the
// corpus serves several recspace rows ∀-closed (suc_not_zero, suc_injective,
// pair_injective, fst, snd) where the kit instantiates frees; a row already
// in free-variable form passes through unchanged.
func stripRow(w *PropWrapper) *PropWrapper {
	out, _ := w.StripConclForAll()
	return out
}

// orientIff returns w with its ⇔/=-conclusion oriented so wantLeft
// holds of the left side (EqSym when it holds of the right instead).
// The corpus's arrangement freedom (suc_injective serves (n=m) ⇔ (suc n =
// suc m), fst serves x = fst((x,y))) is absorbed here, so the
// derivations consume one orientation.
func orientIff(w *PropWrapper, wantLeft func(l Term) bool) *PropWrapper {
	l, r, ok := MatchesEQ(w.Conclusion())
	Assert(ok)
	if wantLeft(l) {
		return w
	}
	Assert(wantLeft(r))
	return w.EqSym()
}

// mkDestAt returns ⊢ mk(dest t) = t.
func (d *dataDeriver) mkDestAt(t Term) *PropWrapper {
	return d.mkDest.TermInst(MakeTermSubst(d.aVar, t))
}

// destMkFrom turns ⊢/Γ pred·s into ⊢/Γ dest(mk s) = s.
func (d *dataDeriver) destMkFrom(s Term, predThm *PropWrapper) *PropWrapper {
	return d.predIff.TermInst(MakeTermSubst(d.rVar, s)).EqMP(predThm)
}

// predOfDest returns ⊢ pred·(dest x) for a T-typed term x: instantiate
// the typedef iff at dest x; its right side holds by applying dest to
// mk(dest x) = x.
func (d *dataDeriver) predOfDest(x Term) *PropWrapper {
	destX := Apply(d.md.Dest, x).Core()
	iff := d.predIff.TermInst(MakeTermSubst(d.rVar, destX))
	rhs := d.mkDestAt(x).LeftApply(d.md.Dest)
	return iff.EqSym().EqMP(rhs)
}

// predApp returns the unreduced application pred·t.
func (d *dataDeriver) predApp(t Term) Term {
	return Apply(d.md.Pred, t).Core()
}

// predBetaEq returns ⊢ pred·t = body[t] — the one-step β unfold (the
// predicate body is β-normal, so DeepBeta stops there).
func (d *dataDeriver) predBetaEq(t Term) *PropWrapper {
	eq := DeepBeta(d.predApp(t))
	Assert(eq != nil)
	return eq
}

// existsIntroChain introduces target's leading ∃-chain at the given
// witnesses over base (whose conclusion must be the fully substituted
// body).
func existsIntroChain(target Term, wits []Term, base *PropWrapper) *PropWrapper {
	terms := make([]Term, len(wits)+1)
	terms[0] = target
	for i, w := range wits {
		abs := MatchesEXISTS(terms[i])
		Assert(!abs.IsZero())
		terms[i+1] = abs.Body().Substitute(MakeTermSubst(abs.Var(), w))
	}
	Assert(base.Conclusion().AlphaEquals(terms[len(wits)]))
	cur := base
	for i := len(wits) - 1; i >= 0; i-- {
		cur = cur.DeriveTrans(prop.InstExists(terms[i], wits[i]))
	}
	return cur
}

// orIntroAt places a proof of disjuncts[j] into the left-nested
// disjunction over disjuncts.
func orIntroAt(disjuncts []Term, j int, w *PropWrapper) *PropWrapper {
	prefixes := make([]Term, len(disjuncts))
	prefixes[0] = disjuncts[0]
	for k := 1; k < len(disjuncts); k++ {
		prefixes[k] = WrapTerm(prefixes[k-1]).Or(disjuncts[k]).Core()
	}
	cur := w
	if j > 0 {
		cur = cur.DeriveTrans(prop.ConclOR1(prefixes[j-1], disjuncts[j]))
	}
	for k := j + 1; k < len(disjuncts); k++ {
		cur = cur.DeriveTrans(prop.ConclOR0(prefixes[k-1], disjuncts[k]))
	}
	return cur
}

// ruleDisjunctsAt builds the k rule disjuncts at subject term s and
// predicate application function applyQ (Q a variable, or a λ-body
// substitution — the same builder serves both, which keeps the manual
// β-forms and the constructed forms one code path). The ∃-bound
// argument variables are renamed away from the subject's and the
// predicate application's free variables — a caller's own a₀ must
// never be captured by the disjunct's a₀ binder.
func (dd *DataDefinition) ruleDisjunctsAt(v *recspaceVocab, s Term, applyQ func(Term) Term) ([]Term, [][]VarTerm) {
	disjuncts := make([]Term, len(dd.Ctors))
	argVars := make([][]VarTerm, len(dd.Ctors))
	probe := Var("probe", dd.RecspaceType()).Core()
	avoidBase := []Term{s, applyQ(probe)}
	for j := range dd.Ctors {
		c := &dd.Ctors[j]
		avoid := slices.Clone(avoidBase)
		args := make([]VarTerm, c.Arity())
		argTerms := make([]Term, c.Arity())
		for i := range args {
			t := c.ArgTypes[i]
			if c.IsRec[i] {
				t = dd.RecspaceType()
			}
			av := Var(TermName(fmt.Sprintf("a%d", i)), t).Core().(VarTerm).
				RenameToAvoid(avoid...)
			args[i], argTerms[i] = av, av
			avoid = append(avoid, av)
		}
		body := WrapTerm(s).Eq(dd.encode(v, j, argTerms)).Core()
		for i := range args {
			if c.IsRec[i] {
				body = WrapTerm(body).And(applyQ(args[i])).Core()
			}
		}
		for i := len(args) - 1; i >= 0; i-- {
			body = Exists(args[i])(body).Core()
		}
		disjuncts[j] = body
		argVars[j] = args
	}
	return disjuncts, argVars
}

// closureTermAt builds ∀a. (D₀(a) ∨ …) ⇒ apply(a) — closureTerm
// generalized over the predicate application.
func (dd *DataDefinition) closureTermAt(v *recspaceVocab, applyQ func(Term) Term) Term {
	a := Var("a", dd.RecspaceType()).Core().(VarTerm)
	disjuncts, _ := dd.ruleDisjunctsAt(v, a, applyQ)
	disj := disjuncts[0]
	for _, dj := range disjuncts[1:] {
		disj = WrapTerm(disj).Or(dj).Core()
	}
	return ForAll(a)(WrapTerm(disj).Imply(applyQ(a))).Core()
}

// deriveWitnessNonemptiness derives ⊢ pred(witness) — the typedef's
// input — as an APPLICATION of the predicate λ (core.NewTypeDef's
// required shape). Env-free pure logic.
func deriveWitnessNonemptiness(dd *DataDefinition, v *recspaceVocab, pred, witness Term) ThmCert {
	q := Var(dd.predicateName(), MakeFun(dd.RecspaceType(), TypeBool)).Core().(VarTerm)
	applyQ := func(t Term) Term { return Apply(q, t).Core() }
	closure := dd.closureTermAt(v, applyQ)
	ch := WrapProp(core.Assume(closure))

	j := dd.witnessIndex()
	c := &dd.Ctors[j]
	// The witness disjunct: ∃a…. witness = encⱼ(a…) — introduced at
	// the ε-arguments the witness itself is built from, so the
	// substituted equation is literally witness = witness.
	wits := make([]Term, c.Arity())
	for i, t := range c.ArgTypes {
		wits[i] = Var("v", t).SuchThat(T).Core()
	}
	disjuncts, _ := dd.ruleDisjunctsAt(v, witness, applyQ)
	dj := existsIntroChain(disjuncts[j], wits, WrapProp(core.Refl(witness)))
	disjProof := orIntroAt(disjuncts, j, dj)

	qOfW := ch.ConclForAllInst(witness).DemoteHyp().DeriveHypFrom(disjProof)
	closed := qOfW.PromoteHyp(closure).ConclForAll(q)

	predW := Apply(pred, witness).Core()
	eq := DeepBeta(predW)
	Assert(eq != nil)
	return eq.EqSym().EqMP(closed).AsThmCert()
}

// predOfEnc derives Γ ⊢ pred·encⱼ(args) from proofs of pred·rᵢ for the
// recursive rep arguments (args carries the ext args at author types
// and the rec args as recspace-typed terms, in constructor-arg order).
func (d *dataDeriver) predOfEnc(j int, args []Term, predOfRecs []*PropWrapper) *PropWrapper {
	dd := d.md.Def
	c := &dd.Ctors[j]
	q := Var(dd.predicateName(), MakeFun(dd.RecspaceType(), TypeBool)).Core().(VarTerm)
	applyQ := func(t Term) Term { return Apply(q, t).Core() }
	closure := dd.closureTermAt(v(d), applyQ)
	ch := WrapProp(core.Assume(closure))

	enc := dd.encode(v(d), j, args)

	// q(rᵢ) under {closure, pred·rᵢ's hyps}: unfold pred·rᵢ and feed
	// the closure hypothesis.
	qOfRecs := make([]*PropWrapper, len(predOfRecs))
	recIdx := 0
	for i := range args {
		if !c.IsRec[i] {
			continue
		}
		pw := predOfRecs[recIdx]
		unfolded := d.predBetaEq(args[i]).EqMP(pw)
		qOfRecs[recIdx] = unfolded.ConclForAllInst(q).DemoteHyp()
		recIdx++
	}

	// The j-th disjunct at enc, introduced at the actual arguments.
	disjuncts, _ := dd.ruleDisjunctsAt(v(d), enc, applyQ)
	var conj *PropWrapper
	if len(qOfRecs) == 0 {
		// A basal constructor: the disjunct body is the bare equation.
		conj = WrapProp(core.Refl(enc))
	} else {
		pieces := []Term{WrapTerm(Term(enc)).Eq(enc).Core()}
		for i := range args {
			if c.IsRec[i] {
				pieces = append(pieces, applyQ(args[i]))
			}
		}
		conj = ConclANDRecursive(pieces...).
			DeriveHypFrom(WrapProp(core.Refl(enc)))
		for _, qr := range qOfRecs {
			conj = conj.DeriveHypFrom(qr)
		}
	}
	dj := existsIntroChain(disjuncts[j], args, conj)
	disjProof := orIntroAt(disjuncts, j, dj)

	qOfEnc := ch.ConclForAllInst(enc).DemoteHyp().DeriveHypFrom(disjProof)
	closed := qOfEnc.PromoteHyp(closure).ConclForAll(q)
	return d.predBetaEq(enc).EqSym().EqMP(closed)
}

// v is sugar for the deriver's vocab.
func v(d *dataDeriver) *recspaceVocab { return d.md.Vocab }

// destCtorEq derives ⊢ dest(Cⱼ(args)) = encⱼ(ext…, dest recᵢ…) for
// author-typed argument terms (hyp-free: the recursive reps' pred
// facts come from predOfDest).
func (d *dataDeriver) destCtorEq(j int, args []Term) *PropWrapper {
	c := &d.md.Def.Ctors[j]
	encArgs := make([]Term, len(args))
	var predRecs []*PropWrapper
	for i, a := range args {
		if c.IsRec[i] {
			encArgs[i] = Apply(d.md.Dest, a).Core()
			predRecs = append(predRecs, d.predOfDest(a))
		} else {
			encArgs[i] = a
		}
	}
	enc := d.md.Def.encode(v(d), j, encArgs)
	unfold := prop.ExpandDef(d.md.Ctors[j], args...) // Cⱼ(args) = mk(enc)
	destBoth := unfold.LeftApply(d.md.Dest)          // dest(Cⱼ args) = dest(mk enc)
	pe := d.predOfEnc(j, encArgs, predRecs)
	return destBoth.EqTrans(d.destMkFrom(enc, pe))
}

// ---------------------------------------------------------------------------
// INDUCT
// ---------------------------------------------------------------------------

// DeriveDataInduct derives the induction principle (md.InductStmt()):
// the sequent `case₁, …, caseₙ ⊢ P(x)` from the typedef axioms, closed
// into the statement. Env-free: pure logic over the typedef axioms.
func DeriveDataInduct(env *ProverEnv, md *MintedDatatype) (Prop, error) {
	d := newDataDeriver(env, md)
	dd := md.Def
	stmt := md.InductStmt()
	P, x := md.inductVars()
	cases := md.inductCases(P)

	// QL := λr. pred·r ∧ P(mk r); qlBody is its manual β at a term.
	rv := Var("r", dd.RecspaceType()).Core().(VarTerm)
	qlBody := func(t Term) Term {
		return WrapTerm(d.predApp(t)).
			And(Apply(P, Apply(md.Mk, t).Core()).Core()).Core()
	}
	ql := Abs(rv, qlBody(rv))
	qlAbs, ok := ql.AsAbsTerm()
	Assert(ok)

	// L1: the closure at QL, from the goal's case hypotheses.
	b := Var("b", dd.RecspaceType()).Core().(VarTerm)
	disjuncts, argVars := dd.ruleDisjunctsAt(v(d), b, qlBody)

	perCase := make([]*PropWrapper, len(dd.Ctors))
	for j := range dd.Ctors {
		c := &dd.Ctors[j]
		args := argVars[j]

		// Assumed pieces of the opened disjunct.
		eqTerm := WrapTerm(Term(b)).Eq(dd.encode(v(d), j, termsOf(args))).Core()
		pieces := []Term{eqTerm}
		for i := range args {
			if c.IsRec[i] {
				pieces = append(pieces, qlBody(args[i]))
			}
		}
		eqW := WrapProp(core.Assume(eqTerm))
		var predRecs, pMkRecs []*PropWrapper
		for i := range args {
			if !c.IsRec[i] {
				continue
			}
			cond := WrapProp(core.Assume(qlBody(args[i])))
			predRecs = append(predRecs,
				cond.DeriveTrans(HypAND0(d.predApp(args[i]),
					Apply(P, Apply(md.Mk, args[i]).Core()).Core())))
			pMkRecs = append(pMkRecs,
				cond.DeriveTrans(HypAND1(d.predApp(args[i]),
					Apply(P, Apply(md.Mk, args[i]).Core()).Core())))
		}

		// pred·enc from the rec conditions' pred halves.
		encArgs := termsOf(args)
		predEnc := d.predOfEnc(j, encArgs, predRecs)

		// P(mk enc) from the case hypothesis at (ext args, mk rᵢ).
		mixed := make([]Term, len(args))
		var recReps []Term
		for i, a := range args {
			if c.IsRec[i] {
				mixed[i] = Apply(md.Mk, a).Core()
				recReps = append(recReps, Term(a))
			} else {
				mixed[i] = a
			}
		}
		hw := WrapProp(core.Assume(cases[j])).ConclForAllInsts(mixed...)
		for range recReps {
			hw = hw.DemoteHyp()
		}
		// hw: {Hⱼ, P(mk rᵢ)…} ⊢ P(Cⱼ(mixed)); rewrite the constructor
		// application to mk(enc) via the unfold + dest∘mk.
		unfold := prop.ExpandDef(md.Ctors[j], mixed...)
		for k, rep := range recReps {
			dm := d.destMkFrom(rep, predRecs[k])
			unfold = unfold.RewriteConcl(EqRewrite(dm))
		}
		// unfold: Γ ⊢ Cⱼ(mixed) = mk(encⱼ(args)); apply P and EqMP.
		pOfEnc := unfold.LeftApply(P).EqMP(hw)
		// The P(mk rᵢ) hyps entered as assumptions of pMkRecs; align
		// them by deriving from the conjunction pieces.
		for _, pm := range pMkRecs {
			pOfEnc = pOfEnc.DeriveHypFrom(pm)
		}

		conj := prop.ConclAND(predEnc.Conclusion(), pOfEnc.Conclusion()).
			DeriveHypFrom(predEnc).
			DeriveHypFrom(pOfEnc)
		// conj: {Hⱼ, qlBody(rᵢ)…} ⊢ qlBody(enc). Transport to
		// qlBody(b) under the equation hypothesis by TARGETED
		// congruence at the QL lambda — a blanket enc→b rewrite would
		// also rewrite the base encoding's literal occurrence INSIDE
		// the shape predicate's own rule body and corrupt pred.
		enc := dd.encode(v(d), j, termsOf(args))
		qlCongr := DeepBetaAbs(qlAbs)(Apply(ql, enc).Core()).EqSym().
			EqTrans(eqW.EqSym().LeftApply(ql)).
			EqTrans(DeepBetaAbs(qlAbs)(Apply(ql, Term(b)).Core()))
		caseW := qlCongr.EqMP(conj)
		// Repackage the opened pieces into the single ∃-hyp.
		if len(pieces) > 1 {
			projections := prop.HypANDRecursive(pieces...)
			for _, pr := range projections {
				caseW = caseW.DeriveHypFrom(pr)
			}
		}
		for i := len(args) - 1; i >= 0; i-- {
			h := existsBodyAt(disjuncts[j], args[:i+1])
			caseW = caseW.HypExists(args[i], h)
		}
		perCase[j] = caseW.PromoteHyp(disjuncts[j])
	}

	byCases := prop.ByCasesRecursive(qlBody(b), disjuncts...)
	for _, pc := range perCase {
		byCases = byCases.DeriveHypFrom(pc)
	}
	disj := disjuncts[0]
	for _, dj := range disjuncts[1:] {
		disj = WrapTerm(disj).Or(dj).Core()
	}
	closureQL := byCases.PromoteHyp(disj).ConclForAll(b)

	// L2: pred(dest x) instantiated at QL, fed the closure, projected.
	destX := Apply(md.Dest, x).Core()
	unfolded := d.predBetaEq(destX).EqMP(d.predOfDest(x))
	atQL := unfolded.ConclForAllInst(ql).Rewrite(DeepBetaAbs(qlAbs))
	qlOfDest := atQL.DemoteHyp().DeriveHypFrom(closureQL)
	pOfMkDest := qlOfDest.DeriveTrans(HypAND1(
		d.predApp(destX), Apply(P, Apply(md.Mk, destX).Core()).Core()))
	sequent := d.mkDestAt(x).LeftApply(P).EqMP(pOfMkDest)

	// The sequent closed into the statement: the cases one ∧-joined
	// antecedent, the index and the predicate bound.
	all := make([]int, len(cases))
	for j := range all {
		all[j] = j
	}
	for j := range cases {
		sequent = sequent.DeriveHypFrom(prop.ConjunctionPiece(cases, all, j))
	}
	final := sequent.PromoteHyp(prop.ConjunctionOf(cases, all)).ConclForAll(x).ConclForAll(P)

	if !final.AlphaEquals(stmt) {
		panic(fmt.Sprintf("DeriveDataInduct: derived %s ≠ statement %s — kit drift",
			PrintProp(final), PrintProp(stmt)))
	}
	return final, nil
}

// termsOf converts a var slice to a term slice.
func termsOf(vs []VarTerm) []Term {
	out := make([]Term, len(vs))
	for i, v := range vs {
		out[i] = v
	}
	return out
}

// existsBodyAt returns the body of disjunct's ∃-chain opened at the
// given (outermost-first) variables, with vars[:len-1] substituted and
// the LAST variable still free — the hypothesis shape HypExists folds.
func existsBodyAt(disjunct Term, vars []VarTerm) Term {
	cur := disjunct
	for i := 0; i < len(vars); i++ {
		abs := MatchesEXISTS(cur)
		Assert(!abs.IsZero())
		if i == len(vars)-1 {
			return abs.Body().Substitute(MakeTermSubst(abs.Var(), vars[i]))
		}
		cur = abs.Body().Substitute(MakeTermSubst(abs.Var(), vars[i]))
	}
	return cur
}

// ---------------------------------------------------------------------------
// RECURSION
// ---------------------------------------------------------------------------

// fconsClauses type-instantiates the family_cons row at elem type and splits
// it: c1 = ∀a f. family_cons(a,f,0) = a, c2 = ∀a f n. family_cons(a,f,suc n) = f(n).
// The row's zero spelling is asserted against the kit's own (both are
// the DSL's bare _0).
func (d *dataDeriver) fconsClauses(elem HolType) (c1, c2 *PropWrapper, err error) {
	row, err := d.libRow("family_cons_definition")
	if err != nil {
		return nil, nil, err
	}
	// The row states its two clauses either each separately ∀-closed and
	// conjoined at the top (the spelling emit produced) or as one pack
	// under a shared ∀a f prefix (the spelling). Peel a shared
	// prefix — empty in the first case — so both arrive at two
	// conjuncts; the binders go back onto each clause below, which
	// leaves c1/c2 in the ∀a f / ∀a f n order this returns either way.
	packed, shared := row.StripConclForAll()
	conjs := DecomposesAND(packed.Conclusion())
	if len(conjs) != 2 {
		return nil, nil, fmt.Errorf("define data: family_cons row is not the two-clause form: %s",
			PrintProp(row))
	}
	// Read the row's element type letter off the shared prefix, or off
	// clause 1's own ∀a binder when there is none.
	var rowElem HolType
	if len(shared) > 0 {
		rowElem = shared[0].Type()
	} else {
		c1List, _ := DecomposesFORALL(conjs[0])
		Assert(c1List.Size() >= 1)
		rowElem = c1List.Ind(0).Type()
	}
	substs, ok := rowElem.Matches(elem, func(VarType) bool { return true })
	if !ok {
		return nil, nil, fmt.Errorf("define data: family_cons row element type %s cannot instantiate at %s",
			FormatType(rowElem), FormatType(elem))
	}
	instPacked, instShared := row.TypeInst(substs...).StripConclForAll()
	instConjs := DecomposesAND(instPacked.Conclusion())
	c1 = instPacked.DeriveTrans(HypAND0(instConjs[0], instConjs[1])).ConclForAllList(instShared...)
	c2 = instPacked.DeriveTrans(HypAND1(instConjs[0], instConjs[1])).ConclForAllList(instShared...)
	// Zero-spelling tripwire (clause 1's index term).
	_, m1 := DecomposesFORALL(c1.Conclusion())
	l1, _, okEq := MatchesEQ(m1)
	Assert(okEq)
	_, idxArgs := MatchesApply(l1)
	Assert(len(idxArgs) == 3)
	if !idxArgs[2].AlphaEquals(v(d).zero) {
		return nil, nil, fmt.Errorf(
			"define data: family_cons row's zero %s differs from the kit's %s — numeral spelling drift",
			PrintTerm(idxArgs[2]), PrintTerm(v(d).zero))
	}
	return c1, c2, nil
}

// fconsSelect derives ⊢ family_cons(e₀, family_cons(e₁, … tail)…)(idx_t) = e_t —
// the family_cons list computation at index t. c1/c2 are fconsClauses at the
// elements' type.
func (d *dataDeriver) fconsSelect(c1, c2 *PropWrapper, elems []Term, tail Term, t int) *PropWrapper {
	Assert(t < len(elems))
	chains := make([]Term, len(elems)+1)
	chains[len(elems)] = tail
	fcons := elemFconsConst(v(d), elems[0].Type())
	for k := len(elems) - 1; k >= 0; k-- {
		chains[k] = Apply(fcons, elems[k], chains[k+1]).Core()
	}
	var eq *PropWrapper
	for s := 0; s < t; s++ {
		step := c2.ConclForAllInsts(elems[s], chains[s+1], v(d).index(t-s-1))
		if eq == nil {
			eq = step
		} else {
			eq = eq.EqTrans(step)
		}
	}
	last := c1.ConclForAllInsts(elems[t], chains[t+1])
	if eq == nil {
		return last
	}
	return eq.EqTrans(last)
}

// elemFconsConst returns the family_cons const at element type elem.
func elemFconsConst(v *recspaceVocab, elem HolType) ConstTerm {
	numToElem := MakeFun(NumType, elem)
	return MakeConstTerm(v.fcons.Meta(),
		MakeFun(elem, MakeFun(numToElem, numToElem)))
}

// payloadProject derives ⊢ extract-chain(payload) = slot-term for the
// literal nested-pair payload — the fst/snd computation chain to slot
// k. Trivial (reflexivity) for the single-slot payload, where the
// extraction is the identity.
func (d *dataDeriver) payloadProject(payload Term, slots []HolType, k int) (*PropWrapper, error) {
	if len(slots) == 1 {
		return WrapProp(core.Refl(payload)), nil
	}
	fstRow, err := d.libRow("fst_of_pair")
	if err != nil {
		return nil, err
	}
	sndRow, err := d.libRow("snd_of_pair")
	if err != nil {
		return nil, err
	}
	isProjApp := func(l Term) bool {
		head, args := MatchesApply(l)
		_, isConst := head.AsConst()
		return isConst && len(args) == 1
	}
	fstRow = orientIff(stripRow(fstRow), isProjApp)
	sndRow = orientIff(stripRow(sndRow), isProjApp)
	// Walk the literal pair spine: at each level, snd moves right,
	// ending with fst (or landing on the last slot).
	cur := payload
	var eq *PropWrapper // extract-so-far = cur
	step := func(row *PropWrapper, takeFirst bool) error {
		head, args := MatchesApply(cur)
		c, okC := head.AsConst()
		if !okC || c.Name() != ext.CommaConstMeta.Name() || len(args) != 2 {
			return fmt.Errorf("define data: payload projection walked off the pair spine at %s",
				PrintTerm(cur))
		}
		// Row: fst((x,y)) = x / snd((x,y)) = y at the pair's types.
		rowL, _, okEq := MatchesEQ(row.Conclusion())
		Assert(okEq)
		_, rowArgs := MatchesApply(rowL)
		Assert(len(rowArgs) == 1)
		_, pairVars := MatchesApply(rowArgs[0])
		Assert(len(pairVars) == 2)
		xv, okX := pairVars[0].AsVar()
		yv, okY := pairVars[1].AsVar()
		Assert(okX && okY)
		substs, okM := MakeProdType(xv.Type(), yv.Type()).
			Matches(cur.Type(), func(VarType) bool { return true })
		if !okM {
			return fmt.Errorf("define data: fst/snd row cannot instantiate at %s",
				FormatType(cur.Type()))
		}
		rowInst := row.TypeInst(substs...)
		rowInstL, _, _ := MatchesEQ(rowInst.Conclusion())
		_, instArgs := MatchesApply(rowInstL)
		_, instPairVars := MatchesApply(instArgs[0])
		xi, _ := instPairVars[0].AsVar()
		yi, _ := instPairVars[1].AsVar()
		stepEq := rowInst.TermInst(
			MakeTermSubst(xi, args[0]), MakeTermSubst(yi, args[1]))
		// stepEq: PROJ(cur-pair) = component. Chain: build
		// extract(payload) = component from extract-so-far = cur by
		// applying PROJ to both sides, then the computation.
		if eq == nil {
			eq = stepEq
		} else {
			projHead, _ := MatchesApply(Lhs(stepEq))
			eq = eq.LeftApply(projHead).EqTrans(stepEq)
		}
		if takeFirst {
			cur = args[0]
		} else {
			cur = args[1]
		}
		return nil
	}
	for level := 0; level < k; level++ {
		if err := step(sndRow, false); err != nil {
			return nil, err
		}
	}
	if k < len(slots)-1 {
		if err := step(fstRow, true); err != nil {
			return nil, err
		}
	}
	return eq, nil
}

// DeriveDataRecursion derives the recursion principle
// (md.RecursionStmt()) by instantiating recspace_recursion at the family_cons
// case-selector.
func DeriveDataRecursion(env *ProverEnv, md *MintedDatatype) (Prop, error) {
	d := newDataDeriver(env, md)
	dd := md.Def
	stmt := md.RecursionStmt()

	motive := md.motiveLetter()
	pType := dd.PayloadType()
	rType := dd.RecspaceType()
	numToR := MakeFun(NumType, rType)
	numToZ := MakeFun(NumType, motive)
	// W = P → (num→R) → (num→Z) → Z — the case functions' type.
	wType := MakeFun(pType, MakeFun(numToR, MakeFun(numToZ, motive)))

	// The statement's ∀-bound parameters, reused as the derivation's
	// free parameter variables.
	params := make([]VarTerm, len(dd.Ctors))
	for j := range dd.Ctors {
		params[j] = md.recParamVar(j, motive)
	}

	// caseⱼ = λi r s. fⱼ(extract…, mk(r(t)), …, s(t)…).
	iVar := Var("i", pType).Core().(VarTerm)
	rVar := Var("r", numToR).Core().(VarTerm)
	sVar := Var("s", numToZ).Core().(VarTerm)
	extractAt := func(k int) Term {
		// The fst/snd chain to slot k over iVar.
		if len(dd.PayloadSlots) == 1 {
			return iVar
		}
		cur := Term(iVar)
		rest := dd.PayloadType()
		for level := 0; level < k; level++ {
			prod := rest.(CompositeType)
			cur = Apply(sndConst(prod.SubType(0), prod.SubType(1)), cur).Core()
			rest = prod.SubType(1)
		}
		if k < len(dd.PayloadSlots)-1 {
			prod := rest.(CompositeType)
			cur = Apply(fstConst(prod.SubType(0), prod.SubType(1)), cur).Core()
		}
		return cur
	}
	cases := make([]Term, len(dd.Ctors))
	for j := range dd.Ctors {
		c := &dd.Ctors[j]
		rhsArgs := make([]Term, 0, c.Arity()+2)
		recIdx := 0
		for i := range c.ArgTypes {
			if c.IsRec[i] {
				rhsArgs = append(rhsArgs,
					Apply(md.Mk, Apply(rVar, v(d).index(recIdx)).Core()).Core())
				recIdx++
			} else {
				rhsArgs = append(rhsArgs, extractAt(c.PayloadSlot[i]))
			}
		}
		for t := 0; t < recIdx; t++ {
			rhsArgs = append(rhsArgs, Apply(sVar, v(d).index(t)).Core())
		}
		var body Term = params[j]
		if len(rhsArgs) > 0 {
			body = Apply(params[j], rhsArgs...).Core()
		}
		cases[j] = Abs(iVar, Abs(rVar, Abs(sVar, body)))
	}

	// Fn := family_cons(case₀, family_cons(case₁, … family_nil)).
	fnilMeta, err := d.fnilMeta()
	if err != nil {
		return nil, err
	}
	fnil := MakeConstTerm(fnilMeta, numToWType(wType))
	selector := Term(fnil)
	fconsW := elemFconsConst(v(d), wType)
	for j := len(cases) - 1; j >= 0; j-- {
		selector = Apply(fconsW, cases[j], selector).Core()
	}

	// recspace_recursion, type-instantiated to (payload, motive) and
	// term-instantiated at the selector.
	rec, err := d.libRow("recspace_recursion")
	if err != nil {
		return nil, err
	}
	// The row states the case functional either as a leading ∀ (the
	// the chapter spelling — a properly closed theorem) or as a free
	// variable (the spelling emit produced, a sequent). Peel the ∀ when
	// it is there, so both arrive at the ∃f matrix this reads; the
	// binder is re-instantiated at the selector below, in the same place
	// the free-variable form is.
	recConcl := rec.Conclusion()
	recFnBinder := MatchesFORALL(recConcl)
	if !recFnBinder.IsZero() {
		recConcl = recFnBinder.Body()
	}
	recAbs := MatchesEXISTS(recConcl)
	if recAbs.IsZero() {
		return nil, fmt.Errorf("define data: recspace_recursion row is neither ∃-headed nor ∀∃-headed: %s", PrintProp(rec))
	}
	rowFnType := recAbs.Var().Type()
	substs, okM := rowFnType.Matches(MakeFun(rType, motive),
		func(VarType) bool { return true })
	if !okM {
		return nil, fmt.Errorf("define data: recspace_recursion's function type %s cannot instantiate at %s",
			FormatType(rowFnType), FormatType(MakeFun(rType, motive)))
	}
	recInst := rec.TypeInst(substs...)
	if !recFnBinder.IsZero() {
		// Closed form: instantiate the ∀-bound case functional.
		recInst = recInst.ConclForAllInst(selector)
	} else {
		recFrees := recInst.Conclusion().Frees(nil)
		if len(recFrees) != 1 {
			return nil, fmt.Errorf("define data: recspace_recursion row has %d free variables, expected the case functional alone", len(recFrees))
		}
		recInst = recInst.TermInst(MakeTermSubst(recFrees[0], selector))
	}

	// Choose fn and assume its recspace_node equation.
	chosenAbs := MatchesEXISTS(recInst.Conclusion())
	Assert(!chosenAbs.IsZero())
	fnVar := Var("fn", MakeFun(rType, motive)).Core().(VarTerm)
	hfn := chosenAbs.Body().Substitute(MakeTermSubst(chosenAbs.Var(), fnVar))
	hfnW := WrapProp(core.Assume(hfn))

	// fnT := λx. fn(dest x).
	xVar := Var("x", md.AbsType).Core().(VarTerm)
	fnT := Abs(xVar, Apply(fnVar, Apply(md.Dest, xVar).Core()).Core())

	c1W, c2W, err := d.fconsClauses(wType)
	if err != nil {
		return nil, err
	}
	c1R, c2R, err := d.fconsClauses(rType)
	if err != nil {
		return nil, err
	}

	clauses := make([]*PropWrapper, len(dd.Ctors))
	for j := range dd.Ctors {
		c := &dd.Ctors[j]
		args := md.ctorArgVars(j, "")
		argTerms := termsOf(args)

		// LHS chain: fnT(Cⱼ(a…)) = fn(dest(Cⱼ(a…))) = fn(encⱼ(…)).
		lhsApp := Apply(fnT, md.ctorApp(j, args)).Core()
		betaL := DeepBeta(lhsApp)
		Assert(betaL != nil)
		destEq := d.destCtorEq(j, argTerms)
		chain := betaL.EqTrans(destEq.LeftApply(fnVar))

		// The encoding's pieces, for the recspace_recursion equation instance.
		encArgs := make([]Term, len(args))
		var recReps []Term
		for i, a := range args {
			if c.IsRec[i] {
				encArgs[i] = Apply(md.Dest, a).Core()
				recReps = append(recReps, encArgs[i])
			} else {
				encArgs[i] = a
			}
		}
		payload := dd.payloadTuple(c, encArgs)
		subtrees := v(d).subtreeList(recReps)

		// fn(recspace_node(idx, payload, subtrees)) = selector-applied.
		recEq := hfnW.ConclForAllInsts(v(d).index(j), payload, subtrees)
		chain = chain.EqTrans(recEq)

		// Selector computation: family_cons-chain(idxⱼ) = caseⱼ, applied.
		sel := d.fconsSelect(c1W, c2W, cases, Term(fnil), j)
		fnSubs := Abs(
			Var("n", NumType).Core().(VarTerm),
			Apply(fnVar, Apply(subtrees,
				Var("n", NumType).Core()).Core()).Core())
		selApplied := sel.RightApply(payload).RightApply(subtrees).RightApply(fnSubs)
		chain = chain.EqTrans(selApplied)

		// β of the case application.
		caseApp := Apply(cases[j], payload, subtrees, fnSubs).Core()
		betaC := DeepBeta(caseApp)
		Assert(betaC != nil)
		chain = chain.EqTrans(betaC)

		// Residual computation: payload extraction, subtree selection,
		// mk∘dest collapse, and the fnT re-fold.
		for _, slot := range c.PayloadSlot {
			if slot < 0 {
				continue
			}
			if len(dd.PayloadSlots) == 1 {
				continue // single-slot payload: extraction is the identity
			}
			proj, perr := d.payloadProject(payload, dd.PayloadSlots, slot)
			if perr != nil {
				return nil, perr
			}
			chain = chain.RewriteConcl(EqRewrite(proj))
		}
		for t := range recReps {
			subsSel := d.fconsSelect(c1R, c2R, recReps, v(d).bottomTail(), t)
			chain = chain.RewriteConcl(EqRewrite(subsSel))
		}
		for _, i := range c.RecPositions() {
			a := args[i]
			chain = chain.RewriteConcl(EqRewrite(d.mkDestAt(a)))
			fnTfold := DeepBeta(Apply(fnT, a).Core())
			Assert(fnTfold != nil)
			chain = chain.RewriteConcl(EqRewrite(fnTfold.EqSym()))
		}
		clauses[j] = chain.ConclForAllList(args...)
	}

	// Conjoin, ∃-introduce at fnT, discharge the choice, generalize.
	clauseTerms := make([]Term, len(clauses))
	for j, cw := range clauses {
		clauseTerms[j] = cw.Conclusion()
	}
	var conj *PropWrapper
	if len(clauses) == 1 {
		conj = clauses[0]
	} else {
		conj = ConclANDRecursive(clauseTerms...)
		for _, cw := range clauses {
			conj = conj.DeriveHypFrom(cw)
		}
	}

	// The ∃-target: the statement with its parameter ∀s stripped (the
	// params stay free) — then intro at fnT.
	existsTarget := stmt.Conclusion()
	for j := 0; j < len(params); j++ {
		abs := MatchesFORALL(existsTarget)
		Assert(!abs.IsZero())
		existsTarget = abs.Body().Substitute(MakeTermSubst(abs.Var(), params[j]))
	}
	exIntro := existsIntroChain(existsTarget, []Term{fnT}, conj)

	// Discharge the chosen fn against the instantiated recspace_recursion.
	closed := exIntro.HypExists(fnVar, hfn).DeriveHypFrom(recInst)
	final := closed.ConclForAllList(params...)

	if !final.AlphaEquals(stmt) {
		panic(fmt.Sprintf("DeriveDataRecursion: derived %s ≠ statement %s — kit drift",
			PrintProp(final), PrintProp(stmt)))
	}
	return final, nil
}

// fnilMeta resolves the family_nil const meta — from the env's resolver.
func (d *dataDeriver) fnilMeta() (ConstTermMeta, error) {
	if d.env != nil && d.env.ProofService != nil && d.env.ProofService.LoadConstMeta != nil {
		if meta, ok := d.env.ProofService.LoadConstMeta("family_nil"); ok {
			return meta, nil
		}
	}
	return ConstTermMeta{}, fmt.Errorf("define data: constant family_nil is not registered — the recspace layer must be loaded")
}

// numToWType returns num → W.
func numToWType(w HolType) HolType { return MakeFun(NumType, w) }

// fstConst / sndConst build the pair projections at an instance.
func fstConst(a, b HolType) ConstTerm {
	return MakeConstTerm(MakeConstMeta("fst",
		MakeFun(MakeProdType(TypeA, MakeVarType("B")), TypeA)),
		MakeFun(MakeProdType(a, b), a))
}
func sndConst(a, b HolType) ConstTerm {
	return MakeConstTerm(MakeConstMeta("snd",
		MakeFun(MakeProdType(TypeA, MakeVarType("B")), MakeVarType("B"))),
		MakeFun(MakeProdType(a, b), b))
}

// ---------------------------------------------------------------------------
// INJ / DISTINCT
// ---------------------------------------------------------------------------

// constrInjInstance instantiates the recspace_node_injective row at the datatype's
// payload instance and the two encodings' pieces, returning the ⇔ with
// its component equations:
//
//	(recspace_node(x1,p1,s1) = recspace_node(x2,p2,s2)) ⇔ (x1=x2 ∧ (p1=p2 ∧ s1=s2))
func (d *dataDeriver) constrInjInstance(idx1, pay1, subs1, idx2, pay2, subs2 Term) (*PropWrapper, error) {
	row, err := d.libRow("recspace_node_injective")
	if err != nil {
		return nil, err
	}
	// The corpus serves this row ∀-closed; the kit instantiates
	// its variables as frees, so peel the prefix the way the sibling
	// rows do (stripRow).
	row = stripRow(row)
	l, _, okEq := MatchesEQ(row.Conclusion())
	if !okEq {
		return nil, fmt.Errorf("define data: recspace_node_injective row is not an ⇔: %s", PrintProp(row))
	}
	lhs1, _, okL := MatchesEQ(l)
	Assert(okL)
	_, rowArgs := MatchesApply(lhs1)
	Assert(len(rowArgs) == 3)
	rowPayload := rowArgs[1].Type()
	substs, okM := rowPayload.Matches(d.md.Def.PayloadType(), func(VarType) bool { return true })
	if !okM {
		return nil, fmt.Errorf("define data: recspace_node_injective payload type %s cannot instantiate at %s",
			FormatType(rowPayload), FormatType(d.md.Def.PayloadType()))
	}
	inst := row.TypeInst(substs...)
	li, _, _ := MatchesEQ(inst.Conclusion())
	l1, r1, _ := MatchesEQ(li)
	_, vars1 := MatchesApply(l1)
	_, vars2 := MatchesApply(r1)
	sub := make([]TermSubst, 0, 6)
	for k, val := range []Term{idx1, pay1, subs1} {
		v1, okV := vars1[k].AsVar()
		Assert(okV)
		sub = append(sub, MakeTermSubst(v1, val))
	}
	for k, val := range []Term{idx2, pay2, subs2} {
		v2, okV := vars2[k].AsVar()
		Assert(okV)
		sub = append(sub, MakeTermSubst(v2, val))
	}
	return inst.TermInst(sub...), nil
}

// encPieces computes the encoding's three recspace_node arguments for
// constructor j at the given author-arg terms (recursive positions
// passed through dest).
func (d *dataDeriver) encPieces(j int, args []Term) (idx, payload, subtrees Term, recReps []Term) {
	c := &d.md.Def.Ctors[j]
	encArgs := make([]Term, len(args))
	for i, a := range args {
		if c.IsRec[i] {
			encArgs[i] = Apply(d.md.Dest, a).Core()
			recReps = append(recReps, encArgs[i])
		} else {
			encArgs[i] = a
		}
	}
	return v(d).index(j), d.md.Def.payloadTuple(c, encArgs), v(d).subtreeList(recReps), recReps
}

// pairComponentEq projects component k out of a payload-tuple equation
// pay1 = pay2 (literal nested pairs over the slot list) via pair_injective.
func (d *dataDeriver) pairComponentEq(eq *PropWrapper, slots []HolType, k int) (*PropWrapper, error) {
	if len(slots) == 1 {
		return eq, nil
	}
	pairEqRow, err := d.libRow("pair_injective")
	if err != nil {
		return nil, err
	}
	pairEqRow = orientIff(stripRow(pairEqRow), func(l Term) bool {
		el, _, isEq := MatchesEQ(l)
		if !isEq {
			return false
		}
		_, args := MatchesApply(el)
		return len(args) == 2
	})
	cur := eq
	// Count-driven walk over the payload spine — len(slots)-1 pair
	// levels exist; component k needs k AND1-descents and (unless it is
	// the last slot) one final AND0. Never shape-probed: a slot TYPE
	// may itself be a product, and only the slot count says which
	// commas are spine.
	maxLevel := k
	if k == len(slots)-1 {
		maxLevel = k - 1
	}
	for level := 0; level <= maxLevel; level++ {
		l, r, okEq := MatchesEQ(cur.Conclusion())
		Assert(okEq)
		_, lArgs := MatchesApply(l)
		_, rArgs := MatchesApply(r)
		Assert(len(lArgs) == 2 && len(rArgs) == 2)
		// Instantiate pair_injective at this level's component types/terms.
		rowL, _, _ := MatchesEQ(pairEqRow.Conclusion())
		lhsPair, _, _ := MatchesEQ(rowL)
		_, rowPairVars := MatchesApply(lhsPair)
		xT, yT := rowPairVars[0].Type(), rowPairVars[1].Type()
		substs := make([]core.TypeSubst, 0, 2)
		okX := core.MatchTypeInto(xT, lArgs[0].Type(), func(VarType) bool { return true }, &substs)
		okY := core.MatchTypeInto(yT, lArgs[1].Type(), func(VarType) bool { return true }, &substs)
		if !okX || !okY {
			return nil, fmt.Errorf("define data: pair_injective cannot instantiate at (%s, %s)",
				FormatType(lArgs[0].Type()), FormatType(lArgs[1].Type()))
		}
		rowInst := pairEqRow.TypeInst(substs...)
		riL, _, _ := MatchesEQ(rowInst.Conclusion())
		riLhs, riRhs, _ := MatchesEQ(riL)
		_, riLVars := MatchesApply(riLhs)
		_, riRVars := MatchesApply(riRhs)
		sub := make([]TermSubst, 0, 4)
		for kk, val := range []Term{lArgs[0], lArgs[1]} {
			vv, okV := riLVars[kk].AsVar()
			Assert(okV)
			sub = append(sub, MakeTermSubst(vv, val))
		}
		for kk, val := range []Term{rArgs[0], rArgs[1]} {
			vv, okV := riRVars[kk].AsVar()
			Assert(okV)
			sub = append(sub, MakeTermSubst(vv, val))
		}
		split := rowInst.TermInst(sub...).EqMP(cur)
		firstEq := WrapTerm(lArgs[0]).Eq(rArgs[0]).Core()
		restEq := WrapTerm(lArgs[1]).Eq(rArgs[1]).Core()
		if level == k {
			return split.DeriveTrans(HypAND0(firstEq, restEq)), nil
		}
		cur = split.DeriveTrans(HypAND1(firstEq, restEq))
	}
	// k == len(slots)-1: cur is the last slot's bare component eq.
	return cur, nil
}

// DeriveDataInj derives the constructors-injective theorem
// (md.InjStmt()).
func DeriveDataInj(env *ProverEnv, md *MintedDatatype) (Prop, error) {
	d := newDataDeriver(env, md)
	dd := md.Def
	stmt := md.InjStmt()
	if stmt == nil {
		return nil, fmt.Errorf("define data: %s has no argumented constructor — no INJ theorem", dd.TypeName)
	}

	var c1R, c2R *PropWrapper
	for j := range dd.Ctors {
		if len(dd.Ctors[j].RecPositions()) > 0 {
			var ferr error
			c1R, c2R, ferr = d.fconsClauses(dd.RecspaceType())
			if ferr != nil {
				return nil, ferr
			}
			break
		}
	}

	var clauses []*PropWrapper
	for j := range dd.Ctors {
		c := &dd.Ctors[j]
		if c.Arity() == 0 {
			continue
		}
		l := md.ctorArgVars(j, "")
		r := md.ctorArgVars(j, "'")
		lApp, rApp := md.ctorApp(j, l), md.ctorApp(j, r)
		eqTerm := WrapTerm(lApp).Eq(rApp).Core()

		// FORWARD: Cⱼ(l)=Cⱼ(r) ⊢ ⋀ lᵢ=rᵢ.
		eqW := WrapProp(core.Assume(eqTerm))
		destEq := d.destCtorEq(j, termsOf(l)).EqSym().
			EqTrans(eqW.LeftApply(md.Dest)).
			EqTrans(d.destCtorEq(j, termsOf(r)))
		// destEq: encⱼ(l-pieces) = encⱼ(r-pieces).
		idx1, pay1, subs1, lReps := d.encPieces(j, termsOf(l))
		idx2, pay2, subs2, rReps := d.encPieces(j, termsOf(r))
		inj, err := d.constrInjInstance(idx1, pay1, subs1, idx2, pay2, subs2)
		if err != nil {
			return nil, err
		}
		conjThm := inj.EqMP(destEq)
		// The three component equations, in order: index, payload,
		// sub-encodings. Projected by leaf position so the row's
		// ∧-association does not matter (conjLeaf).
		Assert(len(DecomposesAND(conjThm.Conclusion())) == 3)
		payEq := conjLeaf(conjThm, 1)
		subsEq := conjLeaf(conjThm, 2)

		argEqs := make([]*PropWrapper, c.Arity())
		recIdx := 0
		for i := range c.ArgTypes {
			if c.IsRec[i] {
				// subs1(idx t) = subs2(idx t) → dest lᵢ = dest rᵢ → lᵢ = rᵢ.
				lSel := d.fconsSelect(c1R, c2R, lReps, v(d).bottomTail(), recIdx)
				rSel := d.fconsSelect(c1R, c2R, rReps, v(d).bottomTail(), recIdx)
				applied := subsEq.RightApply(v(d).index(recIdx))
				destsEq := lSel.EqSym().EqTrans(applied).EqTrans(rSel)
				mkBoth := destsEq.LeftApply(md.Mk)
				argEqs[i] = d.mkDestAt(l[i]).EqSym().EqTrans(mkBoth).EqTrans(d.mkDestAt(r[i]))
				recIdx++
			} else {
				comp, err := d.pairComponentEq(payEq, dd.PayloadSlots, c.PayloadSlot[i])
				if err != nil {
					return nil, err
				}
				argEqs[i] = comp
			}
		}
		var fwd *PropWrapper
		if c.Arity() == 1 {
			fwd = argEqs[0]
		} else {
			pieces := make([]Term, c.Arity())
			for i := range argEqs {
				pieces[i] = argEqs[i].Conclusion()
			}
			fwd = ConclANDRecursive(pieces...)
			for _, ae := range argEqs {
				fwd = fwd.DeriveHypFrom(ae)
			}
		}

		// BACKWARD: ⋀ lᵢ=rᵢ ⊢ Cⱼ(l)=Cⱼ(r) — congruence over the
		// constructor application.
		var pieces []Term
		for i := range l {
			pieces = append(pieces, WrapTerm(Term(l[i])).Eq(r[i]).Core())
		}
		var conjT Term
		if len(pieces) == 1 {
			conjT = pieces[0]
		} else {
			conjT = pieces[0]
			for _, p := range pieces[1:] {
				conjT = WrapTerm(conjT).And(p).Core()
			}
		}
		var projs []*PropWrapper
		if len(pieces) == 1 {
			projs = []*PropWrapper{WrapProp(core.Assume(conjT))}
		} else {
			projs = prop.HypANDRecursive(pieces...)
		}
		bwd := WrapProp(core.Refl(Term(md.Ctors[j])))
		for i := range l {
			bwd = bwd.Apply(projs[i])
		}

		iff := bwd.Deduct(fwd)
		// Deduct: {bwd-hyps minus fwd-concl?} — orientation: we want
		// (Cⱼ(l)=Cⱼ(r)) ⇔ conj. fwd: {eqTerm} ⊢ conj; bwd: {conj} ⊢ eqTerm.
		// t0.Deduct(t1): {h0}, r ⊢ l & {h1}, l ⊢ r → l = r with l =
		// t0's concl. bwd.Deduct(fwd): l := eqTerm (bwd concl), r :=
		// conj (fwd concl) → eqTerm ⇔ conj ✓.
		clause := iff
		for i := len(r) - 1; i >= 0; i-- {
			clause = clause.ConclForAll(r[i])
		}
		for i := len(l) - 1; i >= 0; i-- {
			clause = clause.ConclForAll(l[i])
		}
		clauses = append(clauses, clause)
	}

	final := clauses[0]
	if len(clauses) > 1 {
		terms := make([]Term, len(clauses))
		for i, cw := range clauses {
			terms[i] = cw.Conclusion()
		}
		final = ConclANDRecursive(terms...)
		for _, cw := range clauses {
			final = final.DeriveHypFrom(cw)
		}
	}
	if !final.AlphaEquals(stmt) {
		panic(fmt.Sprintf("DeriveDataInj: derived %s ≠ statement %s — kit drift",
			PrintProp(final), PrintProp(stmt)))
	}
	return final, nil
}

// DeriveDataDistinct derives the constructors-distinct theorem
// (md.DistinctStmt()).
func DeriveDataDistinct(env *ProverEnv, md *MintedDatatype) (Prop, error) {
	d := newDataDeriver(env, md)
	dd := md.Def
	stmt := md.DistinctStmt()
	if stmt == nil {
		return nil, fmt.Errorf("define data: %s has a single constructor — no DISTINCT theorem", dd.TypeName)
	}
	notSucRow, err := d.libRow("suc_not_zero")
	if err != nil {
		return nil, err
	}
	// Condition suc_not_zero to the freed-variable form and read its
	// orientation: the corpus serves ∀n. 0 ≠ suc(n); a free-variable
	// suc(n) ≠ 0 arrangement is absorbed the same way.
	notSuc := stripRow(notSucRow)
	nsMatrix := MatchesNOT(notSuc.Conclusion())
	if nsMatrix == nil {
		return nil, fmt.Errorf("define data: suc_not_zero row shape unexpected: %s", PrintProp(notSucRow))
	}
	nsL, nsR, nsOk := MatchesEQ(nsMatrix)
	if !nsOk {
		return nil, fmt.Errorf("define data: suc_not_zero row shape unexpected: %s", PrintProp(notSucRow))
	}
	isSucApp := func(t Term) bool {
		head, args := MatchesApply(t)
		c, isConst := head.AsConst()
		return isConst && c.Name() == "suc" && len(args) == 1
	}
	nsZeroFirst := !isSucApp(nsL)
	nsSucSide := nsL
	if nsZeroFirst {
		nsSucSide = nsR
	}
	_, nsSucArgs := MatchesApply(nsSucSide)
	nsVar, nsIsVar := nsSucArgs[0].AsVar()
	if !nsIsVar {
		return nil, fmt.Errorf("define data: suc_not_zero row shape unexpected: %s", PrintProp(notSucRow))
	}

	var sucInj *PropWrapper
	var siVarL, siVarR VarTerm
	var siBareLeft bool
	if len(dd.Ctors) > 2 {
		sucInjRow, err := d.libRow("suc_injective")
		if err != nil {
			return nil, err
		}
		// Condition suc_injective: freed form, and note which ⇔-side carries
		// the suc applications (the corpus serves (n=m) ⇔ (suc n = suc m)).
		sucInj = stripRow(sucInjRow)
		siL, siR, siOk := MatchesEQ(sucInj.Conclusion())
		if !siOk {
			return nil, fmt.Errorf("define data: suc_injective row shape unexpected: %s", PrintProp(sucInjRow))
		}
		sucSide := siR
		siBareLeft = true
		if sl, _, isEq := MatchesEQ(siL); isEq && isSucApp(sl) {
			sucSide = siL
			siBareLeft = false
		}
		ssl, ssr, ssOk := MatchesEQ(sucSide)
		if !ssOk {
			return nil, fmt.Errorf("define data: suc_injective row shape unexpected: %s", PrintProp(sucInjRow))
		}
		_, la := MatchesApply(ssl)
		_, ra := MatchesApply(ssr)
		var okL, okR bool
		siVarL, okL = la[0].AsVar()
		siVarR, okR = ra[0].AsVar()
		if !okL || !okR {
			return nil, fmt.Errorf("define data: suc_injective row shape unexpected: %s", PrintProp(sucInjRow))
		}
	}

	var clauses []*PropWrapper
	for j := range dd.Ctors {
		for j2 := j + 1; j2 < len(dd.Ctors); j2++ {
			l := md.ctorArgVars(j, "")
			r := md.ctorArgVars(j2, "'")
			eqTerm := WrapTerm(md.ctorApp(j, l)).Eq(md.ctorApp(j2, r)).Core()
			eqW := WrapProp(core.Assume(eqTerm))

			destEq := d.destCtorEq(j, termsOf(l)).EqSym().
				EqTrans(eqW.LeftApply(md.Dest)).
				EqTrans(d.destCtorEq(j2, termsOf(r)))
			idx1, pay1, subs1, _ := d.encPieces(j, termsOf(l))
			idx2, pay2, subs2, _ := d.encPieces(j2, termsOf(r))
			inj, err := d.constrInjInstance(idx1, pay1, subs1, idx2, pay2, subs2)
			if err != nil {
				return nil, err
			}
			// The index equation is the conjunction's FIRST leaf,
			// projected without assuming an association (conjLeaf).
			idxEq := conjLeaf(inj.EqMP(destEq), 0)
			// idxEq: {Cⱼ(l)=Cⱼ'(r)} ⊢ sucʲ(0) = sucʲ'(0), j < j2.
			// Strip j SUCs via suc_injective, then contradict suc_not_zero.
			for s := 0; s < j; s++ {
				lIdx, rIdx, okEq := MatchesEQ(idxEq.Conclusion())
				Assert(okEq)
				_, lA := MatchesApply(lIdx)
				_, rA := MatchesApply(rIdx)
				inst := sucInj.TermInst(
					MakeTermSubst(siVarL, lA[0]), MakeTermSubst(siVarR, rA[0]))
				if siBareLeft {
					// (l' = r') ⇔ (suc l' = suc r'): flip to strip.
					inst = inst.EqSym()
				}
				idxEq = inst.EqMP(idxEq)
			}
			// Now: 0 = suc^(j2-j)(0); orient to the suc_not_zero row's
			// arrangement and contradict.
			if !nsZeroFirst {
				idxEq = idxEq.EqSym()
			}
			eqConcl := idxEq.Conclusion()
			eqL, eqR, eqOk := MatchesEQ(eqConcl)
			Assert(eqOk)
			sucTerm := eqL
			if nsZeroFirst {
				sucTerm = eqR
			}
			_, sucArgs := MatchesApply(sucTerm)
			Assert(len(sucArgs) == 1)
			notInst := notSuc.TermInst(MakeTermSubst(nsVar, sucArgs[0]))
			falsum := prop.Contradict(eqConcl).
				DeriveHypFrom(notInst).
				DeriveHypFrom(idxEq)
			clause := falsum.NegHyp(eqTerm)
			for i := len(r) - 1; i >= 0; i-- {
				clause = clause.ConclForAll(r[i])
			}
			for i := len(l) - 1; i >= 0; i-- {
				clause = clause.ConclForAll(l[i])
			}
			clauses = append(clauses, clause)
		}
	}

	final := clauses[0]
	if len(clauses) > 1 {
		terms := make([]Term, len(clauses))
		for i, cw := range clauses {
			terms[i] = cw.Conclusion()
		}
		final = ConclANDRecursive(terms...)
		for _, cw := range clauses {
			final = final.DeriveHypFrom(cw)
		}
	}
	if !final.AlphaEquals(stmt) {
		panic(fmt.Sprintf("DeriveDataDistinct: derived %s ≠ statement %s — kit drift",
			PrintProp(final), PrintProp(stmt)))
	}
	return final, nil
}

// DeriveDataTheorem dispatches one derived-theorem kind.
func DeriveDataTheorem(env *ProverEnv, md *MintedDatatype, k DataTheoremKind) (Prop, error) {
	switch k {
	case DataInduct:
		return DeriveDataInduct(env, md)
	case DataRecursion:
		return DeriveDataRecursion(env, md)
	case DataInj:
		return DeriveDataInj(env, md)
	case DataDistinct:
		return DeriveDataDistinct(env, md)
	}
	return nil, fmt.Errorf("define data: unknown theorem kind %v", k)
}
