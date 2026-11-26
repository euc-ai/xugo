package core

import (
	"cmp"
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/utils"
)

// ConstTermMeta is a constant: its name, its abstract type, and what
// defines it. It is a handle over a node only this package can reach
// (see VarType).
type ConstTermMeta struct{ *_ConstTermMetaNode }

type _ConstTermMetaNode struct {
	name TermName
	// This is the abstract type of the const term. It matches (but not necessarily
	// equals) the type of the const term. E.g. the abstract type is A->A and the type
	// of the const term might be A->A or bool->bool, but cannot be A->bool.
	absType HolType

	// The definition of this term, if it is defined from NewConstDef, in the form of
	// ⊢ c (this const term) = t (the term it is defined on).
	// The type of the t is always the abstract type.
	// Nil for basic consts (=, ε) AND for consts from NewTypeDef — the latter
	// use `defSource` + `TypeDefExpand` instead.
	def ThmCert

	// For NewTypeDef consts (both abs and rep), this is the Prop form of the
	// existence theorem ⊢ P(_) that was used to define the type — the kernel
	// value NewTypeDef read its input through, never a wrapper. It is a Prop
	// rather than a Thm because from deserialization code we cannot reconstruct
	// the Thm without trusting bytes — and we don't need to: the Thm form is
	// only required when the caller already holds a proved version of it (which
	// they pass to TypeDefExpand).
	//
	// Nil for NewConstDef consts and for basic consts.
	defSource Prop

	// For a NewTypeDef abs-const: the paired rep-const's meta.
	// For all other kinds of const (rep, NewConstDef, basic): the zero handle.
	// Asymmetry is deliberate — the two halves of a type definition are
	// distinguishable (abs : old→new vs rep : new→old) and encoding which side
	// this meta represents via which field is set makes misuse caught early.
	repMeta ConstTermMeta

	// For a NewTypeDef rep-const: the paired abs-const's meta.
	// For all other kinds of const: the zero handle.
	absMeta ConstTermMeta

	// If the abstract type contains no var type,
	// the const term is uniquely determined by its meta.
	// In that case it is put here. Otherwise it is the zero handle.
	term ConstTerm
}

func MakeConstMeta[Name ~string](name Name, absType HolType) ConstTermMeta {
	absType = absType.core()
	meta := ConstTermMeta{&_ConstTermMetaNode{
		name:    TermName(name),
		absType: absType}}
	// If the abs type contains no var type, the const term itself is fully determined.
	// We put the const term here in that case.
	if len(absType.TypeVars()) == 0 {
		meta.term = ConstTerm{&_ConstTermNode{
			meta:    meta,
			holType: absType}}
	}
	return meta
}

// IsZero reports whether c is the zero handle.
func (c ConstTermMeta) IsZero() bool { return c._ConstTermMetaNode == nil }

func (c ConstTermMeta) Name() TermName { return c.name }

func (c ConstTermMeta) AbsType() HolType { return c.absType }

// Returns the const term if it is fully determined by its meta.
// Otherwise returns the zero ConstTerm.
func (c ConstTermMeta) Term() ConstTerm { return c.term }

// DefThm returns the definition ⊢ c = t of a const NewConstDef
// introduced, and the zero ThmCert for any other.
func (c ConstTermMeta) DefThm() ThmCert { return c.def }

// DefSource returns the ⊢ P(_) proposition that defines this const, for
// consts introduced by NewTypeDef. Returns nil for NewConstDef consts and
// for basic consts.
func (c ConstTermMeta) DefSource() Prop { return c.defSource }

// IsTypeDefAbs reports whether this meta is the abs-half of a NewTypeDef pair.
func (c ConstTermMeta) IsTypeDefAbs() bool { return !c.repMeta.IsZero() }

// IsTypeDefRep reports whether this meta is the rep-half of a NewTypeDef pair.
func (c ConstTermMeta) IsTypeDefRep() bool { return !c.absMeta.IsZero() }

// TypeDefCounterpart returns the paired meta for a NewTypeDef const.
// For an abs-const, returns the rep; for a rep-const, returns the abs.
// Returns the zero handle for non-type-def consts.
func (c ConstTermMeta) TypeDefCounterpart() ConstTermMeta {
	if !c.repMeta.IsZero() {
		return c.repMeta
	}
	return c.absMeta
}

// TypeDefExpand returns the two type-definition consequences of the input
// proposition `p` for a const introduced by NewTypeDef:
//
//	out1 = abs(rep a) = a
//	out2 = P(r) = (rep(abs r) = r)
//
// Can be called on either the abs-meta or the rep-meta; orientation is
// recovered from the meta's own repMeta / absMeta field.
//
// The input `p`, read through its kernel value, must α-equal this const's
// stored `defSource`. The outputs
// carry p's provedness through deriveProp: a Proved p lifts both to ThmCert; a
// promise p threads through as derived promises (realized when p is forced); a
// bare unproved p yields plain Props. This is the same "provedness-through-
// operator" pattern used by the other primitives.
//
// Panics if called on a non-NewTypeDef const.
func (c ConstTermMeta) TypeDefExpand(p Prop) (Prop, Prop) {
	p = p.kernel()
	utils.Assert(c.defSource != nil)
	utils.Assert(p.AlphaEquals(c.defSource))

	// Recover abs/rep orientation from the pair pointers.
	var absMeta, repMeta ConstTermMeta
	switch {
	case !c.repMeta.IsZero():
		absMeta, repMeta = c, c.repMeta
	case !c.absMeta.IsZero():
		absMeta, repMeta = c.absMeta, c
	default:
		panic("TypeDefExpand: NewTypeDef meta without paired counterpart")
	}

	s, ok := p.Conclusion().(AppliedTerm)
	utils.Assert(ok)

	// abs has type oldType -> newType, so:
	absFunType := absMeta.absType.(CompositeType)
	repVarType := absFunType.SubType(0) // old (underlying representation)
	absVarType := absFunType.SubType(1) // new (abstract)

	absVar := Var("a", absVarType)
	repVar := Var("r", repVarType)
	absConst := MakeConstTerm(absMeta, absMeta.absType)
	repConst := MakeConstTerm(repMeta, repMeta.absType)

	// ⊢ abs(rep a) = a
	concl1 := Eq(Apply(absConst, Apply(repConst, absVar)), absVar)
	// ⊢ P(r) = (rep(abs r) = r)
	concl2 := Eq(Apply(s.fun, repVar),
		Eq(Apply(repConst, Apply(absConst, repVar)), repVar))

	// deriveProp carries p's provedness through: Proved → ThmCert, promise →
	// derived promise (dep = p), bare → plain Prop. Behavior-identical to the
	// old explicit if/else for the first and last cases; the middle case is
	// what lets a promise-backed TypeDefExpand source thread on the
	// define-then-run path.
	return deriveProp(makeStatement(concl1, nil), p), deriveProp(makeStatement(concl2, nil), p)
}

// ConstTerm is a constant at one of its types. It is a handle over a
// node only this package can reach (see VarType).
type ConstTerm struct{ *_ConstTermNode }

type _ConstTermNode struct {
	meta ConstTermMeta
	// The real type of the term.
	// It is a particular case of the abstract type in the meta,
	// e.g. the abstract type is A->A, this type can be bool->bool but not bool->(bool->bool).
	// If the abstract type contains no var type, this type must equal the abstract type.
	holType HolType

	// The substitutions between the type of the const term and its meta.
	// Useful for returning the def thm of the const term.
	typeSubsts []TypeSubst

	// Term key. Lazily calculated.
	lazyKey utils.Lazy[TermKey]
}

// Make const term with meta and type.
func MakeConstTerm(meta ConstTermMeta, holType HolType) ConstTerm {
	utils.Assert(!meta.IsZero())
	holType = holType.core()
	// If the const term is already fully determined by the meta, simply return it.
	if !meta.term.IsZero() {
		utils.Assert(holType.Equals(meta.absType))
		return meta.term
	}

	if meta.absType.Equals(holType) {
		return ConstTerm{&_ConstTermNode{
			meta:    meta,
			holType: meta.absType}}
	}
	// If the meta contains var type, we need to make sure the specified type
	// matches the abs type.
	typeSubsts, ok := meta.absType.Matches(holType, utils.FullPredicate)
	utils.Assert(ok && len(typeSubsts) > 0)
	return ConstTerm{&_ConstTermNode{
		meta:       meta,
		holType:    holType,
		typeSubsts: typeSubsts}}
}

// IsZero reports whether t is the zero handle.
func (t ConstTerm) IsZero() bool { return t._ConstTermNode == nil }

func (t ConstTerm) Name() TermName { return t.meta.name }

func (t ConstTerm) Meta() ConstTermMeta { return t.meta }

func (t ConstTerm) Type() HolType { return t.holType }

// TypeSubsts returns the type substitutions applied to the const's abstract type,
// in a slice of the caller's own.
// Empty slice means no instantiation beyond the abstract type.
func (t ConstTerm) TypeSubsts() []TypeSubst { return slices.Clone(t.typeSubsts) }

func (ConstTerm) Size() int { return 1 }

// Equals reports whether two metas describe the same constant.
//
// INVARIANT: one const name = one meta per process. Distinct meta
// POINTERS for the same name are tolerated only when structurally
// identical (same absType spelling) — that happens benignly when two
// decoders each restore the same constant. Same-named metas whose
// abstract types differ — even by a mere type-variable renaming — are
// NOT equal-able: they come from a
// producer that bypassed the canonical registry (a scope/resolver
// leak), and letting them compare equal would make DefThm() and
// generic-instance AlphaKeys depend on which pointer the caller holds.
// That is a soundness-adjacent divergence, so it panics loudly instead
// (soundness > availability).
func (t ConstTermMeta) Equals(s ConstTermMeta) bool {
	if t == s {
		return true
	}
	if t.name == s.name {
		if !t.absType.Equals(s.absType) {
			panic(fmt.Sprintf(
				"ConstTermMeta.Equals: two metas for const %q with different "+
					"abstract types: %s vs %s — a producer minted a "+
					"non-canonical meta (scope/resolver leak)",
				t.name, t.absType.Key(), s.absType.Key()))
		}
		return true
	}
	return false
}

func (t ConstTerm) Equals(s Term) bool {
	if s, ok := s.AsConst(); ok {
		return t == s ||
			(t.meta.Equals(s.meta) && t.holType.Equals(s.holType))
	}
	return false
}

func (t ConstTerm) AlphaEquals(s Term) bool { return t.Equals(s) }

func (t ConstTerm) Compare(s Term) int { return t.CompareWithEnv(s, nil) }

func (t ConstTerm) AlphaKey() TermKey {
	return t.lazyKey.InitOrLoad(func() TermKey {
		return TermKey(fmt.Sprintf(
			"%s%s_%s", _CONST_TERM_KEY_PREFIX, t.meta.name, t.holType.Key()))
	})
}

func (t ConstTerm) key() TermKey { return t.AlphaKey() }

func (ConstTerm) Frees(VarPredicate) []VarTerm { return nil }

func (ConstTerm) HasFree(VarTerm) bool { return false }

func (ConstTerm) AllFree(VarPredicate) bool { return true }

func (ConstTerm) HasFreeName(n TermName) bool { return false }

func (t ConstTerm) HasName(n TermName) bool { return t.meta.name == n }

func (t ConstTerm) Substitute(...TermSubst) Term { return t }

func (t ConstTerm) TypeSubstitute(substs ...TypeSubst) Term {
	if !t.meta.term.IsZero() || len(substs) == 0 {
		return t
	}
	s, clashed := t.typeSubstituteImpl(substs, nil, nil)
	utils.Assert(clashed.IsZero())
	return s
}

func (t ConstTerm) DeBruijn(int) Term { return t }

func (t ConstTerm) AlphaEqualsWithEnv(s Term, _ []VarPair) bool { return t.Equals(s) }

func (t ConstTerm) Core() Term { return t }

func (t ConstTerm) kernel() Term {
	if t._ConstTermNode == nil {
		panic("core: the zero ConstTerm stands for no term")
	}
	return t
}

func (ConstTerm) AsVar() (VarTerm, bool) { return VarTerm{}, false }

func (t ConstTerm) AsConst() (ConstTerm, bool) { return t, true }

func (ConstTerm) AsAppliedTerm() (AppliedTerm, bool) { return AppliedTerm{}, false }

func (ConstTerm) AsAbsTerm() (AbsTerm, bool) { return AbsTerm{}, false }

func (t ConstTerm) typeVars() []VarType { return t.holType.TypeVars() }

func (t ConstTerm) CompareWithEnv(s Term, _ []VarPair) int {
	switch s := s.kernel().(type) {
	case ConstTerm:
		// Identity shortcuts. A monomorphic const has ONE object for all
		// its occurrences (MakeConstMeta pins meta.term), and a type is
		// shared across the consts that carry it, so the structural walk
		// below is re-deciding pointer-equal inputs. Both tests are taken
		// where the walk provably returns 0 — the type test only AFTER
		// the metas agree, since distinct consts share types (T and F
		// are both bool).
		if t == s {
			return 0
		}
		if t.meta.Equals(s.meta) {
			if t.holType == s.holType {
				return 0
			}
			return t.holType.Compare(s.holType)
		}
		return cmp.Compare(t.meta.name, s.meta.name)
	case VarTerm:
		return 1
	default:
		return -1
	}
}

func (t ConstTerm) substituteImpl([]TermSubst, _SubstituteMemo) (Term, bool) { return t, false }

// typeSubstituteImpl rewrites the constant's type under substs. A
// shared constant is rewritten once per region of the walk's memo, so
// the result keeps the term's sharing.
func (t ConstTerm) typeSubstituteImpl(
	substs []TypeSubst, _ []VarPair, memo _TypeSubstituteMemo) (Term, VarTerm) {
	if r, ok := memo[t]; ok {
		return r.term, VarTerm{}
	}
	term := Term(t)
	if newType := t.holType.Substitute(substs...); !newType.Equals(t.holType) {
		term = MakeConstTerm(t.meta, newType)
	}
	if memo != nil {
		memo[t] = _TypeSubstituted{term: term}
	}
	return term, VarTerm{}
}

func (t ConstTerm) deBruijnImpl(int, int, _DeBruijnMemo) Term { return t }

// DefThm returns the definition of the const at this term's type, and
// the zero ThmCert for a const NewConstDef did not introduce.
func (t ConstTerm) DefThm() ThmCert {
	if t.meta.def.IsZero() {
		return ThmCert{}
	}
	return PropTypeInst(t.meta.def, t.typeSubsts...).AsThmCert()
}
