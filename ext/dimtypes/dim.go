// Package dimtypes is the dimension-expression phantom framework — the
// typed surface for term-level-dimensioned carriers (vectors, matrices,
// maps between vector spaces), where the dimension of a value rides a Go
// type parameter while the kernel sees an ordinary num-typed TERM. The
// tenants are proofs/vector (every member's vectors are `*Vec[Real,
// DimN]` parameters; the generated cites write the dimension off them)
// and proofs/cartesian/carrier; the proof layer's half — anchoring a
// letter to a section's own binder, pairing a vector with its membership
// — is prover/proof/vec.go.
//
// The layer models the observation it is built on: a dimension in a
// statement is always a GIVEN expression — a letter (`n`), a literal, a
// sum or product of those — never a value computed at proof runtime. A
// closed grammar of given expressions is exactly what a phantom
// vocabulary can spell, so each dimension expression is one Go type,
// and dimension agreement between values is checked by the compiler at
// authoring time.
//
// One dimension the grammar does not spell is the term a PROOF holds a
// vector at without a letter of its own — a Let, `suc(m)`, a degree.
// That vector rides SomeDim, anchored at the term itself (VecAt) or at
// the dimension its membership fact spells (prover/proof's
// InhabitFrom); two SomeDim values have no compile-time tie, and the
// cite's SameDimension check is what ties them.
//
// This is a REFINEMENT vocabulary, deliberately unlike ext's
// TypePhantom: every phantom here reifies to a TERM (`core.Term` of
// type num), not to a HOL type, and two wrappers differing only in
// their dimension phantom wrap terms of the SAME HOL type. The Go
// layer is therefore stricter than the kernel — that is its entire
// point — and dropping the refinement is one explicit step: the
// term Core() yields.
//
// Two consequences of "dimensions are terms", pinned here because they
// shaped the design:
//
//   - Reification must produce POINTER-CANONICAL constants. A `+` built
//     from a fresh ConstTermMeta is a different constant from the
//     engine's `+` even at the same name and type, so SpecTerm lowers
//     through the dsl layer's canonical num metas (NatPlusMeta,
//     NatStarMeta) and ext.MakeNumeral — never through metas of its
//     own.
//
//   - Recasting a BARE wrapper between provably-equal dimension spellings
//     (Plus[DimM, DimN] vs Plus[DimN, DimM]) needs NO kernel evidence. The phantom
//     never reaches the kernel, so a recast moves no term; its only
//     obligation is that the two spellings denote the same number, and
//     the grammar keeps that inside linear arithmetic, where a
//     normal-form comparison is a complete decision procedure. The
//     kernel-level cost of a recast (an `m + n = n + m` rewrite where
//     the dimension occurs inside a statement) falls on the statement's
//     own proof, where it belongs. Evidence-bearing domain wrappers may
//     layer exactly that transport on top (carrier.InhabitedVec does).
package dimtypes

import (
	"fmt"
	"math/big"
	"sort"
	"strconv"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
)

// ─────────────────────────── the spec tree ───────────────────────────

// DimSpec is the value-level shape of a dimension expression: what a
// phantom reports about itself, and the single input to both
// interpretations (the term it denotes, and the normal form that
// decides equality). Sealed — the grammar IS the soundness boundary of
// SameDim, so no outside node kind may join it.
type DimSpec interface{ isDimSpec() }

// SpecLit is a literal dimension.
type SpecLit struct{ N uint64 }

// SpecVar is a dimension letter: a free num-typed variable, given by
// name.
type SpecVar struct{ Name string }

// SpecAdd is the sum of two dimension expressions.
type SpecAdd struct{ L, R DimSpec }

// SpecMul is the product of two dimension expressions.
type SpecMul struct{ L, R DimSpec }

// SpecSome is the dimension a value is anchored at by its TERM, with
// no spelling in the grammar: SomeDim's spec. A leaf only — nothing is
// known of it to normalize, so it joins no sum or product.
type SpecSome struct{}

func (SpecLit) isDimSpec()  {}
func (SpecVar) isDimSpec()  {}
func (SpecAdd) isDimSpec()  {}
func (SpecMul) isDimSpec()  {}
func (SpecSome) isDimSpec() {}

// mentionsSome reports whether a spec is, or contains, SpecSome.
func mentionsSome(s DimSpec) bool {
	switch v := s.(type) {
	case SpecSome:
		return true
	case SpecAdd:
		return mentionsSome(v.L) || mentionsSome(v.R)
	case SpecMul:
		return mentionsSome(v.L) || mentionsSome(v.R)
	}
	return false
}

// spellSpec prints a spec for a message: its term, or "some" for
// SpecSome, which has none to lower.
func spellSpec(s DimSpec) string {
	if mentionsSome(s) {
		return "some"
	}
	return ext.PrintTerm(SpecTerm(s))
}

// ─────────────────────────── the phantoms ───────────────────────────

// DimPhantom is the constraint of the dimension vocabulary: a
// zero-size Go type whose Spec reports the dimension expression it
// stands for. The mirror of ext.TypePhantom, one level down — a
// phantom for a term, not a type.
type DimPhantom interface{ Spec() DimSpec }

// SpecOf reifies a dimension phantom to its spec — the one bridge from
// the type level to the value level, mirroring ext.HolTypeOf.
func SpecOf[D DimPhantom]() DimSpec {
	var d D
	return d.Spec()
}

// DimN, DimM and DimK are the dimension LETTERS — the "arbitrary n" of
// a ∀-quantified dimension, reifying to the free variables `n`, `m`, `k`
// of type num. The alphabet is name-fixed by design (a Go type cannot
// capture a runtime name); the names are full ones so that the bare
// capitals stay the statement letters' phantoms. A chapter needing a
// letter beyond these declares it beside its own vocabulary the same
// three-line way.
type (
	DimN struct{}
	DimM struct{}
	DimK struct{}
)

func (DimN) Spec() DimSpec { return SpecVar{"n"} }
func (DimM) Spec() DimSpec { return SpecVar{"m"} }
func (DimK) Spec() DimSpec { return SpecVar{"k"} }

// SomeDim is the dimension no letter spells: a vector at it is anchored
// at a given num term (VecAt) — a Let, a literal, `suc(m)`, a degree —
// and Dim() is that term. Two SomeDim values are distinct dimensions as
// far as the compiler knows, and the cite's SameDimension check is what
// ties them; the letters keep the compile-time tie for a statement whose
// dimension is a binder. Nothing resolves it by name: the letter doors
// (AnchorVec, the section binder) refuse it.
type SomeDim struct{}

func (SomeDim) Spec() DimSpec { return SpecSome{} }

// D0…D4 are literal dimensions. Geometry rarely needs more; a further
// literal is a two-line declaration.
type (
	D0 struct{}
	D1 struct{}
	D2 struct{}
	D3 struct{}
	D4 struct{}
)

func (D0) Spec() DimSpec { return SpecLit{0} }
func (D1) Spec() DimSpec { return SpecLit{1} }
func (D2) Spec() DimSpec { return SpecLit{2} }
func (D3) Spec() DimSpec { return SpecLit{3} }
func (D4) Spec() DimSpec { return SpecLit{4} }

// Plus and Times are the composite dimension expressions, recursing
// through their phantom arguments like ext.Fun does.
type Plus[A, B DimPhantom] struct{}

func (Plus[A, B]) Spec() DimSpec { return SpecAdd{SpecOf[A](), SpecOf[B]()} }

type Times[A, B DimPhantom] struct{}

func (Times[A, B]) Spec() DimSpec { return SpecMul{SpecOf[A](), SpecOf[B]()} }

// IsPlus pins its implementer to exactly Plus[A, B]: the exact-type
// constraint that carries a composite dimension through a method
// signature where spelling it directly would be an instantiation
// cycle (utils/generic_test.go pins the wall and the smuggle;
// RealVec.Concat is the tenant here).
type IsPlus[A, B DimPhantom] interface {
	DimPhantom
	Plus[A, B]
}

// ─────────────────────────── reification ───────────────────────────

// TermOf reifies a dimension phantom to the num-typed term it denotes.
// This is where a dimension leaves the Go type level: as an ordinary
// argument or witness slot in a statement, built from the canonical
// constant metas only.
func TermOf[D DimPhantom]() core.Term { return SpecTerm(SpecOf[D]()) }

// SpecTerm lowers a spec to its term. Letters become free variables of
// type num; literals become the canonical bare BIT-tower; sums and
// products apply the dsl layer's canonical num operators.
func SpecTerm(s DimSpec) core.Term {
	return SpecTermWith(s, func(name string) core.Term { return core.Var(name, ext.NumType) })
}

// SpecTermWith is SpecTerm with the LETTERS supplied by the caller:
// letter(name) is the num-typed term the letter denotes — inside a
// section, the statement's own binder as the section minted it (`n` or
// `n_0`), which the proof layer resolves through its surface names.
// This is how a dimension label is ANCHORED (AnchorVec) rather than
// bare-reified.
func SpecTermWith(s DimSpec, letter func(name string) core.Term) core.Term {
	switch v := s.(type) {
	case SpecLit:
		return ext.MakeNumeral(new(big.Int).SetUint64(v.N))
	case SpecSome:
		panic("dimtypes: SomeDim carries no spelling to lower — a vector at it is anchored by its term (VecAt) or by its membership fact (proof.InhabitFrom), never by name")
	case SpecVar:
		t := letter(v.Name)
		if t == nil || !t.Type().Equals(ext.NumType) {
			panic(fmt.Sprintf("dimtypes: the dimension letter %s does not denote a num-typed term in scope", v.Name))
		}
		return t
	case SpecAdd:
		return core.Apply(core.Apply(dsl.NatPlusMeta.Term(), SpecTermWith(v.L, letter)), SpecTermWith(v.R, letter))
	case SpecMul:
		return core.Apply(core.Apply(dsl.NatStarMeta.Term(), SpecTermWith(v.L, letter)), SpecTermWith(v.R, letter))
	}
	panic(fmt.Sprintf("dimtypes.SpecTermWith: unknown spec node %T", s))
}

// Letters lists the distinct letters a spec mentions, in first-occurrence
// order — what an anchoring site must resolve.
func Letters(s DimSpec) []string {
	var out []string
	seen := map[string]bool{}
	var walk func(DimSpec)
	walk = func(s DimSpec) {
		switch v := s.(type) {
		case SpecVar:
			if !seen[v.Name] {
				seen[v.Name] = true
				out = append(out, v.Name)
			}
		case SpecAdd:
			walk(v.L)
			walk(v.R)
		case SpecMul:
			walk(v.L)
			walk(v.R)
		}
	}
	walk(s)
	return out
}

// ─────────────────────── the equality decision ───────────────────────

// A dimension expression is a polynomial over the letters with natural
// coefficients, and the grammar (letters, literals, +, ×) cannot leave
// that fragment — so equality of dimension expressions is decided
// completely by comparing expanded normal forms: monomial → coefficient,
// a monomial being the sorted multiset of its letters. The map key uses
// a length-prefixed encoding of that multiset rather than mathematical
// pretty-printing: letter names are public vocabulary, so a delimiter
// spelling such as `m*n` must remain ONE letter and never collide with
// the product of the two letters `m` and `n`.

type monomialKey string

// encodeMonomial is an injective encoding of a sorted letter multiset.
// Each factor is byte-length-prefixed (`3:m*n`), so every possible Go
// string — including the empty string and names containing `*`/`:` —
// remains unambiguous. The empty factor list encodes the constant term.
func encodeMonomial(factors []string) monomialKey {
	var b strings.Builder
	for _, factor := range factors {
		b.WriteString(strconv.Itoa(len(factor)))
		b.WriteByte(':')
		b.WriteString(factor)
	}
	return monomialKey(b.String())
}

func decodeMonomial(key monomialKey) []string {
	s := string(key)
	var factors []string
	for len(s) > 0 {
		colon := strings.IndexByte(s, ':')
		if colon < 0 {
			panic("dimtypes: corrupt monomial key")
		}
		n, err := strconv.Atoi(s[:colon])
		if err != nil || n < 0 || len(s)-colon-1 < n {
			panic("dimtypes: corrupt monomial key")
		}
		s = s[colon+1:]
		factors = append(factors, s[:n])
		s = s[n:]
	}
	return factors
}

func normalForm(s DimSpec) map[monomialKey]*big.Int {
	acc := map[monomialKey]*big.Int{}
	switch v := s.(type) {
	case SpecLit:
		if v.N != 0 {
			acc[encodeMonomial(nil)] = new(big.Int).SetUint64(v.N)
		}
	case SpecVar:
		acc[encodeMonomial([]string{v.Name})] = big.NewInt(1)
	case SpecSome:
		panic("dimtypes: SomeDim is a leaf dimension — it joins no sum or product")
	case SpecAdd:
		for _, side := range []DimSpec{v.L, v.R} {
			for mono, c := range normalForm(side) {
				addInto(acc, mono, c)
			}
		}
	case SpecMul:
		l, r := normalForm(v.L), normalForm(v.R)
		for lm, lc := range l {
			for rm, rc := range r {
				addInto(acc, mulMonomials(lm, rm), new(big.Int).Mul(lc, rc))
			}
		}
	default:
		panic(fmt.Sprintf("dimtypes.normalForm: unknown spec node %T", s))
	}
	return acc
}

func addInto(acc map[monomialKey]*big.Int, mono monomialKey, c *big.Int) {
	if prev, ok := acc[mono]; ok {
		prev.Add(prev, c)
		return
	}
	acc[mono] = new(big.Int).Set(c)
}

func mulMonomials(a, b monomialKey) monomialKey {
	letters := append(decodeMonomial(a), decodeMonomial(b)...)
	sort.Strings(letters)
	return encodeMonomial(letters)
}

// DenotesTerm reports whether t is a term the spec denotes, with the
// LETTER leaves delegated to the caller: letter(name, v) decides
// whether the num variable v may stand for the letter named `name`.
// The delegation is the point — a letter's contract is "the dimension
// the statement spells n", and what that means inside a live proof
// (Skolem subscripting, a surface-name registration) is the proof
// layer's knowledge, not this grammar's.
//
// Letter identity itself remains this grammar's responsibility: within
// ONE traversal, every occurrence of the same SpecVar name must map to
// the same actual VarTerm. The callback is consulted only for the first
// occurrence; later occurrences are checked against the binding recorded
// there. Thus Plus[DimN,DimN] may denote n_0+n_0 but never n_0+n_1 even when
// the proof layer recognizes both variables as Skolem spellings of `n`.
//
// Literals and the two operators are compared structurally against the
// canonical lowering, so a true answer means t is the spec's own shape,
// under one consistent letter substitution — never a merely equal value.
func DenotesTerm(s DimSpec, t core.Term, letter func(name string, v core.VarTerm) bool) bool {
	_, ok := LetterBindings(s, t, letter)
	return ok
}

// LetterBindings is DenotesTerm returning the letter → variable map the
// traversal established — what an anchoring site reads the letters'
// terms off when the dimension term arrives from a fact rather than
// from the scope's names (carrier's Inhabit).
func LetterBindings(s DimSpec, t core.Term, letter func(name string, v core.VarTerm) bool) (map[string]core.VarTerm, bool) {
	bindings := map[string]core.VarTerm{}
	if !denotesTerm(s, t, letter, bindings) {
		return nil, false
	}
	return bindings, true
}

func denotesTerm(s DimSpec, t core.Term, letter func(name string, v core.VarTerm) bool,
	bindings map[string]core.VarTerm) bool {
	switch v := s.(type) {
	case SpecLit:
		return SpecTerm(v).Equals(t)
	case SpecSome:
		return t.Type().Equals(ext.NumType)
	case SpecVar:
		vt, ok := t.(core.VarTerm)
		if !ok || !vt.Type().Equals(ext.NumType) {
			return false
		}
		if bound, exists := bindings[v.Name]; exists {
			return bound.Equals(vt)
		}
		if !letter(v.Name, vt) {
			return false
		}
		bindings[v.Name] = vt
		return true
	case SpecAdd:
		return denotesBinary(dsl.NatPlusMeta, v.L, v.R, t, letter, bindings)
	case SpecMul:
		return denotesBinary(dsl.NatStarMeta, v.L, v.R, t, letter, bindings)
	}
	panic(fmt.Sprintf("dimtypes.DenotesTerm: unknown spec node %T", s))
}

func denotesBinary(meta core.ConstTermMeta, l, r DimSpec, t core.Term,
	letter func(name string, v core.VarTerm) bool, bindings map[string]core.VarTerm) bool {
	outer, ok := t.AsAppliedTerm()
	if !ok {
		return false
	}
	inner, ok := outer.Fun().AsAppliedTerm()
	if !ok {
		return false
	}
	c, ok := inner.Fun().AsConst()
	if !ok || c.Meta() != meta {
		return false
	}
	return denotesTerm(l, inner.Arg(), letter, bindings) &&
		denotesTerm(r, outer.Arg(), letter, bindings)
}

// SameDim reports whether two dimension phantoms denote the same
// number for every valuation of the letters. Complete for the
// vocabulary's grammar: a false answer means the dimensions genuinely
// differ (at some valuation), not that the checker gave up. SomeDim is
// equal to itself alone — anchored at a term the grammar never sees,
// it matches no spelling — and a composite over it is refused.
func SameDim[A, B DimPhantom]() bool {
	sa, sb := SpecOf[A](), SpecOf[B]()
	_, someA := sa.(SpecSome)
	_, someB := sb.(SpecSome)
	if someA || someB {
		return someA && someB
	}
	a, b := normalForm(sa), normalForm(sb)
	if len(a) != len(b) {
		return false
	}
	for mono, c := range a {
		d, ok := b[mono]
		if !ok || c.Cmp(d) != 0 {
			return false
		}
	}
	return true
}

// mustSameDim is the recast gate: relabeling a value's dimension
// phantom is sound exactly when the two spellings denote the same
// number, and a spelling pair outside that is a proof-authoring bug —
// so it panics, naming both terms.
func mustSameDim[A, B DimPhantom]() {
	if !SameDim[A, B]() {
		panic(fmt.Sprintf("dimtypes: recast between unequal dimensions %s and %s",
			spellSpec(SpecOf[A]()), spellSpec(SpecOf[B]())))
	}
}
