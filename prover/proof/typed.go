// typed.go — the typed face of the proof surface: the verbs that mint
// or adopt ext.Expr[T] values, and the deferred explicit type
// instance that lets a theorem wrapper ground without a Script in
// scope.
//
// Every typed spelling maps 1:1 onto the untyped runtime call it
// replaces — same Fact contents, same install form, same recorded
// steps. The typed layer buys compile-time checking and inference,
// never a second grounding path: FixAs is fixImpl plus a type
// assertion, TermAs is Term's parse with the phantom's type as its
// expectation, Inst is Script.AtTypeVars deferred to consumption, and
// a wrapper's At body is the package-level At on the stripped terms.
//
// The verb set grows by demand: only INTRODUCTION verbs — result a
// term the body threads onward (Fix, Term, Let, Obtain, Unpack and
// their two- and three-witness twins; Binder is the reserve bench) —
// get typed variants, as the thin verb+ext.As composition.
// ext.As[φ](verb(…)) at a call site is the same value, and a member
// carrying that wrap is the promotion signal; the one difference is the
// text-reading verbs', TermAs and LetAs, whose expectation also
// instantiates a polymorphic constant the text leaves bare, where
// ext.As[φ](a.Term(…)) refuses it. Slice results (Skolemize) get no
// variant — their typed spelling is typed closure parameters or a
// FixAs chain. The judgment lives in
// library/chapter_constitution.md §"The typed surface".

package proof

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// FixAs is Fix asserting the binder's type: "let x:T be arbitrary",
// with T checked against the goal's actual binder at the Fix site —
// where the author's mental model and the statement first meet —
// instead of surfacing later as a confusing downstream mismatch. The
// optional surface name is Fix's: FixAs[T]("u") makes `u` the one
// claim-text spelling for the mint, loud when `u` already means
// something.
//
// Every verb below adopts through ext.As — the ONE gate into the
// typed world (Expr's storage is sealed, so there is no other
// construction path to duplicate the check in).
func (a *Argument) FixAs[T ext.TypePhantom](name ...string) *ext.Expr[T] {
	a.guard("FixAs")
	surface := fixName("FixAs", name)
	if surface != "" {
		a.assertSpellingFree("FixAs", surface)
	}
	return ext.As[T](a.fixImpl(surface))
}

// TermAs is Term read at the phantom's type. The parse sees the type as
// its expectation (family vocabulary and surface aliases as Term's), so
// a polymorphic constant the text leaves bare takes its instance from
// it — `TermAs[Set[A]]("∅")` is ∅ at set(A), with no `⟨A:A⟩` — and a
// text that cannot be read at the type is refused naming both types.
// ext.As still checks the result, the one gate into the typed world.
func (a *Argument) TermAs[T ext.TypePhantom](raw string) *ext.Expr[T] {
	return ext.As[T](a.termAt("TermAs", raw, ext.HolTypeOf[T]()))
}

// LetAs is Let read at the phantom's type, returning the name beside
// its definition: "let x:T := ⟨text⟩". The text is read as TermAs reads
// one, at T, so a polymorphic constant it leaves bare takes T's
// instance; the equation joins the hypotheses and the goal keeps its
// form, as under Let; and the name comes back adopted through ext.As —
// the handle a typed slot takes, where a claim text spells the name.
// The one verb for what was a Let followed by a TermAs of its own name.
//
//	tower, towerDef := a.LetAs[Set[Set[A]]]("tower", "{t:set(A) | set_tower(f, t)}")
//	inTower := a.Have("…", "∀s:set(A). s ∈ tower ⇔ set_tower(f, s)", BySets(towerDef))
func (a *Argument) LetAs[T ext.TypePhantom](name, text string) (*ext.Expr[T], Fact) {
	t := a.termAt("LetAs", text, ext.HolTypeOf[T]())
	v, d := a.letImpl("LetAs", name, t.Core())
	return ext.As[T](v), d
}

// ObtainAs is Obtain asserting the witness's type: "obtain w:T such
// that P(w)". Obtain's own contract — the claim is proved, then
// Skolemized, the minted name registered for later claim texts — and
// the witness adopted through ext.As, so a typed cite takes it without
// a cast at the site.
func (a *Argument) ObtainAs[T ext.TypePhantom](label string, claim any, proof ...Action) (*ext.Expr[T], Fact) {
	w, f := a.Obtain(label, claim, proof...)
	return ext.As[T](w), f
}

// Obtain2As is Obtain2 with both witnesses asserted at their types.
func (a *Argument) Obtain2As[T, U ext.TypePhantom](label string, claim any, proof ...Action) (*ext.Expr[T], *ext.Expr[U], Fact) {
	w1, w2, f := a.Obtain2(label, claim, proof...)
	return ext.As[T](w1), ext.As[U](w2), f
}

// Obtain3As is Obtain3 with the three witnesses asserted at their types.
func (a *Argument) Obtain3As[T, U, V ext.TypePhantom](label string, claim any, proof ...Action) (*ext.Expr[T], *ext.Expr[U], *ext.Expr[V], Fact) {
	w1, w2, w3, f := a.Obtain3(label, claim, proof...)
	return ext.As[T](w1), ext.As[U](w2), ext.As[V](w3), f
}

// Obtain4As is Obtain4 with the four witnesses asserted at their types.
func (a *Argument) Obtain4As[T, U, V, W ext.TypePhantom](
	label string, claim any, proof ...Action,
) (*ext.Expr[T], *ext.Expr[U], *ext.Expr[V], *ext.Expr[W], Fact) {
	w1, w2, w3, w4, f := a.Obtain4(label, claim, proof...)
	return ext.As[T](w1), ext.As[U](w2), ext.As[V](w3), ext.As[W](w4), f
}

// Obtain5As is Obtain5 with the five witnesses asserted at their types.
func (a *Argument) Obtain5As[T, U, V, W, X ext.TypePhantom](
	label string, claim any, proof ...Action,
) (*ext.Expr[T], *ext.Expr[U], *ext.Expr[V], *ext.Expr[W], *ext.Expr[X], Fact) {
	w1, w2, w3, w4, w5, f := a.Obtain5(label, claim, proof...)
	return ext.As[T](w1), ext.As[U](w2), ext.As[V](w3), ext.As[W](w4), ext.As[X](w5), f
}

// UnpackAs is Unpack asserting the witness's type: "write f as P(w)
// for some w:T", on a fact already established — with Unpack's optional
// name for the witness.
func (a *Argument) UnpackAs[T ext.TypePhantom](target any, name ...string) (*ext.Expr[T], Fact) {
	w, f := a.Unpack(target, name...)
	return ext.As[T](w), f
}

// Unpack2As is Unpack2 with both witnesses asserted at their types (and
// Unpack2's optional names).
func (a *Argument) Unpack2As[T, U ext.TypePhantom](target any, names ...string) (*ext.Expr[T], *ext.Expr[U], Fact) {
	w1, w2, f := a.Unpack2(target, names...)
	return ext.As[T](w1), ext.As[U](w2), f
}

// Unpack3As is Unpack3 with the three witnesses asserted at their types
// (and Unpack3's optional names).
func (a *Argument) Unpack3As[T, U, V ext.TypePhantom](target any, names ...string) (*ext.Expr[T], *ext.Expr[U], *ext.Expr[V], Fact) {
	w1, w2, w3, f := a.Unpack3(target, names...)
	return ext.As[T](w1), ext.As[U](w2), ext.As[V](w3), f
}

// Unpack4As is Unpack4 with the four witnesses asserted at their types
// (and Unpack4's optional names).
func (a *Argument) Unpack4As[T, U, V, W ext.TypePhantom](
	target any, names ...string,
) (*ext.Expr[T], *ext.Expr[U], *ext.Expr[V], *ext.Expr[W], Fact) {
	w1, w2, w3, w4, f := a.Unpack4(target, names...)
	return ext.As[T](w1), ext.As[U](w2), ext.As[V](w3), ext.As[W](w4), f
}

// Unpack5As is Unpack5 with the five witnesses asserted at their types
// (and Unpack5's optional names).
func (a *Argument) Unpack5As[T, U, V, W, X ext.TypePhantom](
	target any, names ...string,
) (*ext.Expr[T], *ext.Expr[U], *ext.Expr[V], *ext.Expr[W], *ext.Expr[X], Fact) {
	w1, w2, w3, w4, w5, f := a.Unpack5(target, names...)
	return ext.As[T](w1), ext.As[U](w2), ext.As[V](w3), ext.As[W](w4), ext.As[X](w5), f
}

// ConstAs is Script.Const with the instance type spelled as a phantom
// rather than assembled from MakeFun/MakeVarType calls — the
// declaration reads as the type it declares.
func (s *Script) ConstAs[T ext.TypePhantom](name string) *ext.Expr[T] {
	return ext.As[T](s.Const(name, ext.HolTypeOf[T]()))
}

// Nat is Script.Numeral in the typed world: numerals are `:num`.
func (s *Script) Nat(n int64) *ext.Expr[ext.Nat] {
	return ext.As[ext.Nat](s.Numeral(n))
}

// VarAs is Script.Var with the variable's type spelled as a phantom —
// the same ParseScope registration (and the same one-type-per-name
// re-declaration panic), returning the variable ready for the typed
// slots (an Arrow's Apply argument, a wrapper's witness). With this verb
// a family needs no runtime type helpers at all: the phantom spelling
// is the only spelling.
func (s *Script) VarAs[T ext.TypePhantom](name string) *ext.Expr[T] {
	return ext.As[T](s.Var(name, ext.HolTypeOf[T]()))
}

// TypeBinding pairs one of a statement's own type variables — under
// the name the STATED form spells, "A", "B", "C" — with the type it
// takes in an explicit instance. Built by TypeVarBinding; consumed by
// Inst and Script.AtTypeVars. Keying the instance by the statement's
// names is what keeps wrapper source free of the positional
// convention (first occurrence in the NORMALIZED form), which no
// author can read off the stated text.
type TypeBinding struct {
	name core.TypeName
	to   core.HolType
}

// typeVarBinding binds the dep statement's type variable `name` to
// the phantom T — one entry of an explicit instance, spelled by the
// letters of the stated form itself:
//
//	Inst(th, typeVarBinding[Carrier]("C"), typeVarBinding[Index]("A"))
//
// The name is checked against the statement's actual type variables
// when the instance resolves; the binding list's order carries no
// meaning.
//
// The two halves carry DIFFERENT information — the name says which
// variable of the statement to substitute, T says what the caller
// substitutes for it — and the name is not derivable from T: inside
// a generic method the type parameter's own name is erased, so at
// runtime T is just whatever concrete type the caller passed. That
// is why a generated wrapper body must spell the letter as a string
// (`typeVarBinding[Type0]("A")` — statement letter A ≔ the caller's
// first type argument), and why the generated parameters are named
// Type0, Type1, … rather than after the letters: the string is the
// only token that means the statement's A, and nothing else should
// look like it does. The two halves denote the same type only under
// the identity instantiation (each letter at its own phantom), which
// makes `name == to.Name()` at identity an oracle for the pairing.
// A statement with ONE type variable has no pairing at all — spell
// it InstSole.
func typeVarBinding[T ext.TypePhantom](name string) TypeBinding {
	return TypeBinding{name: core.TypeName(name), to: ext.HolTypeOf[T]()}
}

// _TypeVarBinder carries the statement alphabet as generic METHODS —
// TypeBinder.BindA[Real]() reads "bind A to Real". A method family on
// a plain value is what makes the bare spelling reach every family
// package: a generic FUNCTION cannot be aliased or bound
// un-instantiated (utils/generic_test.go), but the VALUE
// TypeBinder aliases in one line, methods and all. The type itself is
// never named by callers (the _LetAction convention).
type _TypeVarBinder struct{}

// TypeBinder is the letter-binding namespace: one BindX method per
// statement letter, each returning the TypeBinding "statement's X ≔
// T". Each binding carries its letter in the VALUE, so the argument
// order at an Inst carries no meaning and no positional re-pairing
// exists to drift; a letter the statement does not have panics at
// resolution, listing the letters it does:
//
//	Image.Inst(TypeBinder.BindA[Real](), TypeBinder.BindB[Nat]())
//
// The method set is the corpus's statement alphabet (A–I from the
// stated forms, M and N from the cartesian and word chapters, U the
// host type of the cotangent domain's free algebras, Z from the
// datatype kit's recursion schemas); a
// statement binding a letter outside it takes a new one-line method
// here, and the raw TypeVarBinding spelling remains for a name
// outside any alphabet.
var TypeBinder _TypeVarBinder

// BindA binds the statement's "A" to T; see TypeBinder.
func (_TypeVarBinder) BindA[T ext.TypePhantom]() TypeBinding { return typeVarBinding[T]("A") }

// BindB binds the statement's "B" to T; see TypeBinder.
func (_TypeVarBinder) BindB[T ext.TypePhantom]() TypeBinding { return typeVarBinding[T]("B") }

// BindC binds the statement's "C" to T; see TypeBinder.
func (_TypeVarBinder) BindC[T ext.TypePhantom]() TypeBinding { return typeVarBinding[T]("C") }

// BindD binds the statement's "D" to T; see TypeBinder.
func (_TypeVarBinder) BindD[T ext.TypePhantom]() TypeBinding { return typeVarBinding[T]("D") }

// BindE binds the statement's "E" to T; see TypeBinder.
func (_TypeVarBinder) BindE[T ext.TypePhantom]() TypeBinding { return typeVarBinding[T]("E") }

// BindF binds the statement's "F" to T; see TypeBinder.
func (_TypeVarBinder) BindF[T ext.TypePhantom]() TypeBinding { return typeVarBinding[T]("F") }

// BindG binds the statement's "G" to T; see TypeBinder.
func (_TypeVarBinder) BindG[T ext.TypePhantom]() TypeBinding { return typeVarBinding[T]("G") }

// BindH binds the statement's "H" to T; see TypeBinder.
func (_TypeVarBinder) BindH[T ext.TypePhantom]() TypeBinding { return typeVarBinding[T]("H") }

// BindI binds the statement's "I" to T; see TypeBinder.
func (_TypeVarBinder) BindI[T ext.TypePhantom]() TypeBinding { return typeVarBinding[T]("I") }

// BindM binds the statement's "M" to T; see TypeBinder.
func (_TypeVarBinder) BindM[T ext.TypePhantom]() TypeBinding { return typeVarBinding[T]("M") }

// BindN binds the statement's "N" to T; see TypeBinder.
func (_TypeVarBinder) BindN[T ext.TypePhantom]() TypeBinding { return typeVarBinding[T]("N") }

// BindU binds the statement's "U" to T; see TypeBinder. U is the
// host type every free algebra of the cotangent domain lives in.
func (_TypeVarBinder) BindU[T ext.TypePhantom]() TypeBinding { return typeVarBinding[T]("U") }

// BindZ binds the statement's "Z" to T; see TypeBinder. Z is the
// result-type letter of a datatype's derived recursion schema.
func (_TypeVarBinder) BindZ[T ext.TypePhantom]() TypeBinding { return typeVarBinding[T]("Z") }

// typedInst is the DEFERRED explicit type instance: what Inst carries
// until a justification verb supplies the Script. It resolves through
// Script.AtTypeVars, whose tail is AtTypes' own — so a deferred
// instance and a ctx.AtTypes value install identically, exactness
// flag included (isExplicitInstance).
type typedInst struct {
	dep  NamedDep
	bind []TypeBinding
}

func (t typedInst) resolve(s *Script) *TypedThm {
	return s.AtTypeVars(s.Dep(t.dep), t.bind...)
}

// Inst is the ctx-free spelling of Script.AtTypeVars: the entry taken
// at an explicit type instance, as a pure Fact value. Nothing
// materializes until a verb consumes it, which is when the bindings
// are checked against the statement's type variables (a missing,
// unknown or doubly-bound name panics, listing the statement's own
// letters) and the substitution is built.
//
// Generated theorem wrappers are the intended caller: a wrapper body
// binds each role-named type parameter to the letter the stated form
// declares it under, so the spelling depends on nothing but the
// statement itself — normalization order never enters wrapper source.
func Inst(dep NamedDep, bind ...TypeBinding) Fact {
	if len(bind) == 0 {
		panic("Inst: type bindings required (the uninstantiated entry is cited bare)")
	}
	return Fact{target: typedInst{dep: dep, bind: bind}}
}

// InstSole is Inst for a statement with exactly ONE type variable:
// the sole letter is bound without being named, because a sole
// binding has no pairing to misstate — no letter string to cross, no
// position to drift. This is the generated wrapper-body spelling for
// every single-letter entry (the majority of the corpus), and it is
// rename-proof: restating the entry's letter changes nothing here,
// while the statement GROWING a second type variable panics at
// resolution, listing the letters.
func InstSole[T ext.TypePhantom](dep NamedDep) Fact {
	return Fact{target: _TypedSoleInst{dep: dep, to: ext.HolTypeOf[T]()}}
}

// _TypedSoleInst is InstSole's deferred instance — typedInst's shape
// with the binding reduced to the type alone. Resolves through
// Script.AtSoleType into the same install tail, so the sole spelling
// and a letter-keyed twin install byte-identical forms.
type _TypedSoleInst struct {
	dep NamedDep
	to  core.HolType
}

func (t _TypedSoleInst) resolve(s *Script) *TypedThm {
	return s.AtSoleType(s.Dep(t.dep), t.to)
}

// isExplicitInstance reports whether a cite target is an EXPLICIT
// type instantiation — the author chose the types, so the install
// must be exact rather than adapted (the By path's pr.exact; see the
// *TypedThm comment there).
func isExplicitInstance(target any) bool {
	switch t := target.(type) {
	case *TypedThm, typedInst, _TypedSoleInst:
		return true
	case readingInst:
		// A resident reading keeps its hypothesis types fixed. The By
		// builder reads any loose letters from its witnesses first;
		// no goal-side adaptation may override that instance.
		return t.resident()
	}
	return false
}
