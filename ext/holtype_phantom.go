// holtype_phantom.go — the phantom vocabulary of the typed term
// surface: Go types standing for HOL types, carried as the type
// parameter of Expr and reified to the runtime representation
// (HolType) only at the proof-layer boundary. Surface ergonomics, not
// kernel — nothing in core knows the vocabulary exists.
//
// The vocabulary is DECENTRALIZED by construction: any package may
// declare a phantom for a type it owns as a zero-size struct with a
// Reify — a family that mints a typedef declares the typedef's
// phantom next to the mint, in the family's vocab.go, and a family
// whose statements bind a type letter beyond the core alphabet has
// that letter declared the same way in its generated wrapper file
// (library/registry/typedgen, OwnerOfLetter: monoidal's `I`, for
// `∀op:(I → I → I)`). This file holds the shared core: the
// propositional base, the canonical statement letters A–E (statements
// rarely bind more, and T and F are this package's truth constants),
// the structural constructors, and the concrete phantoms whose
// metatype identities live in this package (Nat beside numeral.go's
// mint, Prod beside basic_defs.go's).
//
// There is deliberately NO untyped sentinel in the vocabulary. The
// untyped wrapper (TermWrapper) is its own struct rather than an Expr
// instantiation, so an untyped term in a typed position is an
// ordinary compile-time type mismatch: the wall between the two
// surfaces is nominal, and TypePhantom is the one constraint.
//
// HOL's polymorphism is prenex, predicative and kind-* only, with no
// type-level λ — constructors are always fully applied. That is
// exactly the fragment Go type parameters model, which is why a
// phantom vocabulary is total for this object logic: every HOL type a
// statement can quantify over has a spelling here, and none needs a
// higher-kinded parameter.

package ext

// TypePhantom is the constraint of the typed surface: a zero-size Go
// type whose Reify names the HOL type it stands for — present only at
// compile time, which is what the name says. It is deliberately NOT
// called anything close to HolType: that is the runtime
// representation Reify produces, this is the type-level stand-in.
type TypePhantom interface{ Reify() HolType }

// HolTypeOf reifies a phantom. The one bridge between the type level
// and the runtime representation; everything typed funnels through
// it.
func HolTypeOf[T TypePhantom]() HolType {
	var t T
	return t.Reify()
}

// Bool is `:bool`.
type Bool struct{}

func (Bool) Reify() HolType { return TypeBool }

// A…E are the canonical HOL type VARIABLES `:A` … `:E` — the letters
// polymorphic statements are stated in. A member proving or citing a
// law at its stated generality uses these; a member pinning an index
// type uses a concrete phantom (Nat, a typedef's own) in the same
// slot. A statement binding a letter outside this alphabet gets that
// letter declared in its family's generated wrapper file, per the
// decentralization rule in the file header.
type (
	A struct{}
	B struct{}
	C struct{}
	D struct{}
	E struct{}
)

func (A) Reify() HolType { return MakeVarType("A") }
func (B) Reify() HolType { return MakeVarType("B") }
func (C) Reify() HolType { return MakeVarType("C") }
func (D) Reify() HolType { return MakeVarType("D") }
func (E) Reify() HolType { return MakeVarType("E") }

// Fun is the function type constructor, under HOL's own name for it
// (`fun(A,B)` is `A → B`). Reify recurses through the phantom
// arguments, so a nested spelling like Fun[Set[A], Bool] reifies in
// one call.
type Fun[X, Y TypePhantom] struct{}

func (Fun[X, Y]) Reify() HolType { return MakeFun(HolTypeOf[X](), HolTypeOf[Y]()) }

// Fun2 and Fun3 are the curried views — the arities the library's
// constants actually have. Aliases, not new types: Fun2[X, Y, R] IS
// Fun[X, Fun[Y, R]], so the two spellings are interchangeable
// everywhere, and a signature may use whichever reads better.
type (
	Fun2[X, Y, R TypePhantom]    = Fun[X, Fun[Y, R]]
	Fun3[X, Y, Z, R TypePhantom] = Fun[X, Fun2[Y, Z, R]]
)

// Set is HOL's set-as-predicate reading: Set[X] IS Fun[X, Bool]. An
// alias for the same reason as Fun2 — `A set` and `A → bool` are one
// type in the logic, so they must be ONE type here, with two names.
type Set[X TypePhantom] = Fun[X, Bool]

// Op is the homogeneous binary operation `X → X → X` — the monoidal
// chapters' alphabet, common enough to earn its own spelling.
type Op[X TypePhantom] = Fun2[X, X, X]

// Nat is the phantom for `:num`. It lives beside the num metatype's
// mint (numeral.go) — metatypes match by POINTER, so a phantom is
// declared where its type's identity lives.
type Nat struct{}

func (Nat) Reify() HolType { return NumType }

// Prod is the phantom for HOL's pair type `prod(X, Y)`, beside the
// metatype it reifies (basic_defs.go) for the same pointer-identity reason
// as Nat.
type Prod[X, Y TypePhantom] struct{}

func (Prod[X, Y]) Reify() HolType {
	return MakeProdType(HolTypeOf[X](), HolTypeOf[Y]())
}

// Arrow[X, Y] wraps a term of HOL type Fun[X, Y] and carries postfix
// Apply; Arrow2 is the curried binary arity — the binder-closure
// shapes members actually declare. Higher arities and partial
// application join when a member needs them.
//
// The family exists because the generic wrapper cannot apply: a
// receiver cannot destructure an arrow, and no method-level
// constraint can equate the receiver's parameter with one (a type
// parameter may not be an interface's type term — spec, probed). The
// shape must be declared AT THE TYPE, and these types are exactly
// that declaration: Arrow's own parameters are the destructured
// arrow, so Apply needs no method type parameters and both domain and
// codomain are fully static.
//
// Values of the family come from typed binder closures — a section
// body that declares an arrow-typed parameter as *Arrow/*Arrow2
// receives the statement's binder born applicable. *Expr[Fun[X, Y]]
// remains the GENERIC spelling (a shape-blind verb like FixAs[T]
// cannot return a shape-dependent type); parameters never choose
// between the two — they accept the Typed currency, which both
// spellings implement.

// Arrow is a function term f : X → Y, born applicable.
type Arrow[X, Y TypePhantom] struct{ _TypedCore[Fun[X, Y]] }

// Apply is postfix typed application f(x): the argument must carry
// the domain phantom, the result carries the codomain's, and both are
// fixed by the receiver's own type — no inference, no annotations.
func (f *Arrow[X, Y]) Apply(x Typed[X]) *Expr[Y] {
	return &Expr[Y]{adopt[Y](Apply(f.Core(), x.Core()))}
}

// Arrow2 is a curried binary function term f : X → Y → R.
type Arrow2[X, Y, R TypePhantom] struct{ _TypedCore[Fun2[X, Y, R]] }

// Apply is the two-argument application f(x, y).
func (f *Arrow2[X, Y, R]) Apply(x Typed[X], y Typed[Y]) *Expr[R] {
	return &Expr[R]{adopt[R](Apply(f.Core(), x.Core(), y.Core()))}
}
