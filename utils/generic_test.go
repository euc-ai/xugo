// generic_test.go — the measured boundary map of Go 1.27 generic
// methods (method-level type parameters), the exploration behind the
// typed proof surface distilled to one file. It exists to PIN that
// knowledge: what the feature can express, and where its walls
// stand, so neither ever has to be re-measured from scratch.
//
// Two enforcement modes:
//
//   - POSITIVE findings are ordinary compiled code. The Go 1
//     compatibility promise keeps them compiling on every future
//     toolchain, so "this trick works" is enforced by the build.
//   - NEGATIVE findings — the walls — cannot be compiled, so each is
//     type-checked at test time from a source snippet via go/types,
//     asserting the rejection and its message. If a future toolchain
//     legalizes one, that subtest FAILS: the signal that new
//     expressiveness has opened up and any design decision the wall
//     forced deserves a fresh look. (TestGenericMethodWalls carries a
//     must-pass control snippet so the instrument cannot be
//     vacuously red.)
//
// The toy vocabulary mirrors the real typed surface: phantom ~
// ext.TypePhantom, fun ~ ext.Fun, sharedCore/typedTerm ~ ext's
// _ExprCore/Expr, the arrow family ~ ext.Arrow, typedValue ~ ext.Typed.
// Where a finding's shipping tenant lives in ext, the comment says
// so; the rest is capability knowledge held in reserve.
package utils

import (
	"go/ast"
	"go/parser"
	"go/token"
	"go/types"
	"strings"
	"testing"
)

// ───────────────────────────── the phantom alphabet ─────────────────────────────

type phantom interface{ tag() string }

type natPhantom struct{}

func (natPhantom) tag() string { return "nat" }

type boolPhantom struct{}

func (boolPhantom) tag() string { return "bool" }

type fun[X, Y phantom] struct{}

func (fun[X, Y]) tag() string {
	var x X
	var y Y
	return "(" + x.tag() + "→" + y.tag() + ")"
}

// isArrow pins its implementer to exactly fun[X, Y]: the type set is
// that single exact term, intersected with phantom (which fun
// implements). This is the exact-type constraint used to smuggle a
// composite past the instantiation-cycle detector — see
// TestGenericMethodConstraintSmuggling.
type isArrow[X, Y phantom] interface {
	phantom
	fun[X, Y]
}

// ───────────────────── finding 1: promotion through embedding ─────────────────────
//
// A generic method promotes through struct embedding with everything
// intact: inference at the call site, explicit instantiation, and
// instantiated method values. This is what lets one embed line hand a
// whole generic method set to another type (the mixin pattern).

type speakerMixin struct{ prefix string }

func (m speakerMixin) speak[T phantom](x T) string { return m.prefix + x.tag() }

type chapterVocab struct {
	speakerMixin
	extra int
}

func TestGenericMethodPromotion(t *testing.T) {
	v := chapterVocab{speakerMixin{"typed:"}, 1}
	if got := v.speak(natPhantom{}); got != "typed:nat" { // inference through the embed
		t.Fatalf("promoted inference: %q", got)
	}
	if got := v.speak(boolPhantom{}); got != "typed:bool" { // explicit instantiation
		t.Fatalf("promoted explicit instantiation: %q", got)
	}
	f := v.speak[natPhantom] // instantiated method value
	if got := f(natPhantom{}); got != "typed:nat" {
		t.Fatalf("method value: %q", got)
	}
}

// ──────────── findings 2–4: the cycle map's legal side, the smuggle, shadowing ────────────
//
// The two-struct split: untyped methods once on a shared core,
// promoted onto both the untyped wrapper and the typed one. The typed
// wrapper's methods map the legal side of the instantiation-cycle
// law, plus the constraint smuggle that defeats it.

type sharedCore struct{ repr string }

func (c *sharedCore) text() string { return c.repr }

// The untyped To, on the shared core — every wrapper promotes it.
func (c *sharedCore) To(s string) *untypedTerm {
	return &untypedTerm{sharedCore{"λ" + c.repr + "." + s}}
}

type untypedTerm struct{ sharedCore }

type typedTerm[T phantom] struct {
	sharedCore
	_ [0]T
}

func mkTyped[T phantom](s string) *typedTerm[T] {
	return &typedTerm[T]{sharedCore: sharedCore{s}}
}

func (x *typedTerm[T]) Untyped() *untypedTerm { return &untypedTerm{x.sharedCore} }

// LEGAL: the receiver's own param absent from the result.
func (x *typedTerm[X]) pick[Y phantom](t *typedTerm[Y]) *typedTerm[Y] { return t }

// LEGAL: a composite built from METHOD params only. The cycle law is
// about SELF-instantiation at a growing argument — receiver's param
// composed back into the receiver's own type — not about composites
// as such (the walls are in TestGenericMethodWalls).
func (x *typedTerm[X]) selfPair[Y phantom](t *typedTerm[Y]) *typedTerm[fun[Y, Y]] {
	return &typedTerm[fun[Y, Y]]{sharedCore: t.sharedCore}
}

// The SMUGGLE: typedTerm[fun[X, Y]] in result position is an
// instantiation cycle, but a fresh method param R with the exact-type
// constraint isArrow[X, Y] carries the same composite with the
// signature spelling only typedTerm[R] — no declaration-level
// self-edge, and constraint type inference fills R with ZERO
// annotations at the call site.
func (x *typedTerm[X]) To[Y phantom, R isArrow[X, Y]](body *typedTerm[Y]) *typedTerm[R] {
	return &typedTerm[R]{sharedCore: sharedCore{"λ" + x.repr + "." + body.repr}}
}

// The same smuggle in PARAMETER position: argument-side application,
// Fn inferred from the argument, Y recovered by unifying Fn against
// the constraint's core type.
func (x *typedTerm[X]) Under[Y phantom, Fn isArrow[X, Y]](f *typedTerm[Fn]) *typedTerm[Y] {
	return &typedTerm[Y]{sharedCore: sharedCore{f.repr + "(" + x.repr + ")"}}
}

func TestGenericMethodCompositionShapes(t *testing.T) {
	x := mkTyped[natPhantom]("x")
	b := mkTyped[boolPhantom]("b")
	var _ *typedTerm[boolPhantom] = x.pick(b)
	var _ *typedTerm[fun[boolPhantom, boolPhantom]] = x.selfPair(b)
}

func TestGenericMethodConstraintSmuggling(t *testing.T) {
	xa := mkTyped[natPhantom]("xa")
	aa := mkTyped[boolPhantom]("aa")
	body := mkTyped[boolPhantom]("b")

	lam := xa.To(aa.To(body)) // nested chain, zero annotations
	// The exact-type assert: fails to compile unless inference
	// produced precisely fun[nat, fun[bool, bool]].
	var _ *typedTerm[fun[natPhantom, fun[boolPhantom, boolPhantom]]] = lam
	if got := lam.text(); got != "λxa.λaa.b" {
		t.Fatalf("smuggled chain built %q", got)
	}

	f := mkTyped[fun[natPhantom, boolPhantom]]("f")
	app := xa.Under(f)
	var _ *typedTerm[boolPhantom] = app
	if got := app.text(); got != "f(xa)" {
		t.Fatalf("argument-side application built %q", got)
	}
}

// A typed generic method SHADOWS the promoted untyped method of the
// same name on typed receivers; the untyped world keeps its own
// spelling untouched, and dropping to it from a typed value is one
// explicit step. (The shipping surface keeps this pattern in
// ext.Arrow's Apply over the promoted untyped Apply.)
func TestGenericMethodShadowing(t *testing.T) {
	xa := mkTyped[natPhantom]("xa")
	body := mkTyped[boolPhantom]("b")

	lam := xa.To(body) // the typed To, through the shadow
	var _ *typedTerm[fun[natPhantom, boolPhantom]] = lam

	w := xa.Untyped().To("raw") // the escape hatch to the untyped To
	if got := w.text(); got != "λxa.raw" {
		t.Fatalf("escape hatch built %q", got)
	}

	tw := &untypedTerm{sharedCore{"t"}}
	if got := tw.To("s").text(); got != "λt.s" { // untyped world untouched
		t.Fatalf("untyped To built %q", got)
	}
}

// ─────────────── finding 5: the shape-specific arrow family (ext.Arrow's design) ───────────────
//
// The cycle law bans composing the receiver's param back into the
// receiver's OWN type, not into another one: a wrapper whose own
// declaration destructures the arrow gets postfix application with no
// method type params at all, and a method on the generic wrapper may
// return that family (cross-type composition — which is why ext.Arrow
// needs no isArrow). A sealed currency interface with T in a method
// PARAMETER position (legal; contrast the interface-type-element wall)
// lets both families flow into one signature with method-set-driven
// inference.

type shapeCore[T phantom] struct {
	sharedCore
	_ [0]T
}

// The currency bridge: T in a method parameter position.
func (c *shapeCore[T]) typedTag(T) {}

type typedValue[T phantom] interface {
	text() string
	typedTag(T)
}

// A shared shape-generic method on the core promotes onto EVERY
// family member — one declaration serves them all.
func (a *shapeCore[T]) eqText(b typedValue[T]) string { return a.text() + " = " + b.text() }

type genericTerm[T phantom] struct{ shapeCore[T] }

type arrowTerm[X, Y phantom] struct {
	shapeCore[fun[X, Y]]
}

type arrowTerm2[X, Y, R phantom] struct {
	shapeCore[fun[X, fun[Y, R]]]
}

func mkGeneric[T phantom](s string) *genericTerm[T] {
	return &genericTerm[T]{shapeCore[T]{sharedCore: sharedCore{s}}}
}

func mkArrow[X, Y phantom](s string) *arrowTerm[X, Y] {
	return &arrowTerm[X, Y]{shapeCore[fun[X, Y]]{sharedCore: sharedCore{s}}}
}

func mkArrow2[X, Y, R phantom](s string) *arrowTerm2[X, Y, R] {
	return &arrowTerm2[X, Y, R]{shapeCore[fun[X, fun[Y, R]]]{sharedCore: sharedCore{s}}}
}

// Postfix application: domain and codomain fixed by the receiver's
// own type — no method type parameters, fully static.
func (f *arrowTerm[X, Y]) Apply(x typedValue[X]) *genericTerm[Y] {
	return mkGeneric[Y](f.text() + "(" + x.text() + ")")
}

func (f *arrowTerm2[X, Y, R]) Apply(x typedValue[X], y typedValue[Y]) *genericTerm[R] {
	return mkGeneric[R](f.text() + "(" + x.text() + ", " + y.text() + ")")
}

// Partial application: one arity down, still applicable.
func (f *arrowTerm2[X, Y, R]) Applied(x typedValue[X]) *arrowTerm[Y, R] {
	return mkArrow[Y, R](f.text() + "(" + x.text() + ")")
}

// Cross-type composition: the receiver's param composed into ANOTHER
// generic type's instantiation is legal — the smuggle is unnecessary
// once the composite lives in the result type's own declaration.
func (x *genericTerm[X]) To[Y phantom](body typedValue[Y]) *arrowTerm[X, Y] {
	return mkArrow[X, Y]("λ" + x.text() + "." + body.text())
}

// Method-set-driven inference through the currency: X and Y are
// solved from whichever family the argument belongs to.
func citeArrow[X, Y phantom](f typedValue[fun[X, Y]], x typedValue[X]) string {
	var xx X
	var yy Y
	return xx.tag() + "|" + yy.tag() + "|" + f.text() + "@" + x.text()
}

// A free static re-wrap from the currency into the applicable family.
func asArrow[X, Y phantom](e typedValue[fun[X, Y]]) *arrowTerm[X, Y] {
	return mkArrow[X, Y](e.text())
}

// Generic ALIASES of the family inherit its methods — several
// spellings, one type (the Set = fun[X, bool] coherence pattern).
type (
	setTerm[X phantom] = arrowTerm[X, boolPhantom]
	opTerm[X phantom]  = arrowTerm2[X, X, X]
)

func TestGenericMethodArrowFamily(t *testing.T) {
	xa := mkGeneric[natPhantom]("xa")
	aa := mkGeneric[boolPhantom]("aa")
	f := mkArrow[natPhantom, boolPhantom]("f")
	var op *opTerm[boolPhantom] = mkArrow2[boolPhantom, boolPhantom, boolPhantom]("op")

	// Static postfix application, one and two arguments.
	var _ *genericTerm[boolPhantom] = f.Apply(xa)
	var _ *genericTerm[boolPhantom] = op.Apply(f.Apply(xa), aa)

	// The fold line: fully postfix, zero annotations. The outer To
	// infers Y = fun[bool, bool] from the inner arrow via the
	// currency's method set.
	lam := xa.To(aa.To(op.Apply(f.Apply(xa), aa)))
	var _ *arrowTerm[natPhantom, fun[boolPhantom, boolPhantom]] = lam
	if got := lam.text(); got != "λxa.λaa.op(f(xa), aa)" {
		t.Fatalf("fold line built %q", got)
	}

	// Currency inference from BOTH families.
	g := mkGeneric[fun[natPhantom, boolPhantom]]("g")
	if got := citeArrow(f, xa); got != "nat|bool|f@xa" {
		t.Fatalf("cite from the arrow family: %q", got)
	}
	if got := citeArrow(g, xa); got != "nat|bool|g@xa" {
		t.Fatalf("cite from the generic wrapper: %q", got)
	}

	// Partial application.
	half := op.Applied(aa)
	var _ *arrowTerm[boolPhantom, boolPhantom] = half

	// The shared core method promotes onto both families, so a
	// cross-family function equation types.
	if got := f.eqText(g); got != "f = g" {
		t.Fatalf("cross-family equality: %q", got)
	}

	// Free re-wrap: the inert generic arrow becomes applicable.
	if got := asArrow(g).Apply(xa).text(); got != "g(xa)" {
		t.Fatalf("re-wrap: %q", got)
	}

	// Aliases inherit methods.
	var s *setTerm[natPhantom] = mkArrow[natPhantom, boolPhantom]("s")
	var _ *genericTerm[boolPhantom] = s.Apply(xa)
}

// ────────── finding 6: deferring the composite into a fresh TYPE param (scheme B) ──────────
//
// The growth-through-the-embedded-body wall (a method on the shared
// core returning the arrow family; pinned in TestGenericMethodWalls)
// falls to the same smuggle one level up: carry fun[X, Y] as a third TYPE parameter F,
// publish the family as a generic alias pinning F, and the method
// spells only the impl at F. Call sites never write F; alias identity
// makes the result type read as the family name. This is the proven
// upgrade path if a method on the shared core must ever produce the
// arrow family. Measured cost (kept as knowledge): a type-error at a
// value of the family renders the TRIPLED impl type
// (*deferredArrowImpl[nat, bool, fun[nat, bool]]), while expected
// types still render as the alias — intrinsic to the scheme.

type deferredCore[T phantom] struct {
	sharedCore
	_ [0]T
}

func (c *deferredCore[T]) holds(T) {}

type deferredValue[T phantom] interface {
	text() string
	holds(T)
}

type deferredTerm[T phantom] struct{ deferredCore[T] }

type deferredArrowImpl[X, Y phantom, F isArrow[X, Y]] struct {
	deferredCore[F]
}

type deferredArrow[X, Y phantom] = deferredArrowImpl[X, Y, fun[X, Y]]

func mkDeferred[T phantom](s string) *deferredTerm[T] {
	return &deferredTerm[T]{deferredCore[T]{sharedCore: sharedCore{s}}}
}

func (f *deferredArrowImpl[X, Y, F]) Apply(x deferredValue[X]) *deferredTerm[Y] {
	return mkDeferred[Y](f.text() + "(" + x.text() + ")")
}

// The walled shape — To on the shared core — deferred through F: legal.
func (x *deferredCore[X]) To[Y phantom, F isArrow[X, Y]](body deferredValue[Y]) *deferredArrowImpl[X, Y, F] {
	return &deferredArrowImpl[X, Y, F]{deferredCore[F]{sharedCore: sharedCore{"λ" + x.text() + "." + body.text()}}}
}

// Mutual mention at a CONSTANT argument (core[X] ↔ term[X]) is legal —
// only a GROWING self-argument cycles.
func (x *deferredCore[X]) SuchThat(body deferredValue[boolPhantom]) *deferredTerm[X] {
	return mkDeferred[X]("ε" + x.text() + "." + body.text())
}

func citeDeferred[X, Y phantom](f deferredValue[fun[X, Y]], x deferredValue[X]) string {
	var xx X
	var yy Y
	return xx.tag() + "|" + yy.tag() + "|" + f.text() + "@" + x.text()
}

func TestGenericMethodDeferredComposite(t *testing.T) {
	x := mkDeferred[natPhantom]("x")
	b := mkDeferred[boolPhantom]("b")

	m := x.To(b) // F inferred, never spelled
	// Alias identity: the impl at F = fun[nat, bool] IS the alias.
	var _ *deferredArrow[natPhantom, boolPhantom] = m
	if got := m.Apply(x).text(); got != "λx.b(x)" {
		t.Fatalf("deferred To/Apply built %q", got)
	}

	// A family value BINDS as a To receiver via promotion: the
	// receiver's X is solved to the value's own F.
	m2 := m.To(b)
	var _ *deferredArrow[fun[natPhantom, boolPhantom], boolPhantom] = m2

	// ε over a function-typed receiver — the constant-argument shape.
	eps := m.SuchThat(b)
	var _ *deferredTerm[fun[natPhantom, boolPhantom]] = eps

	// Currency inference from the impl-typed value.
	if got := citeDeferred(m, x); got != "nat|bool|λx.b@x" {
		t.Fatalf("cite from the deferred family: %q", got)
	}
}

// ────────── finding 7: letter witnesses — named type arguments as a value protocol ──────────
//
// Go has no named type ARGUMENTS, and inside a generic method the
// parameter NAME is erased — the two halves of the wall that leaves a
// positional Inst[τ…] call site silently re-pairable and forces a
// generated body to restate each letter as a string. Both close from
// the VALUE side: one zero-size witness type PER LETTER carries the
// letter in its type name and the instance in its type parameter. The
// method takes one witness per letter, its type params are INFERRED
// from them, and the (name → instance) binding is produced by the
// witness's own method — so the letter string exists once, beside the
// witness declaration, and a body that threads witness values has no
// letter to restate, hence none to cross. A crossed CALL SITE is an
// ordinary type mismatch whose message names the expected letter type
// (pinned below); a missing letter is an arity error. The witness is
// a TYPE spelled as a literal, not a constructor function, because
// generic functions cannot be bound un-instantiated while generic
// type ALIASES work — the alias spelling is what a preamble imports.
// One measured nuance: between DIFFERENT letters at the SAME instance
// an explicit conversion is legal (identical underlying type, tooth
// included) but semantically inert — the instance rides in the type
// parameter, which conversion preserves; cross-instance conversion is
// blocked by the tooth.
//
// What SHIPPED (prover/proof's TypeBinder) is the
// complementary VALUE-side design: letters as named binding values
// (TypeBinder.BindA[τ]() → a TypeBinding carrying "A"), checked
// against the statement at resolution rather than compile time —
// mis-pairing is unwritable because each binding names its letter,
// and order carries no meaning. The witness TYPES here stay in
// reserve for a surface that wants the checks at compile time. Two
// boundaries frame that choice: (1) a FUNCTION spelling of a letter
// cannot stand in for the witness type — an instantiated generic
// function value has an UNNAMED structural type, so assignability
// punches straight through per-letter defined function types and
// letter-typed function parameters check nothing; only a value born
// with a per-letter nominal type (this finding's witness struct)
// checks. (2) The letter constructors ride ONE exported value with
// generic METHODS (TypeBinder) because a value aliases across
// packages in one var line, while generic FUNCTIONS cannot be
// aliased or bound un-instantiated at all.

type letterA[T phantom] struct{ _ [0]T }

type letterB[T phantom] struct{ _ [0]T }

func (letterA[T]) bind() [2]string { var v T; return [2]string{"A", v.tag()} }
func (letterB[T]) bind() [2]string { var v T; return [2]string{"B", v.tag()} }

// A wrapper over a statement with letters {A, B}.
type namedInstThm struct{}

func (namedInstThm) inst[A, B phantom](a letterA[A], b letterB[B]) map[string]string {
	na, nb := a.bind(), b.bind()
	return map[string]string{na[0]: na[1], nb[0]: nb[1]}
}

// The preamble spelling: a generic type alias of the witness.
type letterAAlias[T phantom] = letterA[T]

func TestGenericMethodLetterWitness(t *testing.T) {
	th := namedInstThm{}

	// Inference: no explicit instantiation anywhere at the call.
	got := th.inst(letterA[natPhantom]{}, letterB[boolPhantom]{})
	if got["A"] != "nat" || got["B"] != "bool" {
		t.Fatalf("letter-witness inference bound %v", got)
	}

	// The alias spelling binds identically.
	got = th.inst(letterAAlias[boolPhantom]{}, letterB[natPhantom]{})
	if got["A"] != "bool" || got["B"] != "nat" {
		t.Fatalf("alias witness bound %v", got)
	}

	// The safety half: a CROSSED call site is a type mismatch, and
	// the message names the letter the position wanted.
	messages := typeCheckSnippet(t, "crossed", `package crossed

type phantom interface{ tag() string }

type natP struct{}

func (natP) tag() string { return "nat" }

type letterA[T phantom] struct{ _ [0]T }

type letterB[T phantom] struct{ _ [0]T }

type thm struct{}

func (thm) inst[A, B phantom](a letterA[A], b letterB[B]) {}

func crossed() {
	thm{}.inst(letterB[natP]{}, letterA[natP]{})
}
`)
	joined := strings.Join(messages, "\n")
	if !strings.Contains(joined, "does not match inferred type letterA[natP] for letterA[A]") {
		t.Fatalf("crossed letters must be rejected naming the expected letter; got:\n%s", joined)
	}
}

// ────────── finding 8: mixed bare instantiation across a two-parameter receiver ──────────
//
// A method's own type parameter may join the receiver's parameters in
// fresh instantiations of the receiver's OWN generic type, in argument
// and result positions alike, so long as every type argument is a BARE
// parameter: grid[R, C] · mul[K](grid[C, K]) → grid[R, K] type-checks,
// with K inferred from the argument, and a permutation (transpose) is
// the zero-method-param special case. The cycle law bans GROWTH —
// a receiver parameter composed back into the receiver's type — not
// mixing; pick/selfPair pinned the one-parameter cases, this finding
// pins the two-parameter mixed shape a dimension-typed matrix product
// and transpose stand on. It is held in reserve: ext/dimtypes' Mat
// carries no operation, the matrix operations being constants the
// corpus mints. Its shipping neighbours there are VecFun.Apply, the same
// bare mixing across two generic types (a VecFun[Elem, Source, Target]
// takes a Vec[Elem, Source] to a Vec[Elem, Target]), and
// RealVec.Concat, the composite-result sibling, which rides the
// constraint smuggle and whose tenancy that file's IsPlus records.

type grid[R, C phantom] struct {
	_ [0]R
	_ [0]C
}

func (grid[R, C]) mul[K phantom](grid[C, K]) grid[R, K] { return grid[R, K]{} }

func (grid[R, C]) transpose() grid[C, R] { return grid[C, R]{} }

func TestGenericMethodMixedInstantiation(t *testing.T) {
	a := grid[natPhantom, boolPhantom]{}
	b := grid[boolPhantom, natPhantom]{}
	c := a.mul(b) // K inferred from the argument's second parameter
	var _ grid[natPhantom, natPhantom] = c
	var _ grid[boolPhantom, natPhantom] = a.transpose()
	// Chained: a mixed result feeds a further mixed call.
	var _ grid[natPhantom, boolPhantom] = c.mul(a)
}

// ───────────────────────────── the walls, pinned ─────────────────────────────

// typeCheckSnippet parses and type-checks one standalone source file,
// returning every type-checker message. Parse errors are fatal: the
// walls are TYPE errors, and a snippet that stops parsing would turn
// this instrument vacuous.
func typeCheckSnippet(t *testing.T, name, src string) []string {
	t.Helper()
	fileSet := token.NewFileSet()
	file, err := parser.ParseFile(fileSet, name+".go", src, 0)
	if err != nil {
		t.Fatalf("%s: snippet must PARSE (the walls are type errors): %v", name, err)
	}
	var messages []string
	config := types.Config{Error: func(err error) { messages = append(messages, err.Error()) }}
	_, _ = config.Check(name, fileSet, []*ast.File{file}, nil)
	return messages
}

// TestGenericMethodWalls pins the NEGATIVE half of the boundary map.
// A wall subtest failing means the toolchain now ACCEPTS the shape:
// the wall has fallen, and whatever design it forced (the arrow
// family's existence, the smuggle, prefix application) deserves a
// fresh look before this table is updated.
func TestGenericMethodWalls(t *testing.T) {
	const prelude = `package wall

type phantom interface{ tag() string }

type fun[X, Y phantom] struct{}

func (fun[X, Y]) tag() string { return "fun" }
`

	cases := []struct {
		name string
		src  string
		want string // "" = must type-check (the instrument's control)
	}{
		{
			// The legal shapes from TestGenericMethodCompositionShapes,
			// as the harness control: proves the instrument can pass.
			name: "control: plain and method-param-only composites",
			src: prelude + `
type wrap[T phantom] struct{ _ [0]T }

func (x *wrap[X]) pick[Y phantom](t *wrap[Y]) *wrap[Y] { return t }

func (x *wrap[X]) selfPair[Y phantom](t *wrap[Y]) *wrap[fun[Y, Y]] { return nil }
`,
			want: "",
		},
		{
			// A receiver's type param cannot enter positions demanding
			// a NARROWER bound — the wall that forced the two-struct
			// split (an Expr[T any-phantom] receiver could not reach
			// any Phantom-bound machinery).
			name: "narrower bound rejects the receiver's param",
			src: `package wall

type anyPhantom interface{ tag() string }

type phantom interface {
	anyPhantom
	sealed()
}

type fun[X, Y phantom] struct{}

func (fun[X, Y]) tag() string { return "fun" }
func (fun[X, Y]) sealed()     {}

type wrap[T anyPhantom] struct{ _ [0]T }

func (x *wrap[T]) pair[Y phantom]() (f fun[T, Y]) { return }
`,
			want: "does not satisfy",
		},
		{
			// Self-instantiation at a growing argument, RESULT
			// position: the typed-λ shape that forced the smuggle.
			name: "self-composite in result position",
			src: prelude + `
type wrap[T phantom] struct{ _ [0]T }

func (x *wrap[X]) To[Y phantom](body *wrap[Y]) *wrap[fun[X, Y]] { return nil }
`,
			want: "instantiation cycle",
		},
		{
			// The same wall in PARAMETER position: argument-side
			// application cannot spell the composite either.
			name: "self-composite in parameter position",
			src: prelude + `
type wrap[T phantom] struct{ _ [0]T }

func (x *wrap[X]) Under[Y phantom](f *wrap[fun[X, Y]]) *wrap[Y] { return nil }
`,
			want: "instantiation cycle",
		},
		{
			// A type parameter may not be an interface's type element,
			// so no constraint can EQUATE a receiver's param with a
			// composite of method params — the wall that makes postfix
			// application impossible on the generic wrapper and forces
			// the shape-specific arrow family.
			name: "type parameter as an interface type element",
			src: prelude + `
type sameAs[F, X, Y phantom] interface {
	F
	fun[X, Y]
}
`,
			want: "term cannot be a type parameter",
		},
		{
			// Growth through the embedding's BODY: a method on the
			// shared core returning the arrow family re-materializes
			// core[fun[X, Y]] inside the family's own declaration.
			name: "growth through the embedded body",
			src: prelude + `
type core[T phantom] struct{ _ [0]T }

type arrow[X, Y phantom] struct{ core[fun[X, Y]] }

func (x *core[X]) To[Y phantom]() *arrow[X, Y] { return nil }
`,
			want: "instantiation cycle",
		},
		{
			// Spelling the deferred family's ALIAS as the result
			// re-materializes the composite the third parameter was
			// hiding: the deferral works only while the signature
			// spells the impl at F.
			name: "alias expansion re-materializes the composite",
			src: prelude + `
type isArrow[X, Y phantom] interface {
	phantom
	fun[X, Y]
}

type core[T phantom] struct{ _ [0]T }

type impl[X, Y phantom, F isArrow[X, Y]] struct{ core[F] }

type alias[X, Y phantom] = impl[X, Y, fun[X, Y]]

func (x *core[X]) To[Y phantom]() *alias[X, Y] { return nil }
`,
			want: "instantiation cycle",
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			messages := typeCheckSnippet(t, "wall", tc.src)
			joined := strings.Join(messages, "\n")
			if tc.want == "" {
				if len(messages) > 0 {
					t.Fatalf("control snippet must type-check; got:\n%s", joined)
				}
				return
			}
			if len(messages) == 0 {
				t.Fatalf("the wall has FALLEN: the snippet now type-checks (wanted %q) — re-examine the design this wall forced", tc.want)
			}
			if !strings.Contains(joined, tc.want) {
				t.Fatalf("rejected, but not by the pinned wall: want %q in:\n%s", tc.want, joined)
			}
		})
	}
}
