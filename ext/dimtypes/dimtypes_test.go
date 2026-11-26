// dimtypes_test.go — the framework exercised end to end against real
// core terms: reification shapes, the equality decision, dimension
// flow through every operation (with the reified bound checked against
// independently hand-built terms), the smuggle's inference at call
// sites, and both gates (adoption, recast).
package dimtypes

import (
	"math/big"
	"reflect"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
)

// alphaEqual asserts two terms are α-equal, printing both otherwise.
func alphaEqual(t *testing.T, got, want core.Term) {
	t.Helper()
	if got.AlphaKey() != want.AlphaKey() {
		t.Fatalf("terms differ:\n  got  %s\n  want %s", ext.PrintTerm(got), ext.PrintTerm(want))
	}
}

// mustPanic asserts f panics with a message containing want.
func mustPanic(t *testing.T, want string, f func()) {
	t.Helper()
	defer func() {
		r := recover()
		if r == nil {
			t.Fatalf("expected a panic containing %q, got none", want)
		}
		if msg, ok := r.(string); !ok || !strings.Contains(msg, want) {
			t.Fatalf("expected a panic containing %q, got: %v", want, r)
		}
	}()
	f()
}

// nVar etc. — the letters' terms, built independently of the package's
// own lowering so the tests pin the contract, not the implementation.
func nVar() core.Term { return core.Var("n", ext.NumType) }
func mVar() core.Term { return core.Var("m", ext.NumType) }

func natPlus(l, r core.Term) core.Term {
	return core.Apply(core.Apply(dsl.NatPlusMeta.Term(), l), r)
}

func TestDimReification(t *testing.T) {
	alphaEqual(t, TermOf[DimN](), nVar())
	alphaEqual(t, TermOf[D0](), ext.MakeNumeral(big.NewInt(0)))
	alphaEqual(t, TermOf[D3](), ext.MakeNumeral(big.NewInt(3)))
	alphaEqual(t, TermOf[Plus[DimN, D1]](), natPlus(nVar(), ext.MakeNumeral(big.NewInt(1))))
	// Nested composite, mixing letters, literals and both operators.
	alphaEqual(t, TermOf[Plus[Times[D2, DimM], DimN]](),
		natPlus(
			core.Apply(core.Apply(dsl.NatStarMeta.Term(), ext.MakeNumeral(big.NewInt(2))), mVar()),
			nVar()))
}

func TestSameDim(t *testing.T) {
	for _, tc := range []struct {
		name string
		got  bool
		want bool
	}{
		{"m+n = n+m", SameDim[Plus[DimM, DimN], Plus[DimN, DimM]](), true},
		{"(m+n)+k = m+(n+k)", SameDim[Plus[Plus[DimM, DimN], DimK], Plus[DimM, Plus[DimN, DimK]]](), true},
		{"2*(m+n) = 2*m+2*n", SameDim[Times[D2, Plus[DimM, DimN]], Plus[Times[D2, DimM], Times[D2, DimN]]](), true},
		{"n+n = 2*n", SameDim[Plus[DimN, DimN], Times[D2, DimN]](), true},
		{"n+0 = n", SameDim[Plus[DimN, D0], DimN](), true},
		{"n*n = n*n (as m*n reordered)", SameDim[Times[DimN, DimM], Times[DimM, DimN]](), true},
		{"n ≠ m", SameDim[DimN, DimM](), false},
		{"n+1 ≠ n", SameDim[Plus[DimN, D1], DimN](), false},
		{"n*n ≠ 2*n", SameDim[Times[DimN, DimN], Times[D2, DimN]](), false},
	} {
		if tc.got != tc.want {
			t.Errorf("%s: SameDim = %v, want %v", tc.name, tc.got, tc.want)
		}
	}
}

// Public dimension vocabularies may use any Go string as a letter name.
// The equality normal form must therefore keep a single delimiter-bearing
// letter distinct from a product, and an empty-name letter distinct from
// the constant monomial.
type (
	delimiterLetter struct{}
	emptyLetter     struct{}
)

func (delimiterLetter) Spec() DimSpec { return SpecVar{"m*n"} }
func (emptyLetter) Spec() DimSpec     { return SpecVar{""} }

func TestSameDimMonomialKeysAreUnambiguous(t *testing.T) {
	if SameDim[delimiterLetter, Times[DimM, DimN]]() {
		t.Fatal("the single letter `m*n` must not equal the product m*n")
	}
	if SameDim[emptyLetter, D1]() {
		t.Fatal("an empty-name letter must not equal the constant 1")
	}
}

func TestDenotesTermKeepsRepeatedLettersConsistent(t *testing.T) {
	spec := SpecAdd{SpecVar{"n"}, SpecVar{"n"}}
	n0 := core.Var("n_0", ext.NumType)
	n1 := core.Var("n_1", ext.NumType)
	acceptSkolemN := func(name string, v core.VarTerm) bool {
		return name == "n" && strings.HasPrefix(string(v.Name()), "n_")
	}

	if !DenotesTerm(spec, natPlus(n0, n0), acceptSkolemN) {
		t.Fatal("the same actual variable at both N occurrences must be accepted")
	}
	if DenotesTerm(spec, natPlus(n0, n1), acceptSkolemN) {
		t.Fatal("two different actual variables must not satisfy repeated N occurrences")
	}
}

func TestVectorOps(t *testing.T) {
	u := AsRealVec[DimN](ext.Var("u", vecType))
	v := AsRealVec[DimN](ext.Var("v", vecType))

	// Pointwise addition: no bound in the term.
	alphaEqual(t, u.Add(v).Core(),
		ext.Apply(vecAddMeta.Term(), ext.Var("u", vecType), ext.Var("v", vecType)).Core())

	// The inner product's bound is the phantom, reified — checked
	// against an independently built `n`.
	got := u.Dot(v)
	var _ *ext.Expr[dsl.Real] = got // result is a real scalar, statically
	alphaEqual(t, got.Core(),
		ext.Apply(dotMeta.Term(), nVar(), ext.Var("u", vecType), ext.Var("v", vecType)).Core())

	// A literal-dimensioned pair reifies its literal instead.
	p := AsRealVec[D3](ext.Var("p", vecType))
	q := AsRealVec[D3](ext.Var("q", vecType))
	alphaEqual(t, p.Dot(q).Core(),
		ext.Apply(dotMeta.Term(), ext.MakeNumeral(big.NewInt(3)),
			ext.Var("p", vecType), ext.Var("q", vecType)).Core())

	// The scalar arrives through the typed currency.
	c := ext.As[dsl.Real](ext.Var("c", dsl.RealType))
	alphaEqual(t, u.Scale(c).Core(),
		ext.Apply(vecScalarMulMeta.Term(), ext.Var("c", dsl.RealType), ext.Var("u", vecType)).Core())
}

func TestConcatInference(t *testing.T) {
	u := AsRealVec[DimN](ext.Var("u", vecType))
	w := AsRealVec[D2](ext.Var("w", vecType))

	x := u.Concat(w) // S inferred: no annotations at the call site
	var _ *RealVec[Plus[DimN, D2]] = x
	alphaEqual(t, x.Core(),
		ext.Apply(vconcatMeta.Term(), nVar(), ext.Var("u", vecType), ext.Var("w", vecType)).Core())

	// Chained: the composite dimension feeds a further concat, and the
	// new cut point is the composite's own reification.
	y := x.Concat(u)
	var _ *RealVec[Plus[Plus[DimN, D2], DimN]] = y
	alphaEqual(t, y.Core(),
		ext.Apply(vconcatMeta.Term(),
			natPlus(nVar(), ext.MakeNumeral(big.NewInt(2))),
			x.Core(), ext.Var("u", vecType)).Core())
}

func TestAnchorMat(t *testing.T) {
	carrier := core.MakeFun(ext.NumType, ext.NumType, dsl.RealType)
	a0 := core.Var("A_0", carrier)
	n0, m0 := core.Var("n_0", ext.NumType), core.Var("m_0", ext.NumType)
	letter := func(name string) core.Term {
		return map[string]core.Term{"n": n0, "m": m0}[name]
	}

	a := AnchorMat[dsl.Real, DimN, DimM](ext.WrapTerm(a0), letter)
	if !a.Anchored() {
		t.Fatal("AnchorMat must be anchored")
	}
	alphaEqual(t, a.Rows(), n0)
	alphaEqual(t, a.Cols(), m0)

	// Each phantom anchors on its own, and a composite spelling reaches
	// every letter of both.
	b := AnchorMat[dsl.Real, Plus[DimN, DimM], DimN](ext.WrapTerm(a0), letter)
	alphaEqual(t, b.Rows(), natPlus(n0, m0))
	alphaEqual(t, b.Cols(), n0)
	// A square matrix mentions one letter twice and reports it once.
	square := AnchorMat[dsl.Real, DimN, DimN](ext.WrapTerm(a0), letter)
	if got := square.Letters(); len(got) != 1 || got[0] != "n" {
		t.Fatalf("letters %v", got)
	}
	if got := b.Letters(); len(got) != 2 || got[0] != "n" || got[1] != "m" {
		t.Fatalf("letters %v", got)
	}

	// A bare label has no dimension to write — on either index.
	bare := AsMat[dsl.Real, DimN, DimM](ext.WrapTerm(a0))
	if bare.Anchored() {
		t.Fatal("AsMat must be bare")
	}
	mustPanic(t, "bare dimension label", func() { bare.Rows() })
	mustPanic(t, "bare dimension label", func() { bare.Cols() })
	// An unresolved letter is refused at the anchor, and an anchored
	// matrix is not relabeled by a bare recast.
	mustPanic(t, "letter k does not denote", func() {
		AnchorMat[dsl.Real, DimK, DimM](ext.WrapTerm(a0), letter)
	})
	// (a provably-EQUAL respelling, so it is the anchor that refuses it,
	// not the dimension check)
	mustPanic(t, "relabels a BARE matrix", func() { RecastMat[Plus[DimN, D0], DimM](a) })
}

func TestDescribeMatType(t *testing.T) {
	desc, ok := DescribeMatType(reflect.TypeFor[*Mat[dsl.Real, Plus[DimN, DimM], DimN]]())
	if !ok {
		t.Fatal("not described")
	}
	if !desc.HOLType().Equals(core.MakeFun(ext.NumType, ext.NumType, dsl.RealType)) {
		t.Fatalf("carrier %s", ext.FormatType(desc.HOLType()))
	}
	if l := desc.Letters(); len(l) != 2 || l[0] != "n" || l[1] != "m" {
		t.Fatalf("letters %v", l)
	}
	n0, m0 := core.Var("n_0", ext.NumType), core.Var("m_0", ext.NumType)
	a0 := core.Var("A_0", core.MakeFun(ext.NumType, ext.NumType, dsl.RealType))
	got := desc.Anchor(ext.WrapTerm(a0), func(name string) core.Term {
		return map[string]core.Term{"n": n0, "m": m0}[name]
	})
	a, ok := got.Interface().(*Mat[dsl.Real, Plus[DimN, DimM], DimN])
	if !ok {
		t.Fatalf("anchored value has type %T", got.Interface())
	}
	alphaEqual(t, a.Rows(), natPlus(n0, m0))
	alphaEqual(t, a.Cols(), n0)
	// A type embedding *Mat is not a Mat parameter, and a Vec is not one.
	type wrapped struct{ *Mat[dsl.Real, DimN, DimM] }
	if _, ok := DescribeMatType(reflect.TypeFor[*wrapped]()); ok {
		t.Fatal("an embedder must be rejected")
	}
	if _, ok := DescribeMatType(reflect.TypeFor[*Vec[dsl.Real, DimN]]()); ok {
		t.Fatal("a Vec is not a Mat")
	}
}

func TestRecast(t *testing.T) {
	u := AsRealVec[DimN](ext.Var("u", vecType))
	w := AsRealVec[DimM](ext.Var("w", vecType))
	x := u.Concat(w) // *Vec[Plus[DimN, DimM]]

	// A provably-equal respelling: the term does not move.
	y := RecastRealVec[Plus[DimM, DimN]](x)
	var _ *RealVec[Plus[DimM, DimN]] = y
	alphaEqual(t, y.Core(), x.Core())

	// After the recast, operations reify the NEW spelling — the m+n vs
	// n+m bridge is now visible in the term, where a statement's own
	// proof discharges it.
	alphaEqual(t, y.Dot(y).Core(),
		ext.Apply(dotMeta.Term(), natPlus(mVar(), nVar()), x.Core(), x.Core()).Core())

	// Matrices recast per dimension.
	matCarrier := core.MakeFun(ext.NumType, ext.NumType, dsl.RealType)
	ab := AsMat[dsl.Real, Plus[DimN, D0], Times[D2, DimM]](ext.Var("C", matCarrier))
	var _ *Mat[dsl.Real, DimN, Plus[DimM, DimM]] = RecastMat[DimN, Plus[DimM, DimM]](ab)

	// An unequal pair is a proof-authoring bug: loud, naming both terms.
	mustPanic(t, "recast between unequal dimensions", func() {
		RecastRealVec[DimK](u)
	})
}

func TestAdoptionGate(t *testing.T) {
	// A term of the wrong HOL type cannot enter at any dimension.
	mustPanic(t, "ext.As", func() {
		AsRealVec[DimN](ext.Var("b", ext.NumType))
	})
}

// The refined wrappers remain citizens of the typed surface: a Vec is
// Typed at its CARRIER phantom (the kernel-level invariant — all
// dimensions share it), so it flows into any currency slot a plain
// Expr[VecCarrier] would.
var (
	_ ext.Typed[VecCarrier]         = (*Vec[dsl.Real, DimN])(nil)
	_ ext.Typed[Carrier2[dsl.Real]] = (*Mat[dsl.Real, D2, DimK])(nil)
	_ ext.Typed[VecCarrier]         = (*RealVec[DimN])(nil)
	// A VecFun is Typed at its carrier under either spelling of the arrow:
	// a slot written at the curried arity takes it as it stands.
	_ ext.Typed[VecFunCarrier[dsl.Real]]                                 = (*VecFun[dsl.Real, DimN, DimM])(nil)
	_ ext.Typed[ext.Fun2[ext.Fun[ext.Nat, dsl.Real], ext.Nat, dsl.Real]] = (*VecFun[dsl.Real, DimN, SomeDim])(nil)
)

// ─────────────────────────── the anchor ───────────────────────────

func TestAnchorVec(t *testing.T) {
	carrier := core.MakeFun(ext.NumType, dsl.RealType)
	u := core.Var("u_0", carrier)
	n0, m0 := core.Var("n_0", ext.NumType), core.Var("m_0", ext.NumType)
	letters := map[string]core.Term{"n": n0, "m": m0}
	letter := func(name string) core.Term { return letters[name] }

	v := AnchorVec[dsl.Real, DimN](ext.WrapTerm(u), letter)
	if !v.Anchored() || !v.Dim().Equals(n0) {
		t.Fatalf("anchored at %s, want n_0", ext.PrintTerm(v.Dim()))
	}
	// A composite spec anchors every letter to the scope's variable.
	w := AnchorVec[dsl.Real, Plus[DimN, DimM]](ext.WrapTerm(u), letter)
	alphaEqual(t, w.Dim(), natPlus(n0, m0))
	if got := Letters(SpecOf[Plus[DimN, DimM]]()); len(got) != 2 || got[0] != "n" || got[1] != "m" {
		t.Fatalf("letters %v", got)
	}
	// A bare label has no dimension to write.
	bare := AsVec[dsl.Real, DimN](ext.WrapTerm(u))
	if bare.Anchored() {
		t.Fatal("AsVec must be bare")
	}
	mustPanic(t, "bare dimension label", func() { bare.Dim() })
	// An unresolved letter is refused at the anchor, and an anchored
	// vector is not relabeled by a bare recast.
	mustPanic(t, "letter k does not denote", func() {
		AnchorVec[dsl.Real, DimK](ext.WrapTerm(u), letter)
	})
	mustPanic(t, "relabels a BARE vector", func() { RecastVec[Plus[DimM, DimN]](w) })
}

func TestDescribeVecType(t *testing.T) {
	desc, ok := DescribeVecType(reflect.TypeFor[*Vec[dsl.Real, Plus[DimN, DimM]]]())
	if !ok {
		t.Fatal("not described")
	}
	if !desc.HOLType().Equals(core.MakeFun(ext.NumType, dsl.RealType)) {
		t.Fatalf("carrier %s", ext.FormatType(desc.HOLType()))
	}
	if l := desc.Letters(); len(l) != 2 || l[0] != "n" || l[1] != "m" {
		t.Fatalf("letters %v", l)
	}
	n0, m0 := core.Var("n_0", ext.NumType), core.Var("m_0", ext.NumType)
	u := core.Var("u_0", core.MakeFun(ext.NumType, dsl.RealType))
	got := desc.Anchor(ext.WrapTerm(u), func(name string) core.Term {
		return map[string]core.Term{"n": n0, "m": m0}[name]
	})
	v, ok := got.Interface().(*Vec[dsl.Real, Plus[DimN, DimM]])
	if !ok {
		t.Fatalf("anchored value has type %T", got.Interface())
	}
	alphaEqual(t, v.Dim(), natPlus(n0, m0))
	// A type embedding *Vec is not a Vec parameter.
	type wrapped struct{ *Vec[dsl.Real, DimN] }
	if _, ok := DescribeVecType(reflect.TypeFor[*wrapped]()); ok {
		t.Fatal("an embedder must be rejected")
	}
	if _, ok := DescribeVecType(reflect.TypeFor[*ext.Expr[dsl.Real]]()); ok {
		t.Fatal("a plain Expr is not a Vec")
	}
}

// SomeDim: the dimension no letter spells, anchored at a term (VecAt)
// rather than resolved by name; equal to itself alone; a leaf only.
func TestSomeDim(t *testing.T) {
	carrier := core.MakeFun(ext.NumType, dsl.RealType)
	u := core.Var("u_0", carrier)
	k0 := core.Var("k_0", ext.NumType)
	dim := natPlus(k0, ext.MakeNumeral(big.NewInt(3)))

	v := VecAt[dsl.Real](ext.WrapTerm(u), dim)
	if !v.Anchored() || !v.Dim().Equals(dim) {
		t.Fatalf("anchored at %s, want %s", ext.PrintTerm(v.Dim()), ext.PrintTerm(dim))
	}
	if got := v.Letters(); len(got) != 0 {
		t.Fatalf("SomeDim spells no letter, got %v", got)
	}
	// Equal to itself alone.
	if !SameDim[SomeDim, SomeDim]() || SameDim[SomeDim, DimN]() || SameDim[DimN, SomeDim]() || SameDim[SomeDim, D0]() {
		t.Fatal("SomeDim must equal SomeDim and nothing else")
	}
	// No spelling to lower, bare or by name; no place in a composite.
	mustPanic(t, "carries no spelling", func() { TermOf[SomeDim]() })
	mustPanic(t, "carries no spelling", func() {
		AnchorVec[dsl.Real, SomeDim](ext.WrapTerm(u), func(string) core.Term { return k0 })
	})
	mustPanic(t, "leaf dimension", func() { SameDim[Plus[SomeDim, DimN], Plus[SomeDim, DimN]]() })
	// A dimension is a num term.
	mustPanic(t, "not a num term", func() { VecAt[dsl.Real](ext.WrapTerm(u), u) })
	// The recast gate names it.
	mustPanic(t, "unequal dimensions some and n", func() { RecastVec[DimN](AsVec[dsl.Real, SomeDim](ext.WrapTerm(u))) })
	// A parameter at SomeDim reports itself to the binder door, also
	// inside a composite.
	desc, ok := DescribeVecType(reflect.TypeFor[*Vec[dsl.Real, SomeDim]]())
	if !ok || !desc.AtSomeDim() || len(desc.Letters()) != 0 {
		t.Fatal("a SomeDim vector parameter must describe itself as one")
	}
	if desc, ok := DescribeVecType(reflect.TypeFor[*Vec[dsl.Real, Plus[SomeDim, DimN]]]()); !ok || !desc.AtSomeDim() {
		t.Fatal("a composite over SomeDim must describe itself as one")
	}
	if desc, ok := DescribeVecType(reflect.TypeFor[*Vec[dsl.Real, DimN]]()); !ok || desc.AtSomeDim() {
		t.Fatal("a letter must not")
	}
	// The matrix door, at parity.
	p := core.Var("P_0", core.MakeFun(ext.NumType, ext.NumType, dsl.RealType))
	a := MatAt[dsl.Real](ext.WrapTerm(p), k0, dim)
	if !a.Rows().Equals(k0) || !a.Cols().Equals(dim) {
		t.Fatalf("anchored at %s × %s", ext.PrintTerm(a.Rows()), ext.PrintTerm(a.Cols()))
	}
	if mdesc, ok := DescribeMatType(reflect.TypeFor[*Mat[dsl.Real, DimN, SomeDim]]()); !ok || !mdesc.AtSomeDim() {
		t.Fatal("a matrix parameter at SomeDim must describe itself as one")
	}
}

// ─────────────────────────── the map ───────────────────────────

// vecFunCarrierType is `(num → real) → num → real`, built
// independently of the package's own phantom.
func vecFunCarrierType() core.HolType {
	vector := core.MakeFun(ext.NumType, dsl.RealType)
	return core.MakeFun(vector, vector)
}

func TestAnchorVecFun(t *testing.T) {
	f0 := core.Var("f_0", vecFunCarrierType())
	n0, m0 := core.Var("n_0", ext.NumType), core.Var("m_0", ext.NumType)
	letter := func(name string) core.Term {
		return map[string]core.Term{"n": n0, "m": m0}[name]
	}

	f := AnchorVecFun[dsl.Real, DimN, DimM](ext.WrapTerm(f0), letter)
	if !f.Anchored() {
		t.Fatal("AnchorVecFun must be anchored")
	}
	alphaEqual(t, f.Source(), n0)
	alphaEqual(t, f.Target(), m0)

	// Each phantom anchors on its own, and a composite spelling reaches
	// every letter of both.
	g := AnchorVecFun[dsl.Real, Plus[DimN, DimM], DimN](ext.WrapTerm(f0), letter)
	alphaEqual(t, g.Source(), natPlus(n0, m0))
	alphaEqual(t, g.Target(), n0)
	if got := g.Letters(); len(got) != 2 || got[0] != "n" || got[1] != "m" {
		t.Fatalf("letters %v", got)
	}
	// A map of a space into itself mentions one letter twice and reports
	// it once.
	endo := AnchorVecFun[dsl.Real, DimN, DimN](ext.WrapTerm(f0), letter)
	if got := endo.Letters(); len(got) != 1 || got[0] != "n" {
		t.Fatalf("letters %v", got)
	}
	alphaEqual(t, endo.Source(), endo.Target())

	// A bare label has no dimension to write — on either side.
	bare := AsVecFun[dsl.Real, DimN, DimM](ext.WrapTerm(f0))
	if bare.Anchored() {
		t.Fatal("AsVecFun must be bare")
	}
	mustPanic(t, "bare dimension label", func() { bare.Source() })
	mustPanic(t, "bare dimension label", func() { bare.Target() })
	// An unresolved letter is refused at the anchor.
	mustPanic(t, "letter k does not denote", func() {
		AnchorVecFun[dsl.Real, DimN, DimK](ext.WrapTerm(f0), letter)
	})
	// The carrier is the one kernel invariant: a vector is not a map,
	// and neither is a map into sequences of another element.
	mustPanic(t, "ext.As", func() {
		AsVecFun[dsl.Real, DimN, DimM](ext.Var("u", core.MakeFun(ext.NumType, dsl.RealType)))
	})
	mustPanic(t, "ext.As", func() {
		AsVecFun[dsl.Real, DimN, DimM](ext.Var("g", core.MakeFun(core.MakeFun(ext.NumType, dsl.RealType), ext.NumType, ext.NumType)))
	})
}

// The image of a vector under a map: a vector at the map's target
// phantom, anchored at its target term; the argument's phantom is the
// map's source by the signature, and its anchor by the check.
func TestVecFunApply(t *testing.T) {
	vector := core.MakeFun(ext.NumType, dsl.RealType)
	f0, u0 := core.Var("f_0", vecFunCarrierType()), core.Var("u_0", vector)
	n0, m0 := core.Var("n_0", ext.NumType), core.Var("m_0", ext.NumType)
	letter := func(name string) core.Term {
		return map[string]core.Term{"n": n0, "m": m0}[name]
	}
	f := AnchorVecFun[dsl.Real, DimN, DimM](ext.WrapTerm(f0), letter)
	u := AnchorVec[dsl.Real, DimN](ext.WrapTerm(u0), letter)

	image := f.Apply(u)
	var _ *Vec[dsl.Real, DimM] = image // the target phantom, statically
	alphaEqual(t, image.Core(), core.Apply(f0, u0))
	if !image.Anchored() || !image.Dim().Equals(m0) {
		t.Fatalf("the image is anchored at %s, want m_0", ext.PrintTerm(image.Dim()))
	}

	// Images compose: the next map is read on the first one's target.
	g := AnchorVecFun[dsl.Real, DimM, DimN](ext.WrapTerm(core.Var("g_0", vecFunCarrierType())), letter)
	var _ *Vec[dsl.Real, DimN] = g.Apply(f.Apply(u))

	// A bare map gives a bare image, of a bare or an anchored vector.
	bare := AsVecFun[dsl.Real, DimN, DimM](ext.WrapTerm(f0))
	if bare.Apply(u).Anchored() || bare.Apply(AsVec[dsl.Real, DimN](ext.WrapTerm(u0))).Anchored() {
		t.Fatal("a bare map's image must be bare")
	}
	// An anchored map reads an anchored vector: a bare one has no
	// dimension to check against the map's source.
	mustPanic(t, "bare dimension label", func() { f.Apply(AsVec[dsl.Real, DimN](ext.WrapTerm(u0))) })

	// At SomeDim the compiler ties nothing, and the check is the tie.
	k0 := core.Var("k_0", ext.NumType)
	some := VecFunAt[dsl.Real](ext.WrapTerm(f0), natPlus(k0, n0), m0)
	alphaEqual(t, some.Source(), natPlus(k0, n0))
	alphaEqual(t, some.Target(), m0)
	if got := some.Letters(); len(got) != 0 {
		t.Fatalf("SomeDim spells no letter, got %v", got)
	}
	at := some.Apply(VecAt[dsl.Real](ext.WrapTerm(u0), natPlus(k0, n0)))
	var _ *Vec[dsl.Real, SomeDim] = at
	if !at.Dim().Equals(m0) {
		t.Fatalf("the image is anchored at %s, want m_0", ext.PrintTerm(at.Dim()))
	}
	mustPanic(t, "is read on vectors of dimension", func() {
		some.Apply(VecAt[dsl.Real](ext.WrapTerm(u0), n0))
	})
	// A dimension is a num term, on either side.
	mustPanic(t, "not a num term", func() { VecFunAt[dsl.Real](ext.WrapTerm(f0), u0, m0) })
	mustPanic(t, "not a num term", func() { VecFunAt[dsl.Real](ext.WrapTerm(f0), n0, u0) })
}

func TestDescribeVecFunType(t *testing.T) {
	desc, ok := DescribeVecFunType(reflect.TypeFor[*VecFun[dsl.Real, Plus[DimN, DimM], DimN]]())
	if !ok {
		t.Fatal("not described")
	}
	if !desc.HOLType().Equals(vecFunCarrierType()) {
		t.Fatalf("carrier %s", ext.FormatType(desc.HOLType()))
	}
	if l := desc.Letters(); len(l) != 2 || l[0] != "n" || l[1] != "m" {
		t.Fatalf("letters %v", l)
	}
	n0, m0 := core.Var("n_0", ext.NumType), core.Var("m_0", ext.NumType)
	f0 := core.Var("f_0", vecFunCarrierType())
	got := desc.Anchor(ext.WrapTerm(f0), func(name string) core.Term {
		return map[string]core.Term{"n": n0, "m": m0}[name]
	})
	f, ok := got.Interface().(*VecFun[dsl.Real, Plus[DimN, DimM], DimN])
	if !ok {
		t.Fatalf("anchored value has type %T", got.Interface())
	}
	alphaEqual(t, f.Source(), natPlus(n0, m0))
	alphaEqual(t, f.Target(), n0)
	// A type embedding *VecFun is not a VecFun parameter, and neither a Vec nor
	// a Mat is one; nor is a VecFun either of those.
	type wrapped struct{ *VecFun[dsl.Real, DimN, DimM] }
	if _, ok := DescribeVecFunType(reflect.TypeFor[*wrapped]()); ok {
		t.Fatal("an embedder must be rejected")
	}
	if _, ok := DescribeVecFunType(reflect.TypeFor[*Vec[dsl.Real, DimN]]()); ok {
		t.Fatal("a Vec is not a VecFun")
	}
	if _, ok := DescribeVecFunType(reflect.TypeFor[*Mat[dsl.Real, DimN, DimM]]()); ok {
		t.Fatal("a Mat is not a VecFun")
	}
	if _, ok := DescribeMatType(reflect.TypeFor[*VecFun[dsl.Real, DimN, DimM]]()); ok {
		t.Fatal("a VecFun is not a Mat")
	}
	if _, ok := DescribeVecType(reflect.TypeFor[*VecFun[dsl.Real, DimN, DimM]]()); ok {
		t.Fatal("a VecFun is not a Vec")
	}
	// A parameter at SomeDim, on either side, reports itself to the
	// binder door.
	if d, ok := DescribeVecFunType(reflect.TypeFor[*VecFun[dsl.Real, DimN, SomeDim]]()); !ok || !d.AtSomeDim() {
		t.Fatal("a map parameter at SomeDim must describe itself as one")
	}
	if d, ok := DescribeVecFunType(reflect.TypeFor[*VecFun[dsl.Real, DimN, DimM]]()); !ok || d.AtSomeDim() {
		t.Fatal("letters must not")
	}
}
