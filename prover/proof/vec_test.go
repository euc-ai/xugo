package proof

import (
	"fmt"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dimtypes"
	"github.com/euc-ai/xugo/ext/dsl"
)

// The dimension-refined vector at the section boundary (vec.go): a
// *dimtypes.Vec parameter binds the carrier binder and anchors its
// letter to the dimension binder fixed before it; VecAs anchors a
// vector built mid-proof the same way; Inhabit pairs a vector with the
// membership fact naming its own anchor.

func newVecTestScript() *Script {
	ctx := NewScript(makeStepTestEnv())
	ctx.Var("P", MakeFun(numType, MakeFun(numType, dsl.RealType), TypeBool))
	return ctx
}

const vecTestStatement = "∀n:num. ∀u:(num → real). P(n, u) ⇒ (∃v:(num → real). P(n, v))"

func TestVecBinder_AnchorsToTheDimensionBinder(t *testing.T) {
	ctx := newVecTestScript()
	sec := ctx.Theorem(vecTestStatement,
		func(a *Argument, n *ext.Expr[ext.Nat], u *dimtypes.Vec[dsl.Real, dimtypes.DimN], mem Fact) {
			require.True(t, u.Anchored())
			require.True(t, u.Dim().Equals(n.Core()), "anchored at %s, want the fixed %s", ext.PrintTerm(u.Dim()), ext.PrintTerm(n))
			require.True(t, u.Core().Type().Equals(MakeFun(numType, dsl.RealType)))
			// A vector built mid-proof anchors through the same names.
			again := a.VecAs[dsl.Real, dimtypes.DimN]("u")
			require.True(t, again.Dim().Equals(n.Core()) && again.Core().Equals(u.Core()))
			// The pairing with the membership fact checks the anchor.
			inh := Inhabit(u, mem)
			content, _ := inh.Evidence().BoundContent()
			require.True(t, strings.HasPrefix(ext.PrintTerm(content), "P("), "%s", ext.PrintTerm(content))
			a.Take(u)
			a.Show("the vector itself", By(mem))
		})
	require.True(t, sec.Proved())
}

func TestVecBinder_Refusals(t *testing.T) {
	// The dimension must be bound before the vector.
	ctx := newVecTestScript()
	func() {
		defer func() {
			r := recover()
			require.NotNil(t, r)
			require.Contains(t, fmt.Sprint(r), "declare the dimension parameter before the vectors")
		}()
		ctx.Theorem("∀u:(num → real). ∀n:num. P(n, u) ⇒ (∃v:(num → real). P(n, v))",
			func(a *Argument, u *dimtypes.Vec[dsl.Real, dimtypes.DimN], n *ext.Expr[ext.Nat], mem Fact) {})
	}()
	// A vector parameter asserts the carrier.
	ctx = newVecTestScript()
	func() {
		defer func() {
			r := recover()
			require.NotNil(t, r)
			require.Contains(t, fmt.Sprint(r), "asserts carrier")
		}()
		ctx.Theorem("∀n:num. ∀u:(num → num). P(n, λi:num. &0) ⇒ (∃v:(num → real). P(n, v))",
			func(a *Argument, n *ext.Expr[ext.Nat], u *dimtypes.Vec[dsl.Real, dimtypes.DimN]) {})
	}()
	// VecAs at a letter no binder in scope spells.
	ctx = newVecTestScript()
	func() {
		defer func() {
			r := recover()
			require.NotNil(t, r)
			require.Contains(t, fmt.Sprint(r), "dimension letter m is not a binder in scope")
		}()
		ctx.Theorem(vecTestStatement, func(a *Argument, n Term, u Term, mem Fact) {
			a.VecAs[dsl.Real, dimtypes.DimM]("u")
		})
	}()
	// Inhabit refuses a fact about another vector or dimension.
	ctx = newVecTestScript()
	sec := ctx.Theorem("∀n m:num. ∀u v:(num → real). P(n, v) ⇒ P(m, u) ⇒ (∃w:(num → real). P(m, w))",
		func(a *Argument, n, m *ext.Expr[ext.Nat], u, v *dimtypes.Vec[dsl.Real, dimtypes.DimN], memV, memU Fact) {
			func() {
				defer func() {
					r := recover()
					require.NotNil(t, r)
					require.Contains(t, fmt.Sprint(r), "the vector asserts dimension")
				}()
				Inhabit(u, memU) // u is anchored at n; the fact says m
			}()
			a.Take(u)
			a.Show("the vector itself", By(memU))
		})
	require.True(t, sec.Proved())
	_ = core.TypeBool()
}

// requirePanicContaining asserts f panics with a message containing want.
func requirePanicContaining(t *testing.T, want string, f func()) {
	t.Helper()
	defer func() {
		r := recover()
		require.NotNil(t, r, "expected a panic containing %q", want)
		require.Contains(t, fmt.Sprint(r), want)
	}()
	f()
}

// A vector at a dimension no letter spells (vec.go: VecAt, InhabitFrom)
// is anchored at the term it is given, or at the dimension its
// membership fact spells, and carries SomeDim.
func TestVecAt_AnchorsAtTheGivenTerm(t *testing.T) {
	ctx := newVecTestScript()
	sec := ctx.Theorem("∀k:num. ∀u:(num → real). P(suc(k), u) ⇒ (∃v:(num → real). P(suc(k), v))",
		func(a *Argument, k *ext.Expr[ext.Nat], u *ext.Arrow[ext.Nat, dsl.Real], mem Fact) {
			dim := a.TermAs[ext.Nat]("suc(k)")
			v := a.VecAt[dsl.Real](dim, "u")
			require.True(t, v.Anchored())
			require.True(t, v.Dim().Equals(dim.Core()), "anchored at %s", ext.PrintTerm(v.Dim()))
			require.Empty(t, v.Letters())
			// The anchored vector pairs with the fact through Inhabit, checked.
			require.True(t, Inhabit(v, mem).Dim().Equals(dim.Core()))
			// InhabitFrom reads the dimension off the fact instead.
			inh := InhabitFrom(u, mem)
			require.True(t, inh.Dim().Equals(dim.Core()), "read %s", ext.PrintTerm(inh.Dim()))
			require.True(t, inh.Core().Equals(u.Core()))
			content, _ := inh.Evidence().BoundContent()
			require.True(t, strings.HasPrefix(ext.PrintTerm(content), "P("), "%s", ext.PrintTerm(content))
			a.Take(u)
			a.Show("the vector itself", By(mem))
		})
	require.True(t, sec.Proved())
}

func TestVecAt_Refusals(t *testing.T) {
	// A letter door refuses SomeDim: nothing to resolve by name.
	ctx := newVecTestScript()
	requirePanicContaining(t, "carries no spelling", func() {
		ctx.Theorem(vecTestStatement, func(a *Argument, n Term, u Term, mem Fact) {
			a.VecAs[dsl.Real, dimtypes.SomeDim]("u")
		})
	})
	// A closure parameter at SomeDim is refused at bind.
	ctx = newVecTestScript()
	requirePanicContaining(t, "which a closure parameter cannot anchor", func() {
		ctx.Theorem(vecTestStatement,
			func(a *Argument, n *ext.Expr[ext.Nat], u *dimtypes.Vec[dsl.Real, dimtypes.SomeDim], mem Fact) {})
	})
	// InhabitFrom refuses a fact about another vector.
	ctx = newVecTestScript()
	sec := ctx.Theorem("∀n:num. ∀u v:(num → real). P(n, v) ⇒ P(n, u) ⇒ (∃w:(num → real). P(n, w))",
		func(a *Argument, n *ext.Expr[ext.Nat], u, v *ext.Arrow[ext.Nat, dsl.Real], memV, memU Fact) {
			requirePanicContaining(t, "applied to a dimension and", func() { InhabitFrom(u, memV) })
			require.True(t, InhabitFrom(u, memU).Dim().Equals(n.Core()))
			a.Take(v)
			a.Show("the vector itself", By(memV))
		})
	require.True(t, sec.Proved())
}

// A map between two vector spaces at the section boundary (vec.go): a
// *dimtypes.VecFun parameter binds the map-carrier binder and anchors both
// phantoms' letters to the dimension binders fixed before it; VecFunAs
// anchors a map built mid-proof the same way, VecFunFixAs one dug from the
// goal; and the image of an anchored vector is a vector anchored at the
// map's target.
const vecFunTestStatement = "∀n m:num. ∀f:((num → real) → num → real). ∀u:(num → real). P(n, u) ⇒ P(m, f(u)) ⇒ (∃v:(num → real). P(m, v))"

type realVecFun = dimtypes.VecFun[dsl.Real, dimtypes.DimN, dimtypes.DimM]

func TestVecFunBinder_AnchorsToTheDimensionBinders(t *testing.T) {
	ctx := newVecTestScript()
	sec := ctx.Theorem(vecFunTestStatement,
		func(a *Argument, n, m *ext.Expr[ext.Nat], f *realVecFun, u *dimtypes.Vec[dsl.Real, dimtypes.DimN], memU, mem Fact) {
			require.True(t, f.Anchored())
			require.True(t, f.Source().Equals(n.Core()), "read on %s, want the fixed %s", ext.PrintTerm(f.Source()), ext.PrintTerm(n))
			require.True(t, f.Target().Equals(m.Core()), "read at %s, want the fixed %s", ext.PrintTerm(f.Target()), ext.PrintTerm(m))
			// A map built mid-proof anchors through the same names.
			again := a.VecFunAs[dsl.Real, dimtypes.DimN, dimtypes.DimM]("f")
			require.True(t, again.Source().Equals(n.Core()) && again.Target().Equals(m.Core()) && again.Core().Equals(f.Core()))
			// The image is the term the text spells, at the target.
			image := f.Apply(u)
			var _ *dimtypes.Vec[dsl.Real, dimtypes.DimM] = image
			require.True(t, image.Core().Equals(a.Term("f(u)").Core()))
			require.True(t, image.Dim().Equals(m.Core()), "the image is anchored at %s", ext.PrintTerm(image.Dim()))
			// So it pairs with the membership fact that names m, as the
			// vector does with the one that names n.
			Inhabit(u, memU)
			Inhabit(image, mem)
			a.Take(image)
			a.Show("the image itself", By(mem))
		})
	require.True(t, sec.Proved())
}

func TestVecFunFixAs_DigsAnAnchoredVecFun(t *testing.T) {
	ctx := newVecTestScript()
	sec := ctx.Theorem(vecFunTestStatement,
		func(a *Argument, n, m *ext.Expr[ext.Nat]) {
			f := a.VecFunFixAs[dsl.Real, dimtypes.DimN, dimtypes.DimM]()
			u := a.VecFixAs[dsl.Real, dimtypes.DimN]()
			a.Assume()
			mem := a.Assume()
			require.True(t, f.Source().Equals(n.Core()) && f.Target().Equals(m.Core()))
			require.True(t, f.Core().Equals(a.VecFunAs[dsl.Real, dimtypes.DimN, dimtypes.DimM]("f").Core()), "the dug map is the binder VecFunAs names")
			a.Take(f.Apply(u))
			a.Show("the image itself", By(mem))
		})
	require.True(t, sec.Proved())
}

func TestVecFunBinder_Refusals(t *testing.T) {
	// Both dimensions must be bound before the map.
	ctx := newVecTestScript()
	requirePanicContaining(t, "declare the dimension parameters before the maps", func() {
		ctx.Theorem("∀n:num. ∀f:((num → real) → num → real). ∀m:num. ∀u:(num → real). P(n, u) ⇒ P(m, f(u)) ⇒ (∃v:(num → real). P(m, v))",
			func(a *Argument, n *ext.Expr[ext.Nat], f *realVecFun, m *ext.Expr[ext.Nat]) {})
	})
	// A map parameter asserts the carrier: a matrix binder is not one.
	ctx = newVecTestScript()
	requirePanicContaining(t, "asserts carrier", func() {
		ctx.Theorem("∀n m:num. ∀f:(num → num → real). ∀u:(num → real). P(n, u) ⇒ P(m, f(n)) ⇒ (∃v:(num → real). P(m, v))",
			func(a *Argument, n, m *ext.Expr[ext.Nat], f *realVecFun) {})
	})
	// A closure parameter at SomeDim, on either side, is refused at bind.
	ctx = newVecTestScript()
	requirePanicContaining(t, "is a map at SomeDim, which a closure parameter cannot anchor", func() {
		ctx.Theorem(vecFunTestStatement,
			func(a *Argument, n, m *ext.Expr[ext.Nat], f *dimtypes.VecFun[dsl.Real, dimtypes.DimN, dimtypes.SomeDim]) {
			})
	})
	// VecFunAs at a letter no binder in scope spells, and at SomeDim.
	ctx = newVecTestScript()
	requirePanicContaining(t, "dimension letter k is not a binder in scope", func() {
		ctx.Theorem(vecFunTestStatement, func(a *Argument, n, m, f Term) {
			a.VecFunAs[dsl.Real, dimtypes.DimN, dimtypes.DimK]("f")
		})
	})
	ctx = newVecTestScript()
	requirePanicContaining(t, "carries no spelling", func() {
		ctx.Theorem(vecFunTestStatement, func(a *Argument, n, m, f Term) {
			a.VecFunAs[dsl.Real, dimtypes.SomeDim, dimtypes.DimM]("f")
		})
	})
}

// A map read at dimensions no letter spells (vec.go: VecFunAt) is anchored
// at the two terms it is given and carries SomeDim; its image of a
// vector anchored at its source term is anchored at its target term,
// and a vector anchored elsewhere is refused where the compiler could
// not refuse it.
func TestVecFunAt_AnchorsAtTheGivenTerms(t *testing.T) {
	ctx := newVecTestScript()
	sec := ctx.Theorem("∀k m:num. ∀f:((num → real) → num → real). ∀u:(num → real). P(suc(k), u) ⇒ P(m + k, f(u)) ⇒ (∃v:(num → real). P(m + k, v))",
		func(a *Argument, k, m *ext.Expr[ext.Nat], f *ext.Arrow[ext.Fun[ext.Nat, dsl.Real], ext.Fun[ext.Nat, dsl.Real]], u *ext.Arrow[ext.Nat, dsl.Real], memU, mem Fact) {
			source, target := a.TermAs[ext.Nat]("suc(k)"), a.TermAs[ext.Nat]("m + k")
			g := a.VecFunAt[dsl.Real](source, target, "f")
			require.True(t, g.Anchored())
			require.True(t, g.Source().Equals(source.Core()) && g.Target().Equals(target.Core()))
			require.Empty(t, g.Letters())
			image := g.Apply(a.VecAt[dsl.Real](source, "u"))
			var _ *dimtypes.Vec[dsl.Real, dimtypes.SomeDim] = image
			require.True(t, image.Dim().Equals(target.Core()), "the image is anchored at %s", ext.PrintTerm(image.Dim()))
			Inhabit(image, mem)
			requirePanicContaining(t, "is read on vectors of dimension", func() {
				g.Apply(a.VecAt[dsl.Real](target, "u"))
			})
			a.Take(image)
			a.Show("the image itself", By(mem))
		})
	require.True(t, sec.Proved())
}
