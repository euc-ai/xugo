// vec_fun.go — the dimension-refined FUNCTION between term-level vector
// spaces: VecFun[Elem, Source, Target], the wrapper beside Vec and Mat
// for the third carrier shape a vector chapter states over, a function
// from the vectors of one dimension to those of another, linear or not.
// A map carrying ℝⁿ into ℝᵐ is a term of type `(num → real) → num →
// real` at every n and m — the kernel type says nothing of either — and
// the statement reads it at the two through the constants it is handed
// to (`vec_op_norm⟨n, m⟩(L)`). The two phantoms carry that
// reading: Source is the dimension of the vectors the map is read on,
// Target the dimension its values are read at.
//
// What the wrapper asserts is what Vec's does. The KERNEL invariant is
// the carrier type, checked at the adoption gate; the two phantoms are
// authoring intent, and no fact that the map carries n-vectors to
// m-vectors is pinned to the term. A map is BARE (AsVecFun) or ANCHORED
// (AnchorVecFun — the section binder and Argument.VecFunAs; VecFunAt at
// two given terms, carrying SomeDim), and Source()/Target() are the two
// dimension terms a cite writes for an anchored one.
//
// One element, not two: source and target are sequences over the same
// Elem, which is what a map between two spaces over one ring of scalars
// is. A map whose values are sequences over another type keeps the plain
// typed spelling.

package dimtypes

import (
	"fmt"
	"reflect"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// VecFunCarrier is the kernel-level type of a map between term-level
// vector spaces at a given element, `(num → Elem) → num → Elem`: one HOL
// type across every pair of dimension phantoms, as Carrier is across
// every dimension.
type VecFunCarrier[Elem ext.TypePhantom] = ext.Fun[Carrier[Elem], Carrier[Elem]]

// VecFun is a map term refined by the dimension of the vectors it is read
// on and the dimension its values are read at. The embedded typed
// wrapper carries the kernel invariant (the term's HOL type IS
// `(num → Elem) → num → Elem`); the teeth make maps between different
// dimensions distinct, inconvertible Go types.
type VecFun[Elem ext.TypePhantom, Source, Target DimPhantom] struct {
	ext.Expr[VecFunCarrier[Elem]]
	_      [0]Source
	_      [0]Target
	source core.Term
	target core.Term
}

// AsVecFun adopts a term as a map from Source-vectors to Target-vectors,
// same contract as AsVec: the HOL type is checked, the dimensions are
// the author's asserted intent.
func AsVecFun[Elem ext.TypePhantom, Source, Target DimPhantom](t ext.Term) *VecFun[Elem, Source, Target] {
	return &VecFun[Elem, Source, Target]{Expr: *ext.As[VecFunCarrier[Elem]](t)}
}

// AnchorVecFun adopts a term as a map ANCHORED to the letters' terms, the
// two-dimension AnchorVec: the HOL type is checked (ext.As), and each
// phantom's spec is lowered with letter(name) for each letter.
func AnchorVecFun[Elem ext.TypePhantom, Source, Target DimPhantom](t ext.Term, letter func(name string) core.Term) *VecFun[Elem, Source, Target] {
	f := AsVecFun[Elem, Source, Target](t)
	f.source = SpecTermWith(SpecOf[Source](), letter)
	f.target = SpecTermWith(SpecOf[Target](), letter)
	return f
}

// VecFunAt is VecAt at a map's two dimensions: a map ANCHORED at the given
// source and target terms, carrying SomeDim for both.
func VecFunAt[Elem ext.TypePhantom](t ext.Term, source, target core.Term) *VecFun[Elem, SomeDim, SomeDim] {
	f := AsVecFun[Elem, SomeDim, SomeDim](t)
	f.source, f.target = givenDim(source), givenDim(target)
	return f
}

// Anchored reports whether the map's dimension letters have been
// resolved to terms (AnchorVecFun, VecFunAt) or are bare labels (AsVecFun).
func (f *VecFun[Elem, Source, Target]) Anchored() bool { return f.source != nil }

// Source is the dimension term of the vectors an anchored map is read
// on. A bare label has none and panics, the same way Vec.Dim does.
func (f *VecFun[Elem, Source, Target]) Source() core.Term {
	return f.anchorTerm(f.source, SpecOf[Source]())
}

// Target is the dimension term an anchored map's values are read at.
func (f *VecFun[Elem, Source, Target]) Target() core.Term {
	return f.anchorTerm(f.target, SpecOf[Target]())
}

func (f *VecFun[Elem, Source, Target]) anchorTerm(t core.Term, spec DimSpec) core.Term {
	if t == nil {
		panic(fmt.Sprintf("dimtypes: %s carries a bare dimension label %s — anchor it (a section binder, Argument.VecFunAs, Argument.VecFunAt) before citing at it",
			ext.PrintTerm(f), spellSpec(spec)))
	}
	return t
}

// Letters lists the dimension letters the two phantoms mention, source
// first, each once — what an anchoring site must resolve.
func (f *VecFun[Elem, Source, Target]) Letters() []string {
	return mergeLetters(Letters(SpecOf[Source]()), Letters(SpecOf[Target]()))
}

// Apply is the image f(x) of a vector under the map. The argument is a
// vector at the map's own source phantom and the result a vector at its
// target phantom, both fixed by the receiver's type: a vector of another
// dimension does not compile. The typed Apply shadows the untyped one
// the embedded wrapper promotes, as ext.Arrow's does.
//
// An anchored map gives an image anchored at its target term, and
// checks that the argument is anchored at its source term — the runtime
// half of the compile-time tie, and at SomeDim the whole of it. A bare
// map gives a bare image.
func (f *VecFun[Elem, Source, Target]) Apply(x *Vec[Elem, Source]) *Vec[Elem, Target] {
	image := AsVec[Elem, Target](ext.Apply(f.Core(), x.Core()))
	if f.source == nil {
		return image
	}
	if !x.Dim().Equals(f.source) {
		panic(fmt.Sprintf("dimtypes: %s is read on vectors of dimension %s, and %s is anchored at %s",
			ext.PrintTerm(f), ext.PrintTerm(f.source), ext.PrintTerm(x), ext.PrintTerm(x.Dim())))
	}
	image.dim = f.target
	return image
}

// The map probe is the matrix probe over the map's carrier: a VecFun
// parameter reports one carrier type, the letters of both phantoms, and
// the two-dimension anchoring constructor.

type vecFunRuntime interface {
	vecFunRuntimeInfo() vecFunRuntimeInfo
}

type vecFunRuntimeInfo struct {
	holType core.HolType
	goType  reflect.Type
	letters []string
	some    bool
	anchor  func(t ext.Term, letter func(string) core.Term) ext.TermLike
}

func (*VecFun[Elem, Source, Target]) vecFunRuntimeInfo() vecFunRuntimeInfo {
	return vecFunRuntimeInfo{
		holType: ext.HolTypeOf[VecFunCarrier[Elem]](),
		goType:  reflect.TypeFor[*VecFun[Elem, Source, Target]](),
		letters: mergeLetters(Letters(SpecOf[Source]()), Letters(SpecOf[Target]())),
		some:    mentionsSome(SpecOf[Source]()) || mentionsSome(SpecOf[Target]()),
		anchor: func(t ext.Term, letter func(string) core.Term) ext.TermLike {
			return AnchorVecFun[Elem, Source, Target](t, letter)
		},
	}
}

// VecFunDescriptor is a VecFun instantiation described at runtime — the
// carrier type the parameter asserts, the letters BOTH its phantoms need
// anchored, and the anchoring constructor. From DescribeVecFunType.
type VecFunDescriptor struct{ info vecFunRuntimeInfo }

// DescribeVecFunType reports whether rt is *VecFun[Elem, Source, Target] at
// some phantoms and returns its descriptor. A type EMBEDDING *VecFun
// inherits the probe by promotion; the Go-type identity check rejects
// exactly that.
func DescribeVecFunType(rt reflect.Type) (VecFunDescriptor, bool) {
	if rt == nil || rt.Kind() != reflect.Pointer {
		return VecFunDescriptor{}, false
	}
	probe, ok := reflect.New(rt.Elem()).Interface().(vecFunRuntime)
	if !ok {
		return VecFunDescriptor{}, false
	}
	info := probe.vecFunRuntimeInfo()
	if info.goType != rt {
		return VecFunDescriptor{}, false
	}
	return VecFunDescriptor{info: info}, true
}

// HOLType is the carrier type the parameter asserts.
func (d VecFunDescriptor) HOLType() core.HolType { return d.info.holType }

// Letters lists the dimension letters the parameter's two phantoms need
// resolved, source first, each once.
func (d VecFunDescriptor) Letters() []string { return d.info.letters }

// AtSomeDim reports whether either phantom mentions SomeDim, which no
// name resolves: the section binder refuses such a parameter, and the
// proof adopts the binder with Argument.VecFunAt instead.
func (d VecFunDescriptor) AtSomeDim() bool { return d.info.some }

// Anchor runs the instantiation's anchoring constructor on t and returns
// the value at the descriptor's own Go type, for reflect.Call.
func (d VecFunDescriptor) Anchor(t ext.Term, letter func(string) core.Term) reflect.Value {
	v := reflect.ValueOf(d.info.anchor(t, letter))
	if v.Type() != d.info.goType {
		panic("dimtypes: internal VecFun descriptor type mismatch")
	}
	return v
}
