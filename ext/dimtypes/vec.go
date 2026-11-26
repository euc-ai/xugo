// vec.go — the dimension-refined wrappers over term-level carriers:
// Vec[Elem, D] and Mat[Elem, R, C], each an ext typed wrapper (so the
// kernel-level type invariant and the whole untyped method set come by
// embedding) plus dimension phantoms the compiler enforces across
// operations; VecFun[Elem, Source, Target], the map between two vector
// spaces, is vec_fun.go. The element rides a TypePhantom — a chapter stated
// over the letter A carries its vectors as Vec[A, D], and a concrete
// theory instantiates the same wrapper at its own element.
//
// What the wrapper asserts, and what it does not: the KERNEL invariant
// is the carrier type (`num → Elem`, checked at the adoption gate); the
// DIMENSION phantom alone is authoring intent — a bare AsVec pins no
// membership fact to the term. An ANCHORED Vec (AnchorVec — the proof
// layer's section binder and Argument.VecAs) has resolved its letters
// to the terms the enclosing scope spells them by, and Dim() is what a
// cite writes for it — VecAt anchors a SomeDim vector at a given term,
// the dimension no letter spells; the label becomes trustworthy where it meets
// evidence, in proof.Inhabit, which checks a membership fact against
// that anchor (proofs/cartesian/carrier and proofs/vector are the
// tenants). Keeping the bare wrapper evidence-free is deliberate —
// terms are built long before facts about them exist.
//
// The real-only VECTOR operation set below is PROVISIONAL, chosen to
// exercise the surface: pointwise operations are bound-free, and the
// operations that genuinely consume a dimension (an inner product's
// range, a concatenation's cut) take it as their first num argument —
// which is exactly where a phantom reifies, so the dimension argument
// writes itself and cannot disagree with the checked phantom. Those
// theory constants are package-owned experimental metas standing in for
// a family mint, monomorphic at the ℝ carrier, and their methods live on
// RealVec rather than the element-polymorphic Vec: a typed surface must
// not advertise an operation that only discovers at runtime that Elem
// was not ℝ. A mint replaces the metas, not the structural refinement.
//
// The MATRIX half has been through that replacement, and it is what the
// remaining asymmetry records: proofs/vector/matrix mints `matrix_mul`,
// `matrix_act` and `transpose` over an arbitrary commutative ring, so
// the placeholder ℝ metas and the RealMat that hosted them are gone, and
// Mat carries only the structural refinement — which is now at parity
// with Vec, anchoring included.

package dimtypes

import (
	"fmt"
	"reflect"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
)

// Carrier is the kernel-level type of a term-level vector at a given
// element: an ordinary TypePhantom alias, so every Vec at that element
// shares ONE HOL type across all dimension phantoms (the refinement
// lives in Go only). Carrier2 is the matrix analog.
type (
	Carrier[Elem ext.TypePhantom]  = ext.Fun[ext.Nat, Elem]
	Carrier2[Elem ext.TypePhantom] = ext.Fun2[ext.Nat, ext.Nat, Elem]
)

// VecCarrier is the experimental vector operations' own carrier — the ℝ
// instance the placeholder metas below are typed at.
type VecCarrier = Carrier[dsl.Real]

// The experimental theory constants. Bound-free where the operation is
// pointwise; an explicit leading num bound where the mathematics needs
// one.
var (
	vecType = ext.HolTypeOf[VecCarrier]()

	vecAddMeta       = core.MakeConstMeta("vec_add", core.MakeFun(vecType, vecType, vecType))
	vecScalarMulMeta = core.MakeConstMeta("smul", core.MakeFun(dsl.RealType, vecType, vecType))
	dotMeta          = core.MakeConstMeta("dot", core.MakeFun(ext.NumType, vecType, vecType, dsl.RealType))
	vconcatMeta      = core.MakeConstMeta("vconcat", core.MakeFun(ext.NumType, vecType, vecType, vecType))
)

// Vec is a vector term refined by its dimension phantom. The embedded
// typed wrapper carries the kernel invariant (the term's HOL type IS
// `num → Elem`); the tooth makes Vecs of different dimensions distinct,
// inconvertible Go types.
//
// A Vec is BARE or ANCHORED. Bare (AsVec) the phantom is authoring
// intent and reifies nowhere; anchored (AnchorVec — the section binder
// and Argument.VecAs) the letters of D have been resolved to the terms
// the enclosing section spells them by, and Dim() is the dimension
// term a cite writes for it; a SomeDim vector is anchored by VecAt at
// the term it is given. The distinction is what keeps a letter from
// being reified by NAME into a section that minted the binder as
// `n_0`.
type Vec[Elem ext.TypePhantom, D DimPhantom] struct {
	ext.Expr[Carrier[Elem]]
	_   [0]D
	dim core.Term
}

// AnchorVec adopts a term as a D-dimensional vector ANCHORED to the
// letters' terms: the HOL type is checked (ext.As), and the dimension
// term is D's spec lowered with letter(name) for each letter — the
// scope's own variable for the name, supplied by the proof layer.
func AnchorVec[Elem ext.TypePhantom, D DimPhantom](t ext.Term, letter func(name string) core.Term) *Vec[Elem, D] {
	v := AsVec[Elem, D](t)
	v.dim = SpecTermWith(SpecOf[D](), letter)
	return v
}

// VecAt adopts a term as a vector ANCHORED at the given dimension term
// — the door for a dimension no letter spells (a Let, a literal,
// `suc(m)`, a degree): the HOL type is checked (ext.As), the dimension
// must be a num term, and Dim() is that term. The value carries
// SomeDim, the one phantom with no spelling to resolve by name.
func VecAt[Elem ext.TypePhantom](t ext.Term, dim core.Term) *Vec[Elem, SomeDim] {
	v := AsVec[Elem, SomeDim](t)
	v.dim = givenDim(dim)
	return v
}

// givenDim checks a term handed in as a dimension: a num term.
func givenDim(dim core.Term) core.Term {
	if dim == nil {
		panic("dimtypes: a nil term is not a dimension")
	}
	if !dim.Type().Equals(ext.NumType) {
		panic(fmt.Sprintf("dimtypes: %s is not a num term — a dimension is one", ext.PrintTerm(dim)))
	}
	return dim
}

// Anchored reports whether the vector's dimension letters have been
// resolved to terms (AnchorVec) or are a bare label (AsVec).
func (v *Vec[Elem, D]) Anchored() bool { return v.dim != nil }

// Dim is the dimension term an anchored vector is read at — what a
// cite writes for the statement's dimension binder. A bare label has
// none and panics: adopt the vector through a section binder,
// Argument.VecAs or Argument.VecAt.
func (v *Vec[Elem, D]) Dim() core.Term {
	if v.dim == nil {
		panic(fmt.Sprintf("dimtypes: %s carries a bare dimension label %s — anchor it (a section binder, Argument.VecAs, Argument.VecAt) before citing at it",
			ext.PrintTerm(v), spellSpec(SpecOf[D]())))
	}
	return v.dim
}

// Letters lists the dimension letters the phantom D mentions.
func (v *Vec[Elem, D]) Letters() []string { return Letters(SpecOf[D]()) }

// Mat is a matrix term refined by row and column dimension phantoms —
// Vec's two-index sibling, and BARE or ANCHORED on the same terms. Bare
// (AsMat) the phantoms are authoring intent; anchored (AnchorMat — the
// section binder and Argument.MatAs) each phantom's letters have been
// resolved to the terms the enclosing section spells them by, and
// Rows()/Cols() are the two dimension terms a cite writes for it.
type Mat[Elem ext.TypePhantom, R, C DimPhantom] struct {
	ext.Expr[Carrier2[Elem]]
	_    [0]R
	_    [0]C
	rows core.Term
	cols core.Term
}

// AnchorMat adopts a term as an R×C matrix ANCHORED to the letters'
// terms, the two-dimension AnchorVec: the HOL type is checked (ext.As),
// and each phantom's spec is lowered with letter(name) for each letter.
func AnchorMat[Elem ext.TypePhantom, R, C DimPhantom](t ext.Term, letter func(name string) core.Term) *Mat[Elem, R, C] {
	a := AsMat[Elem, R, C](t)
	a.rows = SpecTermWith(SpecOf[R](), letter)
	a.cols = SpecTermWith(SpecOf[C](), letter)
	return a
}

// MatAt is VecAt at two dimensions: a matrix ANCHORED at the given row
// and column terms, carrying SomeDim for both.
func MatAt[Elem ext.TypePhantom](t ext.Term, rows, cols core.Term) *Mat[Elem, SomeDim, SomeDim] {
	a := AsMat[Elem, SomeDim, SomeDim](t)
	a.rows, a.cols = givenDim(rows), givenDim(cols)
	return a
}

// Anchored reports whether the matrix's dimension letters have been
// resolved to terms (AnchorMat) or are bare labels (AsMat).
func (a *Mat[Elem, R, C]) Anchored() bool { return a.rows != nil }

// Rows is the row-dimension term an anchored matrix is read at. A bare
// label has none and panics, the same way Vec.Dim does.
func (a *Mat[Elem, R, C]) Rows() core.Term { return a.anchorTerm(a.rows, SpecOf[R]()) }

// Cols is the column-dimension term an anchored matrix is read at.
func (a *Mat[Elem, R, C]) Cols() core.Term { return a.anchorTerm(a.cols, SpecOf[C]()) }

func (a *Mat[Elem, R, C]) anchorTerm(t core.Term, spec DimSpec) core.Term {
	if t == nil {
		panic(fmt.Sprintf("dimtypes: %s carries a bare dimension label %s — anchor it (a section binder, Argument.MatAs, Argument.MatAt) before citing at it",
			ext.PrintTerm(a), spellSpec(spec)))
	}
	return t
}

// Letters lists the dimension letters the two phantoms mention, rows
// first, each once — what an anchoring site must resolve.
func (a *Mat[Elem, R, C]) Letters() []string {
	return mergeLetters(Letters(SpecOf[R]()), Letters(SpecOf[C]()))
}

// mergeLetters concatenates two letter lists, keeping first-occurrence
// order and dropping the repeats (a square matrix mentions one letter
// twice).
func mergeLetters(first, second []string) []string {
	out := append([]string(nil), first...)
	seen := map[string]bool{}
	for _, name := range first {
		seen[name] = true
	}
	for _, name := range second {
		if !seen[name] {
			seen[name] = true
			out = append(out, name)
		}
	}
	return out
}

// RealVec is the provisional algebraic face. It keeps the generic
// carrier refinement reusable by polymorphic proof chapters while
// exposing the placeholder operations only at the one HOL element type
// their metas actually accept. There is no RealMat: the matrix
// operations are minted, so a matrix needs no ℝ-only face.
type RealVec[D DimPhantom] struct{ Vec[dsl.Real, D] }

// AsVec adopts a term as a D-dimensional vector: the HOL type is
// CHECKED (through ext.As, the one adoption gate), the dimension is
// the author's asserted intent — the kernel obligations that ground it
// arise later, where the dimension enters a statement (and the label
// becomes checked where it meets its membership fact — see the package
// comment).
func AsVec[Elem ext.TypePhantom, D DimPhantom](t ext.Term) *Vec[Elem, D] {
	return &Vec[Elem, D]{Expr: *ext.As[Carrier[Elem]](t)}
}

// AsMat adopts a term as an R×C matrix, same contract as AsVec.
func AsMat[Elem ext.TypePhantom, R, C DimPhantom](t ext.Term) *Mat[Elem, R, C] {
	return &Mat[Elem, R, C]{Expr: *ext.As[Carrier2[Elem]](t)}
}

func AsRealVec[D DimPhantom](t ext.Term) *RealVec[D] {
	return &RealVec[D]{Vec: *AsVec[dsl.Real, D](t)}
}

// ─────────────────────────── vector operations ───────────────────────────

// Add is pointwise vector addition — same dimension enforced by the
// compiler, no bound in the term.
func (v *RealVec[D]) Add(w *RealVec[D]) *RealVec[D] {
	return AsRealVec[D](ext.Apply(vecAddMeta.Term(), v.Core(), w.Core()))
}

// Scale is scalar multiplication; the scalar arrives through the typed
// currency, so any real-typed wrapper fits.
func (v *RealVec[D]) Scale(c ext.Typed[dsl.Real]) *RealVec[D] {
	return AsRealVec[D](ext.Apply(vecScalarMulMeta.Term(), c.Core(), v.Core()))
}

// Dot is the inner product over the first D coordinates. The bound in
// the term is the receiver's own phantom, reified — the argument
// writes itself.
func (v *RealVec[D]) Dot(w *RealVec[D]) *ext.Expr[dsl.Real] {
	return ext.As[dsl.Real](ext.Apply(dotMeta.Term(), TermOf[D](), v.Core(), w.Core()))
}

// Concat lays w after v; the cut point is v's own dimension, reified.
// The result dimension is the composite Plus[D, E], carried through
// the signature by the exact-type constraint S (the smuggle — spelling
// Vec[Elem, Plus[D, E]] here directly is an instantiation cycle). Call
// sites write no annotations: S is inferred.
func (v *RealVec[D]) Concat[E DimPhantom, S IsPlus[D, E]](w *RealVec[E]) *RealVec[S] {
	return AsRealVec[S](ext.Apply(vconcatMeta.Term(), TermOf[D](), v.Core(), w.Core()))
}

// ─────────────────────────── recasting ───────────────────────────

// RecastVec relabels a vector's dimension phantom to a provably-equal
// spelling (Plus[DimM, DimN] to Plus[DimN, DimM], Times[D2, DimN] to Plus[DimN, DimN], …).
// The term does not move — only the Go-level refinement is renamed —
// so the gate is the complete linear-arithmetic equality decision, and
// an unequal pair panics. Spelled with the TARGET first, so a call
// site reads RecastVec[Plus[DimN, DimM]](v) with the source inferred.
func RecastVec[E DimPhantom, Elem ext.TypePhantom, D DimPhantom](v *Vec[Elem, D]) *Vec[Elem, E] {
	mustSameDim[D, E]()
	if v.dim != nil {
		panic("dimtypes: RecastVec relabels a BARE vector; an anchored dimension moves with its evidence (carrier's Recast)")
	}
	return &Vec[Elem, E]{Expr: v.Expr}
}

// RecastMat is RecastVec for both matrix dimensions, targets first, and
// relabels a BARE matrix for the same reason: an anchored dimension
// moves with its evidence, not with a relabeling.
func RecastMat[R2, C2 DimPhantom, Elem ext.TypePhantom, R, C DimPhantom](a *Mat[Elem, R, C]) *Mat[Elem, R2, C2] {
	mustSameDim[R, R2]()
	mustSameDim[C, C2]()
	if a.rows != nil {
		panic("dimtypes: RecastMat relabels a BARE matrix; an anchored dimension moves with its evidence")
	}
	return &Mat[Elem, R2, C2]{Expr: a.Expr}
}

func RecastRealVec[E, D DimPhantom](v *RealVec[D]) *RealVec[E] {
	mustSameDim[D, E]()
	return &RealVec[E]{Vec: Vec[dsl.Real, E]{Expr: v.Expr}}
}

// ─────────────────────────── the reflection probe ───────────────────────────
//
// The section binder holds a closure parameter's type only as a
// reflect.Type. Like ext's Expr descriptor (expr.go), one sealed method
// on the concrete instantiation re-enters the generic machinery with
// Elem and D bound and hands back plain runtime values: the carrier's
// HOL type, the instantiation's own Go type, and the anchoring
// constructor as a closure.

type vecRuntime interface {
	vecRuntimeInfo() vecRuntimeInfo
}

type vecRuntimeInfo struct {
	holType core.HolType
	goType  reflect.Type
	letters []string
	some    bool
	anchor  func(t ext.Term, letter func(string) core.Term) ext.TermLike
}

func (*Vec[Elem, D]) vecRuntimeInfo() vecRuntimeInfo {
	return vecRuntimeInfo{
		holType: ext.HolTypeOf[Carrier[Elem]](),
		goType:  reflect.TypeFor[*Vec[Elem, D]](),
		letters: Letters(SpecOf[D]()),
		some:    mentionsSome(SpecOf[D]()),
		anchor: func(t ext.Term, letter func(string) core.Term) ext.TermLike {
			return AnchorVec[Elem, D](t, letter)
		},
	}
}

// VecDescriptor is a Vec instantiation described at runtime: the
// carrier type the parameter asserts, the letters it needs anchored,
// and the anchoring constructor. From DescribeVecType.
type VecDescriptor struct{ info vecRuntimeInfo }

// DescribeVecType reports whether rt is *Vec[Elem, D] at some phantoms
// and returns its descriptor. A type EMBEDDING *Vec inherits the probe
// by promotion; the Go-type identity check rejects exactly that.
func DescribeVecType(rt reflect.Type) (VecDescriptor, bool) {
	if rt == nil || rt.Kind() != reflect.Pointer {
		return VecDescriptor{}, false
	}
	probe, ok := reflect.New(rt.Elem()).Interface().(vecRuntime)
	if !ok {
		return VecDescriptor{}, false
	}
	info := probe.vecRuntimeInfo()
	if info.goType != rt {
		return VecDescriptor{}, false
	}
	return VecDescriptor{info: info}, true
}

// HOLType is the carrier type the parameter asserts.
func (d VecDescriptor) HOLType() core.HolType { return d.info.holType }

// Letters lists the dimension letters the parameter's phantom needs
// resolved.
func (d VecDescriptor) Letters() []string { return d.info.letters }

// AtSomeDim reports whether the phantom mentions SomeDim, which no name
// resolves: the section binder refuses such a parameter, and the proof
// adopts the binder with Argument.VecAt instead.
func (d VecDescriptor) AtSomeDim() bool { return d.info.some }

// Anchor runs the instantiation's anchoring constructor on t and
// returns the value at the descriptor's own Go type, for reflect.Call.
func (d VecDescriptor) Anchor(t ext.Term, letter func(string) core.Term) reflect.Value {
	v := reflect.ValueOf(d.info.anchor(t, letter))
	if v.Type() != d.info.goType {
		panic("dimtypes: internal Vec descriptor type mismatch")
	}
	return v
}

// The matrix probe is the same machinery with two dimensions: a Mat
// parameter reports one carrier type, the letters of BOTH phantoms, and
// the two-dimension anchoring constructor.

type matRuntime interface {
	matRuntimeInfo() matRuntimeInfo
}

type matRuntimeInfo struct {
	holType core.HolType
	goType  reflect.Type
	letters []string
	some    bool
	anchor  func(t ext.Term, letter func(string) core.Term) ext.TermLike
}

func (*Mat[Elem, R, C]) matRuntimeInfo() matRuntimeInfo {
	return matRuntimeInfo{
		holType: ext.HolTypeOf[Carrier2[Elem]](),
		goType:  reflect.TypeFor[*Mat[Elem, R, C]](),
		letters: mergeLetters(Letters(SpecOf[R]()), Letters(SpecOf[C]())),
		some:    mentionsSome(SpecOf[R]()) || mentionsSome(SpecOf[C]()),
		anchor: func(t ext.Term, letter func(string) core.Term) ext.TermLike {
			return AnchorMat[Elem, R, C](t, letter)
		},
	}
}

// MatDescriptor is a Mat instantiation described at runtime — the carrier
// type the parameter asserts, the letters BOTH its phantoms need anchored,
// and the anchoring constructor. VecDescriptor's sibling, from
// DescribeMatType.
type MatDescriptor struct{ info matRuntimeInfo }

// DescribeMatType reports whether rt is *Mat[Elem, R, C] at some phantoms
// and returns its descriptor. A type EMBEDDING *Mat inherits the probe by
// promotion; the Go-type identity check rejects exactly that.
func DescribeMatType(rt reflect.Type) (MatDescriptor, bool) {
	if rt == nil || rt.Kind() != reflect.Pointer {
		return MatDescriptor{}, false
	}
	probe, ok := reflect.New(rt.Elem()).Interface().(matRuntime)
	if !ok {
		return MatDescriptor{}, false
	}
	info := probe.matRuntimeInfo()
	if info.goType != rt {
		return MatDescriptor{}, false
	}
	return MatDescriptor{info: info}, true
}

// HOLType is the carrier type the parameter asserts.
func (d MatDescriptor) HOLType() core.HolType { return d.info.holType }

// Letters lists the dimension letters the parameter's two phantoms need
// resolved, rows first, each once.
func (d MatDescriptor) Letters() []string { return d.info.letters }

// AtSomeDim reports whether either phantom mentions SomeDim, which no
// name resolves: the section binder refuses such a parameter, and the
// proof adopts the binder with Argument.MatAt instead.
func (d MatDescriptor) AtSomeDim() bool { return d.info.some }

// Anchor runs the instantiation's anchoring constructor on t and returns
// the value at the descriptor's own Go type, for reflect.Call.
func (d MatDescriptor) Anchor(t ext.Term, letter func(string) core.Term) reflect.Value {
	v := reflect.ValueOf(d.info.anchor(t, letter))
	if v.Type() != d.info.goType {
		panic("dimtypes: internal Mat descriptor type mismatch")
	}
	return v
}
