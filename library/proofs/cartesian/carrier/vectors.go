// vectors.go — the dimension-refined face of the chapter: where the
// dimtypes phantoms meet the theorems.
//
// Everything else in the family is stated and proved over plain terms;
// this file is the ONE seam where a proof body opts into the refined
// reading. Three pieces, and the order is the contract:
//
// - Vec[Elem, Dim] (dimtypes' wrapper, under the authoring surface's
// bare name): a carrier value with its dimension in the Go type. A
// bare adoption (dimtypes.AsVec) is authoring INTENT — nothing ties
// the label to a fact.
// - InhabitedVec[Elem, Dim]: the label made TRUE — the Vec ANCHORED at
// the fact's own dimension term and its resident `tuple(d, v)` fact in
// ONE value (proof.Inhabited, the pairing the vector chapters share).
// Values exist only through Inhabit, which reads the fact's bound
// content and refuses anything but exactly that term. The evidence
// cannot later be crossed with a different vector because there is no
// separable pair to cross.
// - AtVec on a theorem wrapper: the guarded citation. The dimension
// witnesses are NOT parameters — each is read off the checked
// inhabited values (the section's own dimension variable, which the
// phantom was verified against at Inhabit), so a cite can never
// pair a Vec[D3] with the dimension term 2 — and the membership
// evidence is required, checked to guard the vectors cited, and
// travels WITH the cite as one By premise group.
//
// The refinement never reaches the kernel: what the group installs is
// exactly the untyped `At(entry, n, y, x)` plus the membership
// facts as premises (the 1:1 discipline), and a By consuming it is
// checked by the prover as always. What the surface buys is the
// authoring-time geometry: dimension bookkeeping leaves the cite sites,
// and the mistakes the untyped spelling surfaces as late refutation
// failures become compile errors (cross-dimension pairings) or named
// panics at the line that is wrong (mismatched evidence).
//
// The letters N and M are DIMENSION phantoms (num-typed term
// letters n and m), not type letters: this chapter's statements bind
// their dimensions as ∀-quantified nums, and a proof body names those
// binders' phantoms exactly as the statement spells them. AtVec methods
// are hand-written one per consumed theorem, like the rest of the
// vocabulary — a wrapper nothing cites through vectors carries none —
// and generating them wholesale is the promotion the generator owes
// this file if the spelling spreads.

package carrier

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dimtypes"
	"github.com/euc-ai/xugo/ext/dsl"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/prover/proof"
)

// InhabitedVec is a vector together with evidence that it inhabits its
// dimension — proof.Inhabited (the shared pairing: an ANCHORED Vec and
// the resident fact naming its dimension) under the chapter's own name,
// with the block operations that compose evidence (Concat, Recast). Only
// Inhabit constructs one, so holding an InhabitedVec[Elem, Dim] IS
// holding a resident fact that says exactly `tuple(d, v)` — the check
// already ran, and Dim() is that d.
//
// The anchor is read off the factorial, not off the scope's names: inside a
// section the statement's binder `m` lives as its Skolem mint (`m` or
// `m_0` — proof.SkolemNameOf is the one authority), and the phantom
// letter denotes THAT variable. Inhabit matches the fact's dimension
// term against the phantom's spec with letters compared under the
// Skolem convention, and anchors the vector at the variables the match
// bound; proof.Inhabit then re-checks the fact against that anchor.
type InhabitedVec[Elem TypePhantom, Dim dimtypes.DimPhantom] struct {
	*proof.Inhabited[Elem, Dim]
}

// tupleAt is the chapter's membership predicate as a term at the given
// element instance — the minted constant (vocab.go) every statement
// here is written over, so the expected content Inhabit checks against
// is built from the statement's own alphabet.
func tupleAt(elem core.HolType) Term {
	carrier := MakeFun(ext.NumType, elem)
	return ext.Const(TupleMeta, MakeFun(ext.NumType, carrier, core.TypeBool())).Core()
}

// Inhabit adopts a statement binder as a dimensioned vector TOGETHER
// with the membership fact that makes the dimension label true. The
// result is one indivisible value: the vector's HOL type is checked by
// the adoption gate, and the fact's bound content must be exactly
// `tuple(d, v)` with d the phantom's own dimension expression (letters
// compared under the Skolem-name convention — the statement's `m` is
// the section's `m` or `m_0`). Anything else panics, printing what the
// fact says next to what the phantom asserts.
//
// The check reads the fact at its BIND time (Fact.BoundContent):
// it is the authoring tripwire that keeps a Vec label honest, not a
// soundness boundary — what a By ultimately consumes is checked by the
// prover, as everywhere.
func Inhabit[Elem TypePhantom, Dim dimtypes.DimPhantom](
	v Term, membership Fact) *InhabitedVec[Elem, Dim] {
	got, ok := membership.BoundContent()
	if !ok {
		panic(fmt.Sprintf("carrier.Inhabit: the membership fact for %s carries no bound content "+
			"(pass the resident fact the statement's tuple antecedent bound — an a.Assume/a.Have result)",
			ext.PrintTerm(v)))
	}
	_, letters := checkedMembershipDim[Elem, Dim](v, got)
	vec := dimtypes.AnchorVec[Elem, Dim](v, func(name string) core.Term { return letters[name] })
	return &InhabitedVec[Elem, Dim]{Inhabited: proof.Inhabit(vec, membership)}
}

// checkedMembershipDim is the pure half of Inhabit's adoption gate,
// kept separate so the exact term/evidence contract can be unit-tested
// without manufacturing a prover-resident Fact. It returns the fact's
// dimension term and the letter → variable bindings the phantom's spec
// matched it under.
func checkedMembershipDim[Elem TypePhantom, Dim dimtypes.DimPhantom](v, got Term) (Term, map[string]core.VarTerm) {
	complain := func() {
		panic(fmt.Sprintf(
			"carrier.Inhabit: the membership fact says\n  %s\nbut the phantom asserts\n  tuple(%s, %s)",
			ext.PrintTerm(got),
			ext.PrintTerm(dimtypes.TermOf[Dim]()),
			ext.PrintTerm(v)))
	}
	outer, ok := got.AsAppliedTerm()
	if !ok {
		complain()
	}
	inner, ok := outer.Fun().AsAppliedTerm()
	if !ok || !inner.Fun().Equals(tupleAt(ext.HolTypeOf[Elem]())) {
		complain()
	}
	if !outer.Arg().Equals(v.Core()) {
		complain()
	}
	dim := inner.Arg()
	letters, ok := dimtypes.LetterBindings(dimtypes.SpecOf[Dim](), dim,
		func(name string, dv core.VarTerm) bool { return proof.SkolemNameOf(string(dv.Name()), name) })
	if !ok {
		complain()
	}
	return dim, letters
}

// AtVec is Extensionality taken at two vectors of ONE dimension — the
// compiler enforces that the two share it, the inhabited values' own
// dimension term becomes the witness (checked to agree, so the cite
// can never pair a Vec with a foreign dimension), and their membership
// evidence travels with the cite as one premise group:
//
//	By(agree, Extensionality.AtVec(xV, wV))
//
// lowers to exactly By(agree, xMem, wMem,
// At(Extensionality, n, x, w)) — same install, same steps; the dimension spelling and the
// evidence pairing are what the typed surface takes off the page.
func (th extensionalityThm) AtVec[Elem TypePhantom, Dim dimtypes.DimPhantom](
	y, x *InhabitedVec[Elem, Dim]) proof.PremiseGroup {
	return GroupPremises(
		y.Evidence(), x.Evidence(),
		th.At(proof.SameDimension(y.Dim(), x.Dim()), y, x))
}

// AtVec is ConcatClosed at two inhabited vectors. Unlike
// Extensionality.AtVec the dimensions may differ; each witness is read
// from the value whose membership established it.
func (th concatClosedThm) AtVec[
	Elem TypePhantom,
	Left, Right dimtypes.DimPhantom,
](x *InhabitedVec[Elem, Left], y *InhabitedVec[Elem, Right]) proof.PremiseGroup {
	return GroupPremises(
		x.Evidence(), y.Evidence(),
		th.At(ext.As[Nat](x.Dim()), ext.As[Nat](y.Dim()), x, y))
}

// catAt is concatenation at one element instance, in the same minted
// vocabulary.
func catAt(elem core.HolType) Term {
	carrier := MakeFun(ext.NumType, elem)
	return ext.Const(TupleCatMeta, MakeFun(ext.NumType, carrier, carrier, carrier)).Core()
}

// Concat constructs not merely a term tagged with the sum dimension,
// but an inhabited value carrying the theorem-produced membership of
// that term. S is inferred as exactly Plus[Left, Right], so a caller
// writes x.Concat(..., y) without a result annotation.
func (x *InhabitedVec[Elem, Left]) Concat[
	Right dimtypes.DimPhantom,
	S dimtypes.IsPlus[Left, Right],
](a *Argument, y *InhabitedVec[Elem, Right]) *InhabitedVec[Elem, S] {
	sum, term := concatTerms(x.Vec, y.Vec)
	membership := a.Have(
		"the concatenation inhabits the sum dimension",
		core.MakeProp(core.Apply(core.Apply(tupleAt(ext.HolTypeOf[Elem]()), sum), term)),
		By(Normalized, ConcatClosed.AtVec(x, y)))
	return Inhabit[Elem, S](term, membership)
}

func concatTerms[
	Elem TypePhantom,
	Left, Right dimtypes.DimPhantom,
](x *dimtypes.Vec[Elem, Left], y *dimtypes.Vec[Elem, Right]) (sum, term Term) {
	sum = core.Apply(core.Apply(dsl.NatPlusMeta.Term(), x.Dim()), y.Dim())
	term = core.Apply(core.Apply(core.Apply(catAt(ext.HolTypeOf[Elem]()), x.Dim()), x.Core()), y.Core())
	return sum, term
}

// Recast changes an inhabited vector's phantom spelling only when BOTH
// layers agree: the dimension grammar proves From and To denote the
// same polynomial, and a resident equality identifies the actual
// section terms named by the old and new memberships. The latter is
// essential — a bare Vec recast moves no HOL term, but an InhabitedVec
// also carries the proposition tuple(d, v), whose d must be transported.
func (v *InhabitedVec[Elem, From]) Recast[To dimtypes.DimPhantom](
	a *Argument, dimEq Fact) *InhabitedVec[Elem, To] {
	got, ok := dimEq.BoundContent()
	if !ok {
		panic("carrier.InhabitedVec.Recast: the dimension equality carries no bound content")
	}
	target := checkedRecastTarget[From, To](v.Dim(), got)
	left, _, _ := core.MatchesEQ(got)

	// Lift the dimension equality through d ↦ tuple(d,v). Keeping this
	// congruence explicit avoids asking the propositional closer to
	// discover equality transport on its own.
	d := core.Var("_dim", ext.NumType)
	predicate := core.Abs(d,
		core.Apply(core.Apply(tupleAt(ext.HolTypeOf[Elem]()), d), v.Core()))
	a.Do(dimEq.CongrArg(predicate))
	oldMembership := core.Apply(core.Apply(tupleAt(ext.HolTypeOf[Elem]()), v.Dim()), v.Core())
	newMembership := core.Apply(core.Apply(tupleAt(ext.HolTypeOf[Elem]()), target), v.Core())
	bridgeTerm := core.Eq(core.Apply(predicate, v.Dim()), core.Apply(predicate, target))
	if !left.Equals(v.Dim()) {
		bridgeTerm = core.Eq(core.Apply(predicate, target), core.Apply(predicate, v.Dim()))
	}
	bridge := a.Hyp(bridgeTerm)
	transport := a.Have(
		"membership respects the dimension equality",
		core.MakeProp(core.Eq(oldMembership, newMembership)),
		By(Normalized, bridge))
	forward := a.Have(
		"old-dimension membership implies new-dimension membership",
		core.MakeProp(ext.WrapTerm(oldMembership).Imply(newMembership).Core()),
		By(Normalized, transport))

	membership := a.Have(
		"transport membership across the dimension equality",
		core.MakeProp(newMembership),
		By(Normalized, v.Evidence(), forward))
	return Inhabit[Elem, To](v.Core(), membership)
}

// checkedRecastTarget is the pure validation half of Recast.
func checkedRecastTarget[From, To dimtypes.DimPhantom](from, equality Term) Term {
	if !dimtypes.SameDim[From, To]() {
		panic(fmt.Sprintf("carrier.InhabitedVec.Recast: dimension phantoms disagree: %s and %s",
			ext.PrintTerm(dimtypes.TermOf[From]()), ext.PrintTerm(dimtypes.TermOf[To]())))
	}
	left, right, ok := core.MatchesEQ(equality)
	if !ok {
		panic(fmt.Sprintf("carrier.InhabitedVec.Recast: expected a dimension equality, got %s",
			ext.PrintTerm(equality)))
	}

	var target Term
	switch {
	case left.Equals(from):
		target = right
	case right.Equals(from):
		target = left
	default:
		panic(fmt.Sprintf(
			"carrier.InhabitedVec.Recast: equality %s does not mention the inhabited dimension %s",
			ext.PrintTerm(equality),
			ext.PrintTerm(from)))
	}
	if !dimtypes.DenotesTerm(dimtypes.SpecOf[To](), target,
		func(name string, dv core.VarTerm) bool { return proof.SkolemNameOf(string(dv.Name()), name) }) {
		panic(fmt.Sprintf("carrier.InhabitedVec.Recast: equality targets %s, which does not denote %s",
			ext.PrintTerm(target), ext.PrintTerm(dimtypes.TermOf[To]())))
	}
	return target
}
