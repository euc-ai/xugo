// vec.go — the dimension-refined vector, matrix and map at the proof
// surface: how a dimtypes.Vec, dimtypes.Mat or dimtypes.VecFun is ANCHORED
// to the section that spells its letters, and how a vector or a matrix
// travels with its membership evidence.
//
// A dimension letter (dimtypes.N) names the statement's binder `n`.
// Inside a section that binder is a minted variable — `n`, or `n_0`
// after a rename — and the letter must denote THAT variable, never a
// bare `Var("n")` (the carrier chapter's lesson). The surface-name
// aliases every Argument carries (derive.go §"Surface names") are
// exactly the map from the statement's spelling to the section's
// variable, so anchoring is one lookup: `dimensionLetter`. Three doors
// use it — the section binder, for a closure parameter spelled
// *Vec[Elem, D], *Mat[Elem, R, C] or *VecFun[Elem, Source, Target]
// (section.go); VecAs / MatAs / VecFunAs, for a value built mid-proof; and
// carrier's Inhabit, through the same function. A matrix differs only
// in arity: two phantoms, two letters to resolve, two dimension terms to
// write. A map between two vector spaces is the matrix's arity over
// another carrier, `(num → Elem) → num → Elem`: the dimension it is read
// on and the dimension its values are read at.
//
// A dimension no letter spells — a Let, a literal, `suc(m)`, a degree —
// has a fourth door, by TERM: VecAt / MatAt / VecFunAt anchor a value at
// the dimension terms they are given, and the value carries
// dimtypes.SomeDim, the one phantom with no name to resolve. Two
// SomeDim values are tied at the cite (SameDimension) rather than at
// compile time.
//
// Inhabited pairs an anchored vector with the fact that it inhabits
// its dimension — `vec⟨n⟩(zero, u)`, `tuple(n, v)`: the membership
// predicates of both term-level chapters spell the dimension and then
// the vector as their last two arguments, and Inhabit checks the
// fact's bound content against the vector's own anchor, so an
// Inhabited value IS a checked pairing and a generated cite can bundle
// the evidence with the instance (PremiseGroup) without a slot for it.
// InhabitFrom is the same pairing with the dimension READ OFF the
// fact, for a vector the proof holds only through its membership.
// InhabitedMat is the same pairing at a matrix, whose membership
// predicate — `matrix⟨n, m⟩(zero, A)` — spells its two dimensions and
// then the matrix as its last THREE arguments.

package proof

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dimtypes"
)

// dimensionLetter resolves a dimension letter to the section's own
// variable for that surface name, panicking — with the legend — when
// the name is not a binder fixed in this block or an enclosing one.
func (a *Argument) dimensionLetter(name string) core.Term {
	if v, ok := a.surfaceAliases()[name]; ok {
		return v
	}
	if ty, ok := a.s.ParseScope.Vars[name]; ok && ty.Equals(ext.NumType) {
		return core.Var(core.TermName(name), ty)
	}
	panic(a.withAliasLegend(fmt.Sprintf(
		"the dimension letter %s is not a binder in scope — fix the dimension (a closure parameter before the vectors, or a.Fix) before anchoring a vector at it", name)))
}

// VecAs parses a term text as a vector of dimension D, ANCHORED to the
// block's binders: the letters of D resolve through the surface names
// exactly as the text's own names do. The typed variant of Term for
// the vector chapters:
//
//	sum := a.VecAs[Real, DimN]("vadd(u, v)")
//	… NormPow2.At(sum) …
func (a *Argument) VecAs[Elem ext.TypePhantom, D dimtypes.DimPhantom](raw string) *dimtypes.Vec[Elem, D] {
	a.guardRead("VecAs")
	return dimtypes.AnchorVec[Elem, D](a.Term(raw), a.dimensionLetter)
}

// VecAt parses a term text as a vector ANCHORED at the given dimension
// term — the verb for a dimension no letter spells: a Let, a literal,
// `suc(m)`, `polynomial_degree(p)`. The value carries SomeDim, so two
// such vectors are tied at the cite (SameDimension) rather than at
// compile time.
//
//	p := a.VecAt[A](a.TermAs[Nat]("suc(k)"), "p")
//	… VecDef.At(zero, p) …
func (a *Argument) VecAt[Elem ext.TypePhantom](dim ext.Typed[ext.Nat], raw string) *dimtypes.Vec[Elem, dimtypes.SomeDim] {
	a.guardRead("VecAt")
	return dimtypes.VecAt[Elem](a.Term(raw), dim.Core())
}

// VecFixAs is FixAs for a vector binder — "let x be an arbitrary
// vector of dimension D": ∀-introduction of the goal's leading binder,
// the minted variable adopted as a D-dimensional vector anchored to the
// dimension binders already in scope. The one verb for what was
// `a.Fix()` followed by `a.VecAs[Elem, D]("x")` — the binder introduced
// by one call and re-spelled by name to the next, the name that linked
// them being the goal's own. The optional surface name is Fix's.
//
//	x := a.VecFixAs[Real, M]()
//	xM := proof.Inhabit(x, a.Assume())
func (a *Argument) VecFixAs[Elem ext.TypePhantom, D dimtypes.DimPhantom](name ...string) *dimtypes.Vec[Elem, D] {
	a.guard("VecFixAs")
	surface := fixName("VecFixAs", name)
	if surface != "" {
		a.assertSpellingFree("VecFixAs", surface)
	}
	return dimtypes.AnchorVec[Elem, D](a.fixImpl(surface), a.dimensionLetter)
}

// MatAs parses a term text as an R×C matrix, ANCHORED to the block's
// binders: the letters of both phantoms resolve through the surface
// names exactly as the text's own names do. VecAs at two dimensions.
//
//	product := a.MatAs[A, DimN, DimM]("matrix_mul(k, A, B)")
func (a *Argument) MatAs[Elem ext.TypePhantom, R, C dimtypes.DimPhantom](raw string) *dimtypes.Mat[Elem, R, C] {
	a.guardRead("MatAs")
	return dimtypes.AnchorMat[Elem, R, C](a.Term(raw), a.dimensionLetter)
}

// MatAt parses a term text as a matrix ANCHORED at the given row and
// column terms, VecAt at two dimensions; both phantoms are SomeDim.
func (a *Argument) MatAt[Elem ext.TypePhantom](rows, cols ext.Typed[ext.Nat], raw string) *dimtypes.Mat[Elem, dimtypes.SomeDim, dimtypes.SomeDim] {
	a.guardRead("MatAt")
	return dimtypes.MatAt[Elem](a.Term(raw), rows.Core(), cols.Core())
}

// MatFixAs is VecFixAs for a matrix binder — "let A be an arbitrary
// n×m matrix": ∀-introduction of the goal's leading binder, the minted
// variable adopted as an R×C matrix anchored to the dimension binders
// already in scope.
//
//	A := a.MatFixAs[Real, N, M]()
//	An := proof.InhabitMat(A, a.Assume())
func (a *Argument) MatFixAs[Elem ext.TypePhantom, R, C dimtypes.DimPhantom](name ...string) *dimtypes.Mat[Elem, R, C] {
	a.guard("MatFixAs")
	surface := fixName("MatFixAs", name)
	if surface != "" {
		a.assertSpellingFree("MatFixAs", surface)
	}
	return dimtypes.AnchorMat[Elem, R, C](a.fixImpl(surface), a.dimensionLetter)
}

// VecFunAs parses a term text as a map from Source-vectors to
// Target-vectors, ANCHORED to the block's binders: the letters of both
// phantoms resolve through the surface names exactly as the text's own
// names do. VecAs for a map between two vector spaces, and the image of
// a vector under it is a vector at the target (dimtypes.VecFun.Apply).
//
//	chain := a.VecFunAs[Real, DimN, DimK]("K ∘ L")
//	image := L.Apply(u) // u at n, the image at m
func (a *Argument) VecFunAs[Elem ext.TypePhantom, Source, Target dimtypes.DimPhantom](raw string) *dimtypes.VecFun[Elem, Source, Target] {
	a.guardRead("VecFunAs")
	return dimtypes.AnchorVecFun[Elem, Source, Target](a.Term(raw), a.dimensionLetter)
}

// VecFunAt parses a term text as a map ANCHORED at the given source and
// target dimension terms, VecAt for a map; both phantoms are SomeDim.
func (a *Argument) VecFunAt[Elem ext.TypePhantom](source, target ext.Typed[ext.Nat], raw string) *dimtypes.VecFun[Elem, dimtypes.SomeDim, dimtypes.SomeDim] {
	a.guardRead("VecFunAt")
	return dimtypes.VecFunAt[Elem](a.Term(raw), source.Core(), target.Core())
}

// VecFunFixAs is VecFixAs for a map binder — "let L be an arbitrary map of
// n-vectors to m-vectors": ∀-introduction of the goal's leading binder,
// the minted variable adopted as a map anchored to the dimension binders
// already in scope.
//
//	L := a.VecFunFixAs[Real, DimN, DimM]()
func (a *Argument) VecFunFixAs[Elem ext.TypePhantom, Source, Target dimtypes.DimPhantom](name ...string) *dimtypes.VecFun[Elem, Source, Target] {
	a.guard("VecFunFixAs")
	surface := fixName("VecFunFixAs", name)
	if surface != "" {
		a.assertSpellingFree("VecFunFixAs", surface)
	}
	return dimtypes.AnchorVecFun[Elem, Source, Target](a.fixImpl(surface), a.dimensionLetter)
}

// Inhabited is an anchored vector together with the fact that it
// inhabits its dimension. Built only by Inhabit, so holding one IS
// holding the checked pairing.
type Inhabited[Elem ext.TypePhantom, D dimtypes.DimPhantom] struct {
	*dimtypes.Vec[Elem, D]
	evidence Fact
}

// Inhabit pairs an anchored vector with its membership fact, checking
// the fact's bound content: an application whose last two arguments
// are the vector's own dimension term and the vector itself. Anything
// else panics, printing what the fact says next to what the vector
// asserts.
func Inhabit[Elem ext.TypePhantom, D dimtypes.DimPhantom](v *dimtypes.Vec[Elem, D], membership Fact) *Inhabited[Elem, D] {
	got, ok := membership.BoundContent()
	if !ok {
		panic(fmt.Sprintf("proof.Inhabit: the membership fact for %s carries no bound content "+
			"(pass the resident fact the statement's antecedent bound — an a.Assume/a.Have result)", ext.PrintTerm(v)))
	}
	if err := checkInhabits(got, v.Dim(), v.Core()); err != nil {
		panic("proof.Inhabit: " + err.Error())
	}
	return &Inhabited[Elem, D]{Vec: v, evidence: membership}
}

// InhabitFrom pairs a vector with its membership fact, the dimension
// READ OFF the fact: the bound content must be an application whose
// last argument is the vector and whose second-to-last is a num term,
// which becomes the anchor. The pairing for a vector the proof holds
// only through its membership — Inhabit at SomeDim, restating no
// dimension. Elem is inferred from the vector.
//
//	from := a.Have("…", "vec⟨suc(polynomial_degree(zero, p))⟩(zero, p)", …)
//	… DegreeBelow.At(zero, proof.InhabitFrom(p, from)) …
func InhabitFrom[Elem ext.TypePhantom](v ext.Typed[ext.Fun[ext.Nat, Elem]], membership Fact) *Inhabited[Elem, dimtypes.SomeDim] {
	got, ok := membership.BoundContent()
	if !ok {
		panic(fmt.Sprintf("proof.InhabitFrom: the membership fact for %s carries no bound content "+
			"(pass the resident fact the statement's antecedent bound — an a.Assume/a.Have result)", ext.PrintTerm(v)))
	}
	dim, err := membershipDim(got, v.Core())
	if err != nil {
		panic("proof.InhabitFrom: " + err.Error())
	}
	return &Inhabited[Elem, dimtypes.SomeDim]{Vec: dimtypes.VecAt[Elem](v.Core(), dim), evidence: membership}
}

// checkInhabits is Inhabit's pure half: content must be an application
// whose last two arguments are dim and subject.
func checkInhabits(content, dim, subject core.Term) error {
	got, err := membershipDim(content, subject)
	if err != nil {
		return err
	}
	if !got.Equals(dim) {
		return fmt.Errorf("the membership fact says\n  %s\nbut the vector asserts dimension %s for %s",
			ext.PrintTerm(content), ext.PrintTerm(dim), ext.PrintTerm(subject))
	}
	return nil
}

// membershipDim reads a membership fact's bound content as a predicate
// applied to a dimension and the subject — the last argument must be
// the subject, the one before it a num term — and returns that
// dimension term.
func membershipDim(content, subject core.Term) (core.Term, error) {
	outer, ok := content.AsAppliedTerm()
	if !ok {
		return nil, fmt.Errorf("the membership fact says\n  %s\nwhich is not a membership predicate applied to a dimension and a vector",
			ext.PrintTerm(content))
	}
	inner, ok := outer.Fun().AsAppliedTerm()
	if !ok || !outer.Arg().Equals(subject) {
		return nil, fmt.Errorf("the membership fact says\n  %s\nwhich is not a membership predicate applied to a dimension and %s",
			ext.PrintTerm(content), ext.PrintTerm(subject))
	}
	dim := inner.Arg()
	if !dim.Type().Equals(ext.NumType) {
		return nil, fmt.Errorf("the membership fact says\n  %s\nwhose argument before %s is not a num term, so not a dimension",
			ext.PrintTerm(content), ext.PrintTerm(subject))
	}
	return dim, nil
}

// Evidence is the membership fact the pairing carries.
func (v *Inhabited[Elem, D]) Evidence() Fact { return v.evidence }

// With bundles the evidence with a cite as one justification unit —
// what a generated wrapper returns for a statement whose antecedent is
// the vector's membership.
func (v *Inhabited[Elem, D]) With(cite Fact) PremiseGroup { return GroupPremises(v, cite) }

// evidencePremises is the evidence-carrier reading (member.go): the
// vector stands, in a premise list, for its membership.
func (v *Inhabited[Elem, D]) evidencePremises() []any { return []any{v.evidence} }

// InhabitedMat is an anchored matrix together with the fact that it
// inhabits its two dimensions. Built only by InhabitMat.
type InhabitedMat[Elem ext.TypePhantom, R, C dimtypes.DimPhantom] struct {
	*dimtypes.Mat[Elem, R, C]
	evidence Fact
}

// InhabitMat pairs an anchored matrix with its membership fact,
// checking the fact's bound content: an application whose last three
// arguments are the matrix's own row and column dimension terms and the
// matrix itself. Inhabit at two dimensions.
func InhabitMat[Elem ext.TypePhantom, R, C dimtypes.DimPhantom](a *dimtypes.Mat[Elem, R, C], membership Fact) *InhabitedMat[Elem, R, C] {
	got, ok := membership.BoundContent()
	if !ok {
		panic(fmt.Sprintf("proof.InhabitMat: the membership fact for %s carries no bound content "+
			"(pass the resident fact the statement's antecedent bound — an a.Assume/a.Have result)", ext.PrintTerm(a)))
	}
	if err := checkInhabitsMat(got, a.Rows(), a.Cols(), a.Core()); err != nil {
		panic("proof.InhabitMat: " + err.Error())
	}
	return &InhabitedMat[Elem, R, C]{Mat: a, evidence: membership}
}

// InhabitMatFrom pairs a matrix with its membership fact, both
// dimensions READ OFF the fact — InhabitFrom at a matrix, whose
// membership spells its rows, its columns and then itself.
func InhabitMatFrom[Elem ext.TypePhantom](a ext.Typed[ext.Fun2[ext.Nat, ext.Nat, Elem]], membership Fact) *InhabitedMat[Elem, dimtypes.SomeDim, dimtypes.SomeDim] {
	got, ok := membership.BoundContent()
	if !ok {
		panic(fmt.Sprintf("proof.InhabitMatFrom: the membership fact for %s carries no bound content "+
			"(pass the resident fact the statement's antecedent bound — an a.Assume/a.Have result)", ext.PrintTerm(a)))
	}
	rows, cols, err := membershipDims(got, a.Core())
	if err != nil {
		panic("proof.InhabitMatFrom: " + err.Error())
	}
	return &InhabitedMat[Elem, dimtypes.SomeDim, dimtypes.SomeDim]{Mat: dimtypes.MatAt[Elem](a.Core(), rows, cols), evidence: membership}
}

// checkInhabitsMat is InhabitMat's pure half: content must be an
// application whose last three arguments are rows, cols and subject.
func checkInhabitsMat(content, rows, cols, subject core.Term) error {
	gotRows, gotCols, err := membershipDims(content, subject)
	if err != nil {
		return err
	}
	if !gotRows.Equals(rows) || !gotCols.Equals(cols) {
		return fmt.Errorf("the membership fact says\n  %s\nbut the matrix asserts dimensions %s × %s for %s",
			ext.PrintTerm(content), ext.PrintTerm(rows), ext.PrintTerm(cols), ext.PrintTerm(subject))
	}
	return nil
}

// membershipDims is membershipDim at a matrix: the last argument must
// be the subject, the two before it num terms — the rows, then the
// columns.
func membershipDims(content, subject core.Term) (rows, cols core.Term, err error) {
	notMembership := fmt.Errorf("the membership fact says\n  %s\nwhich is not a membership predicate applied to two dimensions and a matrix",
		ext.PrintTerm(content))
	outer, ok := content.AsAppliedTerm()
	if !ok {
		return nil, nil, notMembership
	}
	middle, ok := outer.Fun().AsAppliedTerm()
	if !ok {
		return nil, nil, notMembership
	}
	inner, ok := middle.Fun().AsAppliedTerm()
	if !ok || !outer.Arg().Equals(subject) {
		return nil, nil, fmt.Errorf("the membership fact says\n  %s\nwhich is not a membership predicate applied to two dimensions and %s",
			ext.PrintTerm(content), ext.PrintTerm(subject))
	}
	rows, cols = inner.Arg(), middle.Arg()
	if !rows.Type().Equals(ext.NumType) || !cols.Type().Equals(ext.NumType) {
		return nil, nil, fmt.Errorf("the membership fact says\n  %s\nwhose two arguments before %s are not both num terms, so not dimensions",
			ext.PrintTerm(content), ext.PrintTerm(subject))
	}
	return rows, cols, nil
}

// Evidence is the membership fact the pairing carries.
func (a *InhabitedMat[Elem, R, C]) Evidence() Fact { return a.evidence }

// With bundles the evidence with a cite as one justification unit.
// evidencePremises is the evidence-carrier reading (member.go): the
// matrix stands, in a premise list, for its membership.
func (a *InhabitedMat[Elem, R, C]) evidencePremises() []any { return []any{a.evidence} }

func (a *InhabitedMat[Elem, R, C]) With(cite Fact) PremiseGroup {
	return GroupPremises(a, cite)
}

// sameDimension asserts that values sharing a dimension phantom —
// vectors, matrices, maps — share the anchor term too. The same letter
// in one block always does; the check is the runtime half of the
// compile-time tie.
func sameDimension(dims ...core.Term) core.Term {
	for _, d := range dims[1:] {
		if !d.Equals(dims[0]) {
			panic(fmt.Sprintf("proof: values of one dimension phantom are anchored at different terms, %s and %s",
				ext.PrintTerm(dims[0]), ext.PrintTerm(d)))
		}
	}
	return dims[0]
}

// SameDimension is sameDimension for generated wrappers: the one
// dimension term a set of same-phantom values is cited at.
func SameDimension(dims ...core.Term) *ext.Expr[ext.Nat] {
	return ext.As[ext.Nat](sameDimension(dims...))
}
