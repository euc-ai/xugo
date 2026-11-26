package presheaf

import (
	"context"
	"strconv"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/prover/proof"
)

// GermInput names one presheaf and a germ in its stalk at the chosen point.
// Presheaf may be a resident structure fact or a lazy projection of one.
// A lazy projection used by several inputs is materialized once by the
// caller with a.Simplified; those inputs share the returned resident fact.
// Member proves Germ ∈ stalk(T, F, res, x) for this exact presheaf.
type GermInput struct {
	Presheaf proof.CiteTarget
	Germ     TermLike
	Member   Fact
}

// CommonGerms represents the input germs, in order, over one neighbourhood W.
// NeighborhoodFact proves W ∈ T ∧ x ∈ W. Members[i] proves
// Sections[i] ∈ F_i(W), and Equalities[i] proves that input i is the
// germ of Sections[i] over W, using that input's F_i and res_i.
// Terms retain their HOL types; different entries may have different
// section types.
type CommonGerms struct {
	Neighborhood     Term
	NeighborhoodFact Fact
	Sections         []Term
	Members          []Fact
	Equalities       []Fact
}

// CommonRepresentatives puts a finite list of germs over a common open
// neighbourhood of x inside within. The supplied neighborhood proves
// within ∈ T ∧ x ∈ within; every input is a germ at x of a presheaf on T.
// With no inputs, within and neighborhood are returned unchanged.
//
// Each new representative is chosen inside the current neighbourhood.
// Earlier sections are restricted to the smaller neighbourhood, with their
// memberships and germ equalities proved again there.
func CommonRepresentatives(
	a *Argument,
	x, within TermLike,
	neighborhood Fact,
	inputs ...GermInput,
) CommonGerms {
	out := CommonGerms{
		Neighborhood:     within.Core(),
		NeighborhoodFact: neighborhood,
		Sections:         make([]Term, 0, len(inputs)),
		Members:          make([]Fact, 0, len(inputs)),
		Equalities:       make([]Fact, 0, len(inputs)),
	}
	if len(inputs) == 0 {
		return out
	}

	ctx := a.Ctx()
	pointType := x.Core().Type()
	openType := MakeFun(pointType, TypeBool)
	if !within.Core().Type().Equals(openType) {
		panic("CommonRepresentatives: within must be a set of points of the type of x")
	}
	presheaves := make([]commonGermPresheaf, len(inputs))
	for i, input := range inputs {
		presheaves[i] = readCommonGermPresheaf(a, input)
		if i > 0 && !presheaves[i].topology.AlphaEquals(presheaves[0].topology) {
			panic("CommonRepresentatives: all presheaves must have the same topology")
		}
	}
	topology := presheaves[0].topology
	if !topology.Type().Equals(MakeFun(openType, TypeBool)) {
		panic("CommonRepresentatives: the presheaves must be on the point type of x")
	}

	member := func(element, set TermLike) *TermWrapper {
		return ctx.Const("set_member",
			MakeFun(element.Core().Type(), set.Core().Type(), TypeBool)).
			Apply(element, set)
	}
	subset := ctx.Const("subset", MakeFun(openType, openType, TypeBool))
	near := func(W TermLike) *TermWrapper {
		return member(W, topology).And(member(x, W))
	}

	for i, input := range inputs {
		p := presheaves[i]
		U := out.Neighborhood
		onU := out.NeighborhoodFact
		g := input.Germ.Core()

		// The bound variables are fresh for every term inserted into the
		// existential, so constructing the claim cannot capture a free variable.
		avoid := []Term{x.Core(), U, g, p.topology, p.sections, p.restrict}
		V := commonGermBinder("V", openType, avoid...)
		s := commonGermBinder("s", p.sectionType, append(avoid, V)...)
		claim := MakeProp(Exists(V, s)(ext.And(
			member(V, topology),
			member(x, V),
			subset.Apply(V, U),
			member(s, p.sectionsOver(V)),
			Equal(g, p.germ.Apply(x, V, s)),
		)))
		W, section, representative := a.Obtain2(
			"choose a representative inside the current neighbourhood",
			claim,
			By(Read(GermRepresentativeWithin, p.fact).At(x, U, g), onU, input.Member))
		onW := a.Have(
			"the smaller set is an open neighbourhood of x",
			MakeProp(near(W)),
			By(representative))
		inside := a.Have(
			"the smaller neighbourhood lies inside the current one",
			MakeProp(subset.Apply(W, U)),
			By(representative))
		sectionMember := a.Have(
			"the new representative is a section over the smaller neighbourhood",
			MakeProp(member(section, p.sectionsOver(W))),
			By(representative))
		sectionGerm := a.Have(
			"the new section represents the input germ",
			MakeProp(Equal(g, p.germ.Apply(x, W, section))),
			By(representative))

		for j := range out.Sections {
			previous := presheaves[j]
			oldSection := out.Sections[j]
			restricted := previous.restrict.Apply(U, W, oldSection)
			restrictedMember := a.Have(
				"restrict an earlier section to the smaller neighbourhood",
				MakeProp(member(restricted, previous.sectionsOver(W))),
				By(Read(RestrictIn, previous.fact).At(U, W, oldSection), onU, onW, inside, out.Members[j]))
			unchanged := a.Have(
				"restriction preserves the germ of the earlier section",
				MakeProp(Equal(previous.germ.Apply(x, W, restricted),
					previous.germ.Apply(x, U, oldSection))),
				By(Read(GermRestrict, previous.fact).At(x, U, W, oldSection), onU, onW, inside, out.Members[j]))
			represented := a.Have(
				"the restricted section still represents its input germ",
				MakeProp(Equal(inputs[j].Germ, previous.germ.Apply(x, W, restricted))),
				By(out.Equalities[j], unchanged))
			out.Sections[j] = restricted.Core()
			out.Members[j] = restrictedMember
			out.Equalities[j] = represented
		}

		out.Neighborhood = W.Core()
		out.NeighborhoodFact = onW
		out.Sections = append(out.Sections, section.Core())
		out.Members = append(out.Members, sectionMember)
		out.Equalities = append(out.Equalities, sectionGerm)
	}
	return out
}

// commonGermPresheaf retains the components of one particular presheaf.
// Its germ constructor has those components applied, so two presheaves on
// the same section type remain distinct throughout restriction.
type commonGermPresheaf struct {
	fact        Fact
	topology    Term
	sections    *TermWrapper
	restrict    *TermWrapper
	germ        *TermWrapper
	sectionType HolType
}

// sectionsOver is the presheaf's sections over V, β-reduced: a section
// family written as a λ (`λU. F(U).carrier`) is applied, so a membership
// the helper states is in the instance normal form a closer matches.
func (p commonGermPresheaf) sectionsOver(V TermLike) *TermWrapper {
	return ext.WrapTerm(ext.BetaCollapse(context.Background(), p.sections.Apply(V).Core()))
}

func readCommonGermPresheaf(a *Argument, input GermInput) commonGermPresheaf {
	pre := a.Simplified(input.Presheaf)
	content, bound := pre.BoundContent()
	if !bound {
		panic("CommonRepresentatives: the presheaf fact must materialize as a resident fact")
	}
	head, components := ext.MatchesApply(content)
	constant, isConstant := head.AsConst()
	if !isConstant || !constant.Meta().Equals(a.Ctx().ConstMeta("presheaf")) || len(components) != 3 {
		panic("CommonRepresentatives: each Presheaf must establish a single presheaf(T, F, res) atom")
	}
	T, F, res := components[0], components[1], components[2]
	sectionFamilyType := ext.MatchesFun(F.Type())
	if len(sectionFamilyType) != 3 || !sectionFamilyType[2].Equals(TypeBool) {
		panic("CommonRepresentatives: F must have type set(A) → set(B)")
	}
	sectionType := sectionFamilyType[1]
	openType := sectionFamilyType[0]
	pointType := ext.MatchesFun(openType)
	if len(pointType) != 2 || !pointType[1].Equals(TypeBool) {
		panic("CommonRepresentatives: the presheaf's domains must be sets")
	}
	germ := a.Ctx().Const("sheaf_germ",
		MakeFun(T.Type(), F.Type(), res.Type(), pointType[0], openType,
			sectionType, input.Germ.Core().Type())).Apply(T, F, res)
	return commonGermPresheaf{
		fact:        pre,
		topology:    T,
		sections:    ext.WrapTerm(F),
		restrict:    ext.WrapTerm(res),
		germ:        germ,
		sectionType: sectionType,
	}
}

func commonGermBinder(base string, ty HolType, avoid ...Term) *TermWrapper {
	for suffix := 0; ; suffix++ {
		name := core.TermName(base)
		if suffix > 0 {
			name = core.TermName(base + "_" + strconv.Itoa(suffix))
		}
		used := false
		for _, term := range avoid {
			if term.HasFreeName(name) {
				used = true
				break
			}
		}
		if !used {
			return Var(name, ty)
		}
	}
}
