package proof

// member.go — a point together with the fact that it lies in a set.
//
// A structure over a carrier set states its laws for the points of the
// carrier: `metric_space(M, d) ⇒ ∀x y. x ∈ M ∧ y ∈ M ⇒ d(x, y) = d(y, x)`.
// A consumer that reads such a law at an instance has the points in
// hand and their memberships beside them, and every cite would carry
// the memberships along by hand. Member is the pairing: a term and the
// evidence that it is a member of a set. A generated wrapper whose
// law's antecedent is the memberships of its witnesses in a component
// takes Members and bundles their evidence with the cite — the set
// counterpart of Inhabited (vec.go), where the membership is a vector's
// in its dimension.
//
// The second type parameter is the CARRIER the point lies in, a phantom
// of package on (ext/on): `*Member[A, on.C]` is a point of c. A law
// read at a typed structure fact (structure_fact.go) takes members of that
// fact's carrier alone, so a point of another carrier is a compile
// error. A Member is born three ways: bound by a structure law's door
// (a closure parameter `x *Member[A, on.C]` binds the binder and the
// guard `x ∈ c` that follows its run, section.go), returned by a
// closure law read at a typed fact (`InvIn.Read(group).At(x)` is
// inv(x), a point of the same carrier), or paired by hand with
// MemberOf, whose carrier is on.Any: the hand pairing checks the
// membership and names no binder.

import (
	"fmt"
	"github.com/euc-ai/xugo/prover/tactic"
	"reflect"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/on"
)

// Member is a term together with the evidence that it is a member of
// the carrier Car. Built only in this package — by MemberOf, the
// structure door's binding, or a closure law's typed reading — so
// holding one IS holding the checked pairing.
type Member[Elem ext.TypePhantom, Car on.Carrier] struct {
	ext.Expr[Elem]
	// evidence is the premises that together establish the membership:
	// the membership fact itself, or a closure law's reading with the
	// evidence of the points it was read at.
	evidence []any
}

// MemberOf pairs a term with its membership fact, checking the fact's
// bound content: `x ∈ s` with x the term itself, whatever the set. The
// pairing names no carrier binder, so the result's carrier is on.Any —
// what a law read at an untyped instance takes. Anything else panics,
// printing what the fact says next to the term.
func MemberOf[Elem ext.TypePhantom](x *ext.Expr[Elem], membership Fact) *Member[Elem, on.Any] {
	got, ok := membership.BoundContent()
	if !ok {
		panic(fmt.Sprintf("proof.MemberOf: the membership fact for %s carries no bound content "+
			"(pass the resident fact the statement's antecedent bound — an a.Assume/a.Have result; a "+
			"ground instance f.At(w…) or a law read at a fact pairs through the Argument's MemberOf, "+
			"which materializes it)", ext.PrintTerm(x)))
	}
	if err := checkMember(got, x.Core()); err != nil {
		panic("proof.MemberOf: " + err.Error())
	}
	return &Member[Elem, on.Any]{Expr: *x, evidence: []any{membership}}
}

// MemberOf, on an Argument, pairs a term with its membership fact in
// the carrier Car names — the set the binder of the block resolves to,
// or that record's carrier field — checking both the term and the set:
//
//	fx := b.MemberOf[on.M](F.Apply(x), fxIn)          // fxIn: F(x) ∈ M.carrier
//	qj := b.MemberOf[on.C](q.Apply(j), qIn.At(j))     // qIn: ∀i. q(i) ∈ c
//	one := a.MemberOf[on.R](t, comm_ring.OneIn.Read(ring))
//
// The typed counterpart of the free MemberOf, for a point a body has
// shown to lie in a carrier and hands to a law read at that carrier's
// typed fact. A resident fact is read as it stands; any other fact in
// hand — a ground instance, a law read at a fact — is materialized on
// the spine first (residentHandle), and the member's evidence is the
// resident instance.
func (a *Argument) MemberOf[Car on.Carrier, Elem ext.TypePhantom](x *ext.Expr[Elem], membership any) *Member[Elem, Car] {
	evidence, got := a.membershipInHand(membership)
	if err := checkMember(got, x.Core()); err != nil {
		panic("Argument.MemberOf: " + err.Error() + unsuppliedGuardNote(a.cur, got))
	}
	var car Car
	// on.Any names no carrier: the member is in whatever set the fact
	// says, the pairing the free MemberOf makes, from a fact in hand the
	// free form refuses — what a law read at an untyped instance takes.
	if binder := car.Binder(); binder != "" {
		_, set, _ := membershipSet(got)
		if want := a.carrierSet(binder); !set.Equals(want) {
			panic(a.withAliasLegend(fmt.Sprintf("Argument.MemberOf: %s lies in %s, but the carrier %s names is %s",
				ext.PrintTerm(x), ext.PrintTerm(set), binder, ext.PrintTerm(want))))
		}
	}
	return &Member[Elem, Car]{Expr: *x, evidence: []any{evidence}}
}

// membershipInHand is the fact a membership is read from and what it
// says: a resident fact as it stands — a read, recording nothing, so it
// may stand in the argument list of a split's branch verb — and any
// other fact in hand materialized on the spine (Argument.inHand).
func (a *Argument) membershipInHand(membership any) (Fact, core.Term) {
	if f, ok := membership.(Fact); ok {
		if content, bound := f.BoundContent(); bound {
			return f, content
		}
	}
	a.guard("MemberOf")
	f := a.inHand("MemberOf", membership)
	return f, f.handle.term
}

// checkMember is MemberOf's pure half: content must be `set_member(subject, s)`.
func checkMember(content, subject core.Term) error {
	outer, ok := content.AsAppliedTerm()
	if !ok {
		return fmt.Errorf("the membership fact says\n  %s\nwhich is not a membership of %s in a set",
			ext.PrintTerm(content), ext.PrintTerm(subject))
	}
	inner, ok := outer.Fun().AsAppliedTerm()
	if !ok {
		return fmt.Errorf("the membership fact says\n  %s\nwhich is not a membership of %s in a set",
			ext.PrintTerm(content), ext.PrintTerm(subject))
	}
	c, isConst := inner.Fun().AsConst()
	if !isConst || string(c.Name()) != "set_member" || !inner.Arg().Equals(subject) {
		return fmt.Errorf("the membership fact says\n  %s\nbut the member is %s",
			ext.PrintTerm(content), ext.PrintTerm(subject))
	}
	return nil
}

// membershipSet reads `set_member(x, s)` as its set s; false for any
// other term.
func membershipSet(t core.Term) (member, set core.Term, ok bool) {
	outer, isApp := t.AsAppliedTerm()
	if !isApp {
		return nil, nil, false
	}
	inner, isApp := outer.Fun().AsAppliedTerm()
	if !isApp {
		return nil, nil, false
	}
	c, isConst := inner.Fun().AsConst()
	if !isConst || string(c.Name()) != "set_member" {
		return nil, nil, false
	}
	return inner.Arg(), outer.Arg(), true
}

// Evidence is the membership as one premise: the fact itself, or the
// group of premises that together establish it.
func (m *Member[Elem, Car]) Evidence() any {
	if len(m.evidence) == 1 {
		return m.evidence[0]
	}
	return GroupPremises(m.evidence...)
}

// AsFact is the fact the membership is read from: the membership fact
// itself, or the closure law's reading at the points — the last of the
// evidence, whose other premises are the points' own. A verb that takes
// one fact (a Simp rule, a.Simplified) reads the member through it; a
// premise list reads all of the evidence.
func (m *Member[Elem, Car]) AsFact() Fact {
	last, ok := m.evidence[len(m.evidence)-1].(Fact)
	if !ok {
		panic(fmt.Sprintf("proof.Member: the evidence of %s ends in %T, not a fact", ext.PrintTerm(m), m.evidence[len(m.evidence)-1]))
	}
	return last
}

// With bundles the evidence with a cite as one justification unit.
func (m *Member[Elem, Car]) With(cite Fact) PremiseGroup { return WithMembers(cite, m) }

// evidencePremises is the evidence-carrier reading By and WithMembers
// flatten a Member through.
func (m *Member[Elem, Car]) evidencePremises() []any { return m.evidence }

// _EvidenceCarrier is a value that stands, in a premise list, for the
// premises that establish what it carries: a Member for its membership.
type _EvidenceCarrier interface{ evidencePremises() []any }

// WithMembers is a cite together with the evidence of the members it
// was grounded at — the group a generated reading's At returns. The
// evidence is listed first, carried, in the members' order, and a
// premise two members share (the one guard conjunction a structure door
// binds for a run of points) is listed once.
func WithMembers(cite Fact, members ..._EvidenceCarrier) PremiseGroup {
	var premises []any
	seen := map[*HypHandle]bool{}
	for _, m := range members {
		premises = appendEvidence(premises, m.evidencePremises(), seen)
	}
	cite.members = withoutCarried(cite.members, members)
	return GroupPremises(append(carried(premises), cite)...)
}

// appendEvidence appends evidence premises, skipping a resident
// hypothesis already listed.
func appendEvidence(out, evidence []any, seen map[*HypHandle]bool) []any {
	for _, e := range evidence {
		if f, ok := e.(Fact); ok {
			if h := residentHandleOf(f); h != nil {
				if seen[h] {
					continue
				}
				seen[h] = true
			}
		}
		out = append(out, e)
	}
	return out
}

// residentHandleOf is the handle of a bare resident fact — no
// witnesses, no pins — and nil for any other flavor.
func residentHandleOf(f Fact) *HypHandle {
	if f.handle == nil || f.target != nil || len(f.witnesses) > 0 || len(f.named) > 0 || f.claim != nil {
		return nil
	}
	return f.handle
}

// ReadMember is a closure law read at a typed instance and grounded at
// its points: the term the law's conclusion says is a member, with the
// premises that establish it — the reading at the points and the
// points' own evidence. stated is the law's statement and reading the
// law read at the instance (proof.Read); the instance's content must be
// known, which it is for a structure fact a door bound or a projection
// derived. Called by a generated wrapper; the conclusion of the law
// must be a membership.
func ReadMember[Elem ext.TypePhantom, Car on.Carrier](stated core.Prop, reading Fact, instance any, points ...TermLike) *Member[Elem, Car] {
	content, ok := instanceContent(instance)
	if !ok {
		panic(fmt.Sprintf("proof.ReadMember: the instance %T carries no statement the closure law's member could be read from — "+
			"read the law at the structure fact the door bound or a projection derived", instance))
	}
	read, err := readLawStatementAt(stated, core.Assume(content))
	if err != nil {
		panic("proof.ReadMember: " + err.Error())
	}
	terms := make([]core.Term, len(points))
	for i, p := range points {
		terms[i] = p.Core()
	}
	// A letter the law binds beyond its components' types stays loose in
	// the reading; the points fix it, as they do where the reading is
	// grounded.
	read, terms, err = ReadingAtWitnessTypes(read, terms)
	if err != nil {
		panic("proof.ReadMember: " + err.Error())
	}
	body := read.Conclusion()
	for _, t := range terms {
		abs := ext.MatchesFORALL(body)
		if abs.IsZero() {
			panic(fmt.Sprintf("proof.ReadMember: %d point(s) for a law binding fewer", len(points)))
		}
		body = abs.Body().Substitute(core.MakeTermSubst(abs.Var(), t))
	}
	if _, concl, isImp := ext.MatchesIMPLY(body); isImp {
		body = concl
	}
	body = tactic.InstanceNormalTerm(body)
	member, _, isMembership := membershipSet(body)
	if !isMembership {
		panic(fmt.Sprintf("proof.ReadMember: the law concludes %s, which is no membership", ext.PrintTerm(body)))
	}
	cite := reading
	if len(points) > 0 {
		cite = reading.At(points...)
	}
	var evidence []any
	var carried []_EvidenceCarrier
	seen := map[*HypHandle]bool{}
	for _, p := range points {
		if c, ok := p.(_EvidenceCarrier); ok {
			evidence = appendEvidence(evidence, c.evidencePremises(), seen)
			carried = append(carried, c)
		}
	}
	cite.members = withoutCarried(cite.members, carried)
	evidence = append(evidence, cite)
	return &Member[Elem, Car]{Expr: *ext.As[Elem](member), evidence: evidence}
}

// ---------------------------------------------------------------------------
// The reflection bridge: a Member parameter of a structure law's closure
// ---------------------------------------------------------------------------

// _MemberRuntime is the sealed hook DescribeMemberType reads: only
// *Member[Elem, Car] declares it.
type _MemberRuntime interface{ memberRuntimeInfo() _MemberRuntimeInfo }

// _MemberRuntimeInfo is one Member instantiation's capabilities,
// captured with its parameters bound: the element's HOL type, the
// carrier letter's binder, the Go type, and the constructor of a member
// whose evidence the guard binding fills in.
type _MemberRuntimeInfo struct {
	holType core.HolType
	binder  string
	goType  reflect.Type
	adopt   func(t Term) (value reflect.Value, prove func(evidence Fact))
}

func (*Member[Elem, Car]) memberRuntimeInfo() _MemberRuntimeInfo {
	var car Car
	return _MemberRuntimeInfo{
		holType: ext.HolTypeOf[Elem](),
		binder:  car.Binder(),
		goType:  reflect.TypeFor[*Member[Elem, Car]](),
		adopt: func(t Term) (reflect.Value, func(Fact)) {
			m := &Member[Elem, Car]{Expr: *ext.As[Elem](t)}
			return reflect.ValueOf(m), func(evidence Fact) { m.evidence = []any{evidence} }
		},
	}
}

// describeMemberType reports whether rt is *Member[Elem, Car] at some
// phantoms, and its capabilities.
func describeMemberType(rt reflect.Type) (_MemberRuntimeInfo, bool) {
	if rt == nil || rt.Kind() != reflect.Pointer {
		return _MemberRuntimeInfo{}, false
	}
	probe, ok := reflect.New(rt.Elem()).Interface().(_MemberRuntime)
	if !ok {
		return _MemberRuntimeInfo{}, false
	}
	info := probe.memberRuntimeInfo()
	if info.goType != rt {
		return _MemberRuntimeInfo{}, false
	}
	return info, true
}
