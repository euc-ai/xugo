package chase

// model.go — the diagram a leaf states, read off its hypotheses by
// constant names: the modules (nodes), the homomorphisms (edges), the
// elements and their memberships, the equations among them, exactness,
// surjectivity and injectivity, and the submodule facts a coset is
// reduced through. An element is a ℤ-vector over ATOMS: an unscaled
// atom is a homomorphism word applied to a generator — a term the leaf
// spells or a witness the loop introduced — at one node, and a scaled
// atom is a monomial in the scalars times an unscaled one (scalar.go);
// a homomorphism applied to a sum is read as the sum of its
// applications (linearization), so every atom is of the form
// m • f₁(f₂(…(g))).
//
// Every reading is by shape and name, never by search: a hypothesis
// whose shape none of the readers recognizes is left aside and named
// in the report.

import (
	"fmt"
	"math/big"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/omega"
)

// _Node is one module of the diagram: a carrier set with the operations
// its module structure proves.
type _Node struct {
	owner                      *_Diagram
	scalar                     *_ScalarRing
	scalarLaws                 map[string]*prop.PropWrapper
	scalarBasis                *_PolynomialBasis
	scalarBasisVersion         int
	scalarBasisAtoms           int
	index                      int
	set                        core.Term
	elem                       core.HolType
	add, zero, neg, smul, ring core.Term
	groupRecord                core.Term
	atoms                      []*_Atom
	byKey                      map[core.TermKey]*_Atom
	relations                  []*_Relation

	groupFact, abelianFact, commLaw, smulLaw *prop.PropWrapper
}

// _Atom is one element the chase names at a node: a term with a
// membership proof (derived when first needed).
type _Atom struct {
	schemaGenerated bool
	scalarBase      *_Atom
	scalarMono      _Monomial
	node            *_Node
	index           int
	term            core.Term
	member          *prop.PropWrapper
}

// _Vector is an element as integer coefficients over a node's atoms.
type _Vector map[int]*big.Int

// _Relation is a ground equation l = r at a node, as the vector l − r
// and the theorem Γ ⊢ l = r.
type _Relation struct {
	derived bool
	v       _Vector
	l, r    core.Term
	proof   *prop.PropWrapper
	pushed  map[*_Hom]bool // the homomorphisms it was carried through
}

// _Hom is a homomorphism between two nodes, with the laws derived from
// its premise.
type _Hom struct {
	fn            core.Term
	src, dst      *_Node
	inLaw, addLaw *prop.PropWrapper
	smulLaw       *prop.PropWrapper
	zero          *prop.PropWrapper // Γ ⊢ fn(zero_src) = zero_dst
}

// _Exactness is im g = ker f at the middle node, with the set equation
// image(g, A) = group_kernel(e, B, f) proved.
type _Exactness struct {
	g, f  *_Hom
	e     core.Term
	setEq *prop.PropWrapper
	done  map[int]bool // the atoms of g's source whose image f kills by it
}

// _Surjection is image(p, A) = B as a set equation, or the pointwise
// spelling ∀z. z ∈ B ⇒ ∃u. u ∈ A ∧ p(u) = z.
type _Surjection struct {
	p         *_Hom
	setEq     *prop.PropWrapper
	pointwise *prop.PropWrapper
}

// _Injection is ∀u v. u ∈ A ∧ v ∈ A ∧ g(u) = g(v) ⇒ u = v, in any order
// of the guard's conjuncts.
type _Injection struct {
	g    *_Hom
	fact *prop.PropWrapper
}

// _Schema is an equation law at a node, ∀u. u ∈ M ⇒ l(u) = r(u),
// instantiated at every atom of the node.
type _Schema struct {
	node   *_Node
	fact   *prop.PropWrapper
	binder core.VarTerm
	done   map[int]bool // the atoms it was instantiated at
}

// _SubmoduleFact is submodule(R, M, N): N a subgroup of M's carrier,
// read for the coset reduction and for N ⊆ M. subgroup is the
// canonical subgroup(module_additive_group(M), N) the submodule law
// gives, and group its record subject.
type _SubmoduleFact struct {
	m        *_Node
	n        core.Term
	group    core.Term
	subgroup *prop.PropWrapper
}

// _Source is a witness waiting to be introduced: Γ ⊢ ∃x. body(x) with
// body a conjunction of x ∈ A and t = f(x) (either order, either
// orientation), f : A → B and t an element of B.
type _Source struct {
	exists *prop.PropWrapper
	f      *_Hom
	t      core.Term
	why    string
}

// _Skolem is a witness the loop introduced: the fresh variable, the
// body assumed at it, and the ∃-fact that discharges the assumption.
type _Skolem struct {
	v      core.VarTerm
	body   core.Term
	exists *prop.PropWrapper
}

// _Membership is a resident fact t ∈ M, as assumed.
type _Membership struct {
	node  *_Node
	proof *prop.PropWrapper
}

// _Fact is a hypothesis or a consequence of one, with its proof from the
// leaf's hypotheses.
type _Fact struct {
	term  core.Term
	proof *prop.PropWrapper
	from  string
	why   string // why it was not read, for the report
	// instance marks a ∀-fact over degrees read at one degree.
	instance bool
}

// _ZeroAlias is Γ ⊢ t = z with z the zero of some module of the diagram.
type _ZeroAlias struct {
	zero  core.Term
	proof *prop.PropWrapper
}

type _Diagram struct {
	readingSchema      bool
	scalarRelationSeen map[string]bool
	scalarRings        []*_ScalarRing
	scalarCache        map[string]_ScalarNormalForm
	laws               *Laws
	goal               core.Prop
	indexArith         bool
	// natArith is set once canonEq has rewritten a degree by the nat
	// ring normal form, or a scalar ring's context that has folded
	// numeral literals has been replaced (usedNatArith).
	natArith bool
	// reader is the proof's reading of the record equations, and
	// reading the closer's normal form as it reads them (Laws.reading):
	// the leaf is read in it, and every law's instance handed over in it
	// (at).
	reader  *omega.LibraryReader
	reading *_Reading
	// concl is the goal's conclusion in the normal form with every degree
	// in its canonical spelling, conclEq Γ ⊢ conclusion = concl (nil when
	// they are one);
	// premises are the hypotheses as read, each in that spelling.
	concl    core.Term
	conclEq  *prop.PropWrapper
	premises []_Fact

	nodes       []*_Node
	homs        []*_Hom
	exact       []*_Exactness
	surjections []*_Surjection
	injections  []*_Injection
	schemas     []*_Schema
	submodules  []*_SubmoduleFact
	members     map[core.TermKey]_Membership // generators' memberships, by term
	ringMembers map[string]*prop.PropWrapper
	sources     []*_Source
	skolems     []*_Skolem
	degrees     []core.Term
	degreeFacts []_Fact // the ∀-facts over degrees, read at each degree added
	grown       bool    // growDegrees has run
	// pending holds the facts no reading has read yet, with why: retried
	// at the next reading, and reported (an instance of a fact over
	// degrees only counted, being an instance at a degree the step does
	// not touch).
	pending []_Fact
	// zeroAliases are the elements a hypothesis equates to a module's
	// zero (`b = zero'`): read as that zero at every module whose zero it
	// is, the proof Γ ⊢ b = zero' carried for the certificate.
	zeroAliases map[core.TermKey]_ZeroAlias
	notes       []string
	skolemCount int
	memberCache map[string]*prop.PropWrapper
	// valueBusy holds the node and term of each value being read against
	// a λ's body at a scalar node (scalarNormalizeUncached).
	valueBusy map[string]bool
}

func scalarKey(x, ring core.Term) string { return fmt.Sprintf("%s|%s", x.AlphaKey(), ring.AlphaKey()) }

func newDiagram(laws *Laws, goal core.Prop, indexArith bool, reader *omega.LibraryReader) *_Diagram {
	return &_Diagram{laws: laws, goal: goal, indexArith: indexArith, reader: reader, reading: laws.reading(reader),
		members: map[core.TermKey]_Membership{}, ringMembers: map[string]*prop.PropWrapper{},
		zeroAliases: map[core.TermKey]_ZeroAlias{},
		memberCache: map[string]*prop.PropWrapper{}}
}

// binArgs reads t as op(a, b), the binary map op applied one argument
// at a time — so op may itself be an application (`fun_add(add')`).
func binArgs(t, op core.Term) (core.Term, core.Term, bool) {
	app, ok := t.AsAppliedTerm()
	if !ok {
		return nil, nil, false
	}
	inner, ok := app.Fun().AsAppliedTerm()
	if !ok || !inner.Fun().AlphaEquals(op) {
		return nil, nil, false
	}
	return inner.Arg(), app.Arg(), true
}

// unArg reads t as fn(x), fn applied to one argument — fn may itself be
// an application, the member `d(n + 1)` of an indexed family of maps.
func unArg(t, fn core.Term) (core.Term, bool) {
	app, ok := t.AsAppliedTerm()
	if !ok || !app.Fun().AlphaEquals(fn) {
		return nil, false
	}
	return app.Arg(), true
}

// ── term shapes ─────────────────────────────────────────────────────────────

func headNamed(t core.Term, name string, arity int) ([]core.Term, bool) {
	head, args := ext.MatchesApply(t)
	c, ok := head.AsConst()
	if !ok || string(c.Name()) != name || len(args) != arity {
		return nil, false
	}
	return args, true
}

// membership reads `x ∈ s`.
func (d *_Diagram) matchMembership(t core.Term) (x, s core.Term, ok bool) {
	head, args := ext.MatchesApply(t)
	c, isConst := head.AsConst()
	if !isConst || c.Meta() != d.laws.member || len(args) != 2 {
		return nil, nil, false
	}
	return args[0], args[1], true
}

// memberTerm is `t ∈ s`.
func (d *_Diagram) memberTerm(t, s core.Term) core.Term {
	return ext.Apply(d.memberConst(t, s), t, s)
}

// memberConst is `∈` at t's and s's types.
func (d *_Diagram) memberConst(t, s core.Term) core.Term {
	return core.MakeConstTerm(d.laws.member, core.MakeFun(t.Type(), core.MakeFun(s.Type(), core.TypeBool())))
}

func conjuncts(t core.Term) []core.Term {
	if a, b, ok := ext.MatchesAND(t); ok {
		return append(conjuncts(a), conjuncts(b)...)
	}
	return []core.Term{t}
}

// conjunctProof is {h} ⊢ target when target is a conjunct of h.
func conjunctProof(h, target core.Term) *prop.PropWrapper {
	if h.AlphaEquals(target) {
		return prop.Assume(h)
	}
	a, b, ok := ext.MatchesAND(h)
	if !ok {
		return nil
	}
	if w := conjunctProof(a, target); w != nil {
		return prop.HypAND0(a, b).DeriveTrans(w)
	}
	if w := conjunctProof(b, target); w != nil {
		return prop.HypAND1(a, b).DeriveTrans(w)
	}
	return nil
}

func isSetType(ty core.HolType) bool {
	flat := ext.MatchesFun(ty)
	return len(flat) == 2 && flat[1].Equals(core.TypeBool())
}

// ── reading the leaf ────────────────────────────────────────────────────────

// read classifies every hypothesis of the goal: the ∀-facts over
// degrees are kept (degreeFacts) and read at the degrees the leaf
// spells, the rest read as they stand. The conclusion and every
// hypothesis are first put in the canonical spelling of their record
// definitions and degrees.
func (d *_Diagram) read() error {
	d.concl = d.goal.Conclusion()
	if d.conclEq = d.canonEq(d.concl); d.conclEq != nil {
		d.concl = prop.Rhs(d.conclEq)
	}
	for i, h := range d.goal.Hyps() {
		w := d.canonical(prop.Assume(h))
		d.premises = append(d.premises, _Fact{term: w.Conclusion(), proof: w, from: fmt.Sprintf("hypothesis %d", i)})
	}
	d.degrees = d.collectDegrees()
	var facts []_Fact
	for _, f := range d.premises {
		facts = append(facts, d.expand(f)...)
	}
	return d.ingest(facts)
}

// growDegrees reads the ∀-facts over degrees once more, at the degrees
// the leaf's first reading spells and the leaf does not — a square read
// at n introduces f(n + 1)(dd(n)(u)), and f(n + 1) is a map, Q(n + 1) a
// module, only by the complex's facts read at n + 1 — and retries every
// fact that did not read. The new degrees are the closed num terms of
// the elements built and of the facts and instances still unread. One
// generation only: the degrees the second reading spells are not read
// again, which bounds a complex's infinite diagram to the part a step
// can touch. Reports whether a degree was added.
func (d *_Diagram) growDegrees() (bool, error) {
	if d.grown || len(d.degreeFacts) == 0 {
		return false, nil
	}
	d.grown = true
	seen := map[core.TermKey]bool{}
	for _, deg := range d.degrees {
		seen[deg.AlphaKey()] = true
	}
	var fresh []core.Term
	note := func(t core.Term) {
		for _, deg := range numSubterms(t) {
			if k := deg.AlphaKey(); !seen[k] {
				seen[k] = true
				fresh = append(fresh, deg)
			}
		}
	}
	for _, n := range d.nodes {
		for _, a := range n.atoms {
			note(a.term)
		}
	}
	for _, f := range d.pending {
		note(f.term)
	}
	for _, sc := range d.schemas {
		note(sc.fact.Conclusion())
	}
	if len(fresh) == 0 {
		return false, nil
	}
	sort.Slice(fresh, func(i, j int) bool { return fresh[i].Compare(fresh[j]) < 0 })
	d.degrees = append(d.degrees, fresh...)
	var facts []_Fact
	for _, f := range d.degreeFacts {
		facts = append(facts, d.instances(f, fresh)...)
	}
	return true, d.ingest(facts)
}

// ingest reads facts, the facts an earlier reading left unread retried
// with them: the modules and the homomorphisms' proved endpoint modules
// first, every other reading locating its modules among them; then the
// submodules; then the elements' memberships, a generator read before
// the equations that
// mention it whatever order the kernel keeps the hypotheses in; then
// everything else to a fixpoint, since a kernel membership or a coset
// equation yields elements other facts need. What does not read stays
// pending, for the next reading and for the report.
func (d *_Diagram) ingest(facts []_Fact) error {
	facts = append(d.pending, facts...)
	d.pending = nil
	unread := func(f _Fact, why string) {
		f.why = why
		d.pending = append(d.pending, f)
	}
	var rest []_Fact
	for _, f := range facts {
		if args, ok := headNamed(f.term, moduleOnName, moduleOnArity); ok {
			if _, err := d.addNode(args, f.proof); err != nil {
				return err
			}
			continue
		}
		if args, ok := headNamed(f.term, homomorphismName, homomorphismArity); ok {
			if err := d.addHom(args, f); err != nil {
				return err
			}
			continue
		}
		rest = append(rest, f)
	}
	var later []_Fact
	for _, f := range rest {
		if args, ok := headNamed(f.term, submoduleName, submoduleArity); ok {
			subgroup := d.canonicalAt(d.laws.SubmoduleSubgroup, args, f.proof)
			group, ok := headNamed(subgroup.Conclusion(), subgroupName, subgroupArity)
			if !ok {
				panic("chase: a submodule's subgroup law has the wrong shape")
			}
			if n := d.nodeForGroup(group[0]); n != nil {
				d.addSubmodule(&_SubmoduleFact{m: n, n: group[1], group: group[0], subgroup: subgroup})
			} else {
				unread(f, "its module has no module structure fact")
			}
			continue
		}
		later = append(later, f)
	}
	if err := d.checkAcyclic(); err != nil {
		return err
	}
	var pending []_Fact
	for _, f := range later {
		if x, s, ok := d.matchMembership(f.term); ok && d.plainSet(s) {
			if err := d.readMembership(x, s, f.proof, f.from); err != nil {
				unread(f, err.Error())
			}
			continue
		}
		pending = append(pending, f)
	}
	for progress := true; progress && len(pending) > 0; {
		progress = false
		var next []_Fact
		for _, f := range pending {
			if err := d.readFact(f); err == nil {
				progress = true
			} else {
				f.why = err.Error()
				next = append(next, f)
			}
		}
		pending = next
	}
	for _, f := range pending {
		unread(f, f.why)
	}
	return nil
}

// plainSet reports whether s is a set a membership is read into a
// generator through: a module of the diagram, a submodule a premise
// names, or the ring.
func (d *_Diagram) plainSet(s core.Term) bool {
	if d.nodeOf(s) != nil {
		return true
	}
	for _, sub := range d.submodules {
		if sub.n.AlphaEquals(s) {
			return true
		}
	}
	for _, n := range d.nodes {
		if n.ring.AlphaEquals(s) {
			return true
		}
	}
	return false
}

// expand splits conjunctions and reads a ∀-fact over degrees at the
// degrees the leaf spells, keeping the fact for growDegrees.
func (d *_Diagram) expand(f _Fact) []_Fact {
	f = asImplication(f)
	if a, b, ok := ext.MatchesAND(f.term); ok {
		// {a ∧ b} ⊢ a, routed through f's own proof of the conjunction.
		left := _Fact{term: a, proof: f.proof.DeriveTrans(prop.HypAND0(a, b)), from: f.from, instance: f.instance}
		right := _Fact{term: b, proof: f.proof.DeriveTrans(prop.HypAND1(a, b)), from: f.from, instance: f.instance}
		return append(d.expand(left), d.expand(right)...)
	}
	if abs := ext.MatchesFORALL(f.term); !abs.IsZero() && abs.Var().Type().Equals(dsl.NumType) {
		d.degreeFacts = append(d.degreeFacts, f)
		return d.instances(f, d.degrees)
	}
	return []_Fact{f}
}

// instances is the ∀-fact over degrees f read at each of degs, each
// instance's degrees put in their canonical spelling.
func (d *_Diagram) instances(f _Fact, degs []core.Term) []_Fact {
	var out []_Fact
	for _, deg := range degs {
		inst := d.canonical(f.proof.ConclForAllInsts(deg))
		out = append(out, d.expand(_Fact{term: inst.Conclusion(), proof: inst,
			from: fmt.Sprintf("%s at %s", f.from, ext.PrintTerm(deg)), instance: true})...)
	}
	return out
}

// numSubterms lists t's closed num-typed subterms, outermost first.
func numSubterms(t core.Term) []core.Term {
	var out []core.Term
	var walk func(t core.Term, bound []core.VarTerm)
	walk = func(t core.Term, bound []core.VarTerm) {
		if t.Type().Equals(dsl.NumType) {
			closed := true
			for _, b := range bound {
				if t.HasFree(b) {
					closed = false
					break
				}
			}
			if closed {
				out = append(out, t)
			}
		}
		switch u := t.Core().(type) {
		case core.AppliedTerm:
			walk(u.Fun(), bound)
			walk(u.Arg(), bound)
		case core.AbsTerm:
			walk(u.Body(), append(bound, u.Var()))
		}
	}
	walk(t, nil)
	return out
}

// collectDegrees lists the degree terms the leaf spells: the closed
// num-typed subterms of the conclusion and the hypotheses as read, in a
// fixed order.
func (d *_Diagram) collectDegrees() []core.Term {
	seen := map[core.TermKey]bool{}
	var out []core.Term
	add := func(t core.Term) {
		for _, deg := range numSubterms(t) {
			if k := deg.AlphaKey(); !seen[k] {
				seen[k] = true
				out = append(out, deg)
			}
		}
	}
	add(d.concl)
	for _, f := range d.premises {
		add(f.term)
	}
	sort.Slice(out, func(i, j int) bool { return out[i].Compare(out[j]) < 0 })
	return out
}

// canonEq is Γ ⊢ t = t' with t' the normal form of t (the applications
// of the λs in kept left standing, a law's instance) and every degree t
// spells in its nat ring normal form —
// `n + 1 + 1` and `n + 2` are one term, `0 + 1` and `1`
// another — so a degree reads as one degree however a definition, an
// instance or the leaf spells it. Degree normalization requires the
// nat-arithmetic capability; record rewriting uses only supplied laws.
// Returns nil when the term is already in that spelling.
func (d *_Diagram) canonEq(t core.Term, kept ...core.Term) *prop.PropWrapper {
	eq := d.reading.instance(kept)(t)
	if !d.indexArith {
		return eq
	}
	canonical := t
	if eq != nil {
		canonical = prop.Rhs(eq)
	}
	if degrees := canonicalDegrees(canonical); degrees != nil {
		d.natArith = true
		if eq != nil {
			return eq.EqTrans(degrees)
		}
		return degrees
	}
	return eq
}

// canonicalDegrees is the nat ring normal form's rewrite, read at num
// terms only.
var canonicalDegrees = omega.RingNormalizeRewriteWithPolicy(omega.ArithPolicy{Nat: true})

// at hands a law's instance over in the normal form, the λs it is
// instantiated at left applied where the law applies them
// (_Reading.instance).
func (d *_Diagram) at(law *prop.PropWrapper, lead []core.Term, fact *prop.PropWrapper, args ...core.Term) *prop.PropWrapper {
	return lawAt(law, lead, fact, args...).RewriteConcl(d.reading.instance(applied(lead, args)))
}

// canonicalAt is at's instance with its degrees in canonical spelling
// as well.
func (d *_Diagram) canonicalAt(law *prop.PropWrapper, lead []core.Term, fact *prop.PropWrapper, args ...core.Term) *prop.PropWrapper {
	return d.canonical(d.at(law, lead, fact, args...), applied(lead, args)...)
}

// libraryRead is the reader's read of a record equation's theorem; nil
// for the installed fallback.
func (d *_Diagram) libraryRead() omega.LibraryRead {
	if d.reader == nil {
		return nil
	}
	return d.reader.Read
}

// canonical is w with its conclusion in canonEq's spelling.
func (d *_Diagram) canonical(w *prop.PropWrapper, kept ...core.Term) *prop.PropWrapper {
	if eq := d.canonEq(w.Conclusion(), kept...); eq != nil {
		return eq.EqMP(w)
	}
	return w
}

// ── nodes, homs ─────────────────────────────────────────────────────────────

// atomCount is the number of atoms over every node.
func (d *_Diagram) atomCount() int {
	n := 0
	for _, nd := range d.nodes {
		n += len(nd.atoms)
	}
	return n
}

func (d *_Diagram) nodeOf(set core.Term) *_Node {
	for _, n := range d.nodes {
		if n.set.AlphaEquals(set) {
			return n
		}
	}
	return nil
}

// nodeForGroup is the module whose additive structure is record.
func (d *_Diagram) nodeForGroup(record core.Term) *_Node {
	for _, n := range d.nodes {
		if n.groupRecord.AlphaEquals(record) {
			return n
		}
	}
	return nil
}

// addNode derives and caches a module's carrier laws, read at its record
// projections and normalized.
func (d *_Diagram) addNode(args []core.Term, proof *prop.PropWrapper) (*_Node, error) {
	group := d.canonicalAt(d.laws.AddGroupOn, args, proof)
	comm := d.canonicalAt(d.laws.AddComm, args, proof)
	smul := d.canonicalAt(d.laws.SmulIn, args, proof)
	comps, ok := headNamed(group.Conclusion(), groupOnName, groupOnArity)
	if !ok {
		panic("chase: a module's additive group law has the wrong shape")
	}
	zero, set, err := d.closureComponent(d.laws.OneIn, comps[0], group, 0)
	if err != nil {
		return nil, err
	}
	add, _, err := d.closureComponent(d.laws.MulIn, comps[0], group, 2)
	if err != nil {
		return nil, err
	}
	neg, _, err := d.closureComponent(d.laws.InvIn, comps[0], group, 1)
	if err != nil {
		return nil, err
	}
	vars, body := stripForalls(smul.Conclusion())
	guard, result, ok := ext.MatchesIMPLY(body)
	if !ok || len(vars) != 2 {
		panic("chase: a module's scalar closure law has the wrong shape")
	}
	scalar, vector, ok := ext.MatchesAND(guard)
	c, ring, scalarOK := d.matchMembership(scalar)
	u, carrier, vectorOK := d.matchMembership(vector)
	product, target, resultOK := d.matchMembership(result)
	if !ok || !scalarOK || !vectorOK || !resultOK || !c.AlphaEquals(vars[0]) || !u.AlphaEquals(vars[1]) || !carrier.AlphaEquals(set) || !target.AlphaEquals(carrier) {
		panic("chase: a module's scalar closure law has inconsistent guards")
	}
	// The action is what stands applied to the scalar and the vector; an
	// action the record gives by a λ leaves no such term (closureComponent).
	application, ok := product.AsAppliedTerm()
	if !ok || !application.Arg().AlphaEquals(u) {
		return nil, lambdaOperation(args[1], product)
	}
	action, ok := application.Fun().AsAppliedTerm()
	if !ok || !action.Arg().AlphaEquals(c) || action.Fun().HasFree(vars[0]) || action.Fun().HasFree(vars[1]) {
		return nil, lambdaOperation(args[1], product)
	}
	n := &_Node{owner: d, index: len(d.nodes), set: set, elem: zero.Type(),
		add: add, zero: zero, neg: neg, smul: action.Fun(), ring: ring, groupRecord: comps[0],
		groupFact: group, commLaw: comm, smulLaw: smul, byKey: map[core.TermKey]*_Atom{}}
	if previous := d.nodeOf(n.set); previous != nil {
		if previous.scalar != nil {
			scalarFact := d.canonicalAt(d.laws.Scalars.RingOn, args, proof)
			if !previous.scalar.fact.Conclusion().AlphaEquals(scalarFact.Conclusion()) {
				return nil, fmt.Errorf("the carrier %s has conflicting scalar-ring operations", ext.PrintTerm(n.set))
			}
		}
		if !previous.add.AlphaEquals(n.add) || !previous.zero.AlphaEquals(n.zero) || !previous.neg.AlphaEquals(n.neg) || !previous.smul.AlphaEquals(n.smul) || !previous.ring.AlphaEquals(n.ring) {
			return nil, fmt.Errorf("the carrier %s has conflicting module operations; the chase reads one structure per carrier (add: %s / %s; zero: %s / %s; neg: %s / %s; smul: %s / %s; scalars: %s / %s)",
				ext.PrintTerm(n.set), ext.PrintTerm(previous.add), ext.PrintTerm(n.add), ext.PrintTerm(previous.zero), ext.PrintTerm(n.zero),
				ext.PrintTerm(previous.neg), ext.PrintTerm(n.neg), ext.PrintTerm(previous.smul), ext.PrintTerm(n.smul), ext.PrintTerm(previous.ring), ext.PrintTerm(n.ring))
		}
		return previous, nil
	}
	d.nodes = append(d.nodes, n)
	if err := d.installScalarNode(n, args, proof); err != nil {
		return nil, err
	}
	return n, nil
}

// addSubmodule records a submodule fact once.
func (d *_Diagram) addSubmodule(sub *_SubmoduleFact) {
	for _, s := range d.submodules {
		if s.m == sub.m && s.n.AlphaEquals(sub.n) {
			return
		}
	}
	d.submodules = append(d.submodules, sub)
}

// addHom reads both module structures from the homomorphism's proved
// endpoint laws, so its endpoints need no separate module premises.
func (d *_Diagram) addHom(args []core.Term, f _Fact) error {
	endpoints := make([]*_Node, 2)
	for i, law := range []*prop.PropWrapper{d.laws.HomSource, d.laws.HomTarget} {
		endpoint := d.canonicalAt(law, args, f.proof)
		moduleArgs, ok := headNamed(endpoint.Conclusion(), moduleOnName, moduleOnArity)
		if !ok {
			panic("chase: a homomorphism's endpoint law has the wrong shape")
		}
		n, err := d.addNode(moduleArgs, endpoint)
		if err != nil {
			return err
		}
		endpoints[i] = n
	}
	src, dst := endpoints[0], endpoints[1]
	for _, h := range d.homs {
		if h.fn.AlphaEquals(args[3]) && h.src == src && h.dst == dst {
			return nil
		}
	}
	h := &_Hom{fn: args[3], src: src, dst: dst,
		inLaw:  d.canonicalAt(d.laws.HomIn, args, f.proof),
		addLaw: d.canonicalAt(d.laws.HomAdd, args, f.proof)}
	if src.scalar != nil {
		h.smulLaw = d.canonicalAt(d.laws.Scalars.HomSmul, args, f.proof)
	}
	d.homs = append(d.homs, h)
	return nil
}

// homsNamed are the homomorphisms whose function is fn.
func (d *_Diagram) homsNamed(fn core.Term) []*_Hom {
	var out []*_Hom
	for _, h := range d.homs {
		if h.fn.AlphaEquals(fn) {
			out = append(out, h)
		}
	}
	return out
}

func (d *_Diagram) homFrom(fn core.Term, src *_Node) *_Hom {
	for _, h := range d.homsNamed(fn) {
		if h.src == src {
			return h
		}
	}
	return nil
}

// checkAcyclic refuses a diagram with a cycle among its homomorphisms
// (an endomorphism included): the chase's term universe is bounded by
// the longest path.
func (d *_Diagram) checkAcyclic() error {
	state := make([]int, len(d.nodes)) // 0 unseen, 1 on the stack, 2 done
	var visit func(n *_Node) *_Hom
	visit = func(n *_Node) *_Hom {
		state[n.index] = 1
		for _, h := range d.homs {
			if h.src != n {
				continue
			}
			switch state[h.dst.index] {
			case 1:
				return h
			case 0:
				if back := visit(h.dst); back != nil {
					return back
				}
			}
		}
		state[n.index] = 2
		return nil
	}
	for _, n := range d.nodes {
		if state[n.index] == 0 {
			if h := visit(n); h != nil {
				return fmt.Errorf("the diagram has a cycle through the homomorphism %s: %s → %s; the chase closer reads acyclic diagrams only",
					ext.PrintTerm(h.fn), ext.PrintTerm(h.src.set), ext.PrintTerm(h.dst.set))
			}
		}
	}
	return nil
}

// ── the element-level facts ─────────────────────────────────────────────────

// readFact classifies one hypothesis about elements; the error says
// why its shape is not one the closer reads.
func (d *_Diagram) readFact(f _Fact) error {
	f = asImplication(f)
	t := f.term
	if x, s, ok := d.matchMembership(t); ok {
		return d.readMembership(x, s, f.proof, f.from)
	}
	if l, r, ok := core.MatchesEQ(t); ok {
		if isSetType(l.Type()) {
			return d.readSetEquation(l, r, f)
		}
		if l.Type().Equals(core.TypeBool()) {
			return fmt.Errorf("an ⇔ is not read")
		}
		if d.readScalarEquation(l, r, f.proof) {
			// A module whose elements are the scalars (the ring over
			// itself) holds the equation as a relation too; at any other
			// ring the sides are no module's elements.
			if _, _, err := d.vecOf(l, nil); err != nil {
				return nil
			}
			return d.addRelation(l, r, f.proof)
		}
		return d.addRelation(l, r, f.proof)
	}
	if args, ok := headNamed(t, exactAtName, exactAtArity); ok {
		// exact_at(e, A, B, g, f) ⇔ image(g, A) = group_kernel(e, B, f)
		def := d.at(d.laws.ExactAtDef, args, nil)
		return d.readExactEqFrom(def.EqMP(f.proof))
	}
	if args, ok := headNamed(t, injectiveOnName, injectiveOnArity); ok {
		// injective_on(A, g) ⇔ ∀x y. x ∈ A ∧ y ∈ A ∧ g(x) = g(y) ⇒ x = y
		opened := d.at(d.laws.InjectiveOnDef, args, nil).EqMP(f.proof)
		return d.readForall(_Fact{term: opened.Conclusion(), proof: opened, from: f.from})
	}
	if guard, concl, ok := ext.MatchesIMPLY(t); ok {
		// p ⇒ q, p a premise or decided by the diagram as read: q.
		held, err := d.decideAntecedent(guard)
		if err != nil {
			return fmt.Errorf("an implication whose antecedent is neither a premise nor decided by the diagram: %v", err)
		}
		return d.readFact(_Fact{term: concl, proof: f.proof.DemoteHyp().DeriveHypFrom(held), from: f.from, instance: f.instance})
	}
	if abs := ext.MatchesFORALL(t); !abs.IsZero() {
		return d.readForall(f)
	}
	return fmt.Errorf("no shape the closer knows")
}

// asImplication reads a fact spelled as a clause, `… ∨ ¬p ∨ …`, as the
// guarded law it is, `p ⇒ rest` — the closer's clause form, which a By
// installs a premise in where the context does not supply its guard
// as written — and a fact of any other shape as it stands. Under a
// ∀-prefix the body is read the same way, so a clause over elements
// reaches readForall as the implication it reads.
func asImplication(f _Fact) _Fact {
	eq := clauseImplicationEq(f.term)
	if eq == nil {
		return f
	}
	w := eq.EqMP(f.proof)
	return _Fact{term: w.Conclusion(), proof: w, from: f.from, instance: f.instance}
}

// clauseImplicationEq is ⊢ t = (p ⇒ rest) for a clause t with a negated
// disjunct ¬p — the first one, fronted — and rest the other disjuncts;
// under a ∀-prefix, the equation on the body abstracted back. nil for a
// term that is no such clause.
func clauseImplicationEq(t core.Term) *prop.PropWrapper {
	if abs := ext.MatchesFORALL(t); !abs.IsZero() {
		body := clauseImplicationEq(abs.Body())
		if body == nil {
			return nil
		}
		quantifier, ok := t.AsAppliedTerm()
		if !ok {
			panic("chase: a ∀ that is not the quantifier applied to its body (engine invariant)")
		}
		return body.Abs(abs.Var()).LeftApply(quantifier.Fun())
	}
	if _, _, ok := ext.MatchesOR(t); !ok {
		return nil
	}
	disjuncts := ext.DecomposesOR(t)
	negated := -1
	for i, disjunct := range disjuncts {
		if ext.MatchesNOT(disjunct) != nil {
			negated = i
			break
		}
	}
	if negated < 0 {
		return nil
	}
	fronted := prop.ArrangeORChain(t, -1, negated)
	nh, rest, ok := ext.MatchesOR(prop.Rhs(fronted))
	if !ok {
		panic("chase: fronting a disjunct of a clause lost the disjunction (engine invariant)")
	}
	return fronted.EqTrans(prop.BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](ext.MatchesNOT(nh), rest).EqSym())
}

// decideAntecedent is Γ ⊢ p for the antecedent of a premise p ⇒ q: a
// premise the list states, or a conclusion the diagram decides from what
// it has read — a conjunction conjunct by conjunct. It is the
// zero-binder case of the equation schemas' guards, so a grounded law
// `u ∈ M ⇒ l = r` reads as the schema `∀u. u ∈ M ⇒ l = r` does at u.
func (d *_Diagram) decideAntecedent(p core.Term) (*prop.PropWrapper, error) {
	for _, f := range d.premises {
		if f.term.AlphaEquals(p) {
			return f.proof, nil
		}
	}
	if a, b, ok := ext.MatchesAND(p); ok {
		pa, err := d.decideAntecedent(a)
		if err != nil {
			return nil, err
		}
		pb, err := d.decideAntecedent(b)
		if err != nil {
			return nil, err
		}
		return prop.ConclAND(a, b).DeriveHypFrom(pa).DeriveHypFrom(pb), nil
	}
	return d.prove(p)
}

// readMembership reads `x ∈ s`: a generator at a node, a witness source
// (an image), a kernel membership, a member of a submodule, or a scalar
// of the ring.
func (d *_Diagram) readMembership(x, s core.Term, proof *prop.PropWrapper, from string) error {
	for _, r := range d.scalarRings {
		if r.ops[6].AlphaEquals(s) {
			d.ringMembers[scalarKey(x, s)] = proof
		}
	}
	if n := d.nodeOf(s); n != nil {
		d.members[x.AlphaKey()] = _Membership{node: n, proof: proof}
		n.atomFor(x)
		return nil
	}
	if args, ok := headNamed(s, imageName, imageArity); ok {
		return d.addImageSource(x, args[0], args[1], proof, from)
	}
	if args, ok := headNamed(s, kernelName, kernelArity); ok {
		// x ∈ group_kernel(e, B, g) ⇔ x ∈ B ∧ g(x) = e
		n := d.nodeOf(args[1])
		if n == nil {
			return fmt.Errorf("the kernel's module %s has no module structure fact", ext.PrintTerm(args[1]))
		}
		law := d.at(d.laws.InKernel, []core.Term{args[0], args[1], args[2]}, nil, x)
		both := law.EqMP(proof)
		a, b, _ := ext.MatchesAND(both.Conclusion())
		d.members[x.AlphaKey()] = _Membership{node: n, proof: both.DeriveTrans(prop.HypAND0(a, b))}
		n.atomFor(x)
		return d.addRelation(ext.Apply(args[2], x), args[0], both.DeriveTrans(prop.HypAND1(a, b)))
	}
	for _, sub := range d.submodules {
		if sub.n.AlphaEquals(s) {
			// x ∈ N and N ⊆ M give x ∈ M.
			subset := d.at(d.laws.SubgroupSubset, []core.Term{sub.group, sub.n}, sub.subgroup)
			def := d.at(d.laws.SubsetDef, []core.Term{sub.n, sub.m.set}, nil)
			pointwise := def.EqMP(subset).ConclForAllInsts(x) // Γ ⊢ x ∈ N ⇒ x ∈ M
			d.members[x.AlphaKey()] = _Membership{node: sub.m, proof: pointwise.DemoteHyp().DeriveHypFrom(proof)}
			sub.m.atomFor(x)
			return nil
		}
	}
	// Scalars of the ring: c ∈ R, read for smul(c, u) ∈ M.
	for _, n := range d.nodes {
		if n.ring.AlphaEquals(s) {
			d.ringMembers[scalarKey(x, s)] = proof
			return nil
		}
	}
	return fmt.Errorf("the set %s is no module, image, kernel, submodule or ring of the diagram", ext.PrintTerm(s))
}

// addImageSource records x ∈ image(f, A) as a witness to introduce.
func (d *_Diagram) addImageSource(x, fn, set core.Term, proof *prop.PropWrapper, from string) error {
	src := d.nodeOf(set)
	if src == nil {
		return fmt.Errorf("the image's source %s has no module structure fact", ext.PrintTerm(set))
	}
	h := d.homFrom(fn, src)
	if h == nil {
		return fmt.Errorf("%s has no module_homomorphism fact out of %s", ext.PrintTerm(fn), ext.PrintTerm(set))
	}
	inImage := d.at(d.laws.InImage, []core.Term{fn, set}, nil, x)
	d.sources = append(d.sources, &_Source{exists: inImage.EqMP(proof), f: h, t: x, why: from})
	return nil
}

// readSetEquation reads image(p, A) = B (onto), image(g, A) =
// group_kernel(e, B, f) (exactness unfolded), or a coset equation.
func (d *_Diagram) readSetEquation(l, r core.Term, f _Fact) error {
	if d.readSurjectionEq(l, r, f.proof) || d.readSurjectionEq(r, l, f.proof.EqSym()) {
		return nil
	}
	if d.readExactEq(l, r, f.proof) || d.readExactEq(r, l, f.proof.EqSym()) {
		return nil
	}
	if cl, okl := headNamed(l, leftCosetName, leftCosetArity); okl {
		if cr, okr := headNamed(r, leftCosetName, leftCosetArity); okr && cl[0].AlphaEquals(cr[0]) && cl[2].AlphaEquals(cr[2]) {
			law, err := d.cosetLaw(cl[0], cl[1], cr[1], cl[2])
			if err != nil {
				return err
			}
			reduced := law.EqMP(f.proof) // Γ ⊢ add(neg x, y) ∈ N
			x, s, _ := d.matchMembership(reduced.Conclusion())
			return d.readMembership(x, s, reduced, f.from+" (coset reduced)")
		}
	}
	return fmt.Errorf("an equation between sets that is neither an onto map's image, an exactness, nor two cosets of one subgroup")
}

func (d *_Diagram) readSurjectionEq(l, r core.Term, proof *prop.PropWrapper) bool {
	args, ok := headNamed(l, imageName, imageArity)
	if !ok {
		return false
	}
	src, dst := d.nodeOf(args[1]), d.nodeOf(r)
	if src == nil || dst == nil {
		return false
	}
	h := d.homFrom(args[0], src)
	if h == nil || h.dst != dst {
		return false
	}
	d.surjections = append(d.surjections, &_Surjection{p: h, setEq: proof})
	return true
}

func (d *_Diagram) readExactEq(l, r core.Term, proof *prop.PropWrapper) bool {
	im, ok := headNamed(l, imageName, imageArity)
	if !ok {
		return false
	}
	ker, ok := headNamed(r, kernelName, kernelArity)
	if !ok {
		return false
	}
	a, b := d.nodeOf(im[1]), d.nodeOf(ker[1])
	if a == nil || b == nil {
		return false
	}
	g, f := d.homFrom(im[0], a), d.homFrom(ker[2], b)
	if g == nil || f == nil || g.dst != b || !ker[0].AlphaEquals(f.dst.zero) {
		return false
	}
	d.exact = append(d.exact, &_Exactness{g: g, f: f, e: ker[0], setEq: proof, done: map[int]bool{}})
	return true
}

// readForall reads an exactness fact's expansion, an injectivity, a
// pointwise surjectivity, or an equation schema.
func (d *_Diagram) readForall(f _Fact) error {
	binders, body := stripForalls(f.term)
	switch len(binders) {
	case 1:
		v := binders[0]
		guard, concl, ok := ext.MatchesIMPLY(body)
		if !ok {
			return fmt.Errorf("a ∀-fact of no shape the closer reads: an equation schema, an injectivity, or a pointwise onto map")
		}
		gx, gs, isMember := d.matchMembership(guard)
		if !isMember || !gx.Equals(v) {
			return fmt.Errorf("a ∀-fact of no shape the closer reads: an equation schema, an injectivity, or a pointwise onto map")
		}
		n := d.nodeOf(gs)
		if n == nil {
			return fmt.Errorf("a ∀-fact of no shape the closer reads: an equation schema, an injectivity, or a pointwise onto map")
		}
		if abs := ext.MatchesEXISTS(concl); !abs.IsZero() {
			// ∀z. z ∈ B ⇒ ∃u. u ∈ A ∧ p(u) = z
			h := d.sourceShape(abs, v, n)
			if h == nil {
				return fmt.Errorf("a ∀-fact of no shape the closer reads: an equation schema, an injectivity, or a pointwise onto map")
			}
			d.surjections = append(d.surjections, &_Surjection{p: h, pointwise: f.proof})
			return nil
		}
		if l, _, isEq := core.MatchesEQ(concl); isEq && !isSetType(l.Type()) && !l.Type().Equals(core.TypeBool()) {
			if n.scalar != nil && !d.scalarSchemaIndependent(concl, v) {
				return fmt.Errorf("an equation schema whose scalar depends on its module element is not R-linear")
			}
			d.schemas = append(d.schemas, &_Schema{node: n, fact: f.proof, binder: v, done: map[int]bool{}})
			return nil
		}
		return fmt.Errorf("a ∀-fact of no shape the closer reads: an equation schema, an injectivity, or a pointwise onto map")
	case 2:
		u, v := binders[0], binders[1]
		guard, concl, ok := ext.MatchesIMPLY(body)
		if !ok {
			return fmt.Errorf("a ∀-fact of no shape the closer reads: an equation schema, an injectivity, or a pointwise onto map")
		}
		cl, cr, isEq := core.MatchesEQ(concl)
		if !isEq || !((cl.Equals(u) && cr.Equals(v)) || (cl.Equals(v) && cr.Equals(u))) {
			return fmt.Errorf("a ∀-fact of no shape the closer reads: an equation schema, an injectivity, or a pointwise onto map")
		}
		// The guard's equation states one map's values at u and at v,
		// in either order; the map is told once the memberships have
		// named its source (valuedAtBoth).
		var n *_Node
		var l, r core.Term
		memberships, equations := 0, 0
		for _, c := range conjuncts(guard) {
			if x, s, isMember := d.matchMembership(c); isMember && (x.Equals(u) || x.Equals(v)) {
				if m := d.nodeOf(s); m != nil && (n == nil || n == m) {
					n = m
					memberships++
					continue
				}
				return fmt.Errorf("a ∀-fact of no shape the closer reads: an equation schema, an injectivity, or a pointwise onto map")
			}
			if el, er, eq := core.MatchesEQ(c); eq {
				l, r = el, er
				equations++
				continue
			}
			return fmt.Errorf("a ∀-fact of no shape the closer reads: an equation schema, an injectivity, or a pointwise onto map")
		}
		if n == nil || memberships != 2 || equations != 1 {
			return fmt.Errorf("a ∀-fact of no shape the closer reads: an equation schema, an injectivity, or a pointwise onto map")
		}
		h := d.valuedAtBoth(l, r, u, v, n)
		if h == nil {
			return fmt.Errorf("a ∀-fact of no shape the closer reads: an equation schema, an injectivity, or a pointwise onto map")
		}
		d.injections = append(d.injections, &_Injection{g: h, fact: f.proof})
		return nil
	}
	return fmt.Errorf("a ∀-fact of no shape the closer reads: an equation schema, an injectivity, or a pointwise onto map")
}

// sourceShape reads ∃u. u ∈ A ∧ p(u) = z (either order, either
// orientation) with z the outer binder of a pointwise surjectivity,
// returning the homomorphism p : A → B.
func (d *_Diagram) sourceShape(abs core.AbsTerm, z core.VarTerm, b *_Node) *_Hom {
	u := abs.Var()
	var a *_Node
	var value core.Term
	for _, c := range conjuncts(abs.Body()) {
		if x, s, isMember := d.matchMembership(c); isMember && x.Equals(u) {
			a = d.nodeOf(s)
			continue
		}
		if l, r, isEq := core.MatchesEQ(c); isEq {
			if r.Equals(z) {
				l, r = r, l
			}
			if !l.Equals(z) {
				return nil
			}
			value = r
			continue
		}
		return nil
	}
	if a == nil || value == nil {
		return nil
	}
	h := d.valuedAt(value, u, a)
	if h == nil || h.dst != b {
		return nil
	}
	return h
}

func stripForalls(t core.Term) ([]core.VarTerm, core.Term) {
	var vars []core.VarTerm
	for {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() {
			return vars, t
		}
		vars = append(vars, abs.Var())
		t = abs.Body()
	}
}

// readExactEqFrom reads Γ ⊢ image(g, A) = group_kernel(e, B, f).
func (d *_Diagram) readExactEqFrom(setEq *prop.PropWrapper) error {
	l, r, ok := core.MatchesEQ(setEq.Conclusion())
	if !ok || !d.readExactEq(l, r, setEq) {
		return fmt.Errorf("the exactness names a module or a homomorphism without its fact")
	}
	return nil
}

// ── atoms and linearization ─────────────────────────────────────────────────

func (n *_Node) atomFor(t core.Term) *_Atom {
	k := t.AlphaKey()
	if a, ok := n.byKey[k]; ok {
		return a
	}
	if n.scalar != nil && len(n.atoms) >= polynomialTermCap {
		panic(_PolynomialLimit{"saturation exceeds 4096 monomial-labelled atoms at one module"})
	}
	a := &_Atom{node: n, index: len(n.atoms), term: t}
	n.atoms = append(n.atoms, a)
	n.byKey[k] = a
	return a
}

func (v _Vector) add(w _Vector, scale int64) _Vector {
	out := _Vector{}
	for i, c := range v {
		out[i] = new(big.Int).Set(c)
	}
	for i, c := range w {
		x, ok := out[i]
		if !ok {
			x = new(big.Int)
			out[i] = x
		}
		x.Add(x, new(big.Int).Mul(c, big.NewInt(scale)))
		if x.Sign() == 0 {
			delete(out, i)
		}
	}
	return out
}

func (v _Vector) negate() _Vector { return _Vector{}.add(v, -1) }

func (v _Vector) isZero() bool { return len(v) == 0 }

func (v _Vector) dense(n int) []*big.Int {
	out := zeroRow(n)
	for i, c := range v {
		out[i].Set(c)
	}
	return out
}

func unitVec(i int) _Vector { return _Vector{i: big.NewInt(1)} }

// atomsOf lists the atoms a vector mentions, by index.
func (n *_Node) atomsOf(v _Vector) []*_Atom {
	idx := make([]int, 0, len(v))
	for i := range v {
		idx = append(idx, i)
	}
	sort.Ints(idx)
	out := make([]*_Atom, len(idx))
	for k, i := range idx {
		out[k] = n.atoms[i]
	}
	return out
}

// vecOf linearizes t as an element of expect (nil to infer the node):
// sums and negations of the node's operations split, a homomorphism
// applied to a sum is the sum of its applications, and what remains is
// an atom — a known one, a homomorphism word over one, or a generator
// with a resident membership.
func (d *_Diagram) vecOf(t core.Term, expect *_Node) (_Vector, *_Node, error) {
	if expect != nil && expect.scalar != nil {
		return d.scalarVec(t, expect)
	}
	if expect == nil && len(d.scalarRings) > 0 {
		zero := t
		if a, ok := d.zeroAliases[t.AlphaKey()]; ok {
			zero = a.zero
		}
		for _, n := range d.nodes {
			if n.zero.AlphaEquals(zero) {
				return _Vector{}, nil, nil
			}
		}
		var last error
		for _, n := range d.nodes {
			if n.scalar != nil {
				v, m, err := d.scalarVec(t, n)
				if err == nil {
					return v, m, nil
				}
				last = err
			}
		}
		if last != nil {
			return nil, nil, last
		}
	}
	// An element a hypothesis equates to a zero is that zero.
	if al, ok := d.zeroAliases[t.AlphaKey()]; ok {
		for _, n := range d.nodes {
			if (expect == nil || n == expect) && n.zero.AlphaEquals(al.zero) {
				return _Vector{}, expect, nil
			}
		}
	}
	// The zero of a node.
	for _, n := range d.nodes {
		if (expect == nil || n == expect) && n.zero.AlphaEquals(t) {
			return _Vector{}, expect, nil
		}
	}
	// A known atom.
	if expect != nil {
		if a, ok := expect.byKey[t.AlphaKey()]; ok {
			return unitVec(a.index), expect, nil
		}
	} else {
		for _, n := range d.nodes {
			if a, ok := n.byKey[t.AlphaKey()]; ok {
				return unitVec(a.index), n, nil
			}
		}
	}
	if _, ok := t.AsAppliedTerm(); ok {
		for _, n := range d.nodes {
			if expect != nil && n != expect {
				continue
			}
			if a, b, ok := binArgs(t, n.add); ok {
				va, na, err := d.vecOf(a, expect)
				if err != nil {
					return nil, nil, err
				}
				vb, nb, err := d.vecOf(b, mergeNode(expect, na))
				if err != nil {
					return nil, nil, err
				}
				m := mergeNode(na, nb)
				if m == nil {
					return _Vector{}, expect, nil
				}
				return va.add(vb, 1), m, nil
			}
			if a, ok := unArg(t, n.neg); ok {
				va, na, err := d.vecOf(a, expect)
				if err != nil {
					return nil, nil, err
				}
				return va.negate(), mergeNode(expect, na), nil
			}
		}
	}
	// A homomorphism's value at an element of its source.
	for _, im := range d.images(t, expect) {
		h := im.h
		vs, _, err := d.vecOf(im.arg, h.src)
		if err != nil {
			continue
		}
		out := _Vector{}
		for i, c := range vs {
			a := h.dst.atomFor(d.apply(h, h.src.atoms[i].term))
			out[a.index] = new(big.Int).Set(c)
		}
		return out, h.dst, nil
	}
	// A generator with a resident membership.
	if m, ok := d.members[t.AlphaKey()]; ok && (expect == nil || m.node == expect) {
		return unitVec(m.node.atomFor(t).index), m.node, nil
	}
	// A scalar multiple with its scalar in the ring: an atom.
	for _, n := range d.nodes {
		if expect != nil && n != expect {
			continue
		}
		if c, u, ok := binArgs(t, n.smul); ok {
			if _, scalar := d.ringMembers[scalarKey(c, n.ring)]; scalar {
				if _, _, err := d.vecOf(u, n); err == nil {
					return unitVec(n.atomFor(t).index), n, nil
				}
			}
		}
	}
	where := "any module"
	if expect != nil {
		where = ext.PrintTerm(expect.set)
	}
	return nil, nil, fmt.Errorf("the element %s has no membership in %s among the premises", ext.PrintTerm(t), where)
}

func mergeNode(a, b *_Node) *_Node {
	if a == nil {
		return b
	}
	return a
}

// apply is the atom term f(t), beta-normalized when f is a lambda.
func (d *_Diagram) apply(h *_Hom, t core.Term) core.Term {
	app := ext.Apply(h.fn, t)
	if _, isAbs := h.fn.AsAbsTerm(); isAbs {
		return prop.Rhs(prop.RewriteOrRefl(prop.DeepBeta, app))
	}
	return app
}

// addRelation records the equation l = r as a relation at its node.
// A side that is no element of any module yet — a term with no
// membership, the node's operations not forming it — while the other
// side is an element of M, is an element of M by the equation
// (adoptByEquation): `z = p(w)` with p(w) ∈ B gives z ∈ B.
func (d *_Diagram) addRelation(l, r core.Term, proof *prop.PropWrapper) error {
	if !core.Eq(l, r).AlphaEquals(proof.Conclusion()) {
		panic("chase: a relation certificate does not state its recorded equation")
	}
	vl, nl, err := d.vecOf(l, nil)
	if err != nil {
		if d.aliasZero(l, r, proof) {
			return nil
		}
		if _, nr, errR := d.vecOf(r, nil); errR == nil && nr != nil && d.adoptByEquation(l, r, nr, proof) {
			vl, nl, err = d.vecOf(l, nr)
		}
		if err != nil {
			return err
		}
	}
	vr, nr, err := d.vecOf(r, nl)
	if err != nil {
		if vl.isZero() && d.aliasZero(r, l, proof.EqSym()) {
			return nil
		}
		if nl != nil && d.adoptByEquation(r, l, nl, proof.EqSym()) {
			vr, nr, err = d.vecOf(r, nl)
		}
		if err != nil {
			return err
		}
	}
	n := mergeNode(nl, nr)
	if n == nil {
		return nil // zero = zero at no node: nothing to record
	}
	v := vl.add(vr, -1)
	for _, rel := range n.relations {
		if rel.l.AlphaEquals(l) && rel.r.AlphaEquals(r) {
			return nil
		}
	}
	n.relations = append(n.relations, &_Relation{v: v, l: l, r: r, proof: proof})
	return nil
}

// aliasZero records Γ ⊢ t = z, z the zero of some module of the
// diagram and t a variable or a constant with no membership, as a zero
// alias: t is then read as that zero wherever a module with that zero
// is meant (every module of one type shares its zero, so t gains no
// module of its own). An application is no alias — a map's image
// `dd(n)(u) = zero'` is a relation once the map is read, and the
// relation is what the maps carry onward — and neither is a term with a
// membership or a right side that is no module's zero.
func (d *_Diagram) aliasZero(t, z core.Term, eq *prop.PropWrapper) bool {
	if _, isApp := t.AsAppliedTerm(); isApp {
		return false
	}
	if _, has := d.members[t.AlphaKey()]; has {
		return false
	}
	if _, has := d.zeroAliases[t.AlphaKey()]; has {
		return true
	}
	for _, n := range d.nodes {
		if !n.zero.AlphaEquals(z) || !t.Type().Equals(n.elem) {
			continue
		}
		if d.isFormed(t, n) || n.zero.AlphaEquals(t) {
			return false
		}
		d.zeroAliases[t.AlphaKey()] = _ZeroAlias{zero: z, proof: eq}
		return true
	}
	return false
}

// adoptByEquation makes t an element of n from Γ ⊢ t = u with u an
// element of n: Γ ⊢ t ∈ n by the equation's congruence under `· ∈ n`.
// It declines for a term of another type, one with a membership
// already, and one the node's operations form (a sum, a negation, the
// zero), whose parts are what lacks the membership.
func (d *_Diagram) adoptByEquation(t, u core.Term, n *_Node, eq *prop.PropWrapper) bool {
	if !t.Type().Equals(n.elem) {
		return false
	}
	if _, has := d.members[t.AlphaKey()]; has {
		return false
	}
	if n.zero.AlphaEquals(t) || d.isFormed(t, n) {
		return false
	}
	uIn, err := d.member(u, n)
	if err != nil {
		return false
	}
	memberAt := d.memberConst(t, n.set)              // `∈`, at t's type and the set's
	cong := eq.LeftApply(memberAt).RightApply(n.set) // (t ∈ n) = (u ∈ n)
	d.members[t.AlphaKey()] = _Membership{node: n, proof: cong.EqSym().EqMP(uIn)}
	if _, exists := n.byKey[t.AlphaKey()]; !exists {
		a := n.atomFor(t)
		if _, application := t.AsAppliedTerm(); application && d.readingSchema {
			a.schemaGenerated = true
		}
	}
	return true
}

// ── reporting helpers ───────────────────────────────────────────────────────

func (d *_Diagram) describe() string {
	var b strings.Builder
	fmt.Fprintf(&b, "modules: %d, homomorphisms: %d, exactness: %d, onto: %d, one-to-one: %d, equation schemas: %d, submodules: %d\n",
		len(d.nodes), len(d.homs), len(d.exact), len(d.surjections), len(d.injections), len(d.schemas), len(d.submodules))
	for _, n := range d.nodes {
		fmt.Fprintf(&b, "  %s: %d element(s), %d relation(s)\n", ext.PrintTerm(n.set), len(n.atoms), len(n.relations))
	}
	for _, h := range d.homs {
		fmt.Fprintf(&b, "  %s: %s → %s\n", ext.PrintTerm(h.fn), ext.PrintTerm(h.src.set), ext.PrintTerm(h.dst.set))
	}
	instances := 0
	var unread []string
	for _, f := range d.pending {
		if f.instance {
			instances++
			continue
		}
		unread = append(unread, f.from+": "+ext.PrintTerm(f.term)+" — "+f.why)
	}
	if instances > 0 {
		fmt.Fprintf(&b, "  (%d instance(s) of facts over degrees, at degrees the step does not touch, not read)\n", instances)
	}
	if len(unread) > 0 {
		b.WriteString("hypotheses not read:\n")
		for _, u := range unread {
			b.WriteString("  " + u + "\n")
		}
	}
	for _, note := range d.notes {
		b.WriteString("  note: " + note + "\n")
	}
	return b.String()
}
