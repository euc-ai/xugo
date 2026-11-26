package chase

// loop.go — the chase itself. Round 0 reads the leaf, introduces the
// witnesses its hypotheses hold outright (an element of an image, a
// coset equation reduced to a difference in an image) and saturates:
// every homomorphism applied to every element of its source, every
// equation schema instantiated at every element of its node. Each
// further round pulls back: at every exactness im g = ker f, the
// elements of the middle node that f provably sends to zero — a lattice,
// its basis computed — and that are not yet provably in the image of g
// receive a preimage; at every onto map, every element of the target
// not yet in its image receives one; at every one-to-one map, the
// elements it sends to zero are themselves zero. Then it saturates and
// decides again. The number of rounds is the depth the author wrote,
// and a round that introduces nothing ends the chase early.

import (
	"fmt"
	"math/big"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// saturate closes the atom universe under the homomorphisms, carries
// every relation forward through every homomorphism out of its node
// (an additive map respects an equation), and instantiates every
// schema at every atom, to a fixpoint.
func (d *_Diagram) saturate() {
	for changed := true; changed; {
		changed = d.installScalarRelations()
		for _, h := range d.homs {
			for i := 0; i < len(h.src.atoms); i++ {
				a := h.src.atoms[i]
				t := d.apply(h, a.term)
				if h.src.scalar != nil {
					before := d.atomCount()
					d.scalarHomVector(h, a)
					changed = changed || d.atomCount() > before
				} else if _, seen := h.dst.byKey[t.AlphaKey()]; !seen {
					h.dst.imageAtom(a, t)
					changed = true
				}
			}
			for i := 0; i < len(h.src.relations); i++ {
				rel := h.src.relations[i]
				if rel.derived {
					continue
				}
				if rel.pushed == nil {
					rel.pushed = map[*_Hom]bool{}
				}
				if rel.pushed[h] {
					continue
				}
				rel.pushed[h] = true
				before := len(h.dst.relations)
				left := prop.Rhs(prop.RewriteOrRefl(prop.DeepBeta, d.apply(h, rel.l)))
				right := prop.Rhs(prop.RewriteOrRefl(prop.DeepBeta, d.apply(h, rel.r)))
				certificate := rel.proof.LeftApply(h.fn).RewriteConcl(prop.DeepBeta)
				if err := d.addRelation(left, right, certificate); err != nil {
					panic("chase: " + err.Error() + " (engine invariant: the relation's elements are atoms)")
				}
				if len(h.dst.relations) > before {
					changed = true
				}
			}
		}
		for _, ex := range d.exact {
			for i := 0; i < len(ex.g.src.atoms); i++ {
				if ex.done[i] {
					continue
				}
				ex.done[i] = true
				a := ex.g.src.atoms[i]
				eq := d.composeZero(ex, a)
				l, r, _ := core.MatchesEQ(eq.Conclusion())
				if err := d.addRelation(l, r, eq); err != nil {
					panic("chase: " + err.Error() + " (engine invariant: the composite is an atom)")
				}
				changed = true
			}
		}
		for _, s := range d.schemas {
			for i := 0; i < len(s.node.atoms); i++ {
				if s.done[i] {
					continue
				}
				a := s.node.atoms[i]
				if a.scalarBase != nil || a.schemaGenerated {
					s.done[i] = true
					continue
				}
				inst := s.fact.ConclForAllInsts(a.term)
				member := d.mustMember(a.term, s.node)
				eq := inst.DemoteHyp().DeriveHypFrom(member)
				l, r, _ := core.MatchesEQ(eq.Conclusion())
				d.readingSchema = true
				err := d.addRelation(l, r, eq)
				d.readingSchema = false
				if err != nil {
					// An instance naming a map or a module not read yet is
					// retried once the degrees grow.
					continue
				}
				s.done[i] = true
				changed = true
			}
		}
		// Saturation may establish a pending implication's guard. Read
		// it here, independent of whether the diagram has degree facts.
		var pending []_Fact
		for _, f := range d.pending {
			before := len(d.sources)
			if err := d.readFact(f); err != nil {
				f.why = err.Error()
				pending = append(pending, f)
				continue
			}
			changed = true
			for _, source := range d.sources[before:] {
				d.introduce(source)
			}
		}
		d.pending = pending
	}
}

// composeZero is Γ ⊢ f(g(a)) = e at the exactness im g = ker f: g(a) is
// in the image, hence in the kernel.
func (d *_Diagram) composeZero(ex *_Exactness, a *_Atom) *prop.PropWrapper {
	g, f := ex.g, ex.f
	ga := d.apply(g, a.term)
	member := d.mustMember(a.term, g.src)
	inImage := d.at(d.laws.InImage, []core.Term{g.fn, g.src.set}, nil, ga) // ga ∈ image(g, A) ⇔ ∃x. ga = g(x) ∧ x ∈ A
	exists := prop.Rhs(inImage)
	abs := ext.MatchesEXISTS(exists)
	body := abs.Body().Substitute(core.MakeTermSubst(abs.Var(), a.term))
	bodyProof, err := d.proveGuard(body, g.src, func(l, r core.Term) (*prop.PropWrapper, error) {
		left, right := prop.RewriteOrRefl(prop.DeepBeta, l), prop.RewriteOrRefl(prop.DeepBeta, r)
		if prop.Rhs(left).AlphaEquals(prop.Rhs(right)) {
			return left.EqTrans(right.EqSym()), nil
		}
		return nil, fmt.Errorf("the image membership's equation is not beta-reflexive: %s = %s", ext.PrintTerm(l), ext.PrintTerm(r))
	})
	if err != nil {
		panic("chase: " + err.Error() + " (engine invariant)")
	}
	_ = member
	imageMember := inImage.EqSym().EqMP(bodyProof.DeriveTrans(prop.InstExists(exists, a.term)))
	kernelSet := prop.Rhs(ex.setEq)
	memberOf := ext.Apply(d.memberConst(ga, kernelSet), ga)
	inKernel := ex.setEq.LeftApply(memberOf).EqMP(imageMember) // ga ∈ group_kernel(e, B, f)
	both := d.at(d.laws.InKernel, []core.Term{ex.e, g.dst.set, f.fn}, nil, ga).EqMP(inKernel)
	l, r, _ := ext.MatchesAND(both.Conclusion())
	return both.DeriveTrans(prop.HypAND1(l, r))
}

// introduce brings a witness source's element into the diagram: a fresh
// variable w with the ∃-body assumed at it, its membership read off the
// body and the equation t = f(w) recorded.
func (d *_Diagram) introduce(s *_Source) {
	abs := ext.MatchesEXISTS(s.exists.Conclusion())
	if abs.IsZero() {
		panic("chase: a witness source is not an ∃ (engine invariant)")
	}
	d.skolemCount++
	name := core.TermName(fmt.Sprintf("w%d", d.skolemCount))
	taken := func(name core.TermName) bool {
		return d.goal.Conclusion().HasName(name) || d.goal.AnyHyp(func(h core.Term) bool { return h.HasName(name) })
	}
	for taken(name) {
		d.skolemCount++
		name = core.TermName(fmt.Sprintf("w%d", d.skolemCount))
	}
	w := core.Var(name, abs.Var().Type())
	body := abs.Body().Substitute(core.MakeTermSubst(abs.Var(), w))
	assumed := prop.Assume(body)
	d.skolems = append(d.skolems, &_Skolem{v: w, body: body, exists: s.exists})
	// The membership first, whichever conjunct states it: the equation
	// is read with the witness already an element of its module.
	for _, c := range conjuncts(body) {
		if x, set, ok := d.matchMembership(c); ok && x.Equals(w) {
			if n := d.nodeOf(set); n != nil {
				d.members[w.AlphaKey()] = _Membership{node: n, proof: assumed.DeriveTrans(conjunctProof(body, c))}
			}
		}
	}
	if _, ok := d.members[w.AlphaKey()]; !ok {
		panic("chase: a witness's body gives it no membership (engine invariant)")
	}
	s.f.src.atomFor(w)
	for _, c := range conjuncts(body) {
		if l, r, ok := core.MatchesEQ(c); ok {
			if err := d.addRelation(l, r, assumed.DeriveTrans(conjunctProof(body, c))); err != nil {
				panic("chase: " + err.Error() + " (engine invariant: a witness's equation is between atoms)")
			}
		}
	}
}

// pullbacks runs one round: the preimages exactness provides, then
// those the onto maps provide, then the one-to-one eliminations, the
// diagram saturated after each phase so the next reads what the last
// introduced; it reports whether anything was added.
func (d *_Diagram) pullbacks(round int) bool {
	added := false
	for _, ex := range d.exact {
		for _, v := range d.kernelVectors(ex.f) {
			if d.inImage(ex.g, v) {
				continue
			}
			d.introduce(d.exactSource(ex, v))
			d.note(round, "pulled %s back through %s (exactness at %s)", ext.PrintTerm(ex.f.src.list(ex.f.src.canon(v))), ext.PrintTerm(ex.g.fn), ext.PrintTerm(ex.g.dst.set))
			added = true
		}
	}
	d.saturate()
	for _, sj := range d.surjections {
		for i := 0; i < len(sj.p.dst.atoms); i++ {
			a := sj.p.dst.atoms[i]
			if d.inImage(sj.p, unitVec(a.index)) {
				continue
			}
			d.introduce(d.surjectionSource(sj, a))
			d.note(round, "lifted %s through %s (onto %s)", ext.PrintTerm(a.term), ext.PrintTerm(sj.p.fn), ext.PrintTerm(sj.p.dst.set))
			added = true
		}
	}
	d.saturate()
	for _, in := range d.injections {
		for _, v := range d.kernelVectors(in.g) {
			if _, already := in.g.src.inLattice(v); already {
				continue
			}
			d.injectivityRelation(in, v)
			d.note(round, "%s is zero: %s is one-to-one", ext.PrintTerm(in.g.src.list(in.g.src.canon(v))), ext.PrintTerm(in.g.fn))
			added = true
		}
	}
	d.saturate()
	return added
}

func (d *_Diagram) note(round int, format string, args ...any) {
	d.notes = append(d.notes, fmt.Sprintf("round %d: ", round)+fmt.Sprintf(format, args...))
}

// homMatrix is f's action on the source's atoms: row j is the vector
// of f(aⱼ) at the target. The images are made atoms first and the rows
// spelled after, so every row has the target's final width — an image
// made an atom here (a witness introduced this round, not yet
// saturated) widens the target for every row.
func (d *_Diagram) homMatrix(h *_Hom) [][]*big.Int {
	images := make([]*_Atom, len(h.src.atoms))
	for j, a := range h.src.atoms {
		images[j] = h.dst.atomFor(d.apply(h, a.term))
	}
	rows := make([][]*big.Int, len(images))
	for j, img := range images {
		rows[j] = unitVec(img.index).dense(len(h.dst.atoms))
	}
	return rows
}

// kernelVectors is a basis of the elements of f's source that f
// provably sends to zero: the preimage of the target's relation lattice.
func (d *_Diagram) kernelVectors(h *_Hom) []_Vector {
	if h.src.scalar != nil {
		return d.scalarKernel(h)
	}
	src, dst := h.src, h.dst
	if len(src.atoms) == 0 {
		return nil
	}
	basis := preimageLattice(d.homMatrix(h), len(src.atoms), len(dst.atoms), dst.relationRows())
	out := make([]_Vector, 0, len(basis))
	for _, row := range basis {
		v := _Vector{}
		for i, c := range row {
			if c.Sign() != 0 {
				v[i] = new(big.Int).Set(c)
			}
		}
		if !v.isZero() {
			out = append(out, v)
		}
	}
	return out
}

// imageCoefficients finds u at g's source with g(u) − v in the target's
// relations: v = Σ xⱼ g(aⱼ) + Σ yᵢ relᵢ; ok when it exists.
func (d *_Diagram) imageCoefficients(g *_Hom, v _Vector) (u _Vector, ok bool) {
	if g.src.scalar != nil {
		return d.scalarImage(g, v)
	}
	src, dst := g.src, g.dst
	rows := d.homMatrix(g)
	rows = append(rows, dst.relationRows()...)
	if len(rows) == 0 {
		return nil, v.isZero()
	}
	e := buildEchelon(rows, len(dst.atoms))
	coeffs, _, ok := e.express(v.dense(len(dst.atoms)))
	if !ok {
		return nil, false
	}
	u = _Vector{}
	for j := range src.atoms {
		if coeffs[j].Sign() != 0 {
			u[j] = new(big.Int).Set(coeffs[j])
		}
	}
	return u, true
}

func (d *_Diagram) inImage(g *_Hom, v _Vector) bool {
	_, ok := d.imageCoefficients(g, v)
	return ok
}

// exactSource is the ∃-fact for the preimage of v through g at the
// exactness im g = ker f: f(v) = 0 puts v in the kernel, hence in the
// image.
func (d *_Diagram) exactSource(ex *_Exactness, v _Vector) *_Source {
	b := ex.g.dst
	w := b.list(b.canon(v))
	member := d.mustMember(w, b)
	fw := d.apply(ex.f, w)
	killed, err := d.equation(fw, ex.e, ex.f.dst)
	if err != nil {
		panic("chase: " + err.Error() + " (engine invariant: the kernel computation found it)")
	}
	both := prop.ConclAND(member.Conclusion(), killed.Conclusion()).DeriveHypFrom(member).DeriveHypFrom(killed)
	inKernel := d.at(d.laws.InKernel, []core.Term{ex.e, b.set, ex.f.fn}, nil, w).EqSym().EqMP(both) // w ∈ group_kernel(e, B, f)
	// (w ∈ image) = (w ∈ kernel) by congruence of the set equation under `w ∈ ·`.
	kernelSet := prop.Rhs(ex.setEq)
	memberOf := ext.Apply(d.memberConst(w, kernelSet), w) // `∈ w`, awaiting its set
	cong := ex.setEq.LeftApply(memberOf)                  // (w ∈ image(g, A)) = (w ∈ kernel)
	imageMember := cong.EqSym().EqMP(inKernel)
	exists := d.at(d.laws.InImage, []core.Term{ex.g.fn, ex.g.src.set}, nil, w).EqMP(imageMember)
	return &_Source{exists: exists, f: ex.g, t: w, why: "exactness"}
}

// surjectionSource is the ∃-fact for the preimage of the atom a through
// an onto map.
func (d *_Diagram) surjectionSource(sj *_Surjection, a *_Atom) *_Source {
	member := d.mustMember(a.term, sj.p.dst)
	if sj.pointwise != nil {
		exists := sj.pointwise.ConclForAllInsts(a.term).DemoteHyp().DeriveHypFrom(member)
		return &_Source{exists: exists, f: sj.p, t: a.term, why: "onto"}
	}
	memberOf := ext.Apply(d.memberConst(a.term, sj.p.dst.set), a.term)
	cong := sj.setEq.LeftApply(memberOf) // (a ∈ image(p, A)) = (a ∈ B)
	imageMember := cong.EqSym().EqMP(member)
	exists := d.at(d.laws.InImage, []core.Term{sj.p.fn, sj.p.src.set}, nil, a.term).EqMP(imageMember)
	return &_Source{exists: exists, f: sj.p, t: a.term, why: "onto"}
}

// injectivityRelation records v = 0 at g's source from g(v⁺) = g(v⁻) and
// the injectivity of g.
func (d *_Diagram) injectivityRelation(in *_Injection, v _Vector) {
	a := in.g.src
	plus, minus := _Vector{}, _Vector{}
	for i, c := range v {
		if c.Sign() > 0 {
			plus[i] = new(big.Int).Set(c)
		} else {
			minus[i] = new(big.Int).Neg(c)
		}
	}
	wp, wm := a.list(a.canon(plus)), a.list(a.canon(minus))
	inst := in.fact.ConclForAllInsts(wp, wm)
	guard, _, _ := ext.MatchesIMPLY(inst.Conclusion())
	proof, err := d.proveGuard(guard, a, func(l, r core.Term) (*prop.PropWrapper, error) {
		return d.equation(l, r, in.g.dst)
	})
	if err != nil {
		panic("chase: " + err.Error() + " (engine invariant: the kernel computation found it)")
	}
	eq := inst.DemoteHyp().DeriveHypFrom(proof) // Γ ⊢ wp = wm (or wm = wp)
	l, r, _ := core.MatchesEQ(eq.Conclusion())
	if err := d.addRelation(l, r, eq); err != nil {
		panic("chase: " + err.Error() + " (engine invariant: the elements are atoms)")
	}
}

// ── the goal ────────────────────────────────────────────────────────────────

// decide proves the goal's conclusion from the diagram as it stands, or
// says why not.
func (d *_Diagram) decide() (*prop.PropWrapper, error) {
	thm, err := d.prove(d.concl)
	if err != nil {
		return nil, err
	}
	if d.conclEq != nil {
		thm = d.conclEq.EqSym().EqMP(thm) // back to the goal's own spelling
	}
	return thm, nil
}

// prove is Γ ⊢ c for a conclusion of one of the shapes the closer
// decides.
func (d *_Diagram) prove(c core.Term) (*prop.PropWrapper, error) {
	if x, s, ok := d.matchMembership(c); ok {
		return d.proveMembership(x, s)
	}
	if l, r, ok := core.MatchesEQ(c); ok {
		if isSetType(l.Type()) {
			return d.proveCosetEquation(l, r)
		}
		if l.Type().Equals(core.TypeBool()) {
			return nil, fmt.Errorf("the goal is an ⇔, which the chase closer does not decide")
		}
		return d.equation(l, r, nil)
	}
	if abs := ext.MatchesEXISTS(c); !abs.IsZero() {
		return d.proveExists(abs, c)
	}
	return nil, fmt.Errorf("the goal %s has no shape the chase closer decides: an equation between elements, a membership, an element of an image or a kernel, an existential preimage, or a coset equation", ext.PrintTerm(c))
}

func (d *_Diagram) proveMembership(x, s core.Term) (*prop.PropWrapper, error) {
	for _, r := range d.scalarRings {
		if r.ops[6].AlphaEquals(s) {
			if w, ok := r.member(x); ok {
				return w, nil
			}
		}
	}
	if n := d.nodeOf(s); n != nil {
		return d.member(x, n)
	}
	if args, ok := headNamed(s, imageName, imageArity); ok {
		src := d.nodeOf(args[1])
		if src == nil {
			return nil, fmt.Errorf("the image's source %s has no module structure fact", ext.PrintTerm(args[1]))
		}
		h := d.homFrom(args[0], src)
		if h == nil {
			return nil, fmt.Errorf("%s has no module_homomorphism fact out of %s", ext.PrintTerm(args[0]), ext.PrintTerm(args[1]))
		}
		inImage := d.at(d.laws.InImage, []core.Term{args[0], args[1]}, nil, x)
		exists, err := d.provePreimage(h, x, prop.Rhs(inImage))
		if err != nil {
			return nil, err
		}
		return inImage.EqSym().EqMP(exists), nil
	}
	if args, ok := headNamed(s, kernelName, kernelArity); ok {
		b := d.nodeOf(args[1])
		if b == nil {
			return nil, fmt.Errorf("the kernel's module %s has no module structure fact", ext.PrintTerm(args[1]))
		}
		g := d.homFrom(args[2], b)
		if g == nil {
			return nil, fmt.Errorf("%s has no module_homomorphism fact out of %s", ext.PrintTerm(args[2]), ext.PrintTerm(args[1]))
		}
		member, err := d.member(x, b)
		if err != nil {
			return nil, err
		}
		killed, err := d.equation(d.apply(g, x), args[0], g.dst)
		if err != nil {
			return nil, err
		}
		both := prop.ConclAND(member.Conclusion(), killed.Conclusion()).DeriveHypFrom(member).DeriveHypFrom(killed)
		return d.at(d.laws.InKernel, args, nil, x).EqSym().EqMP(both), nil
	}
	return nil, fmt.Errorf("the set %s is no module of the diagram, image or kernel", ext.PrintTerm(s))
}

// provePreimage is Γ ⊢ ∃u. body(u) where body is a conjunction of u ∈ A
// and t = f(u) in some order and orientation: the witness is the
// element of A that f carries to t modulo the target's relations.
func (d *_Diagram) provePreimage(h *_Hom, t core.Term, exists core.Term) (*prop.PropWrapper, error) {
	abs := ext.MatchesEXISTS(exists)
	v, _, err := d.vecOf(t, h.dst)
	if err != nil {
		return nil, err
	}
	u, ok := d.imageCoefficients(h, v)
	if !ok {
		return nil, fmt.Errorf("%s is not in the image of %s: no element of %s the premises name is carried to it", ext.PrintTerm(t), ext.PrintTerm(h.fn), ext.PrintTerm(h.src.set))
	}
	w := h.src.list(h.src.canon(u))
	body := abs.Body().Substitute(core.MakeTermSubst(abs.Var(), w))
	proof, err := d.proveGuard(body, h.src, func(l, r core.Term) (*prop.PropWrapper, error) {
		return d.equation(l, r, h.dst)
	})
	if err != nil {
		return nil, err
	}
	return proof.DeriveTrans(prop.InstExists(exists, w)), nil
}

func (d *_Diagram) proveExists(abs core.AbsTerm, c core.Term) (*prop.PropWrapper, error) {
	// ∃u. u ∈ A ∧ f(u) = t: find the homomorphism and the target element.
	var a *_Node
	var sides [][2]core.Term
	u := abs.Var()
	for _, conj := range conjuncts(abs.Body()) {
		if x, s, ok := d.matchMembership(conj); ok && x.Equals(u) {
			a = d.nodeOf(s)
			continue
		}
		if l, r, ok := core.MatchesEQ(conj); ok {
			sides = append(sides, [2]core.Term{l, r}, [2]core.Term{r, l})
			continue
		}
		return nil, fmt.Errorf("the existential goal's conjunct %s is neither the witness's membership nor its image", ext.PrintTerm(conj))
	}
	if a == nil || len(sides) == 0 {
		return nil, fmt.Errorf("the existential goal %s does not ask for a preimage under a homomorphism", ext.PrintTerm(c))
	}
	// The side that is a map's value at the witness names the map
	// (valuedAt); the other is the element whose preimage is asked.
	for _, side := range sides {
		if h := d.valuedAt(side[0], u, a); h != nil {
			return d.provePreimage(h, side[1], c)
		}
	}
	return nil, fmt.Errorf("the existential goal %s states no value at its witness of a module_homomorphism out of %s", ext.PrintTerm(c), ext.PrintTerm(a.set))
}

// cosetLaw is Γ ⊢ (left_coset(add, x, N) = left_coset(add, y, N)) ⇔
// add(neg x, y) ∈ N, at the module whose addition is add and of which N
// is a submodule by a premise.
func (d *_Diagram) cosetLaw(add, x, y, set core.Term) (*prop.PropWrapper, error) {
	for _, sub := range d.submodules {
		if !sub.n.AlphaEquals(set) || !sub.m.add.AlphaEquals(add) {
			continue
		}
		n := sub.m
		if _, err := d.member(x, n); err != nil {
			return nil, err
		}
		if _, err := d.member(y, n); err != nil {
			return nil, err
		}
		return n.guarded(d, d.laws.LeftCosetEq, x, y, set)
	}
	return nil, fmt.Errorf("no submodule premise names %s inside the module whose addition is %s", ext.PrintTerm(set), ext.PrintTerm(add))
}

func (d *_Diagram) proveCosetEquation(l, r core.Term) (*prop.PropWrapper, error) {
	cl, okl := headNamed(l, leftCosetName, leftCosetArity)
	cr, okr := headNamed(r, leftCosetName, leftCosetArity)
	if !okl || !okr || !cl[0].AlphaEquals(cr[0]) || !cl[2].AlphaEquals(cr[2]) {
		return nil, fmt.Errorf("the goal is an equation between sets that is not two cosets of one subgroup: %s = %s", ext.PrintTerm(l), ext.PrintTerm(r))
	}
	law, err := d.cosetLaw(cl[0], cl[1], cr[1], cl[2])
	if err != nil {
		return nil, err
	}
	x, s, _ := d.matchMembership(prop.Rhs(law))
	member, err := d.proveMembership(x, s)
	if err != nil {
		return nil, err
	}
	return law.EqSym().EqMP(member), nil
}

// ── assembly ────────────────────────────────────────────────────────────────

// finish discharges every witness assumption the proof used, latest
// first, and checks the result closes the goal.
func (d *_Diagram) finish(thm *prop.PropWrapper) *prop.PropWrapper {
	for i := len(d.skolems) - 1; i >= 0; i-- {
		s := d.skolems[i]
		if !thm.HasHyp(s.body) {
			continue
		}
		thm = thm.HypExists(s.v, s.body).DeriveHypFrom(s.exists)
	}
	if !prop.IsStronger(thm, d.goal) {
		var extra []string
		for h := range thm.HypIter() {
			if !d.goal.HasHyp(h) {
				extra = append(extra, ext.PrintTerm(h))
			}
		}
		panic(fmt.Sprintf("chase: the certificate does not close the goal (engine invariant)\n  concluded: %s\n  hypotheses not the goal's: %s",
			ext.PrintTerm(thm.Conclusion()), strings.Join(extra, "; ")))
	}
	return thm
}
