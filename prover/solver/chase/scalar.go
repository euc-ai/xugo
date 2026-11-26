package chase

// scalar.go — the scalar ring of a module: the commutative ring that
// module_on supplies, read through the chapters' module action laws. A
// scalar expression is an integer polynomial in the ring elements the
// leaf names (sums, differences, negations and products normalize;
// anything else is a scalar atom with a required membership). A scaled
// atom carries its monomial and its base atom apart, so a product of
// scalars never enlarges the generator universe by all ring elements,
// and a homomorphism carries the monomial through HomSmul.

import (
	"fmt"
	"math/big"
	"sort"
	"strconv"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/omega"
)

// _ScalarRing is one scalar ring of the diagram, shared by the modules
// over it: the canonical comm_ring_on fact and its record's seven fields
// (add, zero, neg, mul, one, sub, carrier), the scalar variables in the
// order the diagram met them, the scalar equations the premises state,
// and the explicit ring normalizer bound to the scalar memberships read
// so far.
type _ScalarRing struct {
	d             *_Diagram
	fact          *prop.PropWrapper
	ops           []core.Term
	vars          []core.Term
	byKey         map[core.TermKey]int
	equations     []*prop.PropWrapper
	bound         *omega.StructureRingContext
	memberVersion int
}

// _ScalarNormalForm is a cached normalization: Γ ⊢ t = list(c), and c.
type _ScalarNormalForm struct {
	proof *prop.PropWrapper
	list  []_Signed
}

// installScalarNode binds a new node to its scalar ring (one ring per
// comm_ring_on fact) and reads the module action laws at the node. With
// no scalar table installed the node keeps the additive-only reading.
func (d *_Diagram) installScalarNode(n *_Node, args []core.Term, module *prop.PropWrapper) error {
	l := d.laws.Scalars
	if l.RingOn == nil {
		return nil
	}
	ring := d.canonicalAt(l.RingOn, args, module)
	subjects, ok := headNamed(ring.Conclusion(), "comm_ring_on", 1)
	if !ok {
		panic("chase: RingOn did not give a commutative ring at a record")
	}
	r := subjects[0]
	table := &l.Ring
	var set core.Term
	ops := make([]core.Term, 7) // add, zero, neg, mul, one, sub, carrier
	for _, part := range []struct {
		at    int
		law   *prop.PropWrapper
		arity int
	}{{1, table.ZeroIn, 0}, {4, table.OneIn, 0}, {0, table.AddIn, 2}, {2, table.NegIn, 1}, {3, table.MulIn, 2}, {5, table.SubIn, 2}} {
		op, carrier, err := d.closureComponent(part.law, r, ring, part.arity)
		if err != nil {
			return err
		}
		ops[part.at] = op
		if part.at == 1 {
			set = carrier
		}
	}
	ops[6] = set
	for _, r := range d.scalarRings {
		if r.fact.Conclusion().AlphaEquals(ring.Conclusion()) {
			n.scalar = r
			break
		}
	}
	if n.scalar == nil {
		n.scalar = &_ScalarRing{d: d, fact: ring, ops: ops, byKey: map[core.TermKey]int{}}
		d.scalarRings = append(d.scalarRings, n.scalar)
	}
	n.scalarLaws = map[string]*prop.PropWrapper{}
	for name, law := range map[string]*prop.PropWrapper{"addLeft": l.SmulAddLeft, "addRight": l.SmulAddRight, "mul": l.SmulMul, "one": l.SmulOne, "zero": l.ZeroSmul, "smulZero": l.SmulZero} {
		if law == nil {
			panic("chase: missing scalar law " + name)
		}
		n.scalarLaws[name] = d.canonicalAt(law, args, module)
	}
	return nil
}

// context is the ring normalizer bound to the scalar memberships read
// so far, rebound when a membership arrives.
func (r *_ScalarRing) context() *omega.StructureRingContext {
	if r.bound != nil && r.memberVersion == len(r.d.ringMembers) {
		return r.bound
	}
	keys := make([]string, 0, len(r.d.ringMembers))
	for k := range r.d.ringMembers {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	var members []*prop.PropWrapper
	for _, k := range keys {
		w := r.d.ringMembers[k]
		_, s, ok := r.d.matchMembership(w.Conclusion())
		if ok && s.AlphaEquals(r.ops[6]) {
			members = append(members, w)
		}
	}
	c := omega.BindStructureRing(&r.d.laws.Scalars.Ring, r.d.libraryRead(), r.fact, members...)
	if c == nil {
		panic("chase: the explicit ring normalizer is not installed")
	}
	if r.bound != nil && r.bound.FoldedLiterals() {
		r.d.natArith = true
	}
	r.bound, r.memberVersion = c, len(r.d.ringMembers)
	return c
}

// usedNatArith reports whether the chase has used nat arithmetic: a
// degree rewritten into its nat ring normal form, or numeral literals a
// scalar ring folded.
func (d *_Diagram) usedNatArith() bool {
	if d.natArith {
		return true
	}
	for _, r := range d.scalarRings {
		if r.bound != nil && r.bound.FoldedLiterals() {
			return true
		}
	}
	return false
}

// member is Γ ⊢ t ∈ R.carrier, from the memberships read and the
// ring's closure laws; false for a term of another type or one with an
// atom of no membership.
func (r *_ScalarRing) member(t core.Term) (*prop.PropWrapper, bool) {
	if !t.Type().Equals(r.ops[1].Type()) {
		return nil, false
	}
	return r.context().Member(t)
}

// identity is Γ ⊢ a = b by the ring normalizer. The callers spell one
// polynomial two ways, so a refusal is an engine fault.
func (r *_ScalarRing) identity(a, b core.Term) *prop.PropWrapper {
	w, ok := r.context().Identity(a, b)
	if !ok {
		panic(fmt.Sprintf("chase: scalar normalizer certificate disagrees: %s = %s", ext.PrintTerm(a), ext.PrintTerm(b)))
	}
	return w
}

// variable is the monomial of the scalar atom t, numbered at first
// sight.
func (r *_ScalarRing) variable(t core.Term) _Monomial {
	k := t.AlphaKey()
	i, ok := r.byKey[k]
	if !ok {
		i = len(r.vars)
		r.byKey[k] = i
		r.vars = append(r.vars, t)
	}
	return monomialVariable(i)
}

// poly is t as an integer polynomial in the scalar atoms: zero, one,
// sums, differences, negations and products are read, and anything
// else is an atom.
func (r *_ScalarRing) poly(t core.Term) _PolynomialVector {
	if t.AlphaEquals(r.ops[1]) {
		return _PolynomialVector{}
	}
	if t.AlphaEquals(r.ops[4]) {
		return polynomialUnit(0)
	}
	if a, b, ok := binArgs(t, r.ops[0]); ok {
		return r.poly(a).add(r.poly(b), "", big.NewInt(1))
	}
	if a, b, ok := binArgs(t, r.ops[5]); ok {
		return r.poly(a).add(r.poly(b), "", big.NewInt(-1))
	}
	if a, ok := unArg(t, r.ops[2]); ok {
		return r.poly(a).scale("", big.NewInt(-1))
	}
	if a, b, ok := binArgs(t, r.ops[3]); ok {
		out := _PolynomialVector{}
		pa, pb := r.poly(a), r.poly(b)
		for _, m := range pa.terms() {
			out = out.add(pb, m.mono, pa[m])
			if len(out) > polynomialTermCap {
				panic(_PolynomialLimit{"scalar expansion exceeds 4096 terms"})
			}
		}
		return out
	}
	return _PolynomialVector{_PolynomialTerm{mono: r.variable(t)}: big.NewInt(1)}
}

// monoTerm spells a monomial as the right-nested product of its
// variables, R.one for the empty monomial.
func (r *_ScalarRing) monoTerm(m _Monomial) core.Term {
	if len(m) == 0 {
		return r.ops[4]
	}
	i, err := strconv.ParseUint(string(m[:8]), 16, 32)
	if err != nil {
		panic(err)
	}
	t := r.vars[int(i)]
	if len(m) > 8 {
		t = ext.Apply(r.ops[3], t, r.monoTerm(m[8:]))
	}
	return t
}

// term spells a polynomial as the right-nested sum of its monomials in
// decreasing order, each |c| times and negated when c is negative;
// R.zero for the zero polynomial. The canonical spelling scaleList
// reads.
func (r *_ScalarRing) term(p _PolynomialVector) core.Term {
	var terms []core.Term
	for _, m := range p.terms() {
		c := p[m]
		count := new(big.Int).Abs(c)
		if !count.IsInt64() || count.Int64() > coefficientCap {
			panic(_PolynomialLimit{"scalar coefficient exceeds the certificate cap"})
		}
		t := r.monoTerm(m.mono)
		if c.Sign() < 0 {
			t = ext.Apply(r.ops[2], t)
		}
		for j := int64(0); j < count.Int64(); j++ {
			terms = append(terms, t)
		}
	}
	if len(terms) == 0 {
		return r.ops[1]
	}
	out := terms[len(terms)-1]
	for i := len(terms) - 2; i >= 0; i-- {
		out = ext.Apply(r.ops[0], terms[i], out)
	}
	return out
}

// scaledAtom is the atom m • base at the node, m merged into base's own
// monomial when base is scaled already; base itself for the empty
// monomial.
func (n *_Node) scaledAtom(base *_Atom, m _Monomial) *_Atom {
	if m == "" {
		return base
	}
	if base.scalarBase != nil {
		m = monomialProduct(m, base.scalarMono)
		base = base.scalarBase
	}
	a := n.atomFor(ext.Apply(n.smul, n.scalar.monoTerm(m), base.term))
	a.scalarBase, a.scalarMono = base, m
	a.schemaGenerated = base.schemaGenerated
	return a
}

// scalarDischarge discharges a scalar law's membership guard at the
// node; the decision has established the memberships.
func (d *_Diagram) scalarDischarge(w *prop.PropWrapper, n *_Node) *prop.PropWrapper {
	out, err := d.discharge(w, n)
	if err != nil {
		panic("chase: scalar law guard: " + err.Error())
	}
	return out
}

// scalarLaw reads the node's module action law name at args, its guard
// discharged.
func (d *_Diagram) scalarLaw(n *_Node, name string, args ...core.Term) *prop.PropWrapper {
	return d.scalarDischarge(n.scalarLaws[name].ConclForAllInsts(args...), n)
}

// negScalar is Γ ⊢ (−c) • x = −(c • x): (−c) • x + c • x = (−c + c) • x
// = 0 • x = 0, and the element that adds to c • x to give zero is its
// inverse.
func (d *_Diagram) negScalar(n *_Node, c, x core.Term) *prop.PropWrapper {
	r := n.scalar
	nc := ext.Apply(r.ops[2], c)
	a, b := ext.Apply(n.smul, nc, x), ext.Apply(n.smul, c, x)
	sum := d.scalarLaw(n, "addRight", nc, c, x).EqSym()
	scalarZero := r.identity(ext.Apply(r.ops[0], nc, c), r.ops[1])
	sum = sum.EqTrans(scalarZero.LeftApply(n.smul).RightApply(x)).EqTrans(d.scalarLaw(n, "zero", x))
	return n.mustGuarded(d, d.laws.InvUnique, a, b).EqMP(sum)
}

// negVector is Γ ⊢ c • (−x) = −(c • x): c • (−x) + c • x = c • (−x + x)
// = c • 0 = 0, and the element that adds to c • x to give zero is its
// inverse.
func (d *_Diagram) negVector(n *_Node, c, x core.Term) *prop.PropWrapper {
	nx := ext.Apply(n.neg, x)
	a, b := ext.Apply(n.smul, c, nx), ext.Apply(n.smul, c, x)
	sum := d.scalarLaw(n, "addLeft", c, nx, x).EqSym()
	sum = sum.EqTrans(n.mustGuarded(d, d.laws.LeftInverse, x).LeftApply(ext.Apply(n.smul, c))).EqTrans(d.scalarLaw(n, "smulZero", c))
	return n.mustGuarded(d, d.laws.InvUnique, a, b).EqMP(sum)
}

// scaleList is Γ ⊢ c • list(x) = list(x') with c a canonical scalar
// spelling (term) and x canonical: zero and one by their laws, a sum of
// scalars and a negated scalar distributed (SmulAddRight, negScalar),
// a sum of vectors and a negated vector distributed (SmulAddLeft,
// negVector), and a monomial on one atom the scaled atom, through
// SmulMul when the atom is scaled already.
func (d *_Diagram) scaleList(n *_Node, c core.Term, x []_Signed) (*prop.PropWrapper, []_Signed) {
	r := n.scalar
	xt := n.list(x)
	if c.AlphaEquals(r.ops[1]) {
		return d.scalarLaw(n, "zero", xt), nil
	}
	if c.AlphaEquals(r.ops[4]) {
		return d.scalarLaw(n, "one", xt), x
	}
	if a, b, ok := binArgs(c, r.ops[0]); ok {
		ea, ca := d.scaleList(n, a, x)
		eb, cb := d.scaleList(n, b, x)
		w := d.scalarLaw(n, "addRight", a, b, xt).EqTrans(ea.LeftApply(n.add).Apply(eb))
		merge, out := d.merge(n, ca, cb)
		return w.EqTrans(merge), out
	}
	if a, ok := unArg(c, r.ops[2]); ok {
		ea, ca := d.scaleList(n, a, x)
		ng, out := d.negList(n, ca)
		return d.negScalar(n, a, xt).EqTrans(ea.LeftApply(n.neg)).EqTrans(ng), out
	}
	if len(x) == 0 {
		return d.scalarLaw(n, "smulZero", c), nil
	}
	if len(x) > 1 {
		first, rest := x[:1], x[1:]
		ea, ca := d.scaleList(n, c, first)
		eb, cb := d.scaleList(n, c, rest)
		w := d.scalarLaw(n, "addLeft", c, n.list(first), n.list(rest)).EqTrans(ea.LeftApply(n.add).Apply(eb))
		merge, out := d.merge(n, ca, cb)
		return w.EqTrans(merge), out
	}
	a := x[0]
	if a.neg {
		ea, ca := d.scaleList(n, c, []_Signed{{atom: a.atom}})
		ng, out := d.negList(n, ca)
		return d.negVector(n, c, a.atom.term).EqTrans(ea.LeftApply(n.neg)).EqTrans(ng), out
	}
	base := a.atom
	mono := r.poly(c)
	if len(mono) != 1 {
		panic("chase: a canonical monomial was not a monomial")
	}
	m, k := mono.lead()
	if k.Cmp(big.NewInt(1)) != 0 {
		panic("chase: canonical monomial coefficient is not one")
	}
	var w *prop.PropWrapper
	if base.scalarBase != nil {
		old := r.monoTerm(base.scalarMono)
		w = d.scalarLaw(n, "mul", c, old, base.scalarBase.term).EqSym()
		combined := r.monoTerm(monomialProduct(m.mono, base.scalarMono))
		w = w.EqTrans(r.identity(ext.Apply(r.ops[3], c, old), combined).LeftApply(n.smul).RightApply(base.scalarBase.term))
	} else {
		w = prop.Refl(ext.Apply(n.smul, c, base.term))
	}
	out := n.scaledAtom(base, m.mono)
	return w, []_Signed{{atom: out}}
}

// scalarNormalize is Γ ⊢ t = list(c) at a scalar node, cached by node
// and term. A term with a beta redex is normalized through its reduct,
// unless it is a named homomorphism's application, which pushHom reads
// (a lambda's body through its beta bridge); the atoms a
// schema-generated term's reduct introduces inherit its provenance.
func (d *_Diagram) scalarNormalize(t core.Term, n *_Node) (*prop.PropWrapper, []_Signed, error) {
	if !t.Type().Equals(n.elem) {
		return nil, nil, fmt.Errorf("the element %s has the wrong type for %s", ext.PrintTerm(t), ext.PrintTerm(n.set))
	}
	key := fmt.Sprintf("%d|%s", n.index, t.AlphaKey())
	if cached, ok := d.scalarCache[key]; ok {
		return cached.proof, cached.list, nil
	}
	var w *prop.PropWrapper
	var c []_Signed
	var err error
	directHom := false
	if app, ok := t.AsAppliedTerm(); ok {
		for _, h := range d.homsNamed(app.Fun()) {
			directHom = directHom || h.dst == n
		}
	}
	if beta := prop.DeepBeta(t); beta != nil && !directHom {
		d.rememberBetaImages(t)
		if member, e := d.member(t, n); e == nil {
			image := prop.Rhs(beta)
			bridge := beta.LeftApply(d.memberConst(t, n.set)).RightApply(n.set)
			d.memberCache[fmt.Sprintf("%d|%s", n.index, image.AlphaKey())] = bridge.EqMP(member)
		}
		first := len(n.atoms)
		w, c, err = d.scalarNormalize(prop.Rhs(beta), n)
		if source := n.byKey[t.AlphaKey()]; source != nil && source.schemaGenerated {
			for _, image := range n.atoms[first:] {
				image.schemaGenerated = true
			}
		}
		if err == nil {
			w = beta.EqTrans(w)
		}
	} else {
		w, c, err = d.scalarNormalizeUncached(t, n)
	}
	if err == nil {
		if d.scalarCache == nil {
			d.scalarCache = map[string]_ScalarNormalForm{}
		}
		d.scalarCache[key] = _ScalarNormalForm{w, c}
	}
	return w, c, err
}

// scalarNormalizeUncached follows t's shape: the zero and its aliases,
// a sum and a negation of the node's operations, a scalar multiple
// (the scalar's membership required, its canonical spelling by the
// ring normalizer, then scaleList), a named homomorphism's application
// (its argument normalized at the source, then pushHom), and otherwise
// an atom with a resident membership.
func (d *_Diagram) scalarNormalizeUncached(t core.Term, n *_Node) (*prop.PropWrapper, []_Signed, error) {
	if n.zero.AlphaEquals(t) {
		return prop.Refl(t), nil, nil
	}
	if al, ok := d.zeroAliases[t.AlphaKey()]; ok && n.zero.AlphaEquals(al.zero) {
		return al.proof, nil, nil
	}
	if a, b, ok := binArgs(t, n.add); ok {
		ea, ca, err := d.scalarNormalize(a, n)
		if err != nil {
			return nil, nil, err
		}
		eb, cb, err := d.scalarNormalize(b, n)
		if err != nil {
			return nil, nil, err
		}
		merge, out := d.merge(n, ca, cb)
		return ea.LeftApply(n.add).Apply(eb).EqTrans(merge), out, nil
	}
	if a, ok := unArg(t, n.neg); ok {
		ea, ca, err := d.scalarNormalize(a, n)
		if err != nil {
			return nil, nil, err
		}
		ng, out := d.negList(n, ca)
		return ea.LeftApply(n.neg).EqTrans(ng), out, nil
	}
	if c, x, ok := binArgs(t, n.smul); ok {
		if _, ok := n.scalar.member(c); !ok {
			return nil, nil, fmt.Errorf("the scalar %s has no membership in the ring %s among the premises", ext.PrintTerm(c), ext.PrintTerm(n.ring))
		}
		ex, cx, err := d.scalarNormalize(x, n)
		if err != nil {
			return nil, nil, err
		}
		ct := n.scalar.term(n.scalar.poly(c))
		ec := n.scalar.identity(c, ct)
		scale, out := d.scaleList(n, ct, cx)
		return ec.LeftApply(n.smul).Apply(ex).EqTrans(scale), out, nil
	}
	// A value read against a λ's body is, at an atom of the source, the
	// atom pushHom makes of it: pushHom normalizes that value here, and
	// the reading entered a second time for one term yields to the atom.
	busy := fmt.Sprintf("%d|%s", n.index, t.AlphaKey())
	for _, im := range d.images(t, n) {
		if im.eq != nil && d.valueBusy[busy] {
			continue
		}
		ex, cx, err := d.scalarNormalize(im.arg, im.h.src)
		if err != nil {
			continue
		}
		if d.valueBusy == nil {
			d.valueBusy = map[string]bool{}
		}
		entered := im.eq != nil && !d.valueBusy[busy]
		if entered {
			d.valueBusy[busy] = true
		}
		push, out := d.pushHom(im.h, cx)
		if entered {
			delete(d.valueBusy, busy)
		}
		return im.of(ex.LeftApply(im.h.fn).EqTrans(push)), out, nil
	}
	if _, err := d.member(t, n); err != nil {
		return nil, nil, err
	}
	a := n.atomFor(t)
	return prop.Refl(t), []_Signed{{atom: a}}, nil
}

// scalarVec is vecOf at a scalar node: the atom coefficients of t's
// normal form.
func (d *_Diagram) scalarVec(t core.Term, n *_Node) (_Vector, *_Node, error) {
	_, c, err := d.scalarNormalize(t, n)
	if err != nil {
		return nil, nil, err
	}
	v := _Vector{}
	for _, x := range c {
		sign := int64(1)
		if x.neg {
			sign = -1
		}
		v = v.add(unitVec(x.atom.index), sign)
	}
	return v, n, nil
}

// scalarSchemaIndependent reports whether no scalar in t depends on the
// schema's module binder v, under every application and lambda. Such a
// schema is R-linear: instantiated at the base atoms only, its scalar
// multiples follow from the polynomial relation closure, with no
// instance at a • x, a² • x, … in turn.
func (d *_Diagram) scalarSchemaIndependent(t core.Term, v core.VarTerm) bool {
	for _, n := range d.nodes {
		if c, _, ok := binArgs(t, n.smul); ok && c.HasFree(v) {
			return false
		}
	}
	if a, ok := t.AsAppliedTerm(); ok {
		return d.scalarSchemaIndependent(a.Fun(), v) && d.scalarSchemaIndependent(a.Arg(), v)
	}
	if abs, ok := t.AsAbsTerm(); ok {
		return d.scalarSchemaIndependent(abs.Body(), v)
	}
	return true
}

// equation is Γ ⊢ l = right between scalars of the ring: a ring
// identity, or l − right an integer polynomial combination of the
// scalar equations the premises state, each multiple q·(a − b) zero by
// q·0 = 0, the multiples summed to zero, and l = (l − right) + right =
// 0 + right.
func (r *_ScalarRing) equation(l, right core.Term) (*prop.PropWrapper, bool) {
	if _, ok := r.member(l); !ok {
		return nil, false
	}
	if _, ok := r.member(right); !ok {
		return nil, false
	}
	if w, ok := r.context().Identity(l, right); ok {
		return w, true
	}
	var rows []_PolynomialVector
	for _, e := range r.equations {
		a, b, _ := core.MatchesEQ(e.Conclusion())
		rows = append(rows, r.poly(a).add(r.poly(b), "", big.NewInt(-1)))
	}
	target := r.poly(l).add(r.poly(right), "", big.NewInt(-1))
	coeffs, ok := buildPolynomialBasis(rows).express(target)
	if !ok {
		return nil, false
	}
	add := func(a, b core.Term) core.Term { return ext.Apply(r.ops[0], a, b) }
	mul := func(a, b core.Term) core.Term { return ext.Apply(r.ops[3], a, b) }
	neg := func(a core.Term) core.Term { return ext.Apply(r.ops[2], a) }
	sum := r.ops[1]
	zero := prop.Refl(sum)
	for _, t := range coeffs.terms() {
		q := r.term(_PolynomialVector{_PolynomialTerm{mono: t.mono}: coeffs[t]})
		e := r.equations[t.pos]
		a, b, _ := core.MatchesEQ(e.Conclusion())
		delta := add(a, neg(b))
		deltaZero := e.LeftApply(r.ops[0]).RightApply(neg(b)).EqTrans(r.identity(add(b, neg(b)), r.ops[1]))
		product := mul(q, delta)
		productZero := deltaZero.LeftApply(ext.Apply(r.ops[3], q)).EqTrans(r.identity(mul(q, r.ops[1]), r.ops[1]))
		zero = zero.LeftApply(r.ops[0]).Apply(productZero).EqTrans(r.identity(add(r.ops[1], r.ops[1]), r.ops[1]))
		sum = add(sum, product)
	}
	diff := add(l, neg(right))
	diffZero := r.identity(diff, sum).EqTrans(zero)
	w := r.identity(l, add(diff, right)).EqTrans(diffZero.LeftApply(r.ops[0]).RightApply(right)).EqTrans(r.identity(add(r.ops[1], right), right))
	return w, true
}

// rememberBetaImage stores Γ ⊢ f(u)' ∈ N for a lambda homomorphism's
// image at its beta spelling f(u)', from the homomorphism's image law
// at the raw application: the spelling is opaque at the target by
// itself. A membership stored at the spelling already stands.
func (d *_Diagram) rememberBetaImage(h *_Hom, u core.Term) {
	raw := ext.Apply(h.fn, u)
	beta := prop.DeepBeta(raw)
	if beta == nil {
		return
	}
	image := prop.Rhs(beta)
	key := fmt.Sprintf("%d|%s", h.dst.index, image.AlphaKey())
	if _, ok := d.memberCache[key]; ok {
		return
	}
	member, err := d.member(u, h.src)
	if err != nil {
		return
	}
	proof := d.homIn(h, u, member)
	bridge := beta.LeftApply(d.memberConst(raw, h.dst.set)).RightApply(h.dst.set)
	d.memberCache[key] = bridge.EqMP(proof)
}

// rememberBetaImages is rememberBetaImage at every named homomorphism's
// application inside t.
func (d *_Diagram) rememberBetaImages(t core.Term) {
	if app, ok := t.AsAppliedTerm(); ok {
		for _, h := range d.homsNamed(app.Fun()) {
			d.rememberBetaImage(h, app.Arg())
		}
		d.rememberBetaImages(app.Fun())
		d.rememberBetaImages(app.Arg())
	}
}

// imageAtom is the atom t at the node, the image of source under a
// homomorphism: a new atom inherits source's schema provenance, so an
// opaque atom a schema introduced seeds no further instance through
// its images either, and an undeclared map cannot feed a named
// homomorphism back into the same schema indefinitely.
func (n *_Node) imageAtom(source *_Atom, t core.Term) *_Atom {
	if a, ok := n.byKey[t.AlphaKey()]; ok {
		return a
	}
	a := n.atomFor(t)
	a.schemaGenerated = source.schemaGenerated
	return a
}
