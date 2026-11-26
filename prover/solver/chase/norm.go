package chase

// norm.go — the kernel certificates of the chase: memberships by the
// closure laws and the homomorphisms' image law, the group laws read at
// a node with their guards discharged, the laws a homomorphism's
// additivity yields (f(0) = 0, f(−u) = −f(u)), the normalizer that
// carries an element to its canonical spelling — a right-nested sum of
// signed atoms in a fixed order, inverse pairs cancelled — and the
// ℤ-linear step: an equation that is an integer combination of the
// node's relations, proved by normalizing both the difference of its
// sides and the combination's sum to one spelling.
//
// Every derivation is a composition of law instances and the kernel's
// congruence rules; nothing is searched for, and a shape the code
// cannot derive is an engine fault that panics.

import (
	"fmt"
	"math/big"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// coefficientCap bounds Σ|cᵢ| over an integer combination's
// coefficients: the certificate spells each relation |cᵢ| times.
const coefficientCap = 64

// _Signed is one summand of a canonical spelling: an atom or its
// negation.
type _Signed struct {
	atom *_Atom
	neg  bool
}

func (s _Signed) term() core.Term {
	if s.neg {
		return ext.Apply(s.atom.node.neg, s.atom.term)
	}
	return s.atom.term
}

// before orders signed atoms: by atom, the atom before its negation.
func (s _Signed) before(t _Signed) bool {
	if s.atom.index != t.atom.index {
		return s.atom.index < t.atom.index
	}
	return !s.neg && t.neg
}

func (s _Signed) cancels(t _Signed) bool { return s.atom == t.atom && s.neg != t.neg }

// list spells a canonical list as a term: zero when empty, otherwise a
// right-nested sum.
func (n *_Node) list(c []_Signed) core.Term {
	if len(c) == 0 {
		return n.zero
	}
	t := c[len(c)-1].term()
	for i := len(c) - 2; i >= 0; i-- {
		t = ext.Apply(n.add, c[i].term(), t)
	}
	return t
}

// canon is the canonical list of a vector: atoms by index, each
// |coefficient| times, negated when the coefficient is negative.
func (n *_Node) canon(v _Vector) []_Signed {
	var out []_Signed
	for _, a := range n.atomsOf(v) {
		c := v[a.index]
		count := new(big.Int).Abs(c)
		if !count.IsInt64() || count.Int64() > coefficientCap {
			if n.scalar != nil {
				panic(_PolynomialLimit{"module coefficient exceeds the certificate cap"})
			}
			panic(fmt.Sprintf("chase: a coefficient of %s exceeds the certificate's cap of %d", ext.PrintTerm(a.term), coefficientCap))
		}
		for i := int64(0); i < count.Int64(); i++ {
			out = append(out, _Signed{atom: a, neg: c.Sign() < 0})
		}
	}
	return out
}

func sameList(a, b []_Signed) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

// ── memberships ─────────────────────────────────────────────────────────────

// member is Γ ⊢ t ∈ n: a resident fact, a witness's own, or the closure
// laws and the homomorphisms' image law at the parts.
func (d *_Diagram) member(t core.Term, n *_Node) (*prop.PropWrapper, error) {
	key := fmt.Sprintf("%d|%s", n.index, t.AlphaKey())
	if w, ok := d.memberCache[key]; ok {
		return w, nil
	}
	w, err := d.memberUncached(t, n)
	if err != nil {
		return nil, err
	}
	d.memberCache[key] = w
	return w, nil
}

func (d *_Diagram) memberUncached(t core.Term, n *_Node) (*prop.PropWrapper, error) {
	if m, ok := d.members[t.AlphaKey()]; ok && m.node == n {
		return m.proof, nil
	}
	if al, ok := d.zeroAliases[t.AlphaKey()]; ok && n.zero.AlphaEquals(al.zero) {
		// t = zero and zero ∈ n
		cong := al.proof.LeftApply(d.memberConst(t, n.set)).RightApply(n.set) // (t ∈ n) = (zero ∈ n)
		return cong.EqSym().EqMP(n.at(d, d.laws.OneIn)), nil
	}
	if n.zero.AlphaEquals(t) {
		return n.at(d, d.laws.OneIn), nil
	}
	if a, b, ok := binArgs(t, n.add); ok {
		return n.guarded(d, d.laws.MulIn, a, b)
	}
	if a, ok := unArg(t, n.neg); ok {
		return n.guarded(d, d.laws.InvIn, a)
	}
	if c, x, ok := binArgs(t, n.smul); ok {
		scalar, ok := d.ringMembers[scalarKey(c, n.ring)]
		if n.scalar != nil {
			scalar, ok = n.scalar.member(c)
		}
		if !ok {
			return nil, fmt.Errorf("the scalar %s has no membership in the ring %s among the premises", ext.PrintTerm(c), ext.PrintTerm(n.ring))
		}
		u, err := d.member(x, n)
		if err != nil {
			return nil, err
		}
		law := n.smulLaw.ConclForAllInsts(c, x)
		guard := prop.ConclAND(scalar.Conclusion(), u.Conclusion()).DeriveHypFrom(scalar).DeriveHypFrom(u)
		return law.DemoteHyp().DeriveHypFrom(guard), nil
	}
	for _, im := range d.images(t, n) {
		if u, err := d.member(im.arg, im.h.src); err == nil {
			return im.member(d, d.homIn(im.h, im.arg, u), n.set), nil
		}
	}
	return nil, fmt.Errorf("the element %s has no membership in %s among the premises", ext.PrintTerm(t), ext.PrintTerm(n.set))
}

// mustMember is member where the decision has already checked the
// element's parts.
func (d *_Diagram) mustMember(t core.Term, n *_Node) *prop.PropWrapper {
	w, err := d.member(t, n)
	if err != nil {
		panic("chase: " + err.Error() + " (engine invariant: the decision checked it)")
	}
	return w
}

// ── the group at a node ─────────────────────────────────────────────────────

// group is Γ ⊢ group_on at the node's additive-group record.
func (n *_Node) group(d *_Diagram) *prop.PropWrapper {
	return n.groupFact
}

func (n *_Node) groupSubject() []core.Term { return []core.Term{n.groupRecord} }

// at reads an unguarded group law at the node (OneIn, InvOne).
func (n *_Node) at(d *_Diagram, law *prop.PropWrapper) *prop.PropWrapper {
	return d.at(law, n.groupSubject(), n.group(d))
}

// guarded reads a group law at the node at args and discharges its
// membership guard from the elements' memberships.
func (n *_Node) guarded(d *_Diagram, law *prop.PropWrapper, args ...core.Term) (*prop.PropWrapper, error) {
	return d.discharge(d.at(law, n.groupSubject(), n.group(d), args...), n)
}

// mustGuarded is guarded at elements whose memberships are established.
func (n *_Node) mustGuarded(d *_Diagram, law *prop.PropWrapper, args ...core.Term) *prop.PropWrapper {
	w, err := n.guarded(d, law, args...)
	if err != nil {
		panic("chase: " + err.Error() + " (engine invariant: the elements' memberships were established)")
	}
	return w
}

// discharge removes the guard ahead of w's conclusion, a conjunction
// of memberships at the node and of subgroup facts the submodule
// premises give; a conclusion without an implication is returned as it
// is. A guard that conjoins other hypotheses with them — the equation
// a cancellation law is conditioned on — keeps those, in their order,
// as the antecedent the caller discharges.
func (d *_Diagram) discharge(w *prop.PropWrapper, n *_Node) (*prop.PropWrapper, error) {
	guard, _, isGuarded := ext.MatchesIMPLY(w.Conclusion())
	if !isGuarded {
		return w, nil
	}
	pieces := prop.LeftConjuncts(guard)
	var held, left []int
	for i, p := range pieces {
		if d.guardShaped(p) {
			held = append(held, i)
		} else {
			left = append(left, i)
		}
	}
	if len(held) == 0 || len(left) == 0 {
		proof, err := d.proveGuard(guard, n, nil)
		if err != nil {
			return nil, err
		}
		return w.DemoteHyp().DeriveHypFrom(proof), nil
	}
	all := make([]int, len(pieces))
	for i := range all {
		all[i] = i
	}
	// P₁, …, Pₘ ⊢ C, then each held piece from its proof.
	p := prop.ConjunctionFromPieces(pieces, all).DeriveTrans(w.DemoteHyp())
	for _, i := range held {
		proof, err := d.proveGuard(pieces[i], n, nil)
		if err != nil {
			return nil, err
		}
		p = p.DeriveHypFrom(proof)
	}
	var q core.Prop = p
	for k := range left {
		q = prop.ConjunctionPiece(pieces, left, k).MaybeDeriveTrans(q)
	}
	return prop.WrapProp(q).PromoteHyp(prop.ConjunctionOf(pieces, left)), nil
}

// guardShaped reports whether a guard conjunct is one discharge proves:
// a membership, a subgroup fact, or a conjunction of such.
func (d *_Diagram) guardShaped(t core.Term) bool {
	if a, b, ok := ext.MatchesAND(t); ok {
		return d.guardShaped(a) && d.guardShaped(b)
	}
	if _, _, ok := d.matchMembership(t); ok {
		return true
	}
	_, ok := headNamed(t, subgroupName, subgroupArity)
	return ok
}

// proveGuard is Γ ⊢ guard for a conjunction of memberships at n,
// subgroup facts, and equations proved by equation (when given).
func (d *_Diagram) proveGuard(guard core.Term, n *_Node, equation func(l, r core.Term) (*prop.PropWrapper, error)) (*prop.PropWrapper, error) {
	if a, b, ok := ext.MatchesAND(guard); ok {
		pa, err := d.proveGuard(a, n, equation)
		if err != nil {
			return nil, err
		}
		pb, err := d.proveGuard(b, n, equation)
		if err != nil {
			return nil, err
		}
		w := prop.ConclAND(a, b).DeriveHypFrom(pa)
		return prop.WrapProp(pb.MaybeDeriveTrans(w)), nil
	}
	if x, s, ok := d.matchMembership(guard); ok {
		if m := d.nodeOf(s); m != nil {
			return d.member(x, m)
		}
		for _, r := range d.scalarRings {
			if r.ops[6].AlphaEquals(s) {
				if w, ok := r.member(x); ok {
					return w, nil
				}
			}
		}
		return nil, fmt.Errorf("the guard %s is a membership in no module of the diagram", ext.PrintTerm(guard))
	}
	if args, ok := headNamed(guard, subgroupName, subgroupArity); ok {
		for _, sub := range d.submodules {
			if sub.group.AlphaEquals(args[0]) && sub.n.AlphaEquals(args[1]) {
				if sub.subgroup.Conclusion().AlphaEquals(guard) {
					return sub.subgroup, nil
				}
			}
		}
		return nil, fmt.Errorf("no submodule premise gives %s", ext.PrintTerm(guard))
	}
	if l, r, ok := core.MatchesEQ(guard); ok && equation != nil {
		return equation(l, r)
	}
	return nil, fmt.Errorf("the guard %s is of no shape the closer discharges", ext.PrintTerm(guard))
}

// abelian is Γ ⊢ abelian_group_on at the node's record, from the group
// and the commutativity the module gives, through the definition.
func (n *_Node) abelian(d *_Diagram) *prop.PropWrapper {
	if n.abelianFact == nil {
		comm := n.commLaw
		def := d.at(d.laws.AbelianGroupOnDef, n.groupSubject(), nil)
		group := n.group(d)
		both := prop.ConclAND(group.Conclusion(), comm.Conclusion()).DeriveHypFrom(group).DeriveHypFrom(comm)
		if !prop.Rhs(def).AlphaEquals(both.Conclusion()) {
			panic(fmt.Sprintf("chase: the abelian group definition's right side %s is not the group and the commutativity the module gives, %s",
				ext.PrintTerm(prop.Rhs(def)), ext.PrintTerm(both.Conclusion())))
		}
		n.abelianFact = def.EqSym().EqMP(both)
	}
	return n.abelianFact
}

// comm is Γ ⊢ add'(x, y) = add'(y, x).
func (n *_Node) comm(d *_Diagram, x, y core.Term) *prop.PropWrapper {
	w, err := d.discharge(n.commLaw.ConclForAllInsts(x, y), n)
	if err != nil {
		panic("chase: " + err.Error() + " (engine invariant)")
	}
	return w
}

// negAdd is Γ ⊢ neg'(add'(x, y)) = add'(neg'(x), neg'(y)).
func (n *_Node) negAdd(d *_Diagram, x, y core.Term) *prop.PropWrapper {
	w, err := d.discharge(d.at(d.laws.NegAdd, n.groupSubject(), n.abelian(d), x, y), n)
	if err != nil {
		panic("chase: " + err.Error() + " (engine invariant)")
	}
	return w
}

// ── the homomorphisms' laws ─────────────────────────────────────────────────

// homIn is Γ ⊢ f(u) ∈ M' from Γ ⊢ u ∈ M.
func (d *_Diagram) homIn(h *_Hom, u core.Term, member *prop.PropWrapper) *prop.PropWrapper {
	return h.inLaw.ConclForAllInsts(u).DemoteHyp().DeriveHypFrom(member)
}

// homAdd is Γ ⊢ f(add'(a, b)) = add”(f(a), f(b)).
func (d *_Diagram) homAdd(h *_Hom, a, b core.Term) *prop.PropWrapper {
	w, err := d.discharge(h.addLaw.ConclForAllInsts(a, b), h.src)
	if err != nil {
		panic("chase: " + err.Error() + " (engine invariant)")
	}
	return w
}

// homZero is Γ ⊢ f(zero') = zero”: f(0) = f(0 + 0) = f(0) + f(0), and
// the element equal to its own double is the zero. The certificate
// spells f's application unreduced, as the homomorphism laws do; a
// lambda's image is read through its beta bridge by the caller.
func (d *_Diagram) homZero(h *_Hom) *prop.PropWrapper {
	if h.zero != nil {
		return h.zero
	}
	src, dst := h.src, h.dst
	zz := src.mustGuarded(d, d.laws.LeftIdentity, src.zero) // add'(0, 0) = 0
	f0 := ext.Apply(h.fn, src.zero)                         // f(0)
	fzz := zz.EqSym().LeftApply(h.fn)                       // f(0) = f(add'(0, 0))
	double := fzz.EqTrans(d.homAdd(h, src.zero, src.zero))  // f(0) = add''(f(0), f(0))
	idem := dst.mustGuarded(d, d.laws.IdempotentIsOne, f0)  // add''(f0, f0) = f0 ⇒ f0 = 0''
	h.zero = idem.DemoteHyp().DeriveHypFrom(double.EqSym()) // f0 = 0''
	return h.zero
}

// homNeg is Γ ⊢ f(neg'(u)) = neg”(f(u)): f(−u) + f(u) = f(−u + u) =
// f(0) = 0, and the element that adds to f(u) to give zero is its
// inverse. f's applications are spelled unreduced, as in homZero.
func (d *_Diagram) homNeg(h *_Hom, u core.Term) *prop.PropWrapper {
	src, dst := h.src, h.dst
	negU := ext.Apply(src.neg, u)
	li := src.mustGuarded(d, d.laws.LeftInverse, u) // add'(−u, u) = 0
	sum := d.homAdd(h, negU, u).EqSym().            // add''(f(−u), f(u)) = f(add'(−u, u))
							EqTrans(li.LeftApply(h.fn)). // = f(0)
							EqTrans(d.homZero(h))        // = 0''
	iu := dst.mustGuarded(d, d.laws.InvUnique, ext.Apply(h.fn, negU), ext.Apply(h.fn, u)) // add''(x, y) = 0'' ⇔ x = neg''(y)
	return iu.EqMP(sum)
}

// ── the normalizer ──────────────────────────────────────────────────────────

// insert is Γ ⊢ add'(x, list(c)) = list(c') with c canonical and c' the
// canonical list of x :: c.
func (d *_Diagram) insert(n *_Node, x _Signed, c []_Signed) (*prop.PropWrapper, []_Signed) {
	xt := x.term()
	if len(c) == 0 {
		return n.mustGuarded(d, d.laws.RightIdentity, xt), []_Signed{x} // add'(x, 0) = x
	}
	y, rest := c[0], c[1:]
	yt, restT := y.term(), n.list(rest)
	switch {
	case x.cancels(y):
		var inverse *prop.PropWrapper // add'(x, y) = 0
		if x.neg {
			inverse = n.mustGuarded(d, d.laws.LeftInverse, y.atom.term) // add'(neg a, a) = 0
		} else {
			inverse = n.mustGuarded(d, d.laws.RightInverse, x.atom.term) // add'(a, neg a) = 0
		}
		if len(rest) == 0 {
			return inverse, nil
		}
		assoc := n.mustGuarded(d, d.laws.Assoc, xt, yt, restT) // add'(x, add'(y, R)) = add'(add'(x, y), R)
		w := assoc.EqTrans(inverse.LeftApply(n.add).RightApply(restT)).
			EqTrans(n.mustGuarded(d, d.laws.LeftIdentity, restT)) // = add'(0, R) = R
		return w, rest
	case x.before(y) || x == y:
		return prop.Refl(ext.Apply(n.add, xt, n.list(c))), append([]_Signed{x}, c...)
	default:
		// y comes first: add'(x, add'(y, R)) = add'(y, add'(x, R)), then insert x into R.
		if len(rest) == 0 {
			return n.comm(d, xt, yt), []_Signed{y, x}
		}
		swap := n.mustGuarded(d, d.laws.Assoc, xt, yt, restT). // add'(x, add'(y, R)) = add'(add'(x, y), R)
									EqTrans(n.comm(d, xt, yt).LeftApply(n.add).RightApply(restT)). // = add'(add'(y, x), R)
									EqTrans(n.mustGuarded(d, d.laws.Assoc, yt, xt, restT).EqSym()) // = add'(y, add'(x, R))
		inner, merged := d.insert(n, x, rest)
		w := trans(swap, inner.LeftApply(ext.Apply(n.add, yt)))
		if len(merged) == 0 {
			// x cancelled all of R: add'(y, 0) is y.
			w = trans(w, n.mustGuarded(d, d.laws.RightIdentity, yt))
		}
		return w, append([]_Signed{y}, merged...)
	}
}

// merge is Γ ⊢ add'(list(a), list(b)) = list(c) with c canonical.
func (d *_Diagram) merge(n *_Node, a, b []_Signed) (*prop.PropWrapper, []_Signed) {
	switch len(a) {
	case 0:
		return n.mustGuarded(d, d.laws.LeftIdentity, n.list(b)), b
	case 1:
		return d.insert(n, a[0], b)
	}
	x, rest := a[0], a[1:]
	xt, restT, bt := x.term(), n.list(rest), n.list(b)
	assoc := n.mustGuarded(d, d.laws.Assoc, xt, restT, bt).EqSym() // add'(add'(x, R), B) = add'(x, add'(R, B))
	inner, merged := d.merge(n, rest, b)
	w := trans(assoc, inner.LeftApply(ext.Apply(n.add, xt)))
	ins, out := d.insert(n, x, merged)
	return trans(w, ins), out
}

// negList is Γ ⊢ neg'(list(c)) = list(c') with c' the canonical list of
// −c (the signs flipped, the order kept).
func (d *_Diagram) negList(n *_Node, c []_Signed) (*prop.PropWrapper, []_Signed) {
	switch len(c) {
	case 0:
		return n.at(d, d.laws.InvOne), nil
	case 1:
		x := c[0]
		if x.neg {
			return n.mustGuarded(d, d.laws.InvInv, x.atom.term), []_Signed{{atom: x.atom}}
		}
		return prop.Refl(ext.Apply(n.neg, x.atom.term)), []_Signed{{atom: x.atom, neg: true}}
	}
	x, rest := c[0], c[1:]
	push := n.negAdd(d, x.term(), n.list(rest)) // neg'(add'(x, R)) = add'(neg' x, neg' R)
	ex, cx := d.negList(n, []_Signed{x})
	er, cr := d.negList(n, rest)
	return push.EqTrans(ex.LeftApply(n.add).Apply(er)), append(cx, cr...)
}

// pushHom is Γ ⊢ f(list(c)) = list(c') with c canonical at the source
// and c' canonical at the target.
func (d *_Diagram) pushHom(h *_Hom, c []_Signed) (*prop.PropWrapper, []_Signed) {
	src, dst := h.src, h.dst
	switch len(c) {
	case 0:
		return d.homZero(h), nil
	case 1:
		// Γ ⊢ f(t) = list(out), f's application unreduced on the left: a
		// scaled atom m • b through HomSmul, f(m • b) = m • f(b),
		// normalized at the target; a lambda through its beta bridge, the
		// body normalized at a scalar target and the atom elsewhere; a
		// named map's application the atom itself.
		x := c[0]
		t := x.atom.term
		var image *prop.PropWrapper
		var out []_Signed
		_, lambda := h.fn.AsAbsTerm()
		switch {
		case x.atom.scalarBase != nil:
			m := src.scalar.monoTerm(x.atom.scalarMono)
			image = d.scalarDischarge(h.smulLaw.ConclForAllInsts(m, x.atom.scalarBase.term), src)
			normal, terms, err := d.scalarNormalize(prop.Rhs(image), dst)
			if err != nil {
				panic(err)
			}
			image, out = image.EqTrans(normal), terms
		case lambda:
			beta := prop.RewriteOrRefl(prop.DeepBeta, ext.Apply(h.fn, t))
			if src.scalar == nil {
				image, out = beta, []_Signed{{atom: dst.imageAtom(x.atom, prop.Rhs(beta))}}
				break
			}
			d.rememberBetaImage(h, t)
			first := len(dst.atoms)
			normal, terms, err := d.scalarNormalize(prop.Rhs(beta), dst)
			if err != nil {
				panic(err)
			}
			if x.atom.schemaGenerated {
				for _, a := range dst.atoms[first:] {
					a.schemaGenerated = true
				}
			}
			image, out = beta.EqTrans(normal), terms
		default:
			raw := ext.Apply(h.fn, t)
			image, out = prop.Refl(raw), []_Signed{{atom: dst.imageAtom(x.atom, raw)}}
		}
		if x.neg {
			negative, negated := d.negList(dst, out)
			return d.homNeg(h, t).EqTrans(image.LeftApply(dst.neg)).EqTrans(negative), negated
		}
		return image, out
	}
	x, rest := c[0], c[1:]
	split := d.homAdd(h, x.term(), src.list(rest)) // f(add'(x, R)) = add''(f(x), f(R))
	ex, cx := d.pushHom(h, []_Signed{x})
	er, cr := d.pushHom(h, rest)
	w := split.EqTrans(ex.LeftApply(dst.add).Apply(er)) // = add''(x', list(R'))
	ins, out := d.merge(dst, cx, cr)
	return w.EqTrans(ins), out
}

// normalize is Γ ⊢ t = list(c) with c the canonical list of t's vector
// at the node (vecOf's reading, spelled).
func (d *_Diagram) normalize(t core.Term, expect *_Node) (*prop.PropWrapper, []_Signed, *_Node, error) {
	v, n, err := d.vecOf(t, expect)
	if err != nil {
		return nil, nil, nil, err
	}
	if n == nil {
		n = expect
	}
	if n == nil {
		return nil, nil, nil, fmt.Errorf("the element %s is a zero at no module the goal fixes", ext.PrintTerm(t))
	}
	w, c := d.normalizeAt(t, n)
	if want := n.canon(v); !sameList(c, want) {
		panic(fmt.Sprintf("chase: the normalizer and the linearization disagree on %s (engine invariant)", ext.PrintTerm(t)))
	}
	return w, c, n, nil
}

// normalizeAt builds the normalization proof of t at n, following
// vecOf's reading.
func (d *_Diagram) normalizeAt(t core.Term, n *_Node) (*prop.PropWrapper, []_Signed) {
	if n.scalar != nil {
		w, c, err := d.scalarNormalize(t, n)
		if err != nil {
			panic(err)
		}
		return w, c
	}
	if n.zero.AlphaEquals(t) {
		return prop.Refl(t), nil
	}
	if al, ok := d.zeroAliases[t.AlphaKey()]; ok && n.zero.AlphaEquals(al.zero) {
		return al.proof, nil
	}
	if a, ok := n.byKey[t.AlphaKey()]; ok && !d.isFormed(t, n) {
		return prop.Refl(t), []_Signed{{atom: a}}
	}
	if a, b, ok := binArgs(t, n.add); ok {
		ea, ca := d.normalizeAt(a, n)
		eb, cb := d.normalizeAt(b, n)
		m, cm := d.merge(n, ca, cb)
		return ea.LeftApply(n.add).Apply(eb).EqTrans(m), cm
	}
	if a, ok := unArg(t, n.neg); ok {
		ea, ca := d.normalizeAt(a, n)
		ng, cn := d.negList(n, ca)
		return ea.LeftApply(n.neg).EqTrans(ng), cn
	}
	for _, im := range d.images(t, n) {
		if _, _, err := d.vecOf(im.arg, im.h.src); err != nil {
			continue
		}
		es, cs := d.normalizeAt(im.arg, im.h.src)
		ph, cp := d.pushHom(im.h, cs)
		return im.of(es.LeftApply(im.h.fn).EqTrans(ph)), cp
	}
	a, ok := n.byKey[t.AlphaKey()]
	if !ok {
		panic(fmt.Sprintf("chase: %s is no atom of %s although its vector was read (engine invariant)", ext.PrintTerm(t), ext.PrintTerm(n.set)))
	}
	return prop.Refl(t), []_Signed{{atom: a}}
}

// isFormed reports whether t is a sum, negation or homomorphism
// application the normalizer decomposes (so a term that is both an
// atom's spelling and formed is read as formed — it cannot be: atoms are
// words over generators, and a sum is never an atom).
func (d *_Diagram) isFormed(t core.Term, n *_Node) bool {
	if _, _, ok := binArgs(t, n.add); ok {
		return true
	}
	_, ok := unArg(t, n.neg)
	return ok
}

// ── the ℤ-linear step ───────────────────────────────────────────────────────

// relationRows are the node's relations as dense rows over its atoms.
func (n *_Node) relationRows() [][]*big.Int {
	rows := make([][]*big.Int, len(n.relations))
	for i, r := range n.relations {
		rows[i] = r.v.dense(len(n.atoms))
	}
	return rows
}

// inLattice reports whether v lies in the node's relation lattice, with
// the coefficients over the relations.
func (n *_Node) inLattice(v _Vector) ([]*big.Int, bool) {
	if n.scalar != nil {
		return n.owner.scalarExpress(n, v)
	}
	if v.isZero() {
		return zeroRow(len(n.relations)), true
	}
	if len(n.relations) == 0 {
		return nil, false
	}
	e := buildEchelon(n.relationRows(), len(n.atoms))
	coeffs, _, ok := e.express(v.dense(len(n.atoms)))
	return coeffs, ok
}

// equation is Γ ⊢ l = r at the node when l − r is an integer
// combination of its relations; otherwise the residue is reported.
func (d *_Diagram) equation(l, r core.Term, expect *_Node) (*prop.PropWrapper, error) {
	if expect == nil {
		for _, s := range d.scalarRings {
			if w, ok := s.equation(l, r); ok {
				return w, nil
			}
		}
	}
	if expect == nil {
		if _, n, err := d.vecOf(r, nil); err == nil && n != nil {
			expect = n
		}
	}
	el, cl, n, err := d.normalize(l, expect)
	if err != nil {
		return nil, err
	}
	er, cr, _, err := d.normalize(r, n)
	if err != nil {
		return nil, err
	}
	if sameList(cl, cr) {
		return el.EqTrans(er.EqSym()), nil
	}
	vl, _, _ := d.vecOf(l, n)
	vr, _, _ := d.vecOf(r, n)
	v := vl.add(vr, -1)
	coeffs, ok := n.inLattice(v)
	if !ok {
		kind := "an integer combination"
		if n.scalar != nil {
			kind = "an integral polynomial combination"
		}
		return nil, fmt.Errorf("%s = %s does not follow: %s is not %s of the %d relation(s) at %s",
			ext.PrintTerm(l), ext.PrintTerm(r), ext.PrintTerm(n.list(n.canon(v))), kind, len(n.relations), ext.PrintTerm(n.set))
	}
	total := new(big.Int)
	for _, c := range coeffs {
		total.Add(total, new(big.Int).Abs(c))
	}
	if !total.IsInt64() || total.Int64() > coefficientCap {
		return nil, fmt.Errorf("%s = %s follows, but the combination's coefficients sum to %s, past the certificate's cap of %d",
			ext.PrintTerm(l), ext.PrintTerm(r), total, coefficientCap)
	}
	// The difference l − r, as a term, and the combination's sum S of
	// the relations' differences, each |cᵢ| times: both normalize to one
	// spelling, and S is zero summand by summand.
	diff := ext.Apply(n.add, l, ext.Apply(n.neg, r))
	var summands []core.Term
	var zeros []*prop.PropWrapper
	for i, c := range coeffs {
		rel := n.relations[i]
		for k := int64(0); k < new(big.Int).Abs(c).Int64(); k++ {
			var s core.Term
			var z *prop.PropWrapper
			if c.Sign() > 0 {
				s = ext.Apply(n.add, rel.l, ext.Apply(n.neg, rel.r))
				z = rel.proof.LeftApply(n.add).RightApply(ext.Apply(n.neg, rel.r)). // add'(l, −r) = add'(r, −r)
													EqTrans(n.mustGuarded(d, d.laws.RightInverse, rel.r)) // = 0
			} else {
				s = ext.Apply(n.add, rel.r, ext.Apply(n.neg, rel.l))
				z = rel.proof.EqSym().LeftApply(n.add).RightApply(ext.Apply(n.neg, rel.l)).
					EqTrans(n.mustGuarded(d, d.laws.RightInverse, rel.l))
			}
			summands = append(summands, s)
			zeros = append(zeros, z)
		}
	}
	sum, sumZero := d.zeroSum(n, summands, zeros)
	ed, cd, _, err := d.normalize(diff, n)
	if err != nil {
		return nil, err
	}
	es, cs, _, err := d.normalize(sum, n)
	if err != nil {
		return nil, err
	}
	if !sameList(cd, cs) {
		panic(fmt.Sprintf("chase: the difference %s and the relation combination normalize apart (engine invariant)", ext.PrintTerm(diff)))
	}
	diffZero := ed.EqTrans(es.EqSym()).EqTrans(sumZero) // add'(l, −r) = 0
	// l = add'(l, 0) = add'(l, add'(−r, r)) = add'(add'(l, −r), r) = add'(0, r) = r
	negR := ext.Apply(n.neg, r)
	w := n.mustGuarded(d, d.laws.RightIdentity, l).EqSym().
		EqTrans(n.mustGuarded(d, d.laws.LeftInverse, r).EqSym().LeftApply(ext.Apply(n.add, l))).
		EqTrans(n.mustGuarded(d, d.laws.Assoc, l, negR, r)).
		EqTrans(diffZero.LeftApply(n.add).RightApply(r)).
		EqTrans(n.mustGuarded(d, d.laws.LeftIdentity, r))
	return w, nil
}

// zeroSum spells the summands as a right-nested sum and proves it zero,
// each summand being zero.
func (d *_Diagram) zeroSum(n *_Node, summands []core.Term, zeros []*prop.PropWrapper) (core.Term, *prop.PropWrapper) {
	if len(summands) == 0 {
		return n.zero, prop.Refl(n.zero)
	}
	if len(summands) == 1 {
		return summands[0], zeros[0]
	}
	rest, restZero := d.zeroSum(n, summands[1:], zeros[1:])
	sum := ext.Apply(n.add, summands[0], rest)
	w := zeros[0].LeftApply(n.add).Apply(restZero). // add'(s, R) = add'(0, 0)
							EqTrans(n.mustGuarded(d, d.laws.LeftIdentity, n.zero))
	return sum, w
}

// trans is EqTrans with the mismatch named: an engine fault in the
// normalizer reports the two equations it tried to chain.
func trans(a, b *prop.PropWrapper) *prop.PropWrapper {
	if !prop.Rhs(a).AlphaEquals(prop.Lhs(b)) {
		panic(fmt.Sprintf("chase: the normalizer chained two equations that do not meet (engine invariant)\n  first:  %s\n  second: %s",
			ext.PrintTerm(a.Conclusion()), ext.PrintTerm(b.Conclusion())))
	}
	return a.EqTrans(b)
}
