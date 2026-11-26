// Package ac is the associative-commutative rearrangement solver: given
// a caller-supplied assoc/sym certificate pair for one binary op ⊕, it
// derives the kernel-checked ⊢ lhs = rhs for any two ground ⊕-sums that
// flatten to the same leaf multiset.
//
// Layer (why this lives under prover/solver/ while `algebra` is a tent
// sibling of proof — see prover/README.md): the two sit on OPPOSITE
// sides of the proof calculus in the dependency order, and the tree
// records that.
//
//   - `algebra` is ABOVE proof — a ladder generator. Its output is
//     proof.Action values composed from the exported cite verbs; it
//     writes proof script programmatically.
//   - `ac` is BELOW proof — a certificate manufacturer, kin to refuter
//     and omega. It never touches the goal stack: every step is a direct
//     kernel composition (Refl / Apply / EqSym / EqTrans) over ground
//     instances of the supplied certs, and the result is one closed Prop.
//
// That is what lets package proof build a primitive Action on top of it
// (proof.CiteACRegroup) — which a package above proof could not supply,
// since the Action must inspect goal state at apply time.
//
// The layer direction also fixes the shape of the premise surface. The
// kit hands out a VALUE, not an Action: `New(assoc, sym).Eq(lhs, rhs)`
// returns an Equation carrying the closed certificate, and package
// proof adopts it through its SelfProvingPremise outlet (an interface
// over kernel Props — the only vocabulary the two layers share) when a
// By consumes it. A premise that carries its own proof is the one thing
// this kit exports to a proof body; everything else it does, it does
// through proof.CiteACRegroup.
//
// The derivation is a pure function of (assoc, sym, lhs, rhs) — no
// search, no cache state, no CNF refute — so a Build re-run
// reproduces it byte-for-byte.
//
// Everything is soundness-first: every misuse panics loudly, nothing
// degrades to a weaker result.
package ac

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

// ---------------------------------------------------------------------------
// Certificate parsing
// ---------------------------------------------------------------------------

// Deriver carries the parsed shape of one AC op's assoc/sym certificate
// pair: the op itself, its operand type, and — for each cert — the binder
// order, the binder→argument-role mapping (a cert may bind its variables
// in any order), and whether the stored assoc orientation needs an EqSym
// to read (a⊕b)⊕c = a⊕(b⊕c).
type Deriver struct {
	assoc, sym core.Thm
	op         core.Term
	operandTy  core.HolType

	// assocRole[k] = which of the instance arguments (0 = a, 1 = b,
	// 2 = c in (a⊕b)⊕c = a⊕(b⊕c)) the k-th ∀-binder receives; likewise
	// symRole for (a, b) in a⊕b = b⊕a.
	assocRole [3]int
	symRole   [2]int
	assocFlip bool // stored orientation is a⊕(b⊕c) = (a⊕b)⊕c

	// certPatterns are the two sides of each cert's own equation, as
	// written with the cert's ∀-binders still free. The ground-only
	// guard rejects an lhs/rhs α-equal to one of them.
	//
	// Why not "lhs/rhs mentions a cert binder free": the certs bind the
	// commonest variable names in the corpus (AddAssoc/MulAssoc bind
	// ∀m n p), so that test fires on any legitimate GROUND term built
	// over a fixed variable that merely shares a name with a binder — an
	// induction on `p` over MulAssoc, say. Instantiation is the kernel's
	// capture-avoiding ConclForAllInsts, so such a term is perfectly
	// sound; a name collision is no defect. The defect the guard is for is
	// passing a cert's own PATTERN where a concrete sum belongs, and
	// that is what this tests directly.
	certPatterns []core.Term
}

// New parses an assoc/sym certificate pair over one op ⊕ into a Deriver.
//
// assoc must be a certificate of the shape ∀m n p. (m⊕n)⊕p = m⊕(n⊕p)
// (either orientation), sym of the shape ∀m n. m⊕n = n⊕m, both over the
// SAME op ⊕, which is read off the assoc statement — nothing is
// hardcoded to a particular entry, so any AC op whose certs are supplied
// works.
//
// Panics when either cert carries hypotheses, does not have the required
// ∀-closed shape, or the two disagree on ⊕.
// Certs returns the certificate pair the deriver was built from — the
// composite ministep's payload (prover/proof/step_ac.go records the
// pair, not the derived equation).
func (d *Deriver) Certs() (assoc, sym core.Thm) { return d.assoc, d.sym }

func New(assoc, sym core.Thm) *Deriver {
	d := &Deriver{assoc: assoc, sym: sym}
	d.parseAssoc()
	d.parseSym()
	return d
}

func (d *Deriver) parseAssoc() {
	if d.assoc.NumHyps() != 0 {
		panic(fmt.Sprintf("AC regroup: assoc cert carries hypotheses — need a closed "+
			"∀m n p. (m⊕n)⊕p = m⊕(n⊕p) theorem:\n%s", prop.PrintProp(d.assoc)))
	}
	vars, body := StripForallBinders(d.assoc.Conclusion())
	l, r, okEq := ext.MatchesEQ(body)
	if len(vars) != 3 || !okEq {
		panic(fmt.Sprintf("AC regroup: assoc cert is not a 3-binder ∀-closed equation:\n%s",
			prop.PrintProp(d.assoc)))
	}
	shapeErr := func() {
		panic(fmt.Sprintf("AC regroup: assoc cert does not have the "+
			"(m⊕n)⊕p = m⊕(n⊕p) shape (either orientation, one op):\n%s",
			prop.PrintProp(d.assoc)))
	}
	op, a, b, c, ok := matchLeftNested(l)
	if ok {
		// Stored as (a⊕b)⊕c = a⊕(b⊕c) — the reading direction.
		op2, a2, b2, c2, ok2 := matchRightNested(r)
		if !ok2 || !op.Equals(op2) || !a.Equals(a2) || !b.Equals(b2) || !c.Equals(c2) {
			shapeErr()
		}
	} else {
		// Stored as a⊕(b⊕c) = (a⊕b)⊕c (e.g. nat_arith.AddAssoc) — EqSym on read.
		op, a, b, c, ok = matchRightNested(l)
		if !ok {
			shapeErr()
		}
		op2, a2, b2, c2, ok2 := matchLeftNested(r)
		if !ok2 || !op.Equals(op2) || !a.Equals(a2) || !b.Equals(b2) || !c.Equals(c2) {
			shapeErr()
		}
		d.assocFlip = true
	}
	role, ok := binderRoles(vars, []core.Term{a, b, c})
	if !ok {
		shapeErr()
	}
	copy(d.assocRole[:], role)
	d.op = op
	d.operandTy = vars[0].Type()
	d.certPatterns = append(d.certPatterns, l, r)
}

func (d *Deriver) parseSym() {
	if d.sym.NumHyps() != 0 {
		panic(fmt.Sprintf("AC regroup: sym cert carries hypotheses — need a closed "+
			"∀m n. m⊕n = n⊕m theorem:\n%s", prop.PrintProp(d.sym)))
	}
	vars, body := StripForallBinders(d.sym.Conclusion())
	l, r, okEq := ext.MatchesEQ(body)
	if len(vars) != 2 || !okEq {
		panic(fmt.Sprintf("AC regroup: sym cert is not a 2-binder ∀-closed equation:\n%s",
			prop.PrintProp(d.sym)))
	}
	opL, a, b, okL := matchBinApp(l)
	opR, b2, a2, okR := matchBinApp(r)
	if !okL || !okR || !opL.Equals(opR) || !a.Equals(a2) || !b.Equals(b2) {
		panic(fmt.Sprintf("AC regroup: sym cert does not have the m⊕n = n⊕m shape:\n%s",
			prop.PrintProp(d.sym)))
	}
	if !opL.Equals(d.op) {
		panic(fmt.Sprintf("AC regroup: assoc and sym certs are over different ops:\n"+
			"  assoc op: %s\n  sym op:   %s", ext.PrintTerm(d.op), ext.PrintTerm(opL)))
	}
	role, ok := binderRoles(vars, []core.Term{a, b})
	if !ok {
		panic(fmt.Sprintf("AC regroup: sym cert's binders are not exactly its equation's "+
			"two distinct operands:\n%s", prop.PrintProp(d.sym)))
	}
	copy(d.symRole[:], role)
	d.certPatterns = append(d.certPatterns, l, r)
}

// binderRoles maps each ∀-binder variable to the index of the
// argument-role term it plays in the parsed equation body. Every role
// must be a variable, every binder must claim exactly one role, and
// the binders must be pairwise distinct — the AC-lemma shape.
func binderRoles(vars []core.VarTerm, roles []core.Term) ([]int, bool) {
	if len(vars) != len(roles) {
		return nil, false
	}
	out := make([]int, len(vars))
	claimed := make([]bool, len(roles))
	for k, v := range vars {
		out[k] = -1
		for i, role := range roles {
			if !claimed[i] && v.Equals(role) {
				out[k], claimed[i] = i, true
				break
			}
		}
		if out[k] < 0 {
			return nil, false
		}
	}
	return out, true
}

// StripForallBinders strips every leading ∀ off t, returning the binder
// variables in binding order and the remaining body.
func StripForallBinders(t core.Term) ([]core.VarTerm, core.Term) {
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

// matchBinApp decomposes t = ⊕(x)(y) into (⊕, x, y) for an arbitrary
// (not necessarily const) binary-op head.
func matchBinApp(t core.Term) (op, x, y core.Term, ok bool) {
	outer, ok := t.AsAppliedTerm()
	if !ok {
		return nil, nil, nil, false
	}
	inner, ok := outer.Fun().AsAppliedTerm()
	if !ok {
		return nil, nil, nil, false
	}
	return inner.Fun(), inner.Arg(), outer.Arg(), true
}

// matchLeftNested decomposes t = (a⊕b)⊕c (one op at both nodes).
func matchLeftNested(t core.Term) (op, a, b, c core.Term, ok bool) {
	op1, ab, c, ok := matchBinApp(t)
	if !ok {
		return nil, nil, nil, nil, false
	}
	op2, a, b, ok := matchBinApp(ab)
	if !ok || !op1.Equals(op2) {
		return nil, nil, nil, nil, false
	}
	return op1, a, b, c, true
}

// matchRightNested decomposes t = a⊕(b⊕c) (one op at both nodes).
func matchRightNested(t core.Term) (op, a, b, c core.Term, ok bool) {
	op1, a, bc, ok := matchBinApp(t)
	if !ok {
		return nil, nil, nil, nil, false
	}
	op2, b, c, ok := matchBinApp(bc)
	if !ok || !op1.Equals(op2) {
		return nil, nil, nil, nil, false
	}
	return op1, a, b, c, true
}

// ---------------------------------------------------------------------------
// Input validation
// ---------------------------------------------------------------------------

// Validate checks that lhs and rhs are legal inputs for RegroupEq. Call
// it once, up front (the Action surface validates at construction so
// misuse surfaces at the authoring call site, not mid-proof).
//
// Panics when lhs or rhs is not of ⊕'s operand type (a polymorphic cert
// must be type-specialized by the caller first); is α-equal to one of
// the certs' own equation sides (a lemma pattern passed where a
// concrete ground sum belongs); lhs α-equals rhs
// (nothing to regroup — the derived equation would normalize to ⊤); or
// the flattened leaf multisets differ (the panic prints both).
func (d *Deriver) Validate(lhs, rhs core.Term) {
	if !lhs.Type().Equals(d.operandTy) || !rhs.Type().Equals(d.operandTy) {
		panic(fmt.Sprintf("AC regroup: lhs/rhs are not of the certs' operand type %v — "+
			"a polymorphic cert must be type-specialized by the caller first\n  lhs: %s\n  rhs: %s",
			d.operandTy, ext.PrintTerm(lhs), ext.PrintTerm(rhs)))
	}
	for _, pat := range d.certPatterns {
		for _, in := range []core.Term{lhs, rhs} {
			if in.AlphaEquals(pat) {
				panic(fmt.Sprintf("AC regroup: an input is one of the certs' own equation sides "+
					"(%s) — a lemma PATTERN was passed where a concrete ground sum belongs\n"+
					"  lhs: %s\n  rhs: %s",
					ext.PrintTerm(pat), ext.PrintTerm(lhs), ext.PrintTerm(rhs)))
			}
		}
	}
	if lhs.AlphaEquals(rhs) {
		panic(fmt.Sprintf("AC regroup: lhs α-equals rhs — nothing to regroup "+
			"(the derived equation would normalize to ⊤)\n  lhs: %s", ext.PrintTerm(lhs)))
	}
	L, M := d.flatten(lhs), d.flatten(rhs)
	counts := make(map[core.TermKey]int, len(L))
	for _, t := range L {
		counts[t.AlphaKey()]++
	}
	for _, t := range M {
		counts[t.AlphaKey()]--
	}
	for _, n := range counts {
		if n != 0 {
			panic(fmt.Sprintf("AC regroup: leaf multisets differ — lhs and rhs are not "+
				"AC-rearrangements of the same sum\n  lhs leaves: %s\n  rhs leaves: %s",
				printLeaves(L), printLeaves(M)))
		}
	}
}

func printLeaves(leaves []core.Term) string {
	parts := make([]string, len(leaves))
	for i, t := range leaves {
		parts[i] = ext.PrintTerm(t)
	}
	return "[" + strings.Join(parts, ", ") + "]"
}

// ---------------------------------------------------------------------------
// Eq — the rearrangement as a self-proving premise
// ---------------------------------------------------------------------------

// Eq is the AC rearrangement AS A PREMISE: `ac.New(assoc, sym).Eq(lhs,
// rhs)` states "these are the same leaves in a different order" once,
// as the two terms, and the equation proves itself when a By consumes
// it — the rearrangement is COMPUTED from lhs and rhs.
//
// It replaces the two-writings spelling that a premise list otherwise
// forces: `a.Have(label, <the equation, restated as a claim>,
// CiteACRegroup(assoc, sym, lhs, rhs))` followed by the Have's fact in
// the list. Same equation, written twice, with a claim text that has to
// agree with the endpoints by hand.
//
// Validation is up front (the authoring call site, not mid-proof): Eq
// panics on everything Validate panics on. The derivation itself is a
// pure function of (assoc, sym, lhs, rhs) — no goal state is read and
// no search runs — so a Build re-run reproduces it
// byte-for-byte.
func (d *Deriver) Eq(lhs, rhs ext.TermLike) Equation {
	if lhs == nil || rhs == nil {
		panic("AC regroup: nil lhs/rhs term")
	}
	l, r := lhs.Core(), rhs.Core()
	d.Validate(l, r)
	return Equation{eq: d.RegroupEq(l, r)}
}

// Equation is one derived AC-rearrangement equation, ready to be
// consumed as a premise. It satisfies package proof's
// SelfProvingPremise outlet — stated over kernel Props alone, since ac
// sits BELOW proof and cannot name it (see the package doc) — so a
// body passes it straight into a premise list:
//
//	By(ih, ac.New(mulAssoc, mulSym).Eq(spareOutside, spareInside), …)
//
// The value is inert: it holds a closed certificate and touches no goal
// state until the consuming By materializes it.
type Equation struct{ eq core.Prop }

// SelfProof returns the kernel-derived, closed ⊢ lhs = rhs.
func (e Equation) SelfProof() core.Prop { return e.eq }

// ---------------------------------------------------------------------------
// Kernel-level derivation
// ---------------------------------------------------------------------------

// RegroupEq derives the closed ⊢ lhs = rhs.
//
// Let canon be the right-associated chain over lhs's leaves in
// first-appearance order. Each side is proved equal to canon — flatten
// by recursion on the ⊕-tree (assoc instances + congruence), then
// reorder by selection sort (each adjacent swap is one assoc⁻¹/sym/assoc
// sandwich) — and the two halves compose by EqTrans + EqSym.
//
// Validate must have run on the same (lhs, rhs) first.
func (d *Deriver) RegroupEq(lhs, rhs core.Term) core.Prop {
	L, M := d.flatten(lhs), d.flatten(rhs)
	lhsEq := d.flattenEq(lhs) // ⊢ lhs = RA(L)
	rhsEq := d.flattenEq(rhs) // ⊢ rhs = RA(M)
	perm := d.sortEq(M, L)    // ⊢ RA(M) = RA(M reordered along L)
	eq := lhsEq.EqTrans(rhsEq.EqTrans(perm).EqSym())
	utils.Assert(eq.NumHyps() == 0)
	utils.Assert(eq.Conclusion().AlphaEquals(core.Eq(lhs, rhs)))
	return eq
}

// bin builds the application ⊕(x)(y).
func (d *Deriver) bin(x, y core.Term) core.Term {
	return core.Apply(core.Apply(d.op, x), y)
}

// flatten returns t's maximal ⊕-leaf list, left to right.
func (d *Deriver) flatten(t core.Term) []core.Term {
	if op, x, y, ok := matchBinApp(t); ok && op.Equals(d.op) {
		return append(d.flatten(x), d.flatten(y)...)
	}
	return []core.Term{t.Core()}
}

// chain builds the right-associated ⊕-chain over leaves (len ≥ 1).
func (d *Deriver) chain(leaves []core.Term) core.Term {
	utils.Assert(len(leaves) > 0)
	t := leaves[len(leaves)-1]
	for i := len(leaves) - 2; i >= 0; i-- {
		t = d.bin(leaves[i], t)
	}
	return t
}

// assocAt is the ground associativity instance ⊢ (x⊕y)⊕z = x⊕(y⊕z),
// oriented left-nested → right-nested regardless of the cert's stored
// orientation.
func (d *Deriver) assocAt(x, y, z core.Term) *prop.PropWrapper {
	args := [3]core.Term{x, y, z}
	w := make([]core.Term, 3)
	for k := range w {
		w[k] = args[d.assocRole[k]]
	}
	inst := prop.WrapProp(d.assoc).ConclForAllInsts(w...)
	if d.assocFlip {
		inst = inst.EqSym()
	}
	utils.Assert(inst.Conclusion().AlphaEquals(
		core.Eq(d.bin(d.bin(x, y), z), d.bin(x, d.bin(y, z)))))
	return inst
}

// symAt is the ground commutativity instance ⊢ x⊕y = y⊕x.
func (d *Deriver) symAt(x, y core.Term) *prop.PropWrapper {
	args := [2]core.Term{x, y}
	w := make([]core.Term, 2)
	for k := range w {
		w[k] = args[d.symRole[k]]
	}
	inst := prop.WrapProp(d.sym).ConclForAllInsts(w...)
	utils.Assert(inst.Conclusion().AlphaEquals(core.Eq(d.bin(x, y), d.bin(y, x))))
	return inst
}

// flattenEq proves ⊢ t = RA(flatten(t)) by recursion on the ⊕-tree:
// flatten both children (congruence via Refl(⊕) + Apply), then merge
// the two right-associated chains (mergeEq).
func (d *Deriver) flattenEq(t core.Term) *prop.PropWrapper {
	op, x, y, ok := matchBinApp(t)
	if !ok || !op.Equals(d.op) {
		return prop.Refl(t) // leaf: ⊢ t = t
	}
	ex := d.flattenEq(x) // ⊢ x = RA(X)
	ey := d.flattenEq(y) // ⊢ y = RA(Y)
	// ⊢ x⊕y = RA(X)⊕RA(Y)
	e := prop.Refl(d.op).Apply(ex).Apply(ey)
	// ⊢ RA(X)⊕RA(Y) = RA(X++Y)
	return e.EqTrans(d.mergeEq(d.flatten(x), d.flatten(y)))
}

// mergeEq proves ⊢ RA(X)⊕RA(Y) = RA(X++Y) by peeling X's head with
// one assoc instance per element.
func (d *Deriver) mergeEq(X, Y []core.Term) *prop.PropWrapper {
	if len(X) == 1 {
		// x⊕RA(Y) IS RA(x:Y) syntactically.
		return prop.Refl(d.chain(append(append([]core.Term{}, X...), Y...)))
	}
	x := X[0]
	// (x⊕RA(X'))⊕RA(Y) = x⊕(RA(X')⊕RA(Y))
	a := d.assocAt(x, d.chain(X[1:]), d.chain(Y))
	// x⊕(RA(X')⊕RA(Y)) = x⊕RA(X'++Y)
	lift := d.mergeEq(X[1:], Y).LeftApply(core.Apply(d.op, x))
	return a.EqTrans(lift)
}

// moveToFrontEq proves ⊢ RA(M) = RA(M[i] : M∖i): bubble element i to
// the front, one assoc⁻¹/sym/assoc sandwich per position.
func (d *Deriver) moveToFrontEq(M []core.Term, i int) *prop.PropWrapper {
	utils.Assert(i >= 0 && i < len(M))
	if i == 0 {
		return prop.Refl(d.chain(M))
	}
	x, Mp := M[0], M[1:]
	// ⊢ RA(M') = RA(y : rest), y = M'[i-1]
	sub := d.moveToFrontEq(Mp, i-1)
	// ⊢ x⊕RA(M') = x⊕RA(y : rest)   (LHS is RA(M) syntactically)
	lift := sub.LeftApply(core.Apply(d.op, x))
	y := Mp[i-1]
	rest := deleteAt(Mp, i-1)
	var swap *prop.PropWrapper
	if len(rest) == 0 {
		// ⊢ x⊕y = y⊕x   (RA(y:rest) = y, RA(y:x:rest) = y⊕x)
		swap = d.symAt(x, y)
	} else {
		R := d.chain(rest)
		// x⊕(y⊕R) = (x⊕y)⊕R = (y⊕x)⊕R = y⊕(x⊕R)
		a1 := d.assocAt(x, y, R)
		sl := prop.Refl(d.op).Apply(d.symAt(x, y)).RightApply(R)
		a2 := d.assocAt(y, x, R)
		swap = a1.EqSym().EqTrans(sl).EqTrans(a2)
	}
	return lift.EqTrans(swap)
}

// sortEq proves ⊢ RA(M) = RA(M reordered along L) for M a permutation
// of L (validated up front): selection sort — bring L[0]'s first
// α-match in M to the front, recurse on the tails.
func (d *Deriver) sortEq(M, L []core.Term) *prop.PropWrapper {
	utils.Assert(len(M) == len(L) && len(M) > 0)
	if len(M) == 1 {
		return prop.Refl(M[0])
	}
	i := -1
	want := L[0].AlphaKey()
	for k, t := range M {
		if t.AlphaKey() == want {
			i = k
			break
		}
	}
	utils.Assert(i >= 0)        // multiset equality was validated at construction
	mv := d.moveToFrontEq(M, i) // ⊢ RA(M) = RA(M[i] : M∖i)
	rest := deleteAt(M, i)
	// ⊢ M[i]⊕RA(M∖i) = M[i]⊕RA(sorted tail)
	lift := d.sortEq(rest, L[1:]).LeftApply(core.Apply(d.op, M[i]))
	return mv.EqTrans(lift)
}

// deleteAt returns a fresh slice with element i removed.
func deleteAt(s []core.Term, i int) []core.Term {
	out := make([]core.Term, 0, len(s)-1)
	out = append(out, s[:i]...)
	return append(out, s[i+1:]...)
}
