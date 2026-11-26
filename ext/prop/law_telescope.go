package prop

import (
	"slices"

	"github.com/euc-ai/xugo/ext"
)

// HypothesisFirst derives, from a law `Γ ⊢ ∀b₁ … bₙ. P₁ ∧ … ∧ Pₘ ⇒ C`, the
// telescope that reads one of its hypotheses first:
//
//	Γ ⊢ ∀G. Pᵢ ⇒ ∀R. P₁ ∧ … ∧ Pₘ ⇒ C   (Pᵢ left out of the inner antecedent)
//
// where G is the binders free in Pᵢ and R the others, each in binder
// order, and the inner antecedent is absent when Pᵢ is the only piece.
// The pieces are the antecedent's LeftConjuncts; Pᵢ is the first one
// take accepts, shown the piece and the law's binders as the stripped
// body names them — away from Γ's free variables. The law comes back as
// it is when take accepts no piece, when it binds nothing, has no
// antecedent or binds one name twice, and when it already reads so (Pᵢ
// its only piece, over every binder).
func HypothesisFirst(law *PropWrapper, take func(piece Term, binders []VarTerm) bool) *PropWrapper {
	stripped, vars := law.StripConclForAll()
	antecedent, _, ok := MatchesIMPLY(stripped.Conclusion())
	if !ok || len(vars) == 0 {
		return law
	}
	for i, v := range vars {
		for _, w := range vars[:i] {
			if v.Equals(w) {
				return law
			}
		}
	}
	pieces := LeftConjuncts(antecedent)
	at := -1
	for i, p := range pieces {
		if take(p, vars) {
			at = i
			break
		}
	}
	if at < 0 {
		return law
	}
	var ground, rest []VarTerm
	for _, v := range vars {
		if freeIn(v, pieces[at]) {
			ground = append(ground, v)
		} else {
			rest = append(rest, v)
		}
	}
	if len(pieces) == 1 && len(rest) == 0 {
		return law
	}
	all := make([]int, len(pieces))
	var others []int
	for i := range pieces {
		all[i] = i
		if i != at {
			others = append(others, i)
		}
	}
	// P₁, …, Pₘ ⊢ C
	p := ConjunctionFromPieces(pieces, all).DeriveTrans(stripped.DemoteHyp())
	if len(others) > 0 {
		var q Prop = p
		for k := range others {
			q = ConjunctionPiece(pieces, others, k).MaybeDeriveTrans(q)
		}
		p = WrapProp(q).PromoteHyp(ConjunctionOf(pieces, others))
	}
	return p.ConclForAllList(rest...).PromoteHyp(pieces[at]).ConclForAllList(ground...)
}

// freeIn reports whether v occurs free in t.
func freeIn(v VarTerm, t Term) bool {
	for _, f := range t.Frees(nil) {
		if f.Equals(v) {
			return true
		}
	}
	return false
}

// LawTelescope reads a law stated in the standard form — `∀bs. H₁ ∧ … ∧
// Hₙ ⇒ C` — as the telescope a reading reads, `∀comps. S(comps) ⇒ ∀xs.
// H₁ ∧ … ∧ Hₙ ⇒ C` with S(comps) left out of the inner antecedent (absent
// when S is the only hypothesis), derived from it, so that a theorem's
// telescope is a theorem. S(comps) is the first hypothesis that is a
// constant applied to distinct binders, comps those binders; a reading
// at an instance picks its hypothesis by the instance instead
// (LawTelescopeAt). A sequent, and any other prop, a law already in that
// shape among them, is returned as it is.
func LawTelescope(law Prop) Prop {
	if law.NumHyps() != 0 {
		return law
	}
	return HypothesisFirst(WrapProp(law), func(piece Term, binders []VarTerm) bool {
		head, args := ext.MatchesApply(piece)
		if _, isConst := head.AsConst(); !isConst || len(args) == 0 {
			return false
		}
		for i, arg := range args {
			v, isVar := arg.AsVar()
			if !isVar || !slices.ContainsFunc(binders, func(b VarTerm) bool { return b.Equals(v) }) {
				return false
			}
			for _, earlier := range args[:i] {
				if earlier.Equals(arg) {
					return false
				}
			}
		}
		return true
	}).Core()
}

// LawTelescopeAt is the telescope a reading at the instance `S(c)` reads:
// the law's first hypothesis that states the instance's predicate, with
// every binder it mentions an argument of its own, read first. The law
// may be a sequent — a reading taken under a resident hypothesis, read
// again at a second instance. An
// argument that is no binder is a component an earlier reading fixed;
// the reading checks the specialized hypothesis against the instance.
func LawTelescopeAt(law Prop, instance Term) Prop {
	instHead, instArgs := ext.MatchesApply(instance)
	instPred, ok := instHead.AsConst()
	if !ok {
		return law
	}
	return HypothesisFirst(WrapProp(law), func(piece Term, binders []VarTerm) bool {
		head, args := ext.MatchesApply(piece)
		pred, isConst := head.AsConst()
		if !isConst || pred.Meta().Name() != instPred.Meta().Name() || len(args) != len(instArgs) {
			return false
		}
		for _, b := range binders {
			if !slices.ContainsFunc(piece.Frees(nil), func(f VarTerm) bool { return f.Equals(b) }) {
				continue
			}
			if !slices.ContainsFunc(args, func(arg Term) bool { return arg.Equals(b) }) {
				return false
			}
		}
		return true
	}).Core()
}

// PrefixTelescope derives, from a law `Γ ⊢ ∀b₁ … bₙ. P₁ ∧ … ∧ Pₘ ⇒ C`,
// the telescope a cite grounding its first k binders reads:
//
//	Γ ⊢ ∀b₁ … bₖ. Pᵢ ∧ … ⇒ ∀bₖ₊₁ … bₙ. Pⱼ ∧ … ⇒ C
//
// the pieces mentioning none of the binders after the k-th ahead, the
// rest behind, each conjunction in the statement's order and absent
// where it has no piece. The law as it is when it binds fewer than k+1
// binders, has no antecedent, binds one name twice, or has no piece to
// bring ahead.
func PrefixTelescope(law Prop, k int) Prop {
	w := WrapProp(law)
	stripped, vars := w.StripConclForAll()
	antecedent, _, ok := MatchesIMPLY(stripped.Conclusion())
	if !ok || k <= 0 || k >= len(vars) {
		return law
	}
	for i, v := range vars {
		for _, u := range vars[:i] {
			if v.Equals(u) {
				return law
			}
		}
	}
	pieces := LeftConjuncts(antecedent)
	var ahead, behind []int
	for i, p := range pieces {
		inner := false
		for _, v := range vars[k:] {
			if freeIn(v, p) {
				inner = true
				break
			}
		}
		if inner {
			behind = append(behind, i)
		} else {
			ahead = append(ahead, i)
		}
	}
	if len(ahead) == 0 {
		return law
	}
	all := make([]int, len(pieces))
	for i := range all {
		all[i] = i
	}
	// P₁, …, Pₘ ⊢ C
	p := ConjunctionFromPieces(pieces, all).DeriveTrans(stripped.DemoteHyp())
	if len(behind) > 0 {
		var q Prop = p
		for i := range behind {
			q = ConjunctionPiece(pieces, behind, i).MaybeDeriveTrans(q)
		}
		p = WrapProp(q).PromoteHyp(ConjunctionOf(pieces, behind))
	}
	p = p.ConclForAllList(vars[k:]...)
	var q Prop = p
	for i := range ahead {
		q = ConjunctionPiece(pieces, ahead, i).MaybeDeriveTrans(q)
	}
	return WrapProp(q).PromoteHyp(ConjunctionOf(pieces, ahead)).ConclForAllList(vars[:k]...).Core()
}
