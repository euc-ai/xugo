package tactic

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

// Telescope is a statement's leading telescope read as blocks: a block
// is a run of ∀-binders and the ⇒-antecedent that closes it, nil when
// the run ends the telescope. `∀x y. A ∧ B ⇒ C` is one block, `∀x. A ⇒
// ∀y. B ⇒ C` two; a statement in the standard form has one.
type Telescope struct {
	// Binders are the telescope's ∀-binders in order, and BlockOf the
	// block each one belongs to.
	Binders []core.VarTerm
	BlockOf []int
	// Antes are the blocks' antecedents, Pieces each antecedent's
	// conjuncts as the parser joins them (prop.LeftConjuncts), and Tails
	// what the statement says after each block.
	Antes  []core.Term
	Pieces [][]core.Term
	Tails  []core.Term
}

// ReadTelescope reads t's leading telescope.
func ReadTelescope(t core.Term) Telescope {
	var tel Telescope
	for {
		block := len(tel.Antes)
		run := 0
		for abs := ext.MatchesFORALL(t); !abs.IsZero(); abs = ext.MatchesFORALL(t) {
			tel.Binders = append(tel.Binders, abs.Var())
			tel.BlockOf = append(tel.BlockOf, block)
			t = abs.Body()
			run++
		}
		ante, rest, ok := ext.MatchesIMPLY(t)
		if !ok {
			if run > 0 {
				tel.Antes = append(tel.Antes, nil)
				tel.Pieces = append(tel.Pieces, nil)
				tel.Tails = append(tel.Tails, t)
			}
			return tel
		}
		tel.Antes = append(tel.Antes, ante)
		tel.Pieces = append(tel.Pieces, prop.LeftConjuncts(ante))
		tel.Tails = append(tel.Tails, rest)
		t = rest
	}
}

// TelescopeItem is one move of the order a section opens a statement
// in: the telescope's binder of index Binder, or, with Binder < 0, the
// hypothesis that joins the pieces named, in order.
type TelescopeItem struct {
	Binder int
	Pieces []PieceRef
}

// PieceRef names a piece of a block's antecedent.
type PieceRef struct{ Block, Index int }

// Deps are the indices of the binders in scope at block b — its own and
// the blocks' before it — that t mentions. A variable of the same name a
// later block binds is another variable, free where t stands.
func (tel Telescope) Deps(t core.Term, b int) []int {
	var out []int
	for i, v := range tel.Binders {
		if tel.BlockOf[i] <= b && freeIn(v, t) {
			out = append(out, i)
		}
	}
	return out
}

// captures reports whether binding the binders listed, ahead of a piece
// of block b, would capture a variable the piece mentions free: a
// binder of a later block, of that variable's name.
func (tel Telescope) captures(piece core.Term, b int, binders []int) bool {
	for _, i := range binders {
		if tel.BlockOf[i] > b && freeIn(tel.Binders[i], piece) {
			return true
		}
	}
	return false
}

// Open is the statement opened in the order items gives: each item in
// turn — the binder bound, or the pieces joined into one antecedent —
// then the rest of the blocks the items reach (the window), as one
// block: its binders not listed, then its pieces not taken, conjoined,
// ahead of what the statement says after the window. The items bind
// the window's first binders, in order; a hypothesis follows every
// binder it mentions; no piece is taken twice. The statement itself
// when items is empty.
func (tel Telescope) Open(items []TelescopeItem, statement core.Term) (core.Term, error) {
	window := -1
	bound := 0
	taken := map[PieceRef]bool{}
	for _, it := range items {
		if it.Binder >= 0 {
			if it.Binder != bound || it.Binder >= len(tel.Binders) {
				return nil, fmt.Errorf("binder %d is not the next one (%d)", it.Binder, bound)
			}
			window = max(window, tel.BlockOf[it.Binder])
			bound++
			continue
		}
		if len(it.Pieces) == 0 {
			return nil, fmt.Errorf("a hypothesis joins no piece")
		}
		for _, ref := range it.Pieces {
			if ref.Block < 0 || ref.Block >= len(tel.Pieces) || ref.Index < 0 || ref.Index >= len(tel.Pieces[ref.Block]) {
				return nil, fmt.Errorf("no piece %d of block %d", ref.Index, ref.Block)
			}
			if taken[ref] {
				return nil, fmt.Errorf("piece %d of block %d is taken twice", ref.Index, ref.Block)
			}
			taken[ref] = true
			piece := tel.Pieces[ref.Block][ref.Index]
			for _, d := range tel.Deps(piece, ref.Block) {
				if d >= bound {
					return nil, fmt.Errorf("piece %d of block %d mentions %s, not yet bound", ref.Index, ref.Block, tel.Binders[d].Name())
				}
			}
			if tel.captures(piece, ref.Block, upTo(bound)) {
				return nil, fmt.Errorf("piece %d of block %d mentions a variable a binder bound before it captures", ref.Index, ref.Block)
			}
			window = max(window, ref.Block)
		}
	}
	if window < 0 {
		return statement, nil
	}
	for i, v := range tel.Binders {
		for _, w := range tel.Binders[:i] {
			if tel.BlockOf[i] <= window && v.Equals(w) {
				return nil, fmt.Errorf("the statement binds %s twice", v.Name())
			}
		}
	}
	acc := tel.Tails[window]
	windowBinders := upTo(bound)
	for i := bound; i < len(tel.Binders) && tel.BlockOf[i] <= window; i++ {
		windowBinders = append(windowBinders, i)
	}
	var rest []core.Term
	for b := 0; b <= window; b++ {
		for i, p := range tel.Pieces[b] {
			if !taken[PieceRef{b, i}] {
				if tel.captures(p, b, windowBinders) {
					return nil, fmt.Errorf("piece %d of block %d mentions a variable a binder of the window captures", i, b)
				}
				rest = append(rest, p)
			}
		}
	}
	if len(rest) > 0 {
		acc = ext.WrapTerm(conjoined(rest)).Imply(acc).Core()
	}
	for i := len(tel.Binders) - 1; i >= bound; i-- {
		if tel.BlockOf[i] <= window {
			acc = ext.ForAll(tel.Binders[i])(acc).Core()
		}
	}
	for k := len(items) - 1; k >= 0; k-- {
		it := items[k]
		if it.Binder >= 0 {
			acc = ext.ForAll(tel.Binders[it.Binder])(acc).Core()
			continue
		}
		acc = ext.WrapTerm(conjoined(tel.terms(it.Pieces))).Imply(acc).Core()
	}
	return acc, nil
}

// upTo is 0 … n-1.
func upTo(n int) []int {
	out := make([]int, n)
	for i := range out {
		out[i] = i
	}
	return out
}

// terms are the pieces refs name.
func (tel Telescope) terms(refs []PieceRef) []core.Term {
	out := make([]core.Term, len(refs))
	for i, ref := range refs {
		out[i] = tel.Pieces[ref.Block][ref.Index]
	}
	return out
}

// conjoined joins ts to the left, in order.
func conjoined(ts []core.Term) core.Term {
	idx := make([]int, len(ts))
	for i := range idx {
		idx[i] = i
	}
	return prop.ConjunctionOf(ts, idx)
}

// OpenTelescopeTactic opens the goal's statement in the order items
// gives (Telescope.Open):
//
//	goal:     Γ ⊢ G
//	subgoal:  Γ ⊢ G opened
//
// The two state the same theorem; the reconstruct derives G from the
// opened form by the kernel. nil when items do not open G or leave it
// as it is.
func OpenTelescopeTactic(goal Prop, items []TelescopeItem) *SubGoals {
	statement := goal.Conclusion()
	tel := ReadTelescope(statement)
	opened, err := tel.Open(items, statement)
	if err != nil || opened.AlphaEquals(statement) {
		return nil
	}
	goal0 := MakeProp(opened, goal.Hyps()...)
	reconstruct := func(thms ...Prop) Prop {
		if !thms[0].Conclusion().AlphaEquals(opened) {
			// A child closed some other way (⊥ from the hypotheses).
			return thms[0]
		}
		return tel.closeFrom(thms[0], items, statement)
	}
	return MakeTrackedSubGoals(goal, reconstruct, [][]int{keptSuccessors(goal, goal0)}, goal0)
}

// closeFrom derives Γ ⊢ G from Γ ⊢ G opened: the window's binders fixed
// at variables free of Γ and its antecedents assumed, the opened form
// instantiated at the same variables, each hypothesis it states
// discharged from the pieces of the assumed antecedents, and G closed
// again over the window.
func (tel Telescope) closeFrom(thm Prop, items []TelescopeItem, statement core.Term) Prop {
	window := -1
	bound := 0
	taken := map[PieceRef]bool{}
	for _, it := range items {
		if it.Binder >= 0 {
			window = max(window, tel.BlockOf[it.Binder])
			bound++
			continue
		}
		for _, ref := range it.Pieces {
			taken[ref] = true
			window = max(window, ref.Block)
		}
	}
	// The window's binders at variables neither Γ nor the statement
	// mentions free.
	w := prop.WrapProp(thm)
	used := map[core.TermName]bool{}
	for _, v := range statement.Frees(nil) {
		used[v.Name()] = true
	}
	fresh := make([]core.VarTerm, len(tel.Binders))
	for i, v := range tel.Binders {
		if tel.BlockOf[i] > window {
			break
		}
		name := v.Name()
		for used[name] || !prop.NotFreeInHyps(w, core.Var(name, v.Type())) {
			name = utils.NextName(name)
		}
		used[name] = true
		fresh[i] = core.Var(name, v.Type())
	}
	// at reads a term of block b at the fresh variables of the binders
	// in scope there.
	at := func(t core.Term, b int) core.Term {
		var substs []core.TermSubst
		for i, v := range tel.Binders {
			if tel.BlockOf[i] <= b && !fresh[i].Equals(v) {
				substs = append(substs, core.MakeTermSubst(v, fresh[i]))
			}
		}
		if len(substs) == 0 {
			return t
		}
		return t.Substitute(substs...)
	}
	pieces := make([][]core.Term, window+1)
	all := make([][]int, window+1)
	for b := 0; b <= window; b++ {
		for i, p := range tel.Pieces[b] {
			pieces[b] = append(pieces[b], at(p, b))
			all[b] = append(all[b], i)
		}
	}
	// A's ⊢ the pieces refs name, joined.
	hypothesis := func(refs []PieceRef) *prop.PropWrapper {
		ts := make([]core.Term, len(refs))
		idx := make([]int, len(refs))
		for i, ref := range refs {
			ts[i], idx[i] = pieces[ref.Block][ref.Index], i
		}
		var p Prop = prop.ConjunctionFromPieces(ts, idx)
		for _, ref := range refs {
			p = prop.ConjunctionPiece(pieces[ref.Block], all[ref.Block], ref.Index).MaybeDeriveTrans(p)
		}
		return prop.WrapProp(p)
	}
	discharge := func(refs []PieceRef) {
		w = hypothesis(refs).DeriveTrans(w.DemoteHyp())
	}
	for _, it := range items {
		if it.Binder >= 0 {
			w = w.ConclForAllInsts(fresh[it.Binder])
			continue
		}
		discharge(it.Pieces)
	}
	for i := bound; i < len(tel.Binders) && tel.BlockOf[i] <= window; i++ {
		w = w.ConclForAllInsts(fresh[i])
	}
	var rest []PieceRef
	for b := 0; b <= window; b++ {
		for i := range tel.Pieces[b] {
			if !taken[PieceRef{b, i}] {
				rest = append(rest, PieceRef{b, i})
			}
		}
	}
	if len(rest) > 0 {
		discharge(rest)
	}
	// Γ, A₀ … A_window ⊢ the tail; G closed again, innermost block first.
	for b := window; b >= 0; b-- {
		if tel.Antes[b] != nil {
			w = w.PromoteHyp(at(tel.Antes[b], b))
		}
		for i := len(tel.Binders) - 1; i >= 0; i-- {
			if tel.BlockOf[i] == b {
				w = w.ConclForAll(fresh[i])
			}
		}
	}
	return w.Core()
}

// freeIn reports whether v occurs free in t.
func freeIn(v core.VarTerm, t core.Term) bool {
	for _, f := range t.Frees(nil) {
		if f.Equals(v) {
			return true
		}
	}
	return false
}
