// Package chase is the diagram-chase closer: given the facts of an
// abelian diagram — modules on sets over one ring, homomorphisms
// between them, commuting squares and other equation laws, exactness,
// onto and one-to-one maps, submodules for the cosets — it decides one
// step of a chase (an equation between elements, a membership in an
// image or a kernel, the existence of a preimage, a coset equation, and
// the facts it reads when they are the goal: injectivity on a set,
// exactness, an equation between images, kernels and carriers) and
// hands the kernel the derivation. Elements have integer polynomial
// coefficients, in the leaf's scalars, over homomorphism words applied
// to generators. Equality is membership in the polynomial module the
// relations span (strong standard bases over ℤ, Hermite form for
// constants; no scalar is inverted), and a preimage is introduced where
// an exactness or an onto map provably provides one, for as many rounds
// as the author's depth. Deterministic and bounded, it records no key
// and searches nothing at replay. The laws it reads are installed by
// library/serve (SetLaws); a diagram with a cycle is refused.
package chase

import (
	"fmt"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Options are one call's parameters.
type Options struct {
	// Depth is the number of pull-back rounds after the reading of the
	// premises.
	Depth int
	// IndexArith allows a ∀-fact over degrees to be instantiated at a
	// degree the leaf spells differently from the instance (`n + 2`
	// against `(n + 1) + 1`), bridged by the nat ring normalizer; the
	// caller grants it where its proof scope allows nat arithmetic.
	IndexArith bool
	// Reader is the proof's reading of the record equations: the laws'
	// record projections and the scalar rings compute through its read,
	// so the equations are the proof's own cites. nil reads through the
	// fallback library/serve installs.
	Reader *omega.LibraryReader
}

// Result is what a call reports beside the theorem: the rounds it ran,
// the account of the diagram it read, and whether it used nat
// arithmetic — it rewrote a degree into its nat ring normal form, or a
// scalar ring of the diagram folded numeral literals. A theorem of such
// a chase stands on the nat-arithmetic laws, which the caller records.
type Result struct {
	Rounds   int
	Report   string
	NatArith bool
}

// Close decides the goal: the theorem closing it, or nil with the
// report saying what the diagram held and where the chase stopped. An
// error is a refusal — no laws installed, a cyclic diagram, a negative
// depth — before any chase was tried.
func Close(goal core.Prop, opts Options) (theorem *prop.PropWrapper, result Result, refusal error) {
	defer func() {
		if r := recover(); r != nil {
			if limit, ok := r.(_PolynomialLimit); ok {
				theorem = nil
				result.Report = limit.Error()
				refusal = nil
			} else {
				panic(r)
			}
		}
	}()
	return closeGoal(goal, opts)
}

func closeGoal(goal core.Prop, opts Options) (*prop.PropWrapper, Result, error) {
	laws := Installed()
	if laws == nil {
		return nil, Result{}, fmt.Errorf("the chase closer's laws are not installed (library/serve installs them)")
	}
	if opts.Depth < 0 {
		return nil, Result{}, fmt.Errorf("the chase depth is negative: %d", opts.Depth)
	}
	if red := reduceGoal(laws, goal); red != nil {
		thms := make([]*prop.PropWrapper, len(red.subs))
		var res Result
		for i, sub := range red.subs {
			thm, r, err := Close(sub, opts)
			res.Rounds = max(res.Rounds, r.Rounds)
			res.NatArith = res.NatArith || r.NatArith
			if err != nil || thm == nil {
				r.Report = fmt.Sprintf("%s, reduced to %d chase(s): part %d of %d, ⊢ %s, did not close\n%s",
					red.what, len(red.subs), i+1, len(red.subs), ext.PrintTerm(sub.Conclusion()), r.Report)
				return nil, r, err
			}
			thms[i] = thm
			res.Report += r.Report
		}
		thm := red.rebuild(thms)
		if !prop.IsStronger(thm, goal) {
			panic(fmt.Sprintf("chase: the reduced goal's certificate does not close it (engine invariant): %s", prop.PrintProp(thm)))
		}
		return thm, res, nil
	}
	d := newDiagram(laws, goal, opts.IndexArith, opts.Reader)
	if err := d.read(); err != nil {
		return nil, Result{Report: d.describe()}, err
	}
	for _, s := range d.sources {
		d.introduce(s)
	}
	d.saturate()
	if grew, err := d.growDegrees(); err != nil {
		return nil, Result{Report: d.describe()}, err
	} else if grew {
		d.saturate()
	}
	var lastErr error
	rounds := 0
	for {
		before := d.atomCount()
		thm, err := d.decide()
		if err == nil {
			return d.finish(thm), Result{Rounds: rounds, Report: d.describe(), NatArith: d.usedNatArith()}, nil
		}
		lastErr = err
		if d.atomCount() > before {
			// The goal named elements no premise had: saturate over them
			// and decide again before spending a round.
			d.saturate()
			continue
		}
		if rounds == opts.Depth {
			break
		}
		rounds++
		if !d.pullbacks(rounds) {
			d.notes = append(d.notes, fmt.Sprintf("round %d: nothing to pull back — the named facts are exhausted", rounds))
			break
		}
	}
	var b strings.Builder
	fmt.Fprintf(&b, "the chase did not close the goal after %d round(s) (depth %d): %s\n", rounds, opts.Depth, lastErr)
	b.WriteString(d.describe())
	return nil, Result{Rounds: rounds, Report: b.String()}, nil
}
