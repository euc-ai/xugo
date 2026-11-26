// by_tactic.go — the agent-facing `by` tactic: the math layer's
// premise-disciplined close (`By(premises…)` / `ByArith(…)`,
// prover/proof/fact.go) as a session move.
//
// `by` is `auto_with`'s DECLARED sibling. auto_with is a search: clear
// the noisy ∀-hyps, install the scoped lemmas, then run arith +
// autoexpand and keep whatever fired. by is a statement: THESE premises
// (resident hyps kept + named lemmas installed, ground where
// witnessed), THIS shaping, ONE refutation — exactly the `By` a
// proof will spell, executed by exactly the code that will replay it
// (proof.ApplyByStep → _ByStep.apply, the shared executor). What the
// session validates is therefore what the Go says, 1:1: emit renders
// the recorded composite back as `By(...)` with nothing lost in
// translation, and the closer choice is explicit — `by` never takes the
// arith fast-path silently, so the de-Arith trap (a recorded Arith()
// on a foundation-resident target) cannot arise from it.
//
// The 1:1 contract covers the premise INSTALL FORM too: a key-resolved
// premise is handed to the composite as the entry's statement, the form
// the Go twin's name cite resolves to (prover/proof/action.go
// resolveLemmaTarget), and what installs from it is the composite's one
// rule on both surfaces (proof.ApplyByStep and the executor's
// named-fact arm): a bare premise in the closer's clause form, a
// witnessed one in its stated form grounded at the tuple, an explicit
// type instance as it is.
//
// Close-or-fail: the clone must be fully proved — premise claim
// children closed against the entries they name, residual refuted — or the
// call errors and the session absorbs nothing (the auto_with
// convention).

package engine

import (
	"context"
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	extprop "github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/utils"
)

// ByHypSpec names ONE resident hypothesis of the focused goal as a
// premise of a `by` close. The hyp is located by 0-based index (the
// session's addressing convention — `inspect` shows the indices) but
// RECORDED by statement, so the persisted composite is index-free.
// Terms optionally grounds the ∀-hyp at those witnesses, in the hyp's
// own binder order (the math layer's `f.At(w…)`).
type ByHypSpec struct {
	HypIndex *int     `json:"hyp_index,omitempty"`
	Terms    []string `json:"terms,omitempty"`
	// Coefficient scales the premise (the Go Scaled(c, h); Lean's
	// linear_combination coefficient): the hyp, an equation l = r once
	// grounded, is followed by its congruence c·l = c·r under the
	// carrier's multiplication, added as a hypothesis and proved from
	// it. A term text, parsed in the goal's scope.
	Coefficient string `json:"coefficient,omitempty"`
}

// ByShapeReq is the wire form of the math layer's shaping values.
// Fields merge exactly as the By premise-list merge does.
type ByShapeReq struct {
	// Raw suppresses By's conditioning stage for this call (the
	// math layer's proof.Raw — the author's-hand escape hatch).
	Raw bool `json:"raw,omitempty"`
	// Normalized runs Basic() between the installs and the close.
	Normalized bool `json:"normalized,omitempty"`
	// PreNormalized runs Basic() BEFORE the denote/realize stage (the
	// fan-producing normalize; on its own it equals Normalized).
	PreNormalized bool `json:"pre_normalized,omitempty"`
	// Denoted runs Denote(n) + Basic() — the size-threshold denote, the
	// SEARCH form: the engine picks the term.
	Denoted int `json:"denoted,omitempty"`
	// Hilbert runs HilbertDenote() + Basic() — ε-term realization, the
	// search form.
	Hilbert bool `json:"hilbert,omitempty"`
	// DenotedAs names the term and the variable that abbreviates it —
	// the EXPLICIT form, the Go `DenotedAs(name, term)` a chapter
	// writes: the session validates the very shaping the file will
	// carry, where a close found under `denoted` proves only that SOME
	// denote closes the leaf. A By names at most one term, as in Go.
	DenotedAs *ByDenoteAsReq `json:"denoted_as,omitempty"`
	// HilbertDenotedAs is DenotedAs for an ε-term, the Go
	// `HilbertDenotedAs(name, term)`.
	HilbertDenotedAs *ByDenoteAsReq `json:"hilbert_denoted_as,omitempty"`
}

// ByChaseReq is the diagram-chase closer's parameter: the number of
// pull-back rounds (the Go `Depth(k)`).
type ByChaseReq struct {
	Depth int `json:"depth"`
}

// ByDenoteAsReq is the payload of an explicit denote shaping: the term,
// a text read in the goal's scope, and the name of the variable that
// stands for it.
type ByDenoteAsReq struct {
	Name string `json:"name"`
	Term string `json:"term"`
}

// shapes is the shaping values the request spells, in the order the Go
// premise list would hold them; term reads an explicit denote's term
// text at the goal. Conflicts between them are MergeByShapes's to
// refuse, as for a chapter's list.
func (r *ByShapeReq) shapes(term func(text string) (core.Term, error)) ([]proof.ByShape, error) {
	if r == nil {
		return nil, nil
	}
	var out []proof.ByShape
	if r.Raw {
		out = append(out, proof.Raw)
	}
	if r.Normalized {
		out = append(out, proof.Normalized)
	}
	if r.PreNormalized {
		out = append(out, proof.PreNormalized)
	}
	if r.Denoted > 0 {
		out = append(out, proof.Denoted(r.Denoted))
	}
	if r.Hilbert {
		out = append(out, proof.HilbertDenoted)
	}
	for _, explicit := range []struct {
		field string
		req   *ByDenoteAsReq
		shape func(string, proof.TermLike) proof.ByShape
	}{
		{"denoted_as", r.DenotedAs, proof.DenotedAs},
		{"hilbert_denoted_as", r.HilbertDenotedAs, proof.HilbertDenotedAs},
	} {
		if explicit.req == nil {
			continue
		}
		if explicit.req.Name == "" || explicit.req.Term == "" {
			return nil, fmt.Errorf("by_shape.%s takes {\"name\": the variable, \"term\": the term it abbreviates} — both",
				explicit.field)
		}
		t, err := term(explicit.req.Term)
		if err != nil {
			return nil, fmt.Errorf("by_shape.%s.term: %w", explicit.field, err)
		}
		name, _ := dsl.NormalizeTextSymbols(explicit.req.Name)
		out = append(out, explicit.shape(name, t))
	}
	return out, nil
}

// applyByOnClone implements the `by` tactic on the focused clone.
// Resolution happens here (keys against the registry, witnesses
// against the goal scope); execution is proof.ApplyByStep — the same
// composite By(...) runs. On success the clone is fully proved
// and carries ONE `by` ministep plus the auto-matched premise claims.
func (e *Engine) applyByOnClone(
	ctx context.Context,
	s *Session,
	clone *proof.GoalStackNode,
	req TacticReq,
) error {
	goal := clone.Goal
	if len(req.WithLemmas) == 0 && len(req.ByHyps) == 0 && !req.Arith && !req.Settac {
		// A premise-free by{settac} or by{arith} is a legal bare form —
		// the closer's own procedure is its content (BySets, ByArith,
		// fact.go).
		return fmt.Errorf("by: empty premise list — name the resident hyps (by_hyps) and/or the lemmas (with_lemmas) the close uses; a bare refutation is `auto`")
	}
	if req.Arith && req.Settac {
		return fmt.Errorf("by: arith and settac are mutually exclusive closers — pick one")
	}
	if req.Chase != nil {
		if req.Arith || req.Settac {
			return fmt.Errorf("by: chase is mutually exclusive with arith and settac — pick one closer")
		}
		if req.Chase.Depth < 0 {
			return fmt.Errorf("by: chase.depth is negative")
		}
		if len(req.WithLemmas) == 0 && len(req.ByHyps) == 0 {
			return fmt.Errorf("by: chase reads its diagram from the premises — name the module, homomorphism, exactness and element facts (by_hyps / with_lemmas)")
		}
	}
	if len(req.KeepHypIndices) > 0 || len(req.DropHypIndices) > 0 {
		// Declared on the shared tactic struct for auto_with, so the wire
		// door cannot refuse them by name; silently dropping them reads
		// as "your premise is missing" one failure later.
		return fmt.Errorf("by: keep_hyp_indices / drop_hyp_indices are auto_with's fields and by does not read them — " +
			"name the resident premises with by_hyps:[{hyp_index:…}]")
	}

	premises, srcs, certs, err := e.byPremiseSpecs(s, goal, req)
	if err != nil {
		return err
	}

	// Execute the composite. ApplyByStep panics with the By diagnostics
	// (premise economy, cleared-hyp list, the CNF-MISS split); recover
	// them into the error channel — the agent reads the same text a
	// chapter author would. A fault is none of them and goes up to the
	// command's boundary (utils.Failure, fault.go). A leaf the close refuted that Basic() would
	// have closed is reported on SUCCESS (the economy audit's first
	// probe): the session is where the spelling is chosen, and the
	// recorder would say the same only after a key was written.
	shapes, err := req.ByShape.shapes(func(text string) (core.Term, error) {
		return e.resolveTermWithFallback(text, goal, nil, s.familyScope())
	})
	if err != nil {
		return fmt.Errorf("by: %w", err)
	}
	var applyErr error
	var economy []string
	var closedBy string
	var records string
	var cuts []skeleton.WhistleEvent
	func() {
		defer func() {
			if r := utils.Failure(recover()); r != nil {
				applyErr = fmt.Errorf("by: %v", r)
			}
		}()
		if !proof.ApplyByStep(clone, s.env, ctx, proof.BySpec{
			Premises: premises,
			Shapes:   shapes,
			Arith:    req.Arith,
			Settac:   req.Settac,
			Chase:    req.Chase != nil,
			ChaseDepth: func() int {
				if req.Chase == nil {
					return 0
				}
				return req.Chase.Depth
			}(),
			Broadcast: req.Broadcast,
			Report:    func(finding string) { economy = append(economy, finding) },
			Closed:    func(route string) { closedBy = route },
			Records:   func(keys, plans []core.PropKey) { records = formatByRecords(keys, plans) },
			Whistle:   func(fired []skeleton.WhistleEvent) { cuts = fired },
		}) {
			applyErr = fmt.Errorf("by: the composite did not apply")
		}
	}()
	if applyErr != nil {
		// An arithmetic close of an equation at a ring on a carrier SET
		// decides only over atoms whose membership the premises hold —
		// the goal's, and those of the equation premises it combines:
		// name the ones they lack, so the author names the fact rather
		// than a law. Read against the hypotheses by_hyps named — the
		// composite clears the others before the closer runs.
		if req.Arith {
			var named []core.Term
			for _, h := range req.ByHyps {
				if h.HypIndex != nil && *h.HypIndex >= 0 && *h.HypIndex < goal.NumHyps() {
					named = append(named, goal.Hyp(*h.HypIndex))
				}
			}
			if set, atoms := omega.StructureRingMissingMemberships(named, goal.Conclusion()); len(atoms) > 0 {
				names := make([]string, len(atoms))
				for i, a := range atoms {
					names[i] = s.Spelling().Term(a)
				}
				applyErr = fmt.Errorf("%w\n  The structure ring reads the goal at the ring on %s but the premises hold no membership in it for %s: "+
					"a term's membership in the carrier must be named, as a hypothesis or a conjunct of one (a closure law decides a formed term's); "+
					"an equation premise over such a term is not read into the combination, and "+
					"the closer does not infer the membership from one in a subset.",
					applyErr, s.Spelling().Term(set), strings.Join(names, ", "))
			}
		}
		return applyErr
	}

	// Certify the premise claim children: generic α-key auto-match plus
	// the type-instance channel per key-loaded entry (the same two
	// channels `lemma` and auto_with run — a claim whose install
	// type-adapted α-differs from the entry and is invisible to the
	// generic pass), and a reading's claim from the reading's own
	// derived theorem.
	s.applyAutoMatchOnRoots([]*proof.GoalStackNode{clone}, s.autoMatchCache)
	for _, src := range srcs {
		s.applyAutoMatchTypeInstanceOnRoots(
			[]*proof.GoalStackNode{clone}, src.key, src.prop, nil, s.autoMatchCache)
	}
	s.closeOnCertificates([]*proof.GoalStackNode{clone}, certs)

	// Close-or-fail.
	if !clone.Proved() {
		var open []string
		for _, lf := range clone.UnsolvedLeaves() {
			open = append(open, extprop.PrintProp(lf.Goal))
		}
		return fmt.Errorf("by: the close succeeded but %d premise claim(s) did not certify — a premise is "+
			"certified by the entry it names or by a proved section of this session. A text premise that states "+
			"neither must be proved as its own section first; a key premise of a polymorphic law that did not "+
			"certify installed at a type instance the entry is not read back from — pin the instance with "+
			"type_specialize, or with term_specialize witnesses that bind every type variable of the law:\n  %s",
			len(open), strings.Join(open, "\n  "))
	}
	s.pendingApplyDiagnostics = append(s.pendingApplyDiagnostics, Diagnostic{
		Type: DiagByCloser, Message: "Closed by: " + closedBy,
	})
	if records != "" {
		s.pendingApplyDiagnostics = append(s.pendingApplyDiagnostics, Diagnostic{
			Type: DiagByRecords, Message: records,
		})
	}
	for _, finding := range economy {
		s.pendingApplyDiagnostics = append(s.pendingApplyDiagnostics, Diagnostic{
			Type:    DiagByEconomy,
			Message: finding + "\n  In a session: the same by with by_shape:{\"normalized\":true}.",
		})
	}
	if len(cuts) > 0 {
		s.pendingApplyDiagnostics = append(s.pendingApplyDiagnostics, byWhistleDiagnostic(cuts))
	}
	return nil
}

// byWhistleDiagnostic is the by_whistle diagnostic of a close that
// fired the divergence whistle (proof.BySpec.Whistle): the cuts, each
// with the goal it was made at, and what they cost the step once it is
// written in Go.
func byWhistleDiagnostic(cuts []skeleton.WhistleEvent) Diagnostic {
	described := make([]string, len(cuts))
	for i, cut := range cuts {
		described[i] = tactic.DescribeWhistleCut(cut)
	}
	return Diagnostic{
		Type: DiagByWhistle,
		Message: fmt.Sprintf("The close fired the divergence whistle %d time(s):%s\n"+
			"  The close stands in this session, but the recorder refuses a member whose replay fires the whistle, "+
			"so the Go transcription of this step does not record as written. %s",
			len(cuts), tactic.ListWhistleCuts(described), tactic.WhistleCutAdvice),
	}
}

// byPremiseSpecs resolves a `by` request's premise lists — the resident
// hypotheses of by_hyps and the named entries of with_lemmas — into the
// composite's premises, exactly as the `by` tactic does; `by_induction`
// resolves its extras through the same door. srcs are the key-loaded
// entries whose claim children the type-instance auto-match certifies,
// certs the derived theorems of readings and explicitly cited local sections.
func (e *Engine) byPremiseSpecs(s *Session, goal core.Prop, req TacticReq) (
	premises []proof.ByPremiseSpec, srcs []byInstallSource, certs []core.Prop, err error,
) {
	// Resident premises: locate by index now, record by statement.
	for i, h := range req.ByHyps {
		if h.HypIndex == nil {
			return nil, nil, nil, fmt.Errorf("by: by_hyps[%d] requires hyp_index (use `inspect` to locate the hyp)", i)
		}
		idx := *h.HypIndex
		if idx < 0 || idx >= goal.NumHyps() {
			return nil, nil, nil, fmt.Errorf("by: by_hyps[%d].hyp_index %d out of range [0, %d)", i, idx, goal.NumHyps())
		}
		hypTerm := goal.Hyp(idx)
		var witnesses []core.Term
		if len(h.Terms) > 0 {
			if nextStatedBinder(hypTerm).IsZero() {
				return nil, nil, nil, fmt.Errorf("by: by_hyps[%d] (hyp %d: %s) is not ∀-headed and binds no ∀ behind an antecedent — witnesses need a ∀-hyp",
					i, idx, ext.PrintTerm(hypTerm))
			}
			ws, adapt, werr := e.resolveInstantiateWitnesses(goal, hypTerm, h.Terms, false, nil, s.familyScope())
			if werr != nil {
				return nil, nil, nil, fmt.Errorf("by: by_hyps[%d]: %w", i, werr)
			}
			if adapt != nil {
				return nil, nil, nil, fmt.Errorf("by: by_hyps[%d]: the witnesses need a type-adapted instance of hyp %d — "+
					"ground it with `instantiate` (which re-derives the hyp from the entry stating it) before the by",
					i, idx)
			}
			witnesses = ws
		}
		var coefficient core.Term
		if h.Coefficient != "" {
			c, cerr := e.resolveCoefficient(h.Coefficient, goal, coefficientType(hypTerm, true, nil), s.familyScope())
			if cerr != nil {
				return nil, nil, nil, fmt.Errorf("by: by_hyps[%d]: %w", i, cerr)
			}
			coefficient = c
		}
		premises = append(premises, proof.ByPremiseSpec{
			Install:     extprop.MakeProp(hypTerm),
			Witnesses:   witnesses,
			Resident:    true,
			Coefficient: coefficient,
			Describe:    fmt.Sprintf("hyp %d", idx),
		})
	}

	// Named premises: resolve exactly as `lemma` would, then hand the
	// resolved install form to the composite. An explicit type_specialize
	// σ applies BEFORE term_specialize (binder types lose their free
	// type-vars before term-level unification sees them — `lemma`'s
	// order) and marks the premise EXACT, so the composite installs the
	// instantiated form verbatim instead of letting the speculative
	// goal-side adaptation override the agent's σ (the `lemma` dispatch's
	// explicit-σ fork, on the premise path).
	// certs are the readings among the premises: derived theorems no
	// entry states, which certify their own claim children.
	for i, l := range req.WithLemmas {
		if l.Flip {
			return nil, nil, nil, fmt.Errorf("by: with_lemmas[%d]: flip is a simp_with orientation — a by premise has none", i)
		}
		if l.Normalized {
			return nil, nil, nil, fmt.Errorf("by: with_lemmas[%d]: normalized is a simp_with rule form — a by premise has no form to choose: "+
				"bare it installs in the closer's clause form, witnessed in its stated form grounded at the tuple", i)
		}
		if l.HypIndex != nil {
			return nil, nil, nil, fmt.Errorf("by: with_lemmas[%d]: hyp_index names a resident hypothesis as a `simp_with` rule — a by premise names its hypothesis in by_hyps", i)
		}
		if l.ReadAt != nil {
			// A structure law read at an instance (reading.go).
			specs, cert, src, rerr := e.byReadingPremises(s, goal, l, premises)
			if rerr != nil {
				return nil, nil, nil, fmt.Errorf("by: with_lemmas[%d]: %w", i, rerr)
			}
			premises = append(premises, specs...)
			if cert != nil {
				certs = append(certs, cert)
			}
			for _, spec := range specs {
				if spec.Clause != nil {
					certs = append(certs, spec.Clause)
				}
			}
			if src != nil {
				srcs = append(srcs, *src)
			}
			continue
		}
		// The agent's own spelling names the premise in diagnostics.
		cited := l.Key
		lemmaReq := TacticReq{
			Type:      "lemma",
			LemmaKey:  l.Key,
			LemmaText: l.Text,
		}
		lemmaProp, lerr := e.resolveLemma(s, lemmaReq, goal)
		if lerr != nil {
			return nil, nil, nil, fmt.Errorf("by: with_lemmas[%d]: %w", i, lerr)
		}
		if lemmaProp == nil {
			return nil, nil, nil, fmt.Errorf("by: with_lemmas[%d]: missing key or text", i)
		}
		describe := cited
		if describe == "" {
			// Rune-safe clip: this label lands in RPC diagnostics, whose
			// marshal is strict-UTF-8 (see abbreviateString).
			describe = abbreviateTerm(lemmaProp.Conclusion(), 60)
		}
		// rowProp keeps the PRE-σ resolution for the post-close
		// type-instance auto-match: the claim child of a σ-instantiated
		// premise is an instance of the ENTRY, not of the σ'd form.
		rowProp := lemmaProp
		// An explicitly named local statement has the same certificate
		// channel as a structure reading. Keep its proved, stated form
		// so a type instance can certify after the close; localSource is
		// that theorem, the source an explicit instance's clause is
		// formed from.
		var localSource core.Thm
		if l.Key == "" {
			for _, section := range s.sections {
				if !section.root.Proved() || !section.root.Goal.AlphaEquals(rowProp) {
					continue
				}
				if stated := extprop.WeakenTo(section.root.PromisedThm(), rowProp); stated != nil {
					localSource = core.AsThm(stated)
					certs = append(certs, stated)
					break
				}
			}
		}
		exact := false
		var fixed core.VarTypePredicate = utils.EmptyPredicate[core.VarType]
		if len(l.TypeSpecialize) > 0 {
			specialized, goalLetters, sErr := buildSpecializedLemma(lemmaProp, l.TypeSpecialize, goal)
			if sErr != nil {
				return nil, nil, nil, fmt.Errorf("by: with_lemmas[%d]: %w", i, sErr)
			}
			lemmaProp, fixed = specialized, goalLetters
			exact = true
		}
		// The term_specialize table: a PREFIX grounds the premise
		// positionally, a SPARSE one seeds the apply rung
		// (byPremiseTable). Witnesses that bind every type variable of
		// a polymorphic law ARE an explicit instance: Go's typed `.At`
		// installs exactly the instance its witnesses infer, and this
		// is its session twin — so the premise is EXACT, as under
		// type_specialize. The instance may be stated over the goal's
		// own type letters (the law's `B` read at `set(A)`, its two
		// letters swapped); what makes it explicit is that the tuple
		// left none of the LAW's variables free. Left inexact, the law
		// took its clause form at the inferred instance, whose claim
		// child the type-instance auto-match does not read back to the
		// entry (Normalize and type instantiation do not commute): a
		// close that succeeded and a premise that "did not certify".
		install := lemmaProp
		witnesses, named, adapted, typesPinned, terr := e.byPremiseTable(s, goal, lemmaProp, l.TermSpecialize, fixed, nil)
		if terr != nil {
			return nil, nil, nil, fmt.Errorf("by: with_lemmas[%d]: %w", i, terr)
		}
		if len(witnesses) > 0 {
			install = adapted
			if !exact && typesPinned {
				exact = true
			}
		}
		// The install is the served form — the entry's statement —
		// exactly as the Go twin installs a named dep
		// (prover/proof/action.go resolveLemmaTarget: normalize LAST).
		// Install and statement coincide, so no reference form is set.
		var reference core.Prop
		if l.Key != "" {
			srcs = append(srcs, byInstallSource{key: core.PropKey(l.Key), prop: rowProp})
		}
		var coefficient core.Term
		if l.Coefficient != "" {
			if len(named) > 0 {
				return nil, nil, nil, fmt.Errorf("by: with_lemmas[%d]: coefficient on a premise pinned by name (a sparse term_specialize) — "+
					"ground it positionally and scale the instance", i)
			}
			c, cerr := e.resolveCoefficient(l.Coefficient, goal, coefficientType(install.Conclusion(), exact, fixed), s.familyScope())
			if cerr != nil {
				return nil, nil, nil, fmt.Errorf("by: with_lemmas[%d]: %w", i, cerr)
			}
			coefficient = c
		}
		// An explicit instance of a key premise, or of a text premise a
		// proved section of the session states, carries the clause form
		// Go's typed instance of the entry or of the section's local
		// installs, Normalize first and the types after
		// (proof.ExplicitInstanceClause): the session's close installs
		// what the Go spelling of the premise installs, and the clause
		// obligation certifies from that derived form. A text premise no
		// section states has no source to form it from.
		var clause core.Prop
		if exact {
			source := localSource
			if l.Key != "" {
				var serr error
				if source, serr = e.resolveLemmaThm(s, lemmaReq, goal); serr != nil {
					return nil, nil, nil, fmt.Errorf("by: with_lemmas[%d]: %w", i, serr)
				}
			}
			if source != nil {
				clause = proof.ExplicitInstanceClause(source, install)
				certs = append(certs, clause)
			}
		}
		premises = append(premises, proof.ByPremiseSpec{
			Install:     install,
			Reference:   reference,
			Witnesses:   witnesses,
			Named:       named,
			Exact:       exact,
			Clause:      clause,
			Coefficient: coefficient,
			Describe:    describe,
			SourceKey:   core.PropKey(l.Key),
		})
	}
	return premises, srcs, certs, nil
}

// coefficientType is the type a scaled premise's coefficient is read
// at: the type of the sides of the equation the premise states, under
// its ∀-prefix and its guards. The premise's types are settled where
// pinned says every type letter of it is, or where the equation's type
// spells only letters settled admits — the goal's own. nil where the
// premise states no equation between terms, or where the install
// decides the carrier: the coefficient is then read with no type
// expected of it.
func coefficientType(premise core.Term, pinned bool, settled core.VarTypePredicate) core.HolType {
	t := premise
	for {
		if all := ext.MatchesFORALL(t); !all.IsZero() {
			t = all.Body()
			continue
		}
		if _, rest, ok := ext.MatchesIMPLY(t); ok {
			t = rest
			continue
		}
		break
	}
	l, _, ok := core.MatchesEQ(t)
	if !ok || l.Type().Equals(core.TypeBool()) {
		return nil
	}
	if !pinned {
		for _, v := range l.Type().TypeVars() {
			if settled == nil || !settled(v) {
				return nil
			}
		}
	}
	return l.Type()
}

// resolveCoefficient reads a scaled premise's coefficient at carrier,
// the type of the equation it scales (coefficientType): a cast or a
// numeral written `&…` is the carrier's, as the goal prints it. With
// no carrier the text is read as it stands.
func (e *Engine) resolveCoefficient(spec string, goal core.Prop, carrier core.HolType, family *familyScope) (core.Term, error) {
	c, err := e.resolveTermWithFallback(spec, goal, carrier, family)
	if err == nil {
		return c, nil
	}
	if carrier == nil {
		return nil, fmt.Errorf("coefficient: %w", err)
	}
	return nil, fmt.Errorf("coefficient, read at %s — the type of the equation it scales: %w", ext.FormatType(carrier), err)
}

// byInstallSource is a key-loaded premise's entry, for the type-instance
// close of its claim child: the key, and the entry's statement before
// any σ.
type byInstallSource struct {
	key  core.PropKey
	prop core.Prop
}

// byPremiseTable reads a premise's term_specialize table against its
// stated form. A PREFIX table grounds the premise positionally (the
// plain add + Specialize path; the apply rung then reads the grounded
// instance as a resident head): witnesses, in binder order, with the
// stated form type-adapted to them and whether they bind every type
// variable of it. A SPARSE table — a binder the goal must pin sits
// before a named one — seeds the apply rung (Lean's `apply law
// (R := r)`): the premise installs nothing on its own, the rung reads
// the rest off the goal and the context, and it must fire
// (proof.ByPremiseSpec.Named); its terms parse against the goal's
// scope, and the rung checks their types at each type instance it
// tries. An empty table returns nothing. fixed admits the type letters
// of stated that are the goal's own — a reading's hypothesis letters,
// the letters an explicit type_specialize read at the goal's — which no
// witness instantiates and no freshening renames. renamed are the
// binders stated holds under another name than their law gives them
// (sessionReading.renamedBinders; nil for a premise that is no
// reading): a key spelling the law's name is read as that binder.
func (e *Engine) byPremiseTable(
	s *Session, goal, stated core.Prop, table map[string]string, fixed core.VarTypePredicate, renamed map[string]string,
) (
	witnesses []core.Term, named []proof.NamedWitness, adapted core.Prop, typesPinned bool, err error,
) {
	if len(table) == 0 {
		return nil, nil, nil, false, nil
	}
	if table, err = textBinderTable(table); err != nil {
		return nil, nil, nil, false, err
	}
	for lawName, held := range renamed {
		spelling, byLawName := table[lawName]
		if !byLawName {
			continue
		}
		if _, both := table[held]; both {
			return nil, nil, nil, false, fmt.Errorf("term_specialize: %q and %q name one binder — the law states it %s "+
				"and this reading holds it as %s; name it once",
				lawName, held, utils.FormatSubscript(lawName), utils.FormatSubscript(held))
		}
		delete(table, lawName)
		table[held] = spelling
	}
	if termSpecializeNamesPrefix(stated, table) {
		ws, adapted, typesPinned, werr := e.resolveTermSpecializeWitnesses(stated, table, goal, s.familyScope(), fixed)
		if werr != nil {
			return nil, nil, nil, false, werr
		}
		for _, w := range ws {
			if w.free {
				return nil, nil, nil, false, fmt.Errorf("%q names a sequent-level free variable — "+
					"free-var instantiation is `lemma`+term_specialize's path, not a by premise's", w.name)
			}
			witnesses = append(witnesses, w.witness)
		}
		return witnesses, nil, adapted, typesPinned, nil
	}
	available := collectGuardedForAllBinderNames(stated)
	for _, name := range guardedForAllBinderOrder(stated) {
		spelling, present := table[name]
		if !present {
			continue
		}
		w, perr := e.resolveTermWithFallback(spelling, goal, nil, s.familyScope())
		if perr != nil {
			return nil, nil, nil, false, fmt.Errorf("term_specialize[%s]: %w", name, perr)
		}
		named = append(named, proof.NamedWitness{Binder: name, Witness: w})
	}
	for k := range table {
		if !available[k] {
			return nil, nil, nil, false, fmt.Errorf("term_specialize: ∀-binder %q not found in the "+
				"lemma's stated binders; available: %v", k, printedBinderNamesWith(available, renamed))
		}
	}
	return nil, named, nil, false, nil
}

// byReadingPremises resolves one `by` premise that is a law read at an
// instance (LemmaWithSpec.ReadAt) into the composite's premises, as the
// Go macro resolves `law.Read(instance)` (prover/proof/fact.go):
//
//   - at an instance ENTRY the reading is a named premise like any
//     other — bare in the closer's clause form, witnessed in its stated
//     form — whose claim child the derived theorem certifies (cert);
//   - under a RESIDENT hypothesis it is that hypothesis's consequence,
//     kept beside it (proof.ByPremiseSpec.ReadingUnder);
//   - under a resident hypothesis, where the law carries a type letter
//     no component fixes, the reading could not be used — a
//     hypothesis's type variables are rigid in the leaf — so the
//     premise is the law itself cited beside the hypothesis, a tuple
//     grounding the law at the components and the witnesses, each at
//     the binder the law states it at (proof.LooseCiteTuple; source
//     certifies the law's claim child by its key).
//
// listed are the premises resolved so far: a hypothesis already named
// in by_hyps is not added a second time.
func (e *Engine) byReadingPremises(s *Session, goal core.Prop, l LemmaWithSpec, listed []proof.ByPremiseSpec) (
	specs []proof.ByPremiseSpec, cert core.Prop, source *byInstallSource, err error,
) {
	if l.Text != "" {
		return nil, nil, nil, fmt.Errorf("read_at reads a law at an instance — name the law by its key, or a proved section of this session by its id, not by text")
	}
	if len(l.TypeSpecialize) > 0 {
		return nil, nil, nil, fmt.Errorf("read_at with type_specialize: the reading's type letters are the instance's, " +
			"fixed by its components or pinned off the goal or the tuple — drop type_specialize")
	}
	reading, err := e.resolveReading(s, goal, l.Key, l.ReadAt)
	if err != nil {
		return nil, nil, nil, err
	}
	stated := reading.statement()
	// The reading's hypothesis letters are the goal's own, fixed in every
	// reading of it: a witness is read at them, never at a letter of
	// the law's held apart from them.
	witnesses, named, adapted, typesPinned, err := e.byPremiseTable(
		s, goal, stated, l.TermSpecialize, proof.ReadingFixedLetters(reading.theorem), reading.renamedBinders())
	if err != nil {
		return nil, nil, nil, err
	}
	var coefficient core.Term
	if l.Coefficient != "" {
		if len(named) > 0 {
			return nil, nil, nil, fmt.Errorf("coefficient on a premise pinned by name (a sparse term_specialize) — " +
				"ground it positionally and scale the instance")
		}
		scaled, pinned := stated, false
		if len(witnesses) > 0 {
			scaled, pinned = adapted, typesPinned
		}
		carrier := coefficientType(scaled.Conclusion(), pinned, proof.ReadingFixedLetters(reading.theorem))
		if coefficient, err = e.resolveCoefficient(l.Coefficient, goal, carrier, s.familyScope()); err != nil {
			return nil, nil, nil, err
		}
	}

	under := reading.hypothesis()
	if under == nil {
		install, exact := stated, false
		if len(witnesses) > 0 {
			install, exact = adapted, typesPinned
		}
		// An explicit instance of the reading carries the clause form
		// Go's By gives `At(Law.Read(Entry), w…)` (proof.
		// ExplicitReadingClause), derived from the reading itself, so a
		// reading of a proved section's law takes it the same way.
		var clause core.Prop
		if exact {
			clause = proof.ExplicitReadingClause(core.AsThm(reading.theorem), install)
		}
		return []proof.ByPremiseSpec{{
			Install:     install,
			Witnesses:   witnesses,
			Named:       named,
			Exact:       exact,
			Clause:      clause,
			Coefficient: coefficient,
			Reading:     reading.record,
			Describe:    reading.describe,
		}}, reading.theorem, nil, nil
	}

	if reading.record.Inner == nil || len(witnesses) == 0 {
		loose, lerr := proof.ReadingIsLoose(reading.law, reading.instance.Conclusion())
		if lerr != nil {
			return nil, nil, nil, lerr
		}
		if loose {
			if len(named) > 0 {
				return nil, nil, nil, fmt.Errorf("%s carries a type letter its instance does not fix, so it is cited as "+
					"the law beside the hypothesis, grounded positionally — give term_specialize as a prefix of the "+
					"reading's binders", reading.describe)
			}
			lawStatement := core.MakeProp(reading.law.Conclusion())
			// The record keeps what the law was read at: emit spells the
			// premise as the reading the author wrote, `Law.Read(fact)`,
			// whose Go macro makes this same expansion.
			cited := proof.ByPremiseSpec{Install: lawStatement, Coefficient: coefficient, Reading: reading.record, Describe: reading.describe}
			if len(witnesses) > 0 {
				tuple, terr := proof.LooseCiteTuple(reading.law, reading.instance.Conclusion(), witnesses)
				if terr != nil {
					return nil, nil, nil, fmt.Errorf("%s carries a type letter its instance does not fix, so it is cited as "+
						"the law beside the hypothesis: %w", reading.describe, terr)
				}
				cited.Witnesses = tuple
			}
			specs = append(specs, cited)
			if reading.record.Inner != nil {
				if err := proof.CheckLooseReadingCompanion(reading.inner.law, reading.inner.instance.Conclusion()); err != nil {
					return nil, nil, nil, err
				}
				// The outer law reads the inner structure theorem, not
				// the bottom hypothesis from which it was derived.
				specs = append(specs, proof.ByPremiseSpec{
					Install: reading.instance, ReadingUnder: true,
					Reading:  reading.record.Inner,
					Describe: "the structure instance of " + reading.describe,
				})
				return specs, reading.instance, reading.lawSource(lawStatement), nil
			}
			hypothesisListed := false
			for _, p := range listed {
				if p.Resident && len(p.Witnesses) == 0 && p.Install.Conclusion().AlphaEquals(under) {
					hypothesisListed = true
				}
			}
			if !hypothesisListed {
				specs = append(specs, proof.ByPremiseSpec{
					Install:  extprop.MakeProp(under),
					Resident: true,
					Describe: "the hypothesis " + reading.describe + " is under",
				})
			}
			return specs, nil, reading.lawSource(lawStatement), nil
		}
	}

	install, witnesses, err := proof.ReadingAtWitnessTypes(reading.theorem, witnesses)
	if err != nil {
		return nil, nil, nil, fmt.Errorf("%s: %w", reading.describe, err)
	}
	return []proof.ByPremiseSpec{{
		Install:      install,
		Witnesses:    witnesses,
		Named:        named,
		ReadingUnder: true,
		Coefficient:  coefficient,
		Reading:      reading.record,
		Describe:     reading.describe,
	}}, install, nil, nil
}

// formatByRecords renders the rows the recorder would write for a close —
// certificate keys (its refutes) and conditioning plans (its grounding) —
// as the by_records diagnostic. "Records nothing" is the keyless case:
// the apply rung, a shaping, a prelude close, arith/chase. An author
// reads this before a blob is written, where today only the recorder's
// dry run says it. The session's `by` close is its own, so where the
// recorder's route differs the dry run stays the keylessness oracle.
func formatByRecords(keys, plans []core.PropKey) string {
	if len(keys) == 0 && len(plans) == 0 {
		return "Records nothing: the recorder writes no CNF key and no conditioning plan for this close."
	}
	var parts []string
	if len(keys) > 0 {
		parts = append(parts, fmt.Sprintf("%d key%s (%s)", len(keys), byRecordsPlural(len(keys)), byRecordsJoinKeys(keys)))
	}
	if len(plans) > 0 {
		parts = append(parts, fmt.Sprintf("%d plan%s (%s)", len(plans), byRecordsPlural(len(plans)), byRecordsJoinKeys(plans)))
	}
	return "Records " + strings.Join(parts, ", ") + "."
}

func byRecordsPlural(n int) string {
	if n == 1 {
		return ""
	}
	return "s"
}

func byRecordsJoinKeys(keys []core.PropKey) string {
	spelled := make([]string, len(keys))
	for i, k := range keys {
		spelled[i] = string(k)
	}
	return strings.Join(spelled, ", ")
}
