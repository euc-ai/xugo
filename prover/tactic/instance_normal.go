package tactic

// instance_normal.go — the form an instance is handed over in.
//
// An instantiation boundary hands its instance over β-normal, and with
// every record projection applied to a value its record's constructor
// builds computed to the part: a ∀-fact grounded at its witnesses (the
// specialize step), a law read at a structure fact, a definition
// unfolded, a Simp rule's rewrite. `ring_add(mk_ring(a, …, g))` is `a`.
// A projection also reads through a definition whose value is a
// structure, built by a constructor directly (`complex_module(P, n)`)
// or through another such definition (`homology_module(P, n)`):
// `complex_module(P, n).carrier` is `P.terms(n)`. Such a definition is
// unfolded under a projection only, so `module_on(R, complex_module(P,
// n))` keeps its spelling. Which definitions those are is the
// registry's to say (RecordReductions): none into a record that is a
// type of elements, so `re(z * w)` stands as spelled. Every step is the
// kernel's: an instance of the projection equation, or of the
// definition carried under the projection by congruence.
//
// The equations are the corpus's, installed by library/serve
// (InstallRecordNormal) from the record and definition doors; until
// they are installed the form is β-normal alone. A proof reads each
// equation it computes with as it reads any library theorem
// (LibraryRead), so its recorded dependencies hold the equations its
// instances needed. A matcher comparing a term with the instance the
// kernel will hand over computes the same form from the equations'
// statements (InstanceNormalTerm), reading nothing.

import (
	"context"
	"slices"
	"sync"
	"sync/atomic"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// LibraryRead reads a record equation's theorem by its registered name:
// the proof's read of a library theorem.
type LibraryRead func(entry string) *prop.PropWrapper

// RecordEquation is one equation the normal form computes with.
type RecordEquation struct {
	// Head is the constant the equation's left side applies: the
	// projection, or the defined constant.
	Head string
	// Constructor is, for a projection equation, the record's
	// constructor; empty for a definition.
	Constructor string
	// Entry is the equation's registered name, the name a proof reads it
	// by.
	Entry string
	// Statement is the equation as stated, ∀-closed.
	Statement core.Prop
}

type recordTable struct {
	// generation counts the tables installed up to this one.
	generation uint64
	// installed is the equations as installed, projections then valued.
	installed []RecordEquation
	// projections: per projection constant, its equations.
	projections map[string][]RecordEquation
	// constructors: the records' constructors.
	constructors map[string]bool
	// valued: per definition a projection reads through, its equation.
	valued map[string]RecordEquation
	// arity: per constructor and per valued definition, the number of
	// arguments its equation applies it to — what a record value is
	// applied to in full.
	arity map[string]int
	// fallback reads an equation where no proof is being built.
	fallback LibraryRead
}

var (
	installedRecords atomic.Pointer[recordTable]
	installMu        sync.Mutex
)

// InstallRecordNormal installs the record equations of the normal form,
// replacing what was installed: each projection's equation at its
// record's constructor, and the definitions a projection reads through.
// fallback reads an equation for a caller that builds no proof (a
// session's step, a bundle's law). Installing the equations already
// installed, by entry and in order, keeps the table and its generation.
func InstallRecordNormal(projections, valued []RecordEquation, fallback LibraryRead) {
	installMu.Lock()
	defer installMu.Unlock()
	installed := slices.Concat(projections, valued)
	sameEntry := func(a, b RecordEquation) bool {
		return a.Head == b.Head && a.Constructor == b.Constructor && a.Entry == b.Entry
	}
	previous := installedRecords.Load()
	if previous != nil && slices.EqualFunc(previous.installed, installed, sameEntry) {
		return
	}
	tb := newRecordTable(projections, valued)
	tb.fallback = fallback

	tb.generation = 1
	if previous != nil {
		tb.generation = previous.generation + 1
	}
	installedRecords.Store(tb)
}

func newRecordTable(projections, valued []RecordEquation) *recordTable {
	tb := &recordTable{
		installed:    slices.Concat(projections, valued),
		projections:  map[string][]RecordEquation{},
		constructors: map[string]bool{},
		valued:       map[string]RecordEquation{},
		arity:        map[string]int{},
	}
	for _, eq := range projections {
		if eq.Constructor == "" {
			panic("InstallRecordNormal: a projection equation names its record's constructor")
		}
		tb.projections[eq.Head] = append(tb.projections[eq.Head], eq)
		tb.constructors[eq.Constructor] = true
		_, lhs, _ := equationParts(eq.Statement.Conclusion())
		if _, args := ext.MatchesApply(lhs); len(args) == 1 {
			_, built := ext.MatchesApply(args[0])
			tb.arity[eq.Constructor] = len(built)
		}
	}
	for _, eq := range valued {
		if _, twice := tb.valued[eq.Head]; twice {
			panic("InstallRecordNormal: a definition is installed twice: " + eq.Head)
		}
		tb.valued[eq.Head] = eq
		_, lhs, _ := equationParts(eq.Statement.Conclusion())
		_, args := ext.MatchesApply(lhs)
		tb.arity[eq.Head] = len(args)
	}
	return tb
}

// NewRecordTermNormalizer returns the instance normal form computed from
// the supplied statements. It neither installs a global table nor reads
// a theorem, so a source generator can compare record carriers without
// changing a proof environment.
func NewRecordTermNormalizer(projections, valued []RecordEquation) func(core.Term) core.Term {
	tb := newRecordTable(projections, valued)
	return func(t core.Term) core.Term {
		t = ext.BetaCollapse(context.Background(), t)
		reduced, changed := tb.termNormal(t)
		if !changed {
			return t
		}
		return ext.BetaCollapse(context.Background(), reduced)
	}
}

// RecordNormalGeneration counts the tables installed so far, 0 before
// the first: a view computed in the normal form is current while the
// generation it was computed at is.
func RecordNormalGeneration() uint64 {
	if tb := installedRecords.Load(); tb != nil {
		return tb.generation
	}
	return 0
}

// InstanceNormal is the normal form as a rewrite, reading each equation
// it computes with through read; a nil read reads through the installed
// fallback.
func InstanceNormal(read LibraryRead) prop.Rewrite {
	tb := installedRecords.Load()
	if tb == nil || len(tb.projections) == 0 {
		return prop.DeepBeta
	}
	if read == nil {
		read = tb.fallback
	}
	if read == nil {
		return prop.DeepBeta
	}
	return prop.DeepRewrite(prop.BetaRewrite, tb.step(read))
}

// RecordProjections is the record step alone as a rewrite, without β,
// for a caller that computes the applications itself and leaves some
// standing: the chase reads a leaf with every one computed and a law's
// instance with the applications the law states kept (chase.Laws.reading). A nil read reads through the installed fallback;
// with no table installed it is nil.
func RecordProjections(read LibraryRead) prop.Rewrite {
	tb := installedRecords.Load()
	if tb == nil || len(tb.projections) == 0 {
		return nil
	}
	if read == nil {
		read = tb.fallback
	}
	if read == nil {
		return nil
	}
	return prop.DeepRewrite(tb.step(read))
}

// InstanceNormalTactic hands a goal over in the instance normal form:
// its conclusion and every hypothesis rewritten by InstanceNormal(read),
// each through the kernel's equation — the apply rung's record reading
// of a leaf whose context holds a statement up to this form (the
// RecordRead step in prover/proof), so a hypothesis spelled with a
// projection and a cited instance spelled at the part meet. One child,
// the normalized goal, each hypothesis descending from its own slot;
// nil where nothing changes.
func InstanceNormalTactic(read LibraryRead) Tactic {
	rewrite := InstanceNormal(read)
	return func(goal Prop) *SubGoals {
		conclBridge := rewrite(goal.Conclusion())
		if conclBridge != nil && prop.Rhs(conclBridge).AlphaEquals(goal.Conclusion()) {
			conclBridge = nil
		}
		numHyps := goal.NumHyps()
		hypBridges := make([]*prop.PropWrapper, numHyps)
		changedHyp := false
		for i := range numHyps {
			h := goal.Hyp(i)
			if hb := rewrite(h); hb != nil && !prop.Rhs(hb).AlphaEquals(h) {
				hypBridges[i] = hb
				changedHyp = true
			}
		}
		if conclBridge == nil && !changedHyp {
			return nil
		}
		newConcl := goal.Conclusion()
		if conclBridge != nil {
			newConcl = prop.Rhs(conclBridge)
		}
		newHyps := make([]core.Term, numHyps)
		for i := range numHyps {
			newHyps[i] = goal.Hyp(i)
			if hypBridges[i] != nil {
				newHyps[i] = prop.Rhs(hypBridges[i])
			}
		}
		child := makeImageProp(newConcl, newHyps)
		reconstruct := func(thms ...Prop) Prop {
			result := prop.WrapProp(thms[0])
			if conclBridge != nil && !thms[0].Conclusion().Equals(F) {
				result = conclBridge.EqSym().EqMP(result)
			}
			for i := range numHyps {
				if hypBridges[i] == nil {
					continue
				}
				la := hypBridges[i].LeftAssume()
				if result.HasHyp(la.Conclusion()) {
					result = la.DeriveTrans(result)
				}
			}
			return result
		}
		return MakeTrackedSubGoals(goal, reconstruct, [][]int{hypSuccessorsOf(child, newHyps)}, child)
	}
}

// StatedRead reads a record equation as its installed statement, for a
// derivation that states rather than proves. A kernel rule with a
// statement among its premises derives a statement (core, deriveProp),
// so the equation's theorem read there would be built for a certificate
// the result does not carry.
func StatedRead(entry string) *prop.PropWrapper {
	if tb := installedRecords.Load(); tb != nil {
		for _, eq := range tb.installed {
			if eq.Entry == entry {
				return prop.WrapProp(eq.Statement)
			}
		}
	}
	panic("StatedRead: " + entry + " is no installed record equation")
}

// InstanceNormalTerm is t in the normal form, for a matcher comparing an
// instance it builds with the one the kernel hands over: computed from
// the equations' statements, with nothing read. The record steps and β
// alternate to a fixpoint, as the kernel's deep rewrite merges them: a
// projection of a packed value can stand only once a β-redex the step
// before it left is reduced — `category_compose(simplex_category, g, f)`
// opens to `(λg f. mk_morphism(triple_source(f), …))(…)`, whose
// `triple_source(coface_map(n, i))` is a redex only after β — and the
// form a matcher compares with is the kernel's.
func InstanceNormalTerm(t core.Term) core.Term {
	ctx := context.Background()
	t = ext.BetaCollapse(ctx, t)
	tb := installedRecords.Load()
	if tb == nil || len(tb.projections) == 0 {
		return t
	}
	for {
		reduced, changed := tb.termNormal(t)
		if !changed {
			return t
		}
		t = ext.BetaCollapse(ctx, reduced)
	}
}

// IsRecordValue reports whether t's head is a record's constructor or a
// definition a projection reads through: a value the normal form
// computes a projection at.
func IsRecordValue(t core.Term) bool {
	tb := installedRecords.Load()
	if tb == nil {
		return false
	}
	head, _ := ext.MatchesApply(t)
	c, ok := head.AsConst()
	if !ok {
		return false
	}
	name := string(c.Name())
	return tb.constructors[name] || tb.valued[name].Entry != ""
}

// IsRecordProjection reports whether name is a projection the normal
// form computes: one with an installed equation, so that applied to a
// record value (IsRecordValue) it is the part the value holds.
func IsRecordProjection(name core.TermName) bool {
	tb := installedRecords.Load()
	return tb != nil && len(tb.projections[string(name)]) > 0
}

// redex classifies t as a record redex: a projection applied to a value
// its constructor builds (the projection's equations), or to a value a
// definition builds (that definition's equation, unfolded under the
// projection).
func (tb *recordTable) redex(t core.Term) (projection core.AppliedTerm, atConstructor []RecordEquation, unfold RecordEquation, ok bool) {
	app, isApp := t.AsAppliedTerm()
	if !isApp {
		return core.AppliedTerm{}, nil, RecordEquation{}, false
	}
	p, isConst := app.Fun().AsConst()
	if !isConst {
		return core.AppliedTerm{}, nil, RecordEquation{}, false
	}
	equations := tb.projections[string(p.Name())]
	if len(equations) == 0 {
		return core.AppliedTerm{}, nil, RecordEquation{}, false
	}
	head, _ := ext.MatchesApply(app.Arg())
	c, isConst := head.AsConst()
	if !isConst {
		return core.AppliedTerm{}, nil, RecordEquation{}, false
	}
	name := string(c.Name())
	if tb.constructors[name] {
		return app, equations, RecordEquation{}, true
	}
	if def, isDef := tb.valued[name]; isDef {
		return app, nil, def, true
	}
	return core.AppliedTerm{}, nil, RecordEquation{}, false
}

// step is the shallow record step, its equations read through read.
func (tb *recordTable) step(read LibraryRead) prop.Rewrite {
	rewrites := map[string]prop.Rewrite{}
	rewriteOf := func(eq RecordEquation) prop.Rewrite {
		rw, ok := rewrites[eq.Entry]
		if !ok {
			rw = closedEquationRewrite(read(eq.Entry))
			rewrites[eq.Entry] = rw
		}
		return rw
	}
	return func(t core.Term) *prop.PropWrapper {
		app, atConstructor, def, ok := tb.redex(t)
		if !ok {
			return nil
		}
		for _, eq := range atConstructor {
			if w := rewriteOf(eq)(t); w != nil {
				return w
			}
		}
		if def.Entry == "" {
			return nil
		}
		unfolded := rewriteOf(def)(app.Arg())
		if unfolded == nil {
			return nil
		}
		return unfolded.LeftApply(app.Fun())
	}
}

// termNormal computes the record steps over t from the equations'
// statements; changed reports whether any fired. A projection is taken
// before its argument's parts are computed (headNormal), so of a record
// value only the part the projection selects is computed: a definition
// whose value is a module packs every operation, and the operations a
// `.carrier` drops are never read. The parts left are then computed, and
// a step they expose fires last.
func (tb *recordTable) termNormal(t core.Term) (core.Term, bool) {
	t, changed := tb.headNormal(t)
	if app, ok := t.AsAppliedTerm(); ok {
		f, fc := tb.termNormal(app.Fun())
		a, ac := tb.termNormal(app.Arg())
		if fc || ac {
			t, changed = core.Apply(f, a), true
		}
	} else if abs, ok := t.AsAbsTerm(); ok {
		if body, bc := tb.termNormal(abs.Body()); bc {
			t, changed = core.Abs(abs.Var(), body), true
		}
	}
	if r, fired := tb.fire(t); fired {
		reduced, _ := tb.termNormal(r)
		return reduced, true
	}
	return t, changed
}

// headNormal computes the record steps at t's head alone, until its
// head is no projection of a record value: the argument of a projection
// is brought to its own head first, and nothing under that head is
// computed.
func (tb *recordTable) headNormal(t core.Term) (core.Term, bool) {
	changed := false
	for {
		app, ok := t.AsAppliedTerm()
		if !ok {
			return t, changed
		}
		p, ok := app.Fun().AsConst()
		if !ok || len(tb.projections[string(p.Name())]) == 0 {
			return t, changed
		}
		if arg, ac := tb.headNormal(app.Arg()); ac {
			t, changed = core.Apply(app.Fun(), arg), true
		}
		r, fired := tb.fire(t)
		if !fired {
			return t, changed
		}
		t, changed = r, true
	}
}

// fire is the record step at t, computed from the equation's statement:
// the projection's part at its record's constructor, or the projection
// of a definition's value with the definition unfolded.
func (tb *recordTable) fire(t core.Term) (core.Term, bool) {
	app, atConstructor, def, ok := tb.redex(t)
	if !ok {
		return nil, false
	}
	for _, eq := range atConstructor {
		if r, fired := statementInstance(eq.Statement, t); fired {
			return r, true
		}
	}
	if def.Entry == "" {
		return nil, false
	}
	body, fired := statementInstance(def.Statement, app.Arg())
	if !fired {
		return nil, false
	}
	return core.Apply(app.Fun(), body), true
}

// statementInstance is the right side of the equation `∀x̄. l = r` at
// the instance of l that t is.
func statementInstance(stmt core.Prop, t core.Term) (core.Term, bool) {
	vars, lhs, _ := equationParts(stmt.Conclusion())
	values, types, ok := matchLeftSide(vars, lhs, t)
	if !ok {
		return nil, false
	}
	instance := stmt
	if len(types) > 0 {
		instance = core.PropTypeInst(stmt, types...)
	}
	vars, _, rhs := equationParts(instance.Conclusion())
	substs := make([]core.TermSubst, len(vars))
	for i, v := range vars {
		substs[i] = core.MakeTermSubst(v, values[i])
	}
	return rhs.Substitute(substs...), true
}

func equationParts(t core.Term) (vars []core.VarTerm, lhs, rhs core.Term) {
	for {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() {
			break
		}
		vars = append(vars, abs.Var())
		t = abs.Body()
	}
	l, r, ok := core.MatchesEQ(t)
	if !ok {
		panic("InstallRecordNormal: a record equation is an equation")
	}
	return vars, l, r
}

// matchLeftSide matches an equation's left side against t: constants by
// identity, the binders and the type letters by instance.
func matchLeftSide(vars []core.VarTerm, lhs, t core.Term) ([]core.Term, []core.TypeSubst, bool) {
	values := make([]core.Term, len(vars))
	var types []core.TypeSubst
	var match func(p, q core.Term) bool
	match = func(p, q core.Term) bool {
		if !core.MatchTypeInto(p.Type(), q.Type(), func(core.VarType) bool { return true }, &types) {
			return false
		}
		if v, ok := p.AsVar(); ok {
			for i, binder := range vars {
				if !v.EqualsVar(binder) {
					continue
				}
				if values[i] == nil {
					values[i] = q
					return true
				}
				return values[i].AlphaEquals(q)
			}
			return p.AlphaEquals(q)
		}
		if c, ok := p.AsConst(); ok {
			other, ok := q.AsConst()
			return ok && c.Meta() == other.Meta()
		}
		if a, ok := p.AsAppliedTerm(); ok {
			other, ok := q.AsAppliedTerm()
			return ok && match(a.Fun(), other.Fun()) && match(a.Arg(), other.Arg())
		}
		return false
	}
	if !match(lhs, t) || slices.Contains(values, nil) {
		return nil, nil, false
	}
	types = slices.DeleteFunc(types, func(s core.TypeSubst) bool { return s.HolType.Equals(s.VarType) })
	return values, types, true
}

// closedEquationRewrite reads a ∀-closed equation theorem `∀x̄. l = r`
// as a shallow rewrite: a term matching l is rewritten to r's instance.
func closedEquationRewrite(law *prop.PropWrapper) prop.Rewrite {
	if law.NumHyps() != 0 {
		panic("InstallRecordNormal: a record equation is a closed equation")
	}
	vars, lhs, _ := equationParts(law.Conclusion())
	return func(t core.Term) *prop.PropWrapper {
		values, types, ok := matchLeftSide(vars, lhs, t)
		if !ok {
			return nil
		}
		w := law
		if len(types) > 0 {
			w = w.TypeInst(types...)
		}
		w = w.ConclForAllInsts(values...)
		if !prop.Lhs(w).AlphaEquals(t) {
			panic("InstallRecordNormal: an equation's instance does not meet the term it matched")
		}
		return w
	}
}
