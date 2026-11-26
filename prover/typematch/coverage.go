package typematch

import (
	"slices"
	"sort"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// lawConstants is what the choice of a law's instance is judged on: the
// law's constants at a type one of its loose letters reaches, and the
// loose letters themselves. A letter is loose where no hypothesis of the
// lemma and no free term variable of it spells it: those are the
// context's, the same in every reading (proof.ReadingFixedLetters), and
// a lemma all of whose letters they spell has one instance.
type lawConstants struct {
	lemma  core.Prop
	loose  map[core.TypeName]bool
	consts []core.ConstTerm
}

func collectLawConstants(lemma core.Prop) lawConstants {
	fixed := map[core.TypeName]bool{}
	fix := func(v core.VarType) bool {
		fixed[v.Name()] = true
		return false
	}
	for h := range lemma.HypIter() {
		ext.TermAnyTypeVar(h, fix)
	}
	for _, v := range lemma.Conclusion().Frees(nil) {
		ext.TypeAnyVar(v.Type(), fix)
	}
	law := lawConstants{lemma: lemma, loose: map[core.TypeName]bool{}}
	ext.TermAnyTypeVar(lemma.Conclusion(), func(v core.VarType) bool {
		if !fixed[v.Name()] {
			law.loose[v.Name()] = true
		}
		return false
	})
	if len(law.loose) == 0 {
		return law
	}
	consts := map[core.TermKey]core.ConstTerm{}
	ext.CollectConstTerms(lemma.Conclusion(), consts)
	for _, c := range consts {
		if ext.TypeAnyVar(c.Type(), law.isLoose) {
			law.consts = append(law.consts, c)
		}
	}
	return law
}

func (law lawConstants) isLoose(v core.VarType) bool { return law.loose[v.Name()] }

// goalConstants is what a goal holds of the constants asked about: the
// distinct types it carries each at, and the type letters it names.
type goalConstants struct {
	types   map[core.TermName][]core.HolType
	letters map[core.TypeName]bool
}

func collectGoalConstants(goal core.Prop, asked []core.ConstTerm) goalConstants {
	g := goalConstants{types: map[core.TermName][]core.HolType{}, letters: map[core.TypeName]bool{}}
	wanted := map[core.TermName]bool{}
	for _, c := range asked {
		wanted[c.Name()] = true
	}
	consts := map[core.TermKey]core.ConstTerm{}
	name := func(v core.VarType) bool {
		g.letters[v.Name()] = true
		return false
	}
	read := func(t core.Term) {
		ext.CollectConstTerms(t, consts)
		ext.TermAnyTypeVar(t, name)
	}
	read(goal.Conclusion())
	for h := range goal.HypIter() {
		read(h)
	}
	for _, c := range consts {
		if wanted[c.Name()] {
			g.types[c.Name()] = append(g.types[c.Name()], c.Type())
		}
	}
	return g
}

// InstanceReading is what one instance of a law reads at a goal: of the
// law's constants the goal spells, the names of those the goal carries
// at the type the instance gives them, and of those it carries at other
// types alone. A constant the law holds at two types can stand in both.
type InstanceReading struct {
	// Instance is the instance read; nil for the law at its own letters.
	Instance      core.Prop
	Reads, Misses []core.TermName
}

// reading is instance's reading at the goal. A letter of the instance
// whose name the goal spells is the goal's; any other is free, and
// reads every type. An instance that moves a letter the lemma's context
// fixes is not judged.
//
// An instance that misses a constant states nothing about the terms the
// goal builds with it: cardinality.CardClauses at A, where the goal
// holds card at set(A) alone.
func (law lawConstants) reading(g goalConstants, instance core.Prop) (InstanceReading, bool) {
	var subst []core.TypeSubst
	if instance != nil {
		var ok bool
		if subst, ok = prop.IsTypeMatchOf(law.lemma, instance, law.isLoose); !ok {
			return InstanceReading{}, false
		}
	}
	free := func(v core.VarType) bool { return !g.letters[v.Name()] }
	out := InstanceReading{Instance: instance}
	for _, c := range law.consts {
		held := g.types[c.Name()]
		if len(held) == 0 {
			continue
		}
		at := c.Type().Substitute(subst...)
		read := false
		for _, ty := range held {
			var env []core.TypeSubst
			if core.MatchTypeInto(at, ty, free, &env) {
				read = true
				break
			}
		}
		if read {
			out.Reads = appendName(out.Reads, c.Name())
		} else {
			out.Misses = appendName(out.Misses, c.Name())
		}
	}
	sort.Slice(out.Reads, func(i, j int) bool { return out.Reads[i] < out.Reads[j] })
	sort.Slice(out.Misses, func(i, j int) bool { return out.Misses[i] < out.Misses[j] })
	return out, true
}

func appendName(names []core.TermName, name core.TermName) []core.TermName {
	if slices.Contains(names, name) {
		return names
	}
	return append(names, name)
}

// readsEvery is the single adaptation chosen over the sweep's commit:
// `committed` (nil where the sweep made no instance and the lemma stands
// at its own letters), unless it misses a constant of the law and an
// instance the goal offers misses none — then the first such instance of
// the enumeration. An instance that itself misses a constant is never
// taken: where the law's constants disagree about the instance — the
// goal holds one at A alone and another at set(A) alone — the commit
// stands (InstanceReadings is what a caller reports of it).
//
// The sweep commits its largest anchor's first candidate, so a constant
// in a side position of the law (the membership in CardClauses' insert
// clause) decides the instance by the order the goal spells its
// memberships in, and by whether the goal's letter is the law's: at a
// goal holding card at set(A) and a membership at A and at set(A), the
// sweep reads the law at A — the identity, bound, so no renamed-apart
// retry — and the law's every card is one the goal does not hold.
func readsEvery(lemma, goal core.Prop, committed core.Prop) core.Prop {
	law := collectLawConstants(lemma)
	if len(law.consts) == 0 {
		return committed
	}
	g := collectGoalConstants(goal, law.consts)
	if r, judged := law.reading(g, committed); !judged || len(r.Misses) == 0 {
		return committed
	}
	for _, instance := range EnumerateLemmaTypeAdaptations(lemma, goal) {
		if r, judged := law.reading(g, instance); judged && len(r.Misses) == 0 {
			return instance
		}
	}
	return committed
}

// InstanceReadings reports what a law installed at one instance of it —
// `installed`, nil or the lemma itself for the law at its own letters —
// misses at the goal, and where else the goal offers it: the install's
// reading, and the reading of each instance of the enumeration that
// reads a constant the install misses. Both are empty where the install
// misses nothing, or moves a letter the lemma's context fixes.
func InstanceReadings(lemma, goal, installed core.Prop) (install InstanceReading, offered []InstanceReading) {
	law := collectLawConstants(lemma)
	if len(law.consts) == 0 {
		return InstanceReading{}, nil
	}
	g := collectGoalConstants(goal, law.consts)
	install, judged := law.reading(g, installed)
	if !judged || len(install.Misses) == 0 {
		return InstanceReading{}, nil
	}
	for _, instance := range EnumerateLemmaTypeAdaptations(lemma, goal) {
		r, judged := law.reading(g, instance)
		if !judged || (installed != nil && instance.AlphaEquals(installed)) {
			continue
		}
		if slices.ContainsFunc(r.Reads, func(name core.TermName) bool { return slices.Contains(install.Misses, name) }) {
			offered = append(offered, r)
		}
	}
	return install, offered
}
