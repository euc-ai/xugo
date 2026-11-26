// membership_declared.go — the constants whose membership the closers
// read: a constant whose definition is a set-builder over its
// arguments, `c = λā. {x | φ}`, declared at its define door
// (registry.DefEntry.MembershipRead). A membership `x ∈ c(ā)` reads as
// the set-builder's, c opened by its definition first
// (membership_reading.go), and the set driver's vocabulary holds c
// (prover/proof, StandardSetVocabulary): a declared constant reads
// exactly as the set-builder it names, in every closer. An undeclared
// constant stays closed until a proof opens it, whatever its definiens.

package tactic

import (
	"context"
	"fmt"
	"maps"
	"slices"
	"sync"
	"sync/atomic"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// _DeclaredMembership is a declared constant as the table holds it: the
// number of arguments its definiens takes before the set-builder, and
// the meta its door minted, which carries the definition. An occurrence
// is opened through that meta, at the occurrence's own type: a text's
// `m .. n` is built from the parser's operator meta, which carries none,
// and a constant is its name (core.ConstTermMeta.Equals), so the
// definition is the declaration's, whatever meta an occurrence carries.
type _DeclaredMembership struct {
	arity int
	meta  core.ConstTermMeta
}

// membershipReadTable maps each declared constant to its entry. The
// define doors write it at registration, a new map each time, so a
// reading loads it once and looks names up without a lock.
var (
	membershipReadTable   atomic.Pointer[map[core.TermName]_DeclaredMembership]
	membershipReadDeclare sync.Mutex
)

// DeclareMembershipRead enters c in the table — the define door's move
// for an entry declaring MembershipRead, after the mint. c's definition
// must be a set-builder over its arguments (MembershipReadArity); a
// second declaration of one name is a door run twice, an engine defect.
func DeclareMembershipRead(c core.ConstTerm) {
	arity, err := MembershipReadArity(c)
	if err != nil {
		panic(fmt.Sprintf("DeclareMembershipRead(%s): %v", c.Name(), err))
	}
	membershipReadDeclare.Lock()
	defer membershipReadDeclare.Unlock()
	table := map[core.TermName]_DeclaredMembership{}
	if old := membershipReadTable.Load(); old != nil {
		table = maps.Clone(*old)
	}
	if _, ok := table[c.Name()]; ok {
		panic(fmt.Sprintf("DeclareMembershipRead(%s): declared twice", c.Name()))
	}
	table[c.Name()] = _DeclaredMembership{arity: arity, meta: c.Meta()}
	membershipReadTable.Store(&table)
}

// membershipReads is the table as it stands; nil when nothing is
// declared.
func membershipReads() map[core.TermName]_DeclaredMembership {
	if table := membershipReadTable.Load(); table != nil {
		return *table
	}
	return nil
}

// MembershipReadConstants is the declared constants' names, sorted —
// what the set driver's vocabulary adds to the set-theory constants.
func MembershipReadConstants() []core.TermName {
	return slices.Sorted(maps.Keys(membershipReads()))
}

// MembershipReadArity is the arity at which c's membership is read: the
// number of λ-binders its definiens takes before a set-builder — the
// identity form `{x | φ}` or the three-part form `{t | x̄ | φ}`, its
// three constants carrying their definitions. The error says what the
// definition is instead.
func MembershipReadArity(c core.ConstTerm) (int, error) {
	def := c.DefThm()
	if def.IsZero() {
		return 0, fmt.Errorf("%s has no definition to read", c.Name())
	}
	body := definiens(def)
	arity := 0
	for {
		abs, isAbs := body.AsAbsTerm()
		if !isAbs {
			break
		}
		body = abs.Body()
		arity++
	}
	if _, ok := matchSetBuilder(body); !ok {
		return 0, fmt.Errorf("the definiens of %s is no set-builder over its arguments: %s",
			c.Name(), ext.PrintTerm(definiens(def)))
	}
	return arity, nil
}

// definiens is the right side of a definition `⊢ c = t`.
func definiens(def core.ThmCert) core.Term {
	_, rhs, _ := ext.MatchesEQ(def.Conclusion())
	return rhs
}

// openDeclaredSet reads set as a declared constant applied at its
// arity: the constant, its arguments and the definiens at them,
// β-collapsed — the set-builder the constant names there. A constant
// of arity 0, a named set with no parameter, is the constant alone,
// and its definiens is the set-builder. false where set is no such
// application.
func openDeclaredSet(set core.Term) (c core.ConstTerm, args []core.Term, opened core.Term, ok bool) {
	head, args := ext.MatchesApply(set)
	c, isConst := head.AsConst()
	if !isConst {
		return c, nil, nil, false
	}
	entry, declared := membershipReads()[c.Name()]
	if !declared || len(args) != entry.arity {
		return c, nil, nil, false
	}
	opened = definiens(declaredDefThm(c))
	if len(args) > 0 {
		opened = ext.Apply(opened, args...)
	}
	return c, args, ext.BetaCollapse(context.Background(), opened), true
}

// declaredDefThm is the definition of a declared constant at the
// occurrence c's type, through the meta its door minted.
func declaredDefThm(c core.ConstTerm) core.ThmCert {
	entry, ok := membershipReads()[c.Name()]
	if !ok {
		panic(fmt.Sprintf("declaredDefThm(%s): not declared to read its membership", c.Name()))
	}
	return core.MakeConstTerm(entry.meta, c.Type()).DefThm()
}

// seedDeclaredAnchors gives every declared constant of the vocabulary
// that no occurrence anchored the meta its door minted: the set driver
// opens a declared constant whatever meta its occurrences carry
// (_DeclaredMembership).
func seedDeclaredAnchors(anchors map[core.TermName]core.ConstTermMeta, vocab map[core.TermName]bool) {
	for name, entry := range membershipReads() {
		if vocab[name] && anchors[name].IsZero() {
			anchors[name] = entry.meta
		}
	}
}

// mentionsDeclared reports whether t spells a declared constant.
func mentionsDeclared(t core.Term) bool {
	table := membershipReads()
	if len(table) == 0 {
		return false
	}
	var walk func(core.Term) bool
	walk = func(t core.Term) bool {
		switch x := t.Core().(type) {
		case core.ConstTerm:
			_, ok := table[x.Name()]
			return ok
		case core.AppliedTerm:
			return walk(x.Fun()) || walk(x.Arg())
		case core.AbsTerm:
			return walk(x.Body())
		}
		return false
	}
	return walk(t)
}
