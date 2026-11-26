// bundle_fibre.go — bundles whose components are terms: the fibres of
// a structure indexed by another, and a structure fact over terms.
//
// A sheaf of rings carries a ring on each F(U), the ring record F(U)
// itself, and a homomorphism of rings between each two; a locally
// ringed space a local ring at each point. Such a structure's
// definition states the fibre as a conjunct under a ∀ —
// `∀U V:set(A). U ∈ T ∧ V ∈ T ∧ V ⊆ U ⇒ ring_homomorphism(F(U), F(V),
// res(U, V))` — which the registry reads as an INDEXED layout (BundleLayout.Index,
// Templates): the sub-structure's components as terms over the
// structure's components and the index. A fact of the structure then
// states a FAMILY: a bundle whose components are templates with a hole
// per index, named after its subject's template, `F(U)` with the hole
// U. The text names a fibre by its subject's template at a term:
// `F(U)`, `F(U ∩ V)`, `stalk_ring(x)`, and the pass matches the term
// against the family's subject and fills the holes. A fact whose
// subject is a term and not a variable — a resident
// `local_ring_on(stalk_ring(T, F, res, x))` — is the family with no
// hole, named by that term.
//
// The components of every bundle are terms (astNode); a bundle a
// variable fact states, or a binder mints, has variables for them.

package dsl

import (
	"fmt"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// holePrefix spells an index hole in a family's templates: no text
// names a variable so, and an instance replaces every hole.
const holePrefix = "%hole%"

func holeName(i int) string { return fmt.Sprintf("%s%d", holePrefix, i) }

func isHole(name string) bool { return strings.HasPrefix(name, holePrefix) }

// nameOf is the variable a node spells, "" for a node that is no bare
// variable.
func nameOf(n astNode) string {
	if v, ok := n.(*astVar); ok && len(v.typeAnnot) == 0 {
		return v.name
	}
	return ""
}

// varNode is a bare variable node.
func varNode(name string, pos int) astNode { return &astVar{name: name, pos: pos} }

// printKey spells a node for comparison: two nodes that print alike are
// one term to the pass, which reads texts and not kernel terms.
func printKey(n astNode) string { return denormalizeUnicodeSubscripts(printASTNode(n)) }

// cloneAST is a deep copy of a node, so that a template instantiated
// twice yields two trees the later passes may rewrite apart.
func cloneAST(node astNode) astNode {
	return substituteTuple(node, map[string]astNode{}, node.nodePos())
}

// templateOf reads a kernel template as the parser would — the term
// spelled for the parser, parsed as a tuple's term is — with the
// structure's parameters replaced by the bundle's components and the
// index binders by holes. A template that does not read back is an
// engine defect: the registry spelled it.
func templateOf(t core.Term, sub map[string]astNode, pos int) astNode {
	text := ext.FormatTermForParser(t)
	node, err := parseTupleTerm(text)
	if err != nil {
		panic(fmt.Sprintf("bundle: a layout's template %s does not parse: %v", text, err))
	}
	return substituteTuple(node, sub, pos)
}

// matchTemplate matches a template with holes against a node, binding
// each hole to the sub-node it stands over; a hole met twice must
// stand over one term. Leaves that are no hole compare by spelling.
func matchTemplate(tmpl, node astNode, bind map[string]astNode) bool {
	switch t := tmpl.(type) {
	case *astVar:
		if isHole(t.name) && len(t.typeAnnot) == 0 {
			if prev, ok := bind[t.name]; ok {
				return printKey(prev) == printKey(node)
			}
			bind[t.name] = node
			return true
		}
		return printKey(tmpl) == printKey(node)
	case *astField:
		a, ok := node.(*astField)
		return ok && a.name == t.name && matchTemplate(t.receiver, a.receiver, bind)
	case *astApp:
		a, ok := node.(*astApp)
		if !ok || len(a.args) != len(t.args) || !matchTemplate(t.fun, a.fun, bind) {
			return false
		}
		for i := range t.args {
			if !matchTemplate(t.args[i], a.args[i], bind) {
				return false
			}
		}
		return true
	case *astBinOp:
		b, ok := node.(*astBinOp)
		return ok && b.op == t.op && matchTemplate(t.left, b.left, bind) && matchTemplate(t.right, b.right, bind)
	case *astNotNode:
		b, ok := node.(*astNotNode)
		return ok && matchTemplate(t.body, b.body, bind)
	case *astNeg:
		b, ok := node.(*astNeg)
		return ok && matchTemplate(t.operand, b.operand, bind)
	case *astCoerce:
		b, ok := node.(*astCoerce)
		return ok && matchTemplate(t.operand, b.operand, bind)
	}
	return printKey(tmpl) == printKey(node)
}

// holesIn lists the holes a node mentions, in first-occurrence order.
func holesIn(node astNode, into []string) []string {
	walkAST(node, func(n astNode) {
		if v, ok := n.(*astVar); ok && isHole(v.name) && !slices.Contains(into, v.name) {
			into = append(into, v.name)
		}
	})
	return into
}

// instance is the family at the holes' values: every component with
// the holes filled, named by the subject so filled; nil when a hole
// is unbound.
func (b *bundle) instance(bind map[string]astNode, pos int) *bundle {
	sub := make(map[string]astNode, len(bind))
	for hole, val := range bind {
		sub[hole] = val
	}
	for _, h := range b.index {
		if _, ok := sub[h]; !ok {
			return nil
		}
	}
	out := &bundle{structure: b.structure, types: b.types}
	for _, c := range b.comps {
		out.comps = append(out.comps, substituteTuple(c, sub, pos))
	}
	if b.carrier != nil {
		out.carrier = substituteTuple(b.carrier, sub, pos)
		out.name = printKey(out.carrier)
	}
	return out
}

// renumbered is the family with its holes numbered in first-occurrence
// order over the subject then the components, so that two readings of
// one fibre — the ring at U and the ring at V — are one family.
func (b *bundle) renumbered() *bundle {
	var order []string
	if b.carrier != nil {
		order = holesIn(b.carrier, order)
	}
	for _, c := range b.comps {
		order = holesIn(c, order)
	}
	sub := map[string]astNode{}
	for i, h := range order {
		sub[h] = varNode(holeName(i), 0)
	}
	out := &bundle{structure: b.structure, types: b.types}
	for i := range order {
		out.index = append(out.index, holeName(i))
	}
	for _, c := range b.comps {
		out.comps = append(out.comps, substituteTuple(c, sub, c.nodePos()))
	}
	if b.carrier != nil {
		out.carrier = substituteTuple(b.carrier, sub, b.carrier.nodePos())
		out.name = printKey(out.carrier)
	}
	return out
}

// nameable reports whether every hole of the family stands in its
// subject, so that naming the fibre fixes the family's components.
func (b *bundle) nameable() bool {
	if b.carrier == nil {
		return false
	}
	named := holesIn(b.carrier, nil)
	for _, h := range b.index {
		if !slices.Contains(named, h) {
			return false
		}
	}
	return true
}

// key is what two families are compared by: the structure and the
// renumbered spelling of subject and components.
func (b *bundle) key() string {
	parts := []string{b.structure}
	if b.carrier != nil {
		parts = append(parts, printKey(b.carrier))
	}
	for _, c := range b.comps {
		parts = append(parts, printKey(c))
	}
	return strings.Join(parts, "\x00")
}

// LeadingBinders reads the ∀ binders a text opens with — a definition
// equation's parameters — as name and type, so that a definition's
// declared layouts (registry.DefEntry.Bundles) are registered before
// its equation is read and its body may pass them as bundles.
func LeadingBinders(text string) ([]BundleParam, error) {
	normalized, _ := NormalizeTextSymbols(text)
	tokens, lexErr := lex(normalized)
	if lexErr != nil {
		return nil, fmt.Errorf("lex: %s", lexErr.Message)
	}
	par := &parser{tokens: tokens}
	node, perr := par.parseExpr()
	if perr != nil {
		return nil, fmt.Errorf("parse: %s", perr.Message)
	}
	var out []BundleParam
	for {
		q, ok := node.(*astQuantNode)
		if !ok || q.quantifier != "∀" {
			return out, nil
		}
		if q.varType == nil {
			return nil, fmt.Errorf("the binder %s has no type", q.varName)
		}
		out = append(out, BundleParam{Name: q.varName, Type: resolveType(q.varType)})
		node = q.body
	}
}

// foldable reports whether a fold may name the bundle: by a variable,
// or by an application — a fibre F(U), stalk_ring(x) — and not by a λ or
// another term shape a reader would not take for a name.
func (b *bundle) foldable() bool {
	switch b.carrier.(type) {
	case *astVar, *astApp:
		return true
	}
	return false
}

// familyOf is the one family in scope whose subject is the variable
// name applied to its holes — the module P(n) for every n under the
// name P — nil when none or two are.
func (sc *bundleScope) familyOf(name string) *bundle {
	var found *bundle
	for _, b := range sc.bundles {
		if b == nil || len(b.index) == 0 {
			continue
		}
		app, ok := b.carrier.(*astApp)
		if !ok || nameOf(app.fun) != name {
			continue
		}
		if found != nil {
			return nil
		}
		found = b
	}
	return found
}

// fillLayouts are the layouts a bundle fills among a constant's
// parameters: the constant's own layouts over components alone, and,
// through each layout — indexed or not — the layouts of its structure
// composed, where they land on components alone and fill at least two
// of them: the ring of a chain complex, through the module on its
// P(n). An indexed layout itself takes no bundle, its fibre being a
// template no bundle fills.
func (sc *bundleScope) fillLayouts(syn *BundleSyntax) []BundleLayout {
	var out []BundleLayout
	seen := map[string]bool{}
	add := func(l BundleLayout) {
		key := l.Structure + fmt.Sprint(l.Slots)
		if seen[key] {
			return
		}
		seen[key] = true
		out = append(out, l)
	}
	var walk func(layouts []BundleLayout, through []int, depth int)
	walk = func(layouts []BundleLayout, through []int, depth int) {
		if depth > 8 {
			return
		}
		for _, l := range layouts {
			composed := make([]int, len(l.Slots))
			plain := true
			filled := 0
			for k, slot := range l.Slots {
				switch {
				case slot < 0 && k < len(l.Templates) && l.Templates[k] != nil:
					plain = false
				case slot < 0:
					composed[k] = -1
				case through == nil:
					composed[k] = slot
					filled++
				case through[slot] < 0:
					plain = false
				default:
					composed[k] = through[slot]
					filled++
				}
				if !plain {
					break
				}
			}
			if plain && (through == nil || filled >= 2) {
				add(BundleLayout{Structure: l.Structure, Slots: composed})
			}
			sub := sc.bundleSyntax(l.Structure)
			if sub == nil || !sub.Structure {
				continue
			}
			// The path into l's structure: its component i is the
			// constant's parameter through[Slots[i]] (or -1), a template
			// standing for none.
			path := make([]int, len(l.Slots))
			for k, slot := range l.Slots {
				switch {
				case slot < 0:
					path[k] = -1
				case through == nil:
					path[k] = slot
				default:
					path[k] = through[slot]
				}
			}
			walk(sub.Layouts[1:], path, depth+1)
		}
	}
	if syn.Structure {
		walk(syn.Layouts[1:], nil, 0)
	} else {
		walk(syn.Layouts, nil, 0)
	}
	return out
}
