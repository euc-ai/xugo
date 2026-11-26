// bundle.go — bundles: one name standing for a structure's components.
//
// A structure is a predicate over explicit components (constitution
// §Structures), and a statement over several structures spells every
// component of each: an isomorphism between two sheaves of rings takes
// each sheaf's topology, section rings and restriction.
// A BUNDLE is a name that stands for such a tuple in the text, the way
// Isabelle's locales let a context fix its parameters once. The kernel
// never sees one: this pass rewrites the AST into the component form
// before anything else reads it, so the term, its key and every
// consumer downstream are what the spelled-out text would give.
//
// Four forms:
//
//   - A BUNDLE BINDER, `∀G:sheaf_of_rings(C, D). body`: the binder's
//     type is a structure predicate applied to bundles already in scope
//     and to types. It binds a fresh variable for each component the
//     bundles do not supply — named after the definition's component
//     where the text does not hold that name, else under the bundle
//     (`G_T`); the subject (the component the definition declares the
//     predicate said of) is named by the binder — and states the
//     predicate as the antecedent: `∀G_T. ∀G. ∀G_res.
//     sheaf_of_rings(G_T, G, G_res) ⇒ body` under a sheaf F that holds
//     `T`. A structure on a record has the record as its one component:
//     `∀R:comm_ring_on(A). body` is `∀R:ring_ops(A). comm_ring_on(R) ⇒
//     body`. `∃` gives the conjunction instead.
//   - A BUNDLE ARGUMENT, `lrs_isomorphism(F, G, φ, ψ)`: in an
//     application of a constant that declares where a bundle of a
//     structure goes (BundleSyntax.Layouts — a structure's own
//     sub-structures, read off its definition, or a definition's
//     declared Bundles), a bundle fills its layout's parameters with
//     its components, and the other arguments fill the rest in order.
//   - A FIELD, `X.T`: the component of X that the structure's
//     definition names T.
//   - A TUPLE, `spec_sheaf(R)`: a family's named list of terms, spliced
//     among the arguments of the application it stands in.
//   - A FIBRE, `F(U)`, `stalk_ring(x)`: the subject's template at a
//     term names the sub-structure its definition states for every
//     value of an index — the ring on F(U), the local ring at x — whose
//     components are the definition's templates at that term
//     (bundle_fibre.go).
//
// A bundle is read off a STRUCTURE FACT: a structure predicate applied
// to variables — the antecedent a bundle binder states, a law's
// `sheaf_of_rings(T, F, res) ⇒ …`, a goal's resident hypothesis — names
// the bundle after its subject and makes each sub-structure among its
// conjuncts a bundle too, named after that one's subject (a ring
// homomorphism's two rings, R and S). Its scope is the right side of the ⇒ or ∧ that states it.
// A name two facts read differently is no bundle.
//
// foldBundles is the printer's half: a binder run that a structure fact
// closes, with the names the expansion would mint, is written back as
// the bundle binder; a constant's arguments a bundle in scope fills, as
// the bundle; and a run of arguments a tuple matches, as the tuple.

package dsl

import (
	"fmt"
	"slices"
	"strings"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// BundleSyntax is what a constant declares about bundle arguments: its
// parameters, and the layouts in which a bundle of a structure fills
// them. For a structure predicate, Layouts[0] is the structure's own
// components in order, each later layout a sub-structure its
// definition states over its components, and Subject the index of the
// component the definition declares the predicate said of — the record
// a ring is, the map a homomorphism is, the sections a sheaf assigns —
// which names the bundle (-1 when it declares none: a structure on a
// whole type). A structure with no subject may declare the Letter the
// chapter spelling writes its bundle binder under.
type BundleSyntax struct {
	Params    []BundleParam
	Layouts   []BundleLayout
	Structure bool
	Subject   int
	Letter    string
}

// BundleParam is one parameter: the name the definition binds it by,
// and its type in the definition's own type variables.
type BundleParam struct {
	Name string
	Type core.HolType
}

// BundleLayout says where a bundle of Structure goes: per component of
// that structure, the index of the parameter it fills, -1 for a
// component the constant does not take. An INDEXED layout is a
// sub-structure a structure's definition states for every value of
// Index — `∀U V:set(A). … ⇒ ring_homomorphism(F(U), F(V), res(U, V))`
// — and Templates holds, at each component that is a term
// over the structure's components and the index rather than a
// component itself, that term (nil at a component Slots gives).
type BundleLayout struct {
	Structure string
	Slots     []int
	Index     []BundleParam
	Templates []core.Term
}

// TupleSyntax is a family's named tuple: its parameters, each read in
// the terms as a term or a type, and the terms in order.
type TupleSyntax struct {
	Params []string
	Terms  []string
}

// params are the parameter names as the terms read them: a term is
// normalized before it is lexed (a subscript digit is `_` and the digit,
// parseTupleTerm), so a parameter is too, or a subscripted parameter
// would be no name of its terms and would capture the call site's
// variable of that name.
func (tu *TupleSyntax) params() []string {
	out := make([]string, len(tu.Params))
	for i, p := range tu.Params {
		out[i], _ = NormalizeTextSymbols(p)
	}
	return out
}

// bundle is one bundle in scope: the structure, per component the term
// that is it — a variable for one a fact over variables states or a
// binder mints — with its type where the text gives one. A FAMILY
// (bundle_fibre.go) has a hole per index in its components, listed in
// index, and carrier is the subject's template it is named by; a
// bundle over terms with no hole is the family with no index.
type bundle struct {
	name      string
	structure string
	comps     []astNode
	types     []core.HolType
	index     []string
	carrier   astNode
}

func (b *bundle) sameAs(o *bundle) bool { return b.key() == o.key() }

// bundleScope is the pass's view at one point of the text.
type bundleScope struct {
	table SyntaxTable
	// bundles visible here, a plain one under its name and a family
	// under its subject's template; a name read two ways maps to nil.
	bundles map[string]*bundle
	// root holds from a text's root down its leading ∀ binders: the
	// left side of a definition's ⇔ there states the bundles its
	// constant lays out, for the body. leading is those binders in
	// order, the parameters a definiendum there applies its constant to.
	root    bool
	leading []string
	// types of the variables bound here, where an annotation gives one.
	types map[string]core.HolType
	// avoid is every name a fresh component must not take: the binders
	// on the path here, the declared variables, every visible bundle's
	// components.
	avoid map[string]bool
	// bound is every variable in scope here — the binders on the path
	// and the declared variables — the names under which a constant of
	// the table is shadowed. A bundle's component is in avoid and not
	// here: a registered constant standing as a structure fact's
	// subject keeps its own record fields (struct_fields.go).
	bound map[string]bool
	// implicitOK reports whether a name is bound here, for reading an
	// implicit-short structure fact.
	declared map[string]bool
	// surface is the name the text spells a resident fact's variable
	// by, keyed by the variable's own name (ParseScope.ResidentNames):
	// a resident bundle's component `add₀` and the bound `add` are one
	// variable under two spellings.
	surface map[string]string
}

func (sc *bundleScope) clone() *bundleScope {
	out := &bundleScope{table: sc.table, declared: sc.declared, root: sc.root, leading: sc.leading, surface: sc.surface,
		bundles: make(map[string]*bundle, len(sc.bundles)),
		types:   make(map[string]core.HolType, len(sc.types)),
		avoid:   make(map[string]bool, len(sc.avoid)),
		bound:   make(map[string]bool, len(sc.bound))}
	for k, v := range sc.bundles {
		out.bundles[k] = v
	}
	for k, v := range sc.types {
		out.types[k] = v
	}
	for k, v := range sc.avoid {
		out.avoid[k] = v
	}
	for k, v := range sc.bound {
		out.bound[k] = v
	}
	return out
}

// bind is the scope under one more binder.
func (sc *bundleScope) bind(name string, t core.HolType) *bundleScope {
	out := sc.clone()
	out.avoid[name] = true
	out.bound[name] = true
	if sc.root {
		out.leading = append(slices.Clone(sc.leading), name)
	}
	if t != nil {
		out.types[name] = t
	} else {
		delete(out.types, name)
	}
	// A rebound name is no longer a bundle's component here, nor a
	// name a family's subject or components mention, nor the surface
	// spelling of a resident variable.
	for key, b := range out.bundles {
		if b == nil {
			continue
		}
		if key == name || b.mentions(name) {
			delete(out.bundles, key)
		}
	}
	for _, spelled := range out.surface {
		if spelled == name {
			out.surface = withoutSpelling(out.surface, name)
			break
		}
	}
	return out
}

// withoutSpelling is surface without the variables it spells name.
func withoutSpelling(surface map[string]string, name string) map[string]string {
	out := make(map[string]string, len(surface))
	for v, spelled := range surface {
		if spelled != name {
			out[v] = spelled
		}
	}
	return out
}

// leaving is the scope below the root's leading binders.
func (sc *bundleScope) leaving() *bundleScope {
	if !sc.root {
		return sc
	}
	out := sc.clone()
	out.root = false
	return out
}

// mentions reports whether a bundle's components or subject spell the
// variable name.
func (b *bundle) mentions(name string) bool {
	found := false
	visit := func(n astNode) {
		if v, ok := n.(*astVar); ok && v.name == name {
			found = true
		}
	}
	for _, c := range b.comps {
		walkAST(c, visit)
	}
	if b.carrier != nil {
		walkAST(b.carrier, visit)
	}
	return found
}

// withBundles is the scope with bs visible. A name already a bundle of
// a structure the new one is a sub-structure of — a scheme F restated
// as a locally ringed space, a module M as its additive group — keeps
// the richer; a richer fact after a poorer one replaces it; a name two
// facts read apart otherwise becomes none.
func (sc *bundleScope) withBundles(bs []*bundle) *bundleScope {
	if len(bs) == 0 {
		return sc
	}
	out := sc.clone()
	for _, b := range bs {
		if prev, seen := out.bundles[b.name]; seen {
			switch {
			case prev == nil || prev.sameAs(b) || out.subsumes(prev, b):
				continue
			case out.subsumes(b, prev):
			default:
				out.bundles[b.name] = nil
				continue
			}
		}
		out.bundles[b.name] = b
		for _, c := range b.comps {
			if v := nameOf(c); v != "" && !isHole(v) {
				out.avoid[v] = true
			}
		}
	}
	return out
}

// subsumes reports whether small is a sub-structure fact of big over
// big's own components: big's structure lays small's out, and the
// components agree there.
func (sc *bundleScope) subsumes(big, small *bundle) bool {
	syn := sc.bundleSyntax(big.structure)
	if syn == nil || !syn.Structure {
		return false
	}
	for _, l := range sc.fillLayouts(syn) {
		if l.Structure != small.structure || len(l.Slots) != len(small.comps) {
			continue
		}
		match := true
		for k, slot := range l.Slots {
			if slot < 0 || slot >= len(big.comps) || printKey(big.comps[slot]) != printKey(small.comps[k]) {
				match = false
				break
			}
		}
		if match {
			return true
		}
	}
	return false
}

// lookup returns the visible bundle named name, nil when none is.
func (sc *bundleScope) lookup(name string) *bundle {
	return sc.bundles[name]
}

// lookupTerm returns the bundle a node names: a plain bundle by its
// name, a fibre by matching the node — spelled, or in the implicit-
// short form its head's bound components complete — against each
// family's subject, the holes filled from it. nil when none does, or
// two families read it apart.
func (sc *bundleScope) lookupTerm(node astNode) *bundle {
	if name := nameOf(node); name != "" {
		return sc.lookup(name)
	}
	if b, seen := sc.bundles[printKey(node)]; seen {
		return b
	}
	if b, seen := sc.bundles[sc.key(node)]; seen {
		return b
	}
	var found *bundle
	for _, b := range sc.bundles {
		if b == nil || b.carrier == nil || len(b.index) == 0 {
			continue
		}
		bind := map[string]astNode{}
		probe := node
		if full := sc.completedTo(node, b.carrier); full != nil {
			probe = full
		}
		if !matchTemplate(sc.spelledOut(b.carrier), sc.spelledOut(probe), bind) {
			continue
		}
		inst := b.instance(bind, node.nodePos())
		if inst == nil {
			continue
		}
		if found != nil && found.key() != inst.key() {
			return nil
		}
		found = inst
	}
	return found
}

// completedTo is node, an application in the implicit-short form of
// its head, with the prefix written in — the bound names the constant
// declares implicit — where that makes it the arity of the template
// tmpl under the same head; nil otherwise.
func (sc *bundleScope) completedTo(node, tmpl astNode) astNode {
	app, ok := node.(*astApp)
	if !ok {
		return nil
	}
	head, ok := app.fun.(*astVar)
	if !ok || len(head.typeAnnot) > 0 {
		return nil
	}
	t, ok := tmpl.(*astApp)
	if !ok || nameOf(t.fun) != head.name {
		return nil
	}
	s := sc.syntaxOf(head.name)
	if s == nil || len(s.Implicit) == 0 || len(app.args)+len(s.Implicit) != len(t.args) {
		return nil
	}
	full := &astApp{fun: head, pos: app.pos}
	for _, name := range s.Implicit {
		if !sc.avoid[name] {
			return nil
		}
		full.args = append(full.args, varNode(name, app.pos))
	}
	full.args = append(full.args, app.args...)
	return full
}

func (sc *bundleScope) syntaxOf(name string) *ConstSyntax {
	if sc.table == nil {
		return nil
	}
	return sc.table.ConstSyntax(name)
}

func (sc *bundleScope) bundleSyntax(name string) *BundleSyntax {
	if s := sc.syntaxOf(name); s != nil {
		return s.Bundle
	}
	return nil
}

// bundleError is an authoring error the pass reports at a position.
type bundleError struct {
	pos int
	msg string
}

func (e *bundleError) Error() string { return e.msg }

// expandBundleRoots runs the pass over the roots of one parse. resident
// are the goal's resident facts, declared the variables the scope
// declares.
func expandBundleRoots(scope *ParseScope, declared map[string]core.HolType, roots []*astNode) *InputDiagnostic {
	if scope == nil || scope.Syntax == nil {
		return nil
	}
	table := scope.Syntax
	need := false
	for _, r := range roots {
		if mentionsBundles(*r, table) {
			need = true
			break
		}
	}
	if !need {
		return nil
	}
	sc := &bundleScope{table: table, bundles: map[string]*bundle{}, types: map[string]core.HolType{},
		avoid: map[string]bool{}, bound: map[string]bool{}, declared: map[string]bool{}, root: true, surface: scope.ResidentNames}
	for name, t := range declared {
		sc.types[name] = t
		sc.avoid[name] = true
		sc.bound[name] = true
		sc.declared[name] = true
	}
	sc = sc.withBundles(residentBundles(table, scope.ResidentFacts, scope.ResidentNames))
	if len(scope.ResidentNames) > 0 {
		// A surface alias adds a spelling; the original resident name
		// remains available to texts read from an inspected goal.
		var raw []*bundle
		for _, b := range residentBundles(table, scope.ResidentFacts, nil) {
			// An unchanged subject already has its alias-aware components.
			// Adding the raw copy would falsely make that name ambiguous.
			if _, seen := sc.bundles[b.name]; !seen {
				raw = append(raw, b)
			}
		}
		sc = sc.withBundles(raw)
	}
	for _, r := range roots {
		out, err := expandBundles(*r, sc)
		if err != nil {
			pos := 0
			if be, ok := err.(*bundleError); ok {
				pos = be.pos
			}
			return &InputDiagnostic{Position: pos, Code: CodeValidation, Message: err.Error(),
				Suggestion: "a bundle is a structure fact's subject in scope, a bundle binder's name, or a sub-structure's subject (constitution §Structures, \"Bundles\")"}
		}
		*r = out
	}
	return nil
}

// withoutBundleBinders drops from the type names a parse collected each
// bundle binder's type — a structure predicate, not a type — and the
// bundles and type letters among its arguments, which the pass reads.
func withoutBundleBinders(names []*astTypeNamed, scope *ParseScope) []*astTypeNamed {
	if scope == nil || scope.Syntax == nil {
		return names
	}
	skip := map[*astTypeNamed]bool{}
	for _, n := range names {
		if len(n.args) == 0 {
			continue
		}
		s := scope.Syntax.ConstSyntax(n.name)
		if s == nil || s.Bundle == nil || !s.Bundle.Structure {
			continue
		}
		skip[n] = true
		for _, a := range n.args {
			if an, ok := a.(*astTypeNamed); ok && len(an.args) == 0 {
				skip[an] = true
			}
		}
	}
	if len(skip) == 0 {
		return names
	}
	out := make([]*astTypeNamed, 0, len(names))
	for _, n := range names {
		if !skip[n] {
			out = append(out, n)
		}
	}
	return out
}

// mentionsBundles reports whether the text uses any of the four forms,
// so that a text that uses none is not walked.
func mentionsBundles(root astNode, table SyntaxTable) bool {
	found := false
	walkAST(root, func(n astNode) {
		if found {
			return
		}
		switch n := n.(type) {
		case *astVar:
			if strings.Contains(n.name, ".") && n.name != ".." {
				found = true
			}
		case *astQuantNode:
			if t, ok := n.varType.(*astTypeNamed); ok {
				if s := table.ConstSyntax(t.name); s != nil && s.Bundle != nil && s.Bundle.Structure {
					found = true
				}
			}
		case *astApp:
			if h, ok := n.fun.(*astVar); ok {
				if s := table.ConstSyntax(h.name); s != nil && (s.Bundle != nil || s.Tuple != nil) {
					found = true
				}
			}
		}
	})
	return found
}

// residentBundles reads the bundles a goal's resident facts state: a
// structure predicate applied to any terms, each read as the parser
// would spell it, its variables under the names the text spells them
// by (names).
func residentBundles(table SyntaxTable, facts []core.Term, names map[string]string) []*bundle {
	var out []*bundle
	surface := func(v core.VarTerm) string {
		if n, ok := names[string(v.Name())]; ok {
			return n
		}
		return string(v.Name())
	}
	for _, fact := range facts {
		head, args := spineArgs(fact)
		c, ok := head.AsConst()
		if !ok {
			continue
		}
		s := table.ConstSyntax(string(c.Name()))
		if s == nil || s.Bundle == nil || !s.Bundle.Structure || len(args) != len(s.Bundle.Params) {
			continue
		}
		comps := make([]astNode, len(args))
		types := make([]core.HolType, len(args))
		for i, a := range args {
			if v, ok := a.AsVar(); ok {
				comps[i], types[i] = varNode(surface(v), 0), v.Type()
				continue
			}
			sub := map[string]astNode{}
			for _, v := range a.Frees(nil) {
				if n := surface(v); n != string(v.Name()) {
					sub[string(v.Name())] = varNode(n, 0)
				}
			}
			comps[i] = templateOf(a, sub, 0)
		}
		out = append(out, bundlesOfFact(table, string(c.Name()), comps, types, nil)...)
	}
	return out
}

// bundlesOfFact is the bundles a structure fact S(comps) states: S's
// own, named after its subject, and those of each sub-structure fact
// S's definition states over the components — a module's ring; for
// every U, the ring on F(U) — read the same way in turn, unless the
// name is taken already: a module's additive group on its carrier M is
// the module M read as less, and M stays the module. holes are the
// index holes comps already carry when the fact is itself a fibre.
func bundlesOfFact(table SyntaxTable, structure string, comps []astNode, types []core.HolType, holes []string) []*bundle {
	s := table.ConstSyntax(structure)
	if s == nil || s.Bundle == nil || !s.Bundle.Structure || len(comps) != len(s.Bundle.Params) {
		return nil
	}
	syn := s.Bundle
	var out []*bundle
	taken := map[string]bool{}
	add := func(b *bundle) {
		b = b.renumbered()
		if !b.nameable() || taken[b.name] {
			return
		}
		taken[b.name] = true
		out = append(out, b)
	}
	if syn.Subject >= 0 {
		add(&bundle{structure: structure, comps: comps, types: types, index: holes, carrier: comps[syn.Subject]})
	}
	for _, l := range syn.Layouts[1:] {
		subComps, subTypes, subHoles := layoutComps(syn, l, comps, types, holes)
		if subComps == nil {
			continue
		}
		for _, b := range bundlesOfFact(table, l.Structure, subComps, subTypes, subHoles) {
			add(b)
		}
	}
	return out
}

// layoutComps is the sub-structure fact a layout states over a fact's
// components: a component at a slot as it is, a template with the
// structure's parameters replaced by the components and the layout's
// index by fresh holes. nil for a layout that leaves a component out
// (a definition's declared layout with `_`).
func layoutComps(syn *BundleSyntax, l BundleLayout, comps []astNode, types []core.HolType, holes []string) ([]astNode, []core.HolType, []string) {
	subComps := make([]astNode, len(l.Slots))
	subTypes := make([]core.HolType, len(l.Slots))
	var sub map[string]astNode
	subHoles := holes
	pos := 0
	if len(comps) > 0 {
		pos = comps[0].nodePos()
	}
	for k, slot := range l.Slots {
		if slot >= 0 {
			subComps[k], subTypes[k] = comps[slot], types[slot]
			continue
		}
		if k >= len(l.Templates) || l.Templates[k] == nil {
			return nil, nil, nil
		}
		if sub == nil {
			sub = make(map[string]astNode, len(syn.Params)+len(l.Index))
			for i, p := range syn.Params {
				sub[p.Name] = comps[i]
			}
			for j, ip := range l.Index {
				h := holeName(len(holes) + j)
				sub[ip.Name] = varNode(h, pos)
				subHoles = append(subHoles, h)
			}
		}
		subComps[k] = templateOf(l.Templates[k], sub, pos)
	}
	return subComps, subTypes, subHoles
}

// factsOf reads the structure facts a side of a ⇒ or ∧ states, its
// conjuncts flattened: a structure predicate applied to terms, spelled
// out or with its implicit prefix left to names bound here; under a
// run of ∀ binders, and behind the guard of a ⇒, it states a family,
// the binders its index (`∀U V:set(A). … ⇒ ring_homomorphism(F(U),
// F(V), res(U, V))` states the ring F(U) for every U).
func (sc *bundleScope) factsOf(node astNode) []*bundle {
	var out []*bundle
	var walk func(n astNode, index []string)
	walk = func(n astNode, index []string) {
		switch n := n.(type) {
		case *astBinOp:
			switch n.op {
			case "∧":
				walk(n.left, index)
				walk(n.right, index)
			case "⇒":
				walk(n.right, index)
			}
		case *astQuantNode:
			if n.quantifier == "∀" {
				walk(n.body, append(slices.Clone(index), n.varName))
			}
		case *astApp:
			head, ok := n.fun.(*astVar)
			if !ok || len(head.typeAnnot) > 0 {
				return
			}
			s := sc.syntaxOf(head.name)
			if s == nil || s.Bundle == nil || !s.Bundle.Structure {
				return
			}
			var args []astNode
			if missing := len(s.Bundle.Params) - len(n.args); missing > 0 {
				// The implicit-short form: the leading names bound here.
				if missing > len(s.Implicit) {
					return
				}
				for _, name := range s.Implicit[:missing] {
					if !sc.avoid[name] {
						return
					}
					args = append(args, varNode(name, n.pos))
				}
			}
			args = append(args, n.args...)
			if len(args) != len(s.Bundle.Params) {
				return
			}
			sub := make(map[string]astNode, len(index))
			holes := make([]string, len(index))
			for i, name := range index {
				holes[i] = holeName(i)
				sub[name] = varNode(holes[i], n.pos)
			}
			comps := make([]astNode, len(args))
			types := make([]core.HolType, len(args))
			for i, a := range args {
				if v := nameOf(a); v != "" && strings.Contains(v, ".") {
					return
				}
				comps[i] = substituteTuple(a, sub, a.nodePos())
				if v := nameOf(a); v != "" && !slices.Contains(index, v) {
					types[i] = sc.types[v]
				}
			}
			out = append(out, bundlesOfFact(sc.table, head.name, comps, types, holes)...)
		}
	}
	walk(node, nil)
	return out
}

// definitionFacts reads the bundles the left side of a definition's ⇔
// states for its body: a structure's own fact, and for a constant
// that declares layouts (DefEntry.Bundles) the fact each complete
// layout lays its binders out as.
func (sc *bundleScope) definitionFacts(left astNode) []*bundle {
	out := sc.factsOf(left)
	app, ok := left.(*astApp)
	if !ok {
		return out
	}
	head, ok := app.fun.(*astVar)
	if !ok || len(head.typeAnnot) > 0 {
		return out
	}
	syn := sc.bundleSyntax(head.name)
	if syn == nil || syn.Structure || len(app.args) != len(syn.Params) {
		return out
	}
	for _, l := range syn.Layouts {
		comps := make([]astNode, len(l.Slots))
		types := make([]core.HolType, len(l.Slots))
		complete := true
		for k, slot := range l.Slots {
			if slot < 0 {
				complete = false
				break
			}
			comps[k] = app.args[slot]
			if v := nameOf(app.args[slot]); v != "" {
				types[k] = sc.types[v]
			}
		}
		if complete {
			out = append(out, bundlesOfFact(sc.table, l.Structure, comps, types, nil)...)
		}
	}
	return out
}

// markStatements marks what a definition's equation states
// (astApp.stated): its definiendum — the root ⇔'s left side, a constant
// applied to the text's leading binders — and each conjunct of its
// body, through ∀ binders and ⇒ guards, that applies a structure
// predicate: the conjuncts the registry reads as the structure's
// layouts. The left side states their bundles for the body
// (definitionFacts); the body conjunct that states one is its
// statement, not a restatement, and the fold and the elision leave it
// spelled in full. A root ⇔ whose left side is anything else — a law
// over a free variable, `closed_in(T, s) ⇔ …` — states nothing.
func (sc *bundleScope) markStatements(eq *astBinOp) {
	app, ok := eq.left.(*astApp)
	if !ok || !sc.definiendum(app) {
		return
	}
	app.stated = true
	var walk func(n astNode)
	walk = func(n astNode) {
		switch n := n.(type) {
		case *astBinOp:
			switch n.op {
			case "∧":
				walk(n.left)
				walk(n.right)
			case "⇒":
				walk(n.right)
			}
		case *astQuantNode:
			if n.quantifier == "∀" {
				walk(n.body)
			}
		case *astApp:
			head, ok := n.fun.(*astVar)
			if !ok || len(head.typeAnnot) > 0 {
				return
			}
			if s := sc.syntaxOf(head.name); s != nil && s.StructurePredicate {
				n.stated = true
			}
		}
	}
	walk(eq.right)
}

// definiendum reports whether app is a constant applied to the text's
// leading binders, each once.
func (sc *bundleScope) definiendum(app *astApp) bool {
	head, ok := app.fun.(*astVar)
	if !ok || len(head.typeAnnot) > 0 || len(app.args) != len(sc.leading) {
		return false
	}
	seen := map[string]bool{}
	for _, a := range app.args {
		v, ok := a.(*astVar)
		if !ok || len(v.typeAnnot) > 0 || seen[v.name] || !slices.Contains(sc.leading, v.name) {
			return false
		}
		seen[v.name] = true
	}
	return true
}

// expandBundles rewrites node's bundle forms into component form.
func expandBundles(node astNode, sc *bundleScope) (astNode, error) {
	switch n := node.(type) {
	case nil:
		return nil, nil
	case *astVar:
		if strings.Contains(n.name, ".") && n.name != ".." {
			if app, err := sc.structField(n); app != nil || err != nil {
				return app, err
			}
			return sc.field(n)
		}
		return n, nil
	case *astQuantNode:
		if t, ok := n.varType.(*astTypeNamed); ok {
			if syn := sc.bundleSyntax(t.name); syn != nil && syn.Structure {
				return sc.leaving().expandBinder(n, t, syn)
			}
		}
		var t core.HolType
		if n.varType != nil {
			t = resolveType(n.varType)
		}
		inner := sc.bind(n.varName, t)
		if n.quantifier != "∀" {
			inner = inner.leaving()
		}
		body, err := expandBundles(n.body, inner)
		if err != nil {
			return nil, err
		}
		n.body = body
		return n, nil
	case *astBinOp:
		if n.op == "⇔" && sc.root {
			// A definition's equation: its left side states the bundles
			// its constant lays out, for the body.
			sc = sc.leaving()
			left, err := expandBundles(n.left, sc)
			if err != nil {
				return nil, err
			}
			r, err := expandBundles(n.right, sc.withBundles(sc.definitionFacts(left)))
			if err != nil {
				return nil, err
			}
			n.left, n.right = left, r
			return n, nil
		}
		sc = sc.leaving()
		left, err := expandBundles(n.left, sc)
		if err != nil {
			return nil, err
		}
		right := sc
		if n.op == "⇒" || n.op == "∧" {
			right = sc.withBundles(sc.factsOf(left))
		}
		r, err := expandBundles(n.right, right)
		if err != nil {
			return nil, err
		}
		n.left, n.right = left, r
		return n, nil
	}
	sc = sc.leaving()
	switch n := node.(type) {
	case *astAbsNode:
		var t core.HolType
		if n.varType != nil {
			t = resolveType(n.varType)
		}
		body, err := expandBundles(n.body, sc.bind(n.varName, t))
		if err != nil {
			return nil, err
		}
		n.body = body
		return n, nil
	case *astPatternAbs:
		inner := sc
		for _, lf := range n.pat.leaves(nil) {
			var t core.HolType
			if lf.ty != nil {
				t = resolveType(lf.ty)
			}
			inner = inner.bind(lf.name, t)
		}
		body, err := expandBundles(n.body, inner)
		if err != nil {
			return nil, err
		}
		n.body = body
		return n, nil
	case *astBigOp:
		bound, err := expandBundles(n.bound, sc)
		if err != nil {
			return nil, err
		}
		body, err := expandBundles(n.body, sc.bind(n.binder, nil))
		if err != nil {
			return nil, err
		}
		n.bound, n.body = bound, body
		return n, nil
	case *astField:
		var err error
		n.receiver, err = expandBundles(n.receiver, sc)
		return n, err
	case *astApp:
		return sc.expandApp(n)
	case *astCong:
		var err error
		if n.left, err = expandBundles(n.left, sc); err != nil {
			return nil, err
		}
		if n.right, err = expandBundles(n.right, sc); err != nil {
			return nil, err
		}
		if n.modulus, err = expandBundles(n.modulus, sc); err != nil {
			return nil, err
		}
		return n, nil
	case *astTendsAt:
		var err error
		if n.fn, err = expandBundles(n.fn, sc); err != nil {
			return nil, err
		}
		if n.limit, err = expandBundles(n.limit, sc); err != nil {
			return nil, err
		}
		if n.point, err = expandBundles(n.point, sc); err != nil {
			return nil, err
		}
		return n, nil
	case *astNotNode:
		body, err := expandBundles(n.body, sc)
		if err != nil {
			return nil, err
		}
		n.body = body
		return n, nil
	case *astCoerce:
		op, err := expandBundles(n.operand, sc)
		if err != nil {
			return nil, err
		}
		n.operand = op
		return n, nil
	case *astNeg:
		op, err := expandBundles(n.operand, sc)
		if err != nil {
			return nil, err
		}
		n.operand = op
		return n, nil
	case *astOutfix:
		for i, a := range n.args {
			x, err := expandBundles(a, sc)
			if err != nil {
				return nil, err
			}
			n.args[i] = x
		}
		if n.sub != nil {
			x, err := expandBundles(n.sub, sc)
			if err != nil {
				return nil, err
			}
			n.sub = x
		}
		return n, nil
	}
	return node, nil
}

// field resolves `B.c` to the component of bundle B the structure's
// definition names c.
func (sc *bundleScope) field(n *astVar) (astNode, error) {
	name, comp, _ := strings.Cut(n.name, ".")
	b := sc.lookup(name)
	if b == nil {
		b = sc.familyOf(name)
	}
	if b == nil {
		return nil, &bundleError{n.pos, fmt.Sprintf("%s: %s is no bundle in scope", n.name, name)}
	}
	syn := sc.bundleSyntax(b.structure)
	for i, p := range syn.Params {
		if p.Name == comp {
			if v := nameOf(b.comps[i]); v != "" && !isHole(v) {
				return &astVar{name: v, typeAnnot: n.typeAnnot, pos: n.pos}, nil
			}
			if len(holesIn(b.comps[i], nil)) > 0 {
				return nil, &bundleError{n.pos, fmt.Sprintf("%s: the component %s of the family %s varies with its index; name a fibre", n.name, comp, name)}
			}
			if len(n.typeAnnot) > 0 {
				return nil, &bundleError{n.pos, fmt.Sprintf("%s: the component %s of %s is the term %s, which takes no instance annotation", n.name, comp, name, printKey(b.comps[i]))}
			}
			return cloneAST(b.comps[i]), nil
		}
	}
	names := make([]string, len(syn.Params))
	for i, p := range syn.Params {
		names[i] = p.Name
	}
	return nil, &bundleError{n.pos, fmt.Sprintf("%s: %s has no component %s; the components of %s are %s",
		n.name, name, comp, b.structure, strings.Join(names, ", "))}
}

// primed is base with as many primes as make it a name avoid does not
// hold.
func primed(base string, avoid map[string]bool) string {
	name := base
	for avoid[name] {
		name += "'"
	}
	return name
}

// minted is the name a bundle binder gives a component of its subject
// structure: the definition's own name where the text does not hold
// it, else that name under the bundle, N's add being N_add. A text that
// holds the prefixed name too is refused: a component is never primed
// or counted past its bundle.
func minted(bundle, base string, avoid map[string]bool) (string, error) {
	if !avoid[base] {
		return base, nil
	}
	name := bundle + "_" + base
	if avoid[name] {
		return "", fmt.Errorf("%s's component %s would be %s, which the text already binds", bundle, base, name)
	}
	return name, nil
}

// apartPrefix renames a definition's type variables apart from the
// text's while the binder's types are solved.
const apartPrefix = "%bundle%"

func apartTypes(params []BundleParam) []core.HolType {
	out := make([]core.HolType, len(params))
	for i, p := range params {
		var substs []core.TypeSubst
		for _, v := range p.Type.TypeVars() {
			substs = append(substs, core.MakeTypeSubst(v, core.MakeVarType(apartPrefix+string(v.Name()))))
		}
		out[i] = p.Type.Substitute(substs...)
	}
	return out
}

func isApart(v core.VarType) bool { return strings.HasPrefix(string(v.Name()), apartPrefix) }

// unsolvedVars is the renamed-apart variables of pattern no substitution
// in env binds, in first-occurrence order over the components.
func unsolvedVars(pattern []core.HolType, env []core.TypeSubst) []core.VarType {
	var out []core.VarType
	seen := map[core.TypeName]bool{}
	for _, s := range env {
		seen[s.VarType.Name()] = true
	}
	for _, t := range pattern {
		for _, v := range t.TypeVars() {
			if isApart(v) && !seen[v.Name()] {
				seen[v.Name()] = true
				out = append(out, v)
			}
		}
	}
	return out
}

// bundleBinderParts classifies a bundle binder's arguments: the bundles
// in scope, in order, and the types.
func (sc *bundleScope) bundleBinderParts(t *astTypeNamed) (bundles []*bundle, types []astType) {
	for _, a := range t.args {
		name := ""
		switch a := a.(type) {
		case *astTypeVar:
			name = a.name
		case *astTypeNamed:
			if len(a.args) == 0 {
				name = a.name
			}
		}
		if b := sc.lookup(name); name != "" && b != nil {
			bundles = append(bundles, b)
			continue
		}
		types = append(types, a)
	}
	return bundles, types
}

// fillFromBundles fills the structure's component names from the
// bundles, each taking the first unused layout of its structure
// (fillLayouts), and solves the type variables those components fix.
func (sc *bundleScope) fillFromBundles(syn *BundleSyntax, structure string, bundles []*bundle, pattern []core.HolType) (filled []astNode, env []core.TypeSubst, err error) {
	filled = make([]astNode, len(syn.Params))
	layouts := sc.fillLayouts(syn)
	used := make([]bool, len(layouts))
	instantiable := utils.Predicate[core.VarType](isApart)
	for _, b := range bundles {
		li := -1
		for i := range layouts {
			if !used[i] && layouts[i].Structure == b.structure {
				li = i
				break
			}
		}
		if li < 0 {
			return nil, nil, fmt.Errorf("%s is a bundle of %s, which %s takes nowhere (or not once more)", b.name, b.structure, structure)
		}
		used[li] = true
		for k, slot := range layouts[li].Slots {
			if slot < 0 {
				continue
			}
			if filled[slot] != nil && printKey(filled[slot]) != printKey(b.comps[k]) {
				return nil, nil, fmt.Errorf("%s gives %s's component %s as %s, and another bundle gave it as %s",
					b.name, structure, syn.Params[slot].Name, printKey(b.comps[k]), printKey(filled[slot]))
			}
			filled[slot] = b.comps[k]
			if k < len(b.types) && b.types[k] != nil && !core.MatchTypeInto(pattern[slot], b.types[k], instantiable, &env) {
				return nil, nil, fmt.Errorf("%s's component %s has type %s, where %s takes %s",
					b.name, printKey(b.comps[k]), ext.FormatType(b.types[k]), structure, ext.FormatType(syn.Params[slot].Type))
			}
		}
	}
	return filled, env, nil
}

// expandBinder rewrites a bundle binder.
func (sc *bundleScope) expandBinder(n *astQuantNode, t *astTypeNamed, syn *BundleSyntax) (astNode, error) {
	if n.quantifier != "∀" && n.quantifier != "∃" {
		return nil, &bundleError{n.pos, fmt.Sprintf("a bundle binder is ∀ or ∃, not %s", n.quantifier)}
	}
	bs, err := sc.binderScope(n, t, syn)
	if err != nil {
		return nil, err
	}
	body, err := expandBundles(n.body, bs.inner)
	if err != nil {
		return nil, err
	}
	op := "⇒"
	if n.quantifier == "∃" {
		op = "∧"
	}
	var out astNode = &astBinOp{op: op, left: bs.fact, right: body, pos: n.pos}
	for k := len(bs.fresh) - 1; k >= 0; k-- {
		i := bs.fresh[k]
		out = &astQuantNode{quantifier: n.quantifier, varName: bs.names[i], varType: astTypeOf(bs.types[i]), body: out, pos: n.pos}
	}
	return out, nil
}

// _BinderScope is what a bundle binder opens for its body: the scope
// with the binder's components and bundles bound, the structure fact the
// binder states (fact), the components' names and types, and which of
// them the binder binds fresh (the others are given by bundles in scope).
type _BinderScope struct {
	inner *bundleScope
	fact  *astApp
	names []string
	types []core.HolType
	fresh []int
}

// binderScope reads a bundle binder `∀x:S(…).`: its components filled
// from the bundles in scope or minted after the predicate's own names,
// and the scope its body is read in — the fold of a text that already
// spells the binder reads the body there too.
func (sc *bundleScope) binderScope(n *astQuantNode, t *astTypeNamed, syn *BundleSyntax) (*_BinderScope, error) {
	bundles, typeArgs := sc.bundleBinderParts(t)
	pattern := apartTypes(syn.Params)
	filled, env, err := sc.fillFromBundles(syn, t.name, bundles, pattern)
	if err != nil {
		return nil, &bundleError{n.pos, fmt.Sprintf("%s:%s: %v", n.varName, t.name, err)}
	}
	free := unsolvedVars(pattern, env)
	if len(free) != len(typeArgs) {
		return nil, &bundleError{n.pos, fmt.Sprintf("%s:%s takes %d type(s) beside its bundles, for the components no bundle gives; got %d",
			n.varName, t.name, len(free), len(typeArgs))}
	}
	for i, v := range free {
		env = append(env, core.MakeTypeSubst(v, resolveType(typeArgs[i])))
	}
	avoid := make(map[string]bool, len(sc.avoid))
	for k := range sc.avoid {
		avoid[k] = true
	}
	for _, f := range filled {
		if v := nameOf(f); v != "" {
			avoid[v] = true
		}
	}
	comps := make([]astNode, len(syn.Params))
	types := make([]core.HolType, len(syn.Params))
	var fresh []int
	names := make([]string, len(syn.Params))
	for i, p := range syn.Params {
		types[i] = pattern[i].Substitute(env...)
		if filled[i] != nil {
			comps[i] = filled[i]
			continue
		}
		if i == syn.Subject {
			names[i] = n.varName
		} else if syn.Subject >= 0 {
			name, err := minted(n.varName, p.Name, avoid)
			if err != nil {
				return nil, &bundleError{n.pos, fmt.Sprintf("%s:%s: %v", n.varName, t.name, err)}
			}
			names[i] = name
		} else {
			names[i] = primed(p.Name, avoid)
		}
		avoid[names[i]] = true
		comps[i] = varNode(names[i], n.pos)
		fresh = append(fresh, i)
	}
	if syn.Subject >= 0 && filled[syn.Subject] != nil {
		return nil, &bundleError{n.pos, fmt.Sprintf("%s:%s: the subject %s is given by a bundle, so the binder names nothing", n.varName, t.name, printKey(filled[syn.Subject]))}
	}
	inner := sc
	for _, i := range fresh {
		inner = inner.bind(names[i], types[i])
	}
	fact := &astApp{fun: &astVar{name: t.name, pos: n.pos}, pos: n.pos}
	for _, c := range comps {
		fact.args = append(fact.args, cloneAST(c))
	}
	inner = inner.withBundles(bundlesOfFact(sc.table, t.name, comps, types, nil))
	if syn.Subject < 0 {
		inner = inner.bind(n.varName, nil).withBundles([]*bundle{{name: n.varName, structure: t.name, comps: comps, types: types, carrier: varNode(n.varName, n.pos)}})
	}
	return &_BinderScope{inner: inner, fact: fact, names: names, types: types, fresh: fresh}, nil
}

// astTypeOf spells a kernel type as the parser reads it: the type's
// print, read back by the type parser, so that a fold and a parse of
// the folded text give one AST.
func astTypeOf(t core.HolType) astType {
	text := ext.FormatType(t)
	normalized, _ := NormalizeTextSymbols(text)
	tokens, lexErr := lex(normalized)
	if lexErr != nil {
		panic(fmt.Sprintf("bundle: the type %s does not lex: %s", text, lexErr.Message))
	}
	par := &parser{tokens: tokens}
	out, perr := par.parseType()
	if perr != nil {
		panic(fmt.Sprintf("bundle: the type %s does not parse: %s", text, perr.Message))
	}
	return out
}

// expandApp rewrites an application: its tuples spliced, its bundle
// arguments laid out.
func (sc *bundleScope) expandApp(n *astApp) (astNode, error) {
	head, isVar := n.fun.(*astVar)
	if isVar && len(head.typeAnnot) == 0 {
		if s := sc.syntaxOf(head.name); s != nil && s.Tuple != nil {
			return nil, &bundleError{n.pos, fmt.Sprintf("%s is a tuple: it stands among the arguments of an application", head.name)}
		}
	}
	fun, err := expandBundles(n.fun, sc)
	if err != nil {
		return nil, err
	}
	n.fun = fun
	var args []astNode
	spliced := false
	for _, a := range n.args {
		if terms, ok, err := sc.tupleTerms(a); err != nil {
			return nil, err
		} else if ok {
			args = append(args, terms...)
			spliced = true
			continue
		}
		args = append(args, a)
	}
	for i, a := range args {
		x, err := expandBundles(a, sc)
		if err != nil {
			return nil, err
		}
		args[i] = x
	}
	if spliced {
		n.args = args
	}
	if !isVar || len(head.typeAnnot) > 0 {
		n.args = args
		return n, nil
	}
	syn := sc.bundleSyntax(head.name)
	if syn == nil {
		n.args = args
		return n, nil
	}
	laid, changed, err := sc.layOut(head.name, syn, sc.syntaxOf(head.name).Implicit, args)
	if err != nil {
		return nil, &bundleError{n.pos, err.Error()}
	}
	if changed {
		n.args = laid
	} else {
		n.args = args
	}
	return n, nil
}

// layOut fills a constant's parameters from its arguments: a bundle
// whose structure the constant lays out fills that layout, the others
// fill the remaining parameters in order. changed is false when no
// bundle took a layout. An application with every parameter spelled
// is read as spelled; one with exactly the arguments its implicit
// prefix leaves, every implicit name bound here, is the implicit
// completion's (implicit.go) — and where a bundle would lay it out
// differently, the two readings are refused together. A resident
// bundle's component the text spells by a surface name (`X₀` as `X`)
// is the bound implicit name of that spelling: the short spelling under
// the one resident instance reads one way.
func (sc *bundleScope) layOut(constName string, syn *BundleSyntax, implicit []string, args []astNode) ([]astNode, bool, error) {
	if len(args) >= len(syn.Params) {
		return args, false, nil
	}
	if len(implicit) > 0 && len(args) == len(syn.Params)-len(implicit) {
		bound := true
		for _, name := range implicit {
			if !sc.avoid[name] {
				bound = false
				break
			}
		}
		if bound {
			laid, took, err := sc.layOutBundles(constName, syn, args)
			if err != nil || !took {
				return args, false, nil
			}
			same := true
			for i, name := range implicit {
				if v, ok := laid[i].(*astVar); !ok || (v.name != name && sc.surface[v.name] != name) {
					same = false
				}
			}
			for i, a := range args {
				if same && printASTNode(laid[len(implicit)+i]) != printASTNode(a) {
					same = false
				}
			}
			if same {
				return args, false, nil
			}
			return nil, false, fmt.Errorf("%s(%s) reads two ways: its implicit components are the bound %s, "+
				"and its bundles lay out %s — spell the components", constName, printArgs(args),
				strings.Join(implicit, ", "), printArgs(laid))
		}
	}
	return sc.layOutBundles(constName, syn, args)
}

func printArgs(args []astNode) string {
	parts := make([]string, len(args))
	for i, a := range args {
		parts[i] = printASTNode(a)
	}
	return strings.Join(parts, ", ")
}

// layOutBundles is layOut's bundle reading.
func (sc *bundleScope) layOutBundles(constName string, syn *BundleSyntax, args []astNode) ([]astNode, bool, error) {
	usable := func(a astNode) *bundle {
		if v, ok := a.(*astVar); ok && len(v.typeAnnot) > 0 {
			return nil
		}
		return sc.lookupTerm(a)
	}
	layouts := sc.fillLayouts(syn)
	if syn.Structure {
		layouts = append([]BundleLayout{syn.Layouts[0]}, layouts...)
	}
	hasLayout := func(structure string) bool {
		for _, l := range layouts {
			if l.Structure == structure {
				return true
			}
		}
		return false
	}
	any := false
	for _, a := range args {
		if b := usable(a); b != nil && hasLayout(b.structure) {
			any = true
			break
		}
	}
	if !any {
		return args, false, nil
	}
	filled := make([]astNode, len(syn.Params))
	used := make([]bool, len(layouts))
	took := false
	// Arguments past the parameters — a definition applied further than
	// its binders, the map connecting_hom(P', P, i, p, n) at a class.
	var extra []astNode
	for _, a := range args {
		if b := usable(a); b != nil {
			// The first unused layout of its structure whose parameters
			// the arguments so far leave free or fill as the bundle
			// would: a module given operation by operation takes the
			// first layout, and the bundle after it the second.
			li := -1
			for i := range layouts {
				if used[i] || layouts[i].Structure != b.structure {
					continue
				}
				fits := true
				for k, slot := range layouts[i].Slots {
					if slot < 0 || filled[slot] == nil {
						continue
					}
					if sc.key(filled[slot]) != sc.key(b.comps[k]) {
						fits = false
						break
					}
				}
				if fits {
					li = i
					break
				}
			}
			if li >= 0 {
				used[li] = true
				took = true
				for k, slot := range layouts[li].Slots {
					if slot < 0 {
						continue
					}
					c := substituteTuple(b.comps[k], map[string]astNode{}, a.nodePos())
					if prev := filled[slot]; prev != nil {
						if sc.key(prev) != sc.key(c) {
							return nil, false, fmt.Errorf("%s: %s gives the parameter %s as %s, where it is already %s",
								constName, b.name, syn.Params[slot].Name, printKey(c), printASTNode(prev))
						}
						continue
					}
					filled[slot] = c
				}
				continue
			}
		}
		slot := slices.Index(filled, nil)
		if slot < 0 {
			extra = append(extra, a)
			continue
		}
		filled[slot] = a
	}
	if !took {
		return args, false, nil
	}
	last := len(filled)
	for last > 0 && filled[last-1] == nil {
		last--
	}
	for i := range last {
		if filled[i] == nil {
			return nil, false, fmt.Errorf("%s: no argument gives the parameter %s", constName, syn.Params[i].Name)
		}
	}
	if len(extra) > 0 && last < len(filled) {
		return nil, false, fmt.Errorf("%s: no argument gives the parameter %s", constName, syn.Params[last].Name)
	}
	// A reading exists only where the variables it places have the
	// parameters' types: `connecting_hom(P', d', P, d, i, p, n)`, the
	// complexes' components spelled and the map's prefix left out, puts
	// d' where a complex's P goes under the bundles' reading, which is
	// then none, and the implicit completion's stands.
	if sc.laidMistyped(syn, filled[:last]) {
		return args, false, nil
	}
	return append(filled[:last], extra...), true, nil
}

// laidMistyped reports whether an argument the bundles' reading places
// at a parameter is a variable known here to have a type the parameter
// does not take.
func (sc *bundleScope) laidMistyped(syn *BundleSyntax, laid []astNode) bool {
	pattern := apartTypes(syn.Params)
	instantiable := utils.Predicate[core.VarType](isApart)
	var env []core.TypeSubst
	for i, a := range laid {
		v := nameOf(a)
		if v == "" || i >= len(pattern) {
			continue
		}
		t := sc.types[v]
		if t == nil {
			continue
		}
		if !core.MatchTypeInto(pattern[i], t, instantiable, &env) {
			return true
		}
	}
	return false
}

// tupleTerms reads a in an argument position: a tuple's terms, with its
// parameters replaced by the call's arguments.
func (sc *bundleScope) tupleTerms(a astNode) ([]astNode, bool, error) {
	app, ok := a.(*astApp)
	if !ok {
		return nil, false, nil
	}
	head, ok := app.fun.(*astVar)
	if !ok || len(head.typeAnnot) > 0 {
		return nil, false, nil
	}
	s := sc.syntaxOf(head.name)
	if s == nil || s.Tuple == nil {
		return nil, false, nil
	}
	tu := s.Tuple
	params := tu.params()
	if len(app.args) != len(params) {
		return nil, false, &bundleError{app.pos, fmt.Sprintf("the tuple %s takes %d argument(s), got %d", head.name, len(params), len(app.args))}
	}
	sub := map[string]astNode{}
	for i, p := range params {
		sub[p] = app.args[i]
		// A parameter standing for a bundle — a name, or a fibre such
		// as F(U) — reads through its fields: each is the component.
		if b := sc.lookupTerm(app.args[i]); b != nil {
			if syn := sc.bundleSyntax(b.structure); syn != nil {
				for k, bp := range syn.Params {
					if k < len(b.comps) {
						sub[p+"."+bp.Name] = b.comps[k]
					}
				}
			}
		}
	}
	var out []astNode
	for _, text := range tu.Terms {
		tmpl, err := parseTupleTerm(text)
		if err != nil {
			return nil, false, &bundleError{app.pos, fmt.Sprintf("the tuple %s: %v", head.name, err)}
		}
		var untyped string
		term := substituteTyped(tmpl, sub, app.pos, &untyped)
		if untyped != "" {
			return nil, false, &bundleError{app.pos, fmt.Sprintf("the tuple %s: its parameter %s stands for a type, and %s spells none a term can (a function type is no argument)",
				head.name, untyped, printASTNode(sub[untyped]))}
		}
		out = append(out, term)
	}
	return out, true, nil
}

// CheckTupleTerm reports whether text reads as one of a tuple's terms.
func CheckTupleTerm(text string) error {
	_, err := parseTupleTerm(text)
	return err
}

// parseTupleTerm reads one of a tuple's terms.
func parseTupleTerm(text string) (astNode, error) {
	normalized, _ := NormalizeTextSymbols(text)
	tokens, lexErr := lex(normalized)
	if lexErr != nil {
		return nil, fmt.Errorf("lex %q: %s", text, lexErr.Message)
	}
	par := &parser{tokens: tokens}
	node, perr := par.parseExpr()
	if perr != nil {
		return nil, fmt.Errorf("parse %q: %s", text, perr.Message)
	}
	if par.pos < len(par.tokens) && par.tokens[par.pos].kind != tokEOF {
		return nil, fmt.Errorf("trailing tokens in %q", text)
	}
	return node, nil
}

// substituteTuple replaces a tuple's parameters in a fresh copy of its
// term: a parameter as a term by the argument, as a type (an instance
// annotation's, a binder's) by the argument read as a type name.
func substituteTuple(node astNode, sub map[string]astNode, pos int) astNode {
	return substituteTyped(node, sub, pos, nil)
}

// substituteTyped is substituteTuple naming, in untyped, a parameter in
// a type position whose argument reads as no type.
func substituteTyped(node astNode, sub map[string]astNode, pos int, untyped *string) astNode {
	typeOf := func(name string) (astType, bool) {
		a, ok := sub[name]
		if !ok {
			return nil, false
		}
		t := termAsType(a)
		if t == nil && untyped != nil && *untyped == "" {
			*untyped = name
		}
		return t, t != nil
	}
	var subType func(t astType) astType
	subType = func(t astType) astType {
		switch t := t.(type) {
		case *astTypeVar:
			if r, ok := typeOf(t.name); ok {
				return r
			}
			return &astTypeVar{name: t.name}
		case *astTypeNamed:
			if len(t.args) == 0 {
				if r, ok := typeOf(t.name); ok {
					return r
				}
			}
			out := &astTypeNamed{name: t.name}
			for _, a := range t.args {
				out.args = append(out.args, subType(a))
			}
			return out
		case *astTypeFun:
			return &astTypeFun{domain: subType(t.domain), codomain: subType(t.codomain), tuple: t.tuple}
		}
		return t
	}
	subAnnot := func(annot []typeAnnotBinding) []typeAnnotBinding {
		if len(annot) == 0 {
			return nil
		}
		out := make([]typeAnnotBinding, len(annot))
		for i, b := range annot {
			out[i] = b
			out[i].ty = subType(b.ty)
		}
		return out
	}
	var walk func(n astNode) astNode
	walk = func(n astNode) astNode {
		switch n := n.(type) {
		case *astVar:
			if a, ok := sub[n.name]; ok && len(n.typeAnnot) == 0 {
				return a
			}
			// A field of a parameter, `X.add'`: the field of the bundle
			// the argument names.
			if param, field, ok := strings.Cut(n.name, "."); ok {
				if a, isParam := sub[param]; isParam {
					if v, isVar := a.(*astVar); isVar {
						return &astVar{name: v.name + "." + field, typeAnnot: subAnnot(n.typeAnnot), pos: pos}
					}
				}
			}
			return &astVar{name: n.name, typeAnnot: subAnnot(n.typeAnnot), pos: pos}
		case *astField:
			return fieldNode(walk(n.receiver), n.name, pos)
		case *astApp:
			out := &astApp{fun: walk(n.fun), pos: pos, dims: n.dims, dimsPlaced: n.dimsPlaced}
			for _, a := range n.args {
				out.args = append(out.args, walk(a))
			}
			return out
		case *astBinOp:
			return &astBinOp{op: n.op, left: walk(n.left), right: walk(n.right), pos: pos, parens: n.parens}
		case *astNotNode:
			return &astNotNode{body: walk(n.body), pos: pos}
		case *astNeg:
			return &astNeg{operand: walk(n.operand), pos: pos}
		case *astCoerce:
			return &astCoerce{operand: walk(n.operand), pos: pos}
		case *astQuantNode:
			var t astType
			if n.varType != nil {
				t = subType(n.varType)
			}
			return &astQuantNode{quantifier: n.quantifier, varName: n.varName, varType: t, body: walk(n.body), pos: pos}
		case *astAbsNode:
			var t astType
			if n.varType != nil {
				t = subType(n.varType)
			}
			return &astAbsNode{varName: n.varName, varType: t, body: walk(n.body), pos: pos}
		case *astNumLit:
			return &astNumLit{value: n.value, pos: pos}
		case *astConst:
			return &astConst{name: n.name, pos: pos}
		case *astAbbrev:
			return &astAbbrev{name: n.name, ties: subAnnot(n.ties), pos: pos}
		}
		return n
	}
	return walk(node)
}

// termAsType reads a tuple argument that stands where a type does — a
// name, `prod(B, C)` — as that type; nil for one that spells no type.
func termAsType(a astNode) astType {
	switch a := a.(type) {
	case *astVar:
		if len(a.typeAnnot) > 0 || strings.Contains(a.name, ".") {
			return nil
		}
		return &astTypeNamed{name: a.name}
	case *astApp:
		head, ok := a.fun.(*astVar)
		if !ok || len(head.typeAnnot) > 0 {
			return nil
		}
		out := &astTypeNamed{name: head.name}
		for _, x := range a.args {
			t := termAsType(x)
			if t == nil {
				return nil
			}
			out.args = append(out.args, t)
		}
		return out
	}
	return nil
}

// typeAsTerm is termAsType's inverse, for writing a fold's argument;
// nil for a type no term spells (a function type).
func typeAsTerm(t astType, pos int) astNode {
	switch t := t.(type) {
	case *astTypeNamed:
		if len(t.args) == 0 {
			return &astVar{name: t.name, pos: pos}
		}
		out := &astApp{fun: &astVar{name: t.name, pos: pos}, pos: pos}
		for _, x := range t.args {
			a := typeAsTerm(x, pos)
			if a == nil {
				return nil
			}
			out.args = append(out.args, a)
		}
		return out
	case *astTypeVar:
		return &astVar{name: t.name, pos: pos}
	}
	return nil
}

// printASTNode spells a node for a diagnostic.
func printASTNode(n astNode) string {
	var pr stmtPrinter
	if s, err := pr.node(n, 0, true); err == nil {
		return s
	}
	return fmt.Sprintf("%T", n)
}

// ---------------------------------------------------------------------------
// The printer's half
// ---------------------------------------------------------------------------

// foldBundles writes node's spelled-out structure forms back as bundles,
// top-down: a binder run a structure fact closes, as the bundle binder;
// a constant's arguments a bundle in scope fills, as the bundle; a run
// of arguments a tuple matches, as the tuple.
func foldBundles(node astNode, sc *bundleScope, tuples []string, changed *bool) astNode {
	switch n := node.(type) {
	case *astQuantNode:
		if folded := sc.leaving().foldBinder(n, tuples, changed); folded != nil {
			return folded
		}
		if named, ok := n.varType.(*astTypeNamed); ok {
			if syn := sc.bundleSyntax(named.name); syn != nil && syn.Structure {
				// A bundle binder the text already spells: its body is read
				// with the binder's components and bundles in scope, so a
				// fibre or a component in it folds as under the fact.
				if bs, err := sc.leaving().binderScope(n, named, syn); err == nil {
					n.body = foldBundles(n.body, bs.inner, tuples, changed)
					return n
				}
			}
		}
		var t core.HolType
		if n.varType != nil {
			t = resolveType(n.varType)
		}
		inner := sc.bind(n.varName, t)
		if n.quantifier != "∀" {
			inner = inner.leaving()
		}
		n.body = foldBundles(n.body, inner, tuples, changed)
		return n
	case *astBinOp:
		if n.op == "⇔" && sc.root {
			sc = sc.leaving()
			sc.markStatements(n)
			right := sc.withBundles(sc.definitionFacts(n.left))
			n.left = foldBundles(n.left, sc, tuples, changed)
			n.right = foldBundles(n.right, right, tuples, changed)
			return n
		}
		sc = sc.leaving()
		right := sc
		if n.op == "⇒" || n.op == "∧" {
			right = sc.withBundles(sc.factsOf(n.left))
		}
		n.left = foldBundles(n.left, sc, tuples, changed)
		n.right = foldBundles(n.right, right, tuples, changed)
		return n
	}
	sc = sc.leaving()
	switch n := node.(type) {
	case *astAbsNode:
		var t core.HolType
		if n.varType != nil {
			t = resolveType(n.varType)
		}
		n.body = foldBundles(n.body, sc.bind(n.varName, t), tuples, changed)
		return n
	case *astPatternAbs:
		inner := sc
		for _, lf := range n.pat.leaves(nil) {
			inner = inner.bind(lf.name, nil)
		}
		n.body = foldBundles(n.body, inner, tuples, changed)
		return n
	case *astBigOp:
		n.bound = foldBundles(n.bound, sc, tuples, changed)
		n.body = foldBundles(n.body, sc.bind(n.binder, nil), tuples, changed)
		return n
	case *astField:
		n.receiver = foldBundles(n.receiver, sc, tuples, changed)
	case *astApp:
		n.fun = foldBundles(n.fun, sc, tuples, changed)
		for i, a := range n.args {
			n.args[i] = foldBundles(a, sc, tuples, changed)
		}
		sc.foldArgs(n, changed)
		sc.foldTuples(n, tuples, changed)
		return n
	case *astCong:
		n.left = foldBundles(n.left, sc, tuples, changed)
		n.right = foldBundles(n.right, sc, tuples, changed)
		n.modulus = foldBundles(n.modulus, sc, tuples, changed)
	case *astTendsAt:
		n.fn = foldBundles(n.fn, sc, tuples, changed)
		n.limit = foldBundles(n.limit, sc, tuples, changed)
		n.point = foldBundles(n.point, sc, tuples, changed)
	case *astNotNode:
		n.body = foldBundles(n.body, sc, tuples, changed)
	case *astCoerce:
		n.operand = foldBundles(n.operand, sc, tuples, changed)
	case *astNeg:
		n.operand = foldBundles(n.operand, sc, tuples, changed)
	case *astOutfix:
		for i, a := range n.args {
			n.args[i] = foldBundles(a, sc, tuples, changed)
		}
		if n.sub != nil {
			n.sub = foldBundles(n.sub, sc, tuples, changed)
		}
	}
	return node
}

// foldBinder writes `∀x … ∀c₁ … ∀cₖ. S(…) ⇒ body` back as `∀x … ∀N:S(…). body`
// when the trailing binders are exactly the components no bundle in
// scope gives, the subject among them named N, each named as the
// expansion would name it. nil when the run is no such binder.
func (sc *bundleScope) foldBinder(n *astQuantNode, tuples []string, changed *bool) astNode {
	q := n.quantifier
	if q != "∀" && q != "∃" {
		return nil
	}
	if t, ok := n.varType.(*astTypeNamed); ok && sc.bundleSyntax(t.name) != nil {
		return nil
	}
	var run []*astQuantNode
	var inner astNode = n
	for {
		qn, ok := inner.(*astQuantNode)
		if !ok || qn.quantifier != q || qn.varType == nil {
			break
		}
		run = append(run, qn)
		inner = qn.body
	}
	op := "⇒"
	if q == "∃" {
		op = "∧"
	}
	// This is the quantifier run's entire body; enclosing it in
	// parentheses changes neither its operator nor its scope. The
	// residual right side keeps its own grouping when folded below.
	bin, ok := inner.(*astBinOp)
	if !ok || bin.op != op {
		return nil
	}
	fact, ok := bin.left.(*astApp)
	if !ok {
		return nil
	}
	head, ok := fact.fun.(*astVar)
	if !ok || len(head.typeAnnot) > 0 {
		return nil
	}
	syn := sc.bundleSyntax(head.name)
	if syn == nil || !syn.Structure || (syn.Subject < 0 && syn.Letter == "") || len(fact.args) != len(syn.Params) {
		return nil
	}
	args := make([]string, len(fact.args))
	for i, a := range fact.args {
		v, ok := a.(*astVar)
		if !ok || len(v.typeAnnot) > 0 {
			return nil
		}
		args[i] = v.name
	}
	// The run's leading binders stay; the trailing ones are candidates.
	// Which bundles cover which components is decided over the scope
	// AFTER the leading binders, which the trailing ones see.
	for lead := 0; lead < len(run); lead++ {
		outer := sc
		for _, qn := range run[:lead] {
			outer = outer.bind(qn.varName, resolveType(qn.varType))
		}
		trailing := run[lead:]
		folded := outer.foldBinderAt(head.name, syn, args, trailing, bin, tuples, changed)
		if folded == nil {
			continue
		}
		var out = folded
		for k := lead - 1; k >= 0; k-- {
			qn := run[k]
			qn.body = out
			out = qn
		}
		return out
	}
	return nil
}

func (sc *bundleScope) foldBinderAt(structure string, syn *BundleSyntax, args []string, trailing []*astQuantNode, bin *astBinOp, tuples []string, changed *bool) astNode {
	// The bundles in scope that give sub-structures, in layout order.
	var bundles []*bundle
	covered := make([]bool, len(args))
	for _, l := range sc.fillLayouts(syn) {
		for _, b := range sc.bundles {
			if b == nil || b.structure != l.Structure || len(b.index) > 0 {
				continue
			}
			match := true
			for k, slot := range l.Slots {
				if slot < 0 || args[slot] != nameOf(b.comps[k]) {
					match = false
					break
				}
			}
			if match {
				dup := false
				for _, prev := range bundles {
					if prev == b {
						dup = true
					}
				}
				if dup {
					continue
				}
				bundles = append(bundles, b)
				for _, slot := range l.Slots {
					covered[slot] = true
				}
				break
			}
		}
	}
	var fresh []int
	for i := range args {
		if !covered[i] {
			fresh = append(fresh, i)
		}
	}
	if len(fresh) != len(trailing) || (syn.Subject >= 0 && !slices.Contains(fresh, syn.Subject)) {
		return nil
	}
	for k, i := range fresh {
		if trailing[k].varName != args[i] {
			return nil
		}
	}
	// The expansion's names: replay its choice.
	avoid := make(map[string]bool, len(sc.avoid))
	for k := range sc.avoid {
		avoid[k] = true
	}
	for i, c := range covered {
		if c {
			avoid[args[i]] = true
		}
	}
	for _, i := range fresh {
		want := args[i]
		if i != syn.Subject {
			var got string
			if syn.Subject >= 0 {
				name, err := minted(args[syn.Subject], syn.Params[i].Name, avoid)
				if err != nil {
					return nil
				}
				got = name
			} else {
				got = primed(syn.Params[i].Name, avoid)
			}
			if got != want {
				return nil
			}
		}
		avoid[want] = true
	}
	// The types: the fresh binders' annotations and the bundles' types
	// solve the definition's variables; the ones no bundle fixes are
	// the binder's type arguments.
	pattern := apartTypes(syn.Params)
	_, env, err := sc.fillFromBundles(syn, structure, bundles, pattern)
	if err != nil {
		return nil
	}
	free := unsolvedVars(pattern, env)
	instantiable := utils.Predicate[core.VarType](isApart)
	for k, i := range fresh {
		if !core.MatchTypeInto(pattern[i], resolveType(trailing[k].varType), instantiable, &env) {
			return nil
		}
	}
	t := &astTypeNamed{name: structure}
	for _, b := range bundles {
		t.args = append(t.args, &astTypeNamed{name: b.name})
	}
	for _, v := range free {
		var val core.HolType
		for _, s := range env {
			if s.VarType.Name() == v.Name() {
				val = s.HolType
			}
		}
		if val == nil {
			return nil
		}
		t.args = append(t.args, astTypeOf(val))
	}
	// The binder's name: the subject, or the structure's letter primed
	// until free of every name the expansion sees.
	var subject string
	if syn.Subject >= 0 {
		subject = args[syn.Subject]
	} else {
		subject = primed(syn.Letter, avoid)
	}
	*changed = true
	var binds []string
	for i, a := range args {
		if i != syn.Subject {
			binds = append(binds, a)
		}
	}
	inner := sc
	for k, i := range fresh {
		inner = inner.bind(args[i], resolveType(trailing[k].varType))
	}
	types := make([]core.HolType, len(args))
	argNodes := make([]astNode, len(args))
	for i, a := range args {
		types[i] = inner.types[a]
		argNodes[i] = varNode(a, trailing[0].pos)
	}
	inner = inner.withBundles(bundlesOfFact(sc.table, structure, argNodes, types, nil))
	if syn.Subject < 0 {
		inner = inner.bind(subject, nil).withBundles([]*bundle{{name: subject, structure: structure, comps: argNodes, types: types, carrier: varNode(subject, trailing[0].pos)}})
	}
	body := foldBundles(bin.right, inner, tuples, changed)
	return &astQuantNode{quantifier: trailing[0].quantifier, varName: subject, varType: t, body: body, pos: trailing[0].pos, binds: binds}
}

// foldArgs writes the arguments of a constant's application that a
// bundle in scope fills back as the bundle: a structure applied to the
// components of a bundle of it already in scope is written as that
// bundle — `comm_ring_on(F(U))`, `local_ring_on(stalk_ring(x))` — unless its
// layouts name every other component as a bundle too, when it is
// written over those, `ring_homomorphism(F(U), F(V), res(U, V))`; any
// other application folds each layout a bundle in scope fills — a
// plain one by its components, a family by its templates, the holes
// read off the arguments. A structure fact over variables is what
// states its bundles and is left spelled unless it restates one in
// scope; one over terms — the ring on F(U) under the sheaf F — folds
// the layouts its bundles fill. An application a definition's equation
// states (astApp.stated) is left spelled in full.
func (sc *bundleScope) foldArgs(n *astApp, changed *bool) {
	if n.stated {
		return
	}
	head, ok := n.fun.(*astVar)
	if !ok || len(head.typeAnnot) > 0 {
		return
	}
	syn := sc.bundleSyntax(head.name)
	if syn == nil || len(n.args) == 0 {
		return
	}
	// The arguments at the parameters; an application may stop short of
	// them (a map passed on) or run past them (a definition applied
	// further than its binders).
	given := min(len(n.args), len(syn.Params))
	params, rest := n.args[:given], n.args[given:]
	overVariables := syn.Structure
	if syn.Structure {
		for _, a := range params {
			if nameOf(a) == "" {
				overVariables = false
				break
			}
		}
	}
	var args []astNode
	var whole *bundle
	if syn.Structure && len(n.args) == len(syn.Params) {
		whole = sc.bundleOver(head.name, params, syn.Layouts[0].Slots)
	}
	starts := map[int]astNode{}
	if !overVariables {
		consumed := make([]bool, len(params))
		for _, l := range sc.fillLayouts(syn) {
			if slices.ContainsFunc(l.Slots, func(slot int) bool { return slot >= given }) {
				continue
			}
			b := sc.bundleOver(l.Structure, params, l.Slots)
			if b == nil {
				continue
			}
			// The bundle stands at the first of its slots no earlier
			// bundle took: two layouts may share components (the
			// inclusion's and the projection's in `short_exact_modules(i,
			// p)` share the ring and the middle module), as the expansion
			// lets them where the two agree.
			first := -1
			for _, slot := range l.Slots {
				if slot >= 0 && !consumed[slot] && (first < 0 || slot < first) {
					first = slot
				}
			}
			if first < 0 {
				continue
			}
			starts[first] = b.carrier
			for _, slot := range l.Slots {
				if slot >= 0 {
					consumed[slot] = true
				}
			}
		}
		for i, a := range params {
			if len(starts) == 0 {
				break
			}
			if c, ok := starts[i]; ok {
				args = append(args, cloneAST(c))
				continue
			}
			if consumed[i] {
				continue
			}
			args = append(args, a)
		}
	}
	// The bundle itself, unless the layouts leave nothing but the
	// subject beside the bundles they name.
	if whole != nil && (args == nil || len(args) != len(starts)+1 || (syn.Subject >= 0 && starts[syn.Subject] != nil)) {
		args = []astNode{cloneAST(whole.carrier)}
	}
	if args == nil {
		return
	}
	args = append(args, rest...)
	// The expansion must read the same: each bundle takes the first
	// unused layout of its structure, in argument order.
	check := sc.clone()
	laid, took, err := check.layOut(head.name, syn, sc.syntaxOf(head.name).Implicit, args)
	if err != nil || !took || len(laid) != len(n.args) {
		return
	}
	for i := range laid {
		if sc.key(laid[i]) != sc.key(n.args[i]) {
			return
		}
	}
	n.args = args
	*changed = true
}

// bundleOver is the bundle in scope of structure whose components are
// the arguments at slots — a family's, with its holes read off them —
// as the instance; nil when none is, or two read them apart.
func (sc *bundleScope) bundleOver(structure string, args []astNode, slots []int) *bundle {
	var found *bundle
	for _, b := range sc.bundles {
		if b == nil || b.structure != structure || b.carrier == nil || len(b.comps) != len(slots) {
			continue
		}
		bind := map[string]astNode{}
		match := true
		for k, slot := range slots {
			if slot < 0 {
				continue
			}
			if slot >= len(args) || !matchTemplate(sc.spelledOut(b.comps[k]), sc.spelledOut(args[slot]), bind) {
				match = false
				break
			}
		}
		if !match {
			continue
		}
		inst := b.instance(bind, args[0].nodePos())
		if inst == nil || !inst.foldable() {
			continue
		}
		if found != nil && found.key() != inst.key() {
			return nil
		}
		found = inst
	}
	return found
}

// tupleTemplates holds each tuple term parsed once, by its text. The
// folder matches every application of a text against every tuple in
// scope, and a parse reads nothing but the text, so one parse serves
// every match.
var tupleTemplates sync.Map // text → _TupleTemplate

type _TupleTemplate struct {
	node astNode
	err  error
}

// tupleTemplate is parseTupleTerm read through tupleTemplates. The node
// is shared by every caller: it is matched against, never modified
// (matchTuple binds the argument's nodes, not the template's).
func tupleTemplate(text string) (astNode, error) {
	if v, ok := tupleTemplates.Load(text); ok {
		t := v.(_TupleTemplate)
		return t.node, t.err
	}
	node, err := parseTupleTerm(text)
	tupleTemplates.Store(text, _TupleTemplate{node: node, err: err})
	return node, err
}

// foldTuples writes a run of arguments a tuple's terms match back as the
// tuple.
func (sc *bundleScope) foldTuples(n *astApp, tuples []string, changed *bool) {
	for _, name := range tuples {
		s := sc.syntaxOf(name)
		if s == nil || s.Tuple == nil || len(s.Tuple.Terms) == 0 {
			continue
		}
		tu := s.Tuple
		params := tu.params()
		tmpls := make([]astNode, len(tu.Terms))
		ok := true
		for i, text := range tu.Terms {
			t, err := tupleTemplate(text)
			if err != nil {
				ok = false
				break
			}
			tmpls[i] = t
		}
		if !ok {
			continue
		}
		// The fields each parameter is read through, over all the
		// terms: a bundle stands for the parameter only when it has
		// them all.
		used := map[string][]string{}
		for _, tmpl := range tmpls {
			walkAST(tmpl, func(a astNode) {
				if v, ok := a.(*astVar); ok {
					if param, field, isField := strings.Cut(v.name, "."); isField && slices.Contains(params, param) && !slices.Contains(used[param], field) {
						used[param] = append(used[param], field)
					}
				}
			})
		}
		for start := 0; start+len(tmpls) <= len(n.args); start++ {
			bind := map[string]string{}
			bindTypes := map[string]astType{}
			bindTerms := map[string]astNode{}
			match := true
			for k, tmpl := range tmpls {
				if !sc.matchTuple(tmpl, n.args[start+k], params, used, bind, bindTypes, bindTerms) {
					match = false
					break
				}
			}
			if !match || len(bind) != len(params) {
				continue
			}
			pos := n.args[start].nodePos()
			call := &astApp{fun: &astVar{name: name, pos: pos}, pos: pos}
			for _, p := range params {
				if t, isType := bindTypes[p]; isType {
					a := typeAsTerm(t, pos)
					if a == nil {
						match = false
						break
					}
					call.args = append(call.args, a)
					continue
				}
				if a, isTerm := bindTerms[p]; isTerm {
					call.args = append(call.args, a)
					continue
				}
				call.args = append(call.args, &astVar{name: bind[p], pos: pos})
			}
			if !match {
				continue
			}
			args := append([]astNode{}, n.args[:start]...)
			args = append(args, call)
			args = append(args, n.args[start+len(tmpls):]...)
			n.args = args
			*changed = true
		}
	}
}

// matchTuple matches a tuple term against an argument, its parameters
// binding names — a parameter matched as a term binds a variable's
// name, as a type a type name's, and as a bundle (a field of the
// parameter, `X.add'`) the bundle in scope whose field the variable is,
// the one with the fewest components first. It reads every form
// substituteTuple writes: under a binder of the term (`λn:num. …`) the
// argument binds the same name at a matching type, and a parameter
// there binds nothing that binder captures.
func (sc *bundleScope) matchTuple(tmpl, arg astNode, params []string, used map[string][]string, bind map[string]string, bindTypes map[string]astType, bindTerms map[string]astNode) bool {
	return sc.matchTupleIn(tmpl, arg, params, used, bind, bindTypes, bindTerms, nil)
}

func (sc *bundleScope) matchTupleIn(tmpl, arg astNode, params []string, used map[string][]string, bind map[string]string, bindTypes map[string]astType, bindTerms map[string]astNode, binders map[string]bool) bool {
	isParam := func(name string) bool { return slices.Contains(params, name) }
	captured := func(a astNode) bool {
		found := false
		walkAST(a, func(n astNode) {
			if v, ok := n.(*astVar); ok && binders[v.name] {
				found = true
			}
		})
		return found
	}
	under := func(name string) map[string]bool {
		out := make(map[string]bool, len(binders)+1)
		for k := range binders {
			out[k] = true
		}
		out[name] = true
		return out
	}
	match := func(t, a astNode) bool {
		return sc.matchTupleIn(t, a, params, used, bind, bindTypes, bindTerms, binders)
	}
	bindName := func(param, name string) bool {
		if prev, ok := bind[param]; ok {
			return prev == name
		}
		bind[param] = name
		return true
	}
	bindType := func(param string, b astType) bool {
		var pr stmtPrinter
		text, err := pr.typ(b, true)
		if err != nil || !bindName(param, text) {
			return false
		}
		bindTypes[param] = b
		return true
	}
	var types func(a, b astType) bool
	types = func(a, b astType) bool {
		switch a := a.(type) {
		case *astTypeVar:
			if isParam(a.name) {
				return bindType(a.name, b)
			}
			bv, ok := b.(*astTypeVar)
			return ok && bv.name == a.name
		case *astTypeNamed:
			if len(a.args) == 0 && isParam(a.name) {
				return bindType(a.name, b)
			}
			bn, ok := b.(*astTypeNamed)
			if !ok || bn.name != a.name || len(bn.args) != len(a.args) {
				return false
			}
			for i := range a.args {
				if !types(a.args[i], bn.args[i]) {
					return false
				}
			}
			return true
		case *astTypeFun:
			bf, ok := b.(*astTypeFun)
			return ok && types(a.domain, bf.domain) && types(a.codomain, bf.codomain)
		}
		return false
	}
	switch t := tmpl.(type) {
	case *astVar:
		av, ok := arg.(*astVar)
		if isParam(t.name) && len(t.typeAnnot) == 0 {
			// A term parameter binds the argument whatever it is, so
			// long as no binder of the term captures it.
			if captured(arg) {
				return false
			}
			if ok && len(av.typeAnnot) == 0 {
				return bindName(t.name, av.name)
			}
			if !bindName(t.name, printASTNode(arg)) {
				return false
			}
			bindTerms[t.name] = arg
			return true
		}
		if param, field, isField := strings.Cut(t.name, "."); isField && isParam(param) && len(t.typeAnnot) == 0 {
			if ok && len(av.typeAnnot) > 0 {
				return false
			}
			if prev, bound := bind[param]; bound {
				var b *bundle
				if node, isTerm := bindTerms[param]; isTerm {
					b = sc.lookupTerm(node)
				} else {
					b = sc.lookup(prev)
				}
				if b == nil {
					return false
				}
				comp := sc.fieldOf(b, field)
				return comp != nil && sc.key(comp) == sc.key(arg)
			}
			var cands []*bundle
			for _, b := range sc.bundles {
				if b == nil {
					continue
				}
				tmpl := sc.fieldOf(b, field)
				if tmpl == nil || slices.ContainsFunc(used[param], func(f string) bool { return sc.fieldOf(b, f) == nil }) {
					continue
				}
				holes := map[string]astNode{}
				if !matchTemplate(sc.spelledOut(tmpl), sc.spelledOut(arg), holes) {
					continue
				}
				if inst := b.instance(holes, arg.nodePos()); inst != nil {
					cands = append(cands, inst)
				}
			}
			if len(cands) == 0 {
				return false
			}
			slices.SortFunc(cands, func(x, y *bundle) int {
				if len(x.comps) != len(y.comps) {
					return len(x.comps) - len(y.comps)
				}
				return strings.Compare(x.name, y.name)
			})
			if !bindName(param, cands[0].name) {
				return false
			}
			if nameOf(cands[0].carrier) == "" {
				bindTerms[param] = cands[0].carrier
			}
			return true
		}
		if !ok || av.name != t.name || len(av.typeAnnot) != len(t.typeAnnot) {
			return false
		}
		for i := range t.typeAnnot {
			if t.typeAnnot[i].varName != av.typeAnnot[i].varName || !types(t.typeAnnot[i].ty, av.typeAnnot[i].ty) {
				return false
			}
		}
		return true
	case *astField:
		af, ok := arg.(*astField)
		return ok && af.name == t.name && match(t.receiver, af.receiver)
	case *astApp:
		aa, ok := arg.(*astApp)
		if !ok || len(aa.args) != len(t.args) || !match(t.fun, aa.fun) {
			return false
		}
		for i := range t.args {
			if !match(t.args[i], aa.args[i]) {
				return false
			}
		}
		return true
	case *astBinOp:
		ab, ok := arg.(*astBinOp)
		return ok && ab.op == t.op && match(t.left, ab.left) && match(t.right, ab.right)
	case *astNotNode:
		an, ok := arg.(*astNotNode)
		return ok && match(t.body, an.body)
	case *astNeg:
		an, ok := arg.(*astNeg)
		return ok && match(t.operand, an.operand)
	case *astCoerce:
		ac, ok := arg.(*astCoerce)
		return ok && match(t.operand, ac.operand)
	case *astQuantNode:
		aq, ok := arg.(*astQuantNode)
		if !ok || aq.quantifier != t.quantifier || aq.varName != t.varName || isParam(t.varName) ||
			(t.varType == nil) != (aq.varType == nil) || (t.varType != nil && !types(t.varType, aq.varType)) {
			return false
		}
		return sc.matchTupleIn(t.body, aq.body, params, used, bind, bindTypes, bindTerms, under(t.varName))
	case *astAbsNode:
		aa, ok := arg.(*astAbsNode)
		if !ok || aa.varName != t.varName || isParam(t.varName) ||
			(t.varType == nil) != (aa.varType == nil) || (t.varType != nil && !types(t.varType, aa.varType)) {
			return false
		}
		return sc.matchTupleIn(t.body, aa.body, params, used, bind, bindTypes, bindTerms, under(t.varName))
	}
	return printASTNode(tmpl) == printASTNode(arg)
}

// fieldOf is bundle b's component the structure's definition names
// field, nil when it names none.
func (sc *bundleScope) fieldOf(b *bundle, field string) astNode {
	syn := sc.bundleSyntax(b.structure)
	if syn == nil {
		return nil
	}
	for i, p := range syn.Params {
		if p.Name == field && i < len(b.comps) {
			return b.comps[i]
		}
	}
	return nil
}

// typeName is a type's name when it is a bare name, "" otherwise.
func typeName(t astType) string {
	switch t := t.(type) {
	case *astTypeVar:
		return t.name
	case *astTypeNamed:
		if len(t.args) == 0 {
			return t.name
		}
	}
	return ""
}
