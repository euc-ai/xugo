// bundle.go — where a bundle goes among a constant's parameters
// (dsl.BundleSyntax), and the family's tuples (dsl.TupleSyntax).
//
// A bundle is a name standing for a structure's components in the text
// (ext/dsl/bundle.go). The parser lays a bundle argument out by what
// the constant declares here:
//
//   - a STRUCTURE (DefineStructure, StructureOf) lays out its own
//     components in order, and each sub-structure its definition states
//     over its components as a top-level conjunct — `locally_ringed_space`'s
//     `sheaf_of_rings(T, F, res)` — so a sheaf bundle fills those three. A
//     conjunct under ∀ binders and behind a guard, over terms in the
//     components and the binders — `sheaf_of_rings`'s
//     `∀U V:set(A). U ∈ T ∧ V ∈ T ∧ V ⊆ U ⇒ ring_homomorphism(F(U), F(V),
//     res(U, V))` — is an INDEXED layout, the binders its index and the terms its
//     templates: the fibres a fact of the structure states as a family
//     (ext/dsl/bundle_fibre.go). Its SUBJECT is the component its entry declares
//     the predicate said of (DefEntry.Subject): the record a ring is,
//     the map a homomorphism is, the sections a sheaf assigns. The
//     bundle a structure fact states is named after it; a structure
//     that declares none — one on a whole type — is a bundle under the
//     binder's name only.
//   - a DEFINITION declares its layouts (DefEntry.Bundles), each a
//     structure applied to the definition's own binders, `_` for a
//     component it does not take: `presheaf(T, F, res)` on `stalk_map`
//     says a presheaf bundle fills its first three parameters.
//
// A tuple (Family.Tuple) is a named list of terms that stands among an
// application's arguments: `spec_sheaf(R)` for the spectrum's topology,
// section rings and restriction.

package registry

import (
	"fmt"
	"slices"
	"strings"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/utils"
)

// structureBundleSyntax is a structure's layout: its own components,
// then each sub-structure a top-level conjunct of its definition states
// over them, indexed when the conjunct stands under ∀ binders or over
// terms. subject is the component the entry declares, "" for none; the
// error is a subject naming no component.
func structureBundleSyntax(name string, params []dsl.BundleParam, body core.Term, subject string) (*dsl.BundleSyntax, error) {
	b := &dsl.BundleSyntax{Params: params, Structure: true, Subject: -1}
	self := make([]int, len(params))
	for i := range self {
		self[i] = i
	}
	b.Layouts = []dsl.BundleLayout{{Structure: name, Slots: self}}
	if subject != "" {
		b.Subject = slices.IndexFunc(params, func(p dsl.BundleParam) bool { return p.Name == subject })
		if b.Subject < 0 {
			names := make([]string, len(params))
			for i, p := range params {
				names[i] = p.Name
			}
			return nil, fmt.Errorf("Subject %q names none of the components %s", subject, strings.Join(names, ", "))
		}
	}
	if body == nil {
		return b, nil
	}
	index := map[string]int{}
	for i, p := range params {
		index[p.Name] = i
	}
	mgr := GetConstMetaManager()
	for _, conj := range ext.DecomposesAND(body) {
		t := conj
		var binders []core.VarTerm
		for abs := ext.MatchesFORALL(t); !abs.IsZero(); abs = ext.MatchesFORALL(t) {
			binders = append(binders, abs.Var())
			t = abs.Body()
		}
		for {
			_, consequent, ok := ext.MatchesIMPLY(t)
			if !ok {
				break
			}
			t = consequent
		}
		head, args := spineOf(t)
		c, ok := head.AsConst()
		if !ok {
			continue
		}
		sub := mgr.ConstSyntax(string(c.Name()))
		if sub == nil || sub.Bundle == nil || !sub.Bundle.Structure || len(args) != len(sub.Bundle.Params) {
			continue
		}
		bound := map[string]bool{}
		for _, v := range binders {
			bound[string(v.Name())] = true
		}
		slots := make([]int, len(args))
		var templates []core.Term
		ok = true
		for k, a := range args {
			if v, isVar := a.AsVar(); isVar {
				if i, isParam := index[string(v.Name())]; isParam && !bound[string(v.Name())] {
					slots[k] = i
					continue
				}
			}
			// A term over the components and the binders.
			for _, fv := range a.Frees(nil) {
				if _, isParam := index[string(fv.Name())]; !isParam && !bound[string(fv.Name())] {
					ok = false
				}
			}
			if !ok {
				break
			}
			slots[k] = -1
			if templates == nil {
				templates = make([]core.Term, len(args))
			}
			templates[k] = a
		}
		if !ok {
			continue
		}
		layout := dsl.BundleLayout{Structure: string(c.Name()), Slots: slots, Templates: templates}
		for _, v := range binders {
			layout.Index = append(layout.Index, dsl.BundleParam{Name: string(v.Name()), Type: v.Type()})
		}
		b.Layouts = append(b.Layouts, layout)
	}
	return b, nil
}

// declareLetter sets the letter a structure with no subject is folded
// under (DefEntry.Letter): a name, and none of its components'.
func declareLetter(b *dsl.BundleSyntax, letter string) error {
	if b.Subject >= 0 {
		return fmt.Errorf("Letter %q beside Subject %q: a structure with a subject is named after it", letter, b.Params[b.Subject].Name)
	}
	if strings.ContainsAny(letter, " ().,:") {
		return fmt.Errorf("Letter %q is not a name", letter)
	}
	if slices.ContainsFunc(b.Params, func(p dsl.BundleParam) bool { return p.Name == letter }) {
		return fmt.Errorf("Letter %q names a component: declare it the Subject", letter)
	}
	b.Letter = letter
	return nil
}

// directBundleSyntax is the layout of a DefineStructure'd structure,
// read off its direct definition, with the subject its entry declares.
func directBundleSyntax(dd *proof.DirectDefinition, subject string) (*dsl.BundleSyntax, error) {
	params := make([]dsl.BundleParam, len(dd.Args))
	for i, v := range dd.Args {
		params[i] = dsl.BundleParam{Name: string(v.Name()), Type: v.Type()}
	}
	return structureBundleSyntax(string(dd.DefVar.Name()), params, dd.Body, subject)
}

// declaredBundleSyntax reads a definition's Bundles declarations against
// its equation's binders: each a structure applied to the binders it
// fills, `_` for a component the constant does not take.
func declaredBundleSyntax(decls []string, equation core.Prop) (*dsl.BundleSyntax, error) {
	var params []dsl.BundleParam
	t := equation.Conclusion()
	for abs := ext.MatchesFORALL(t); !abs.IsZero(); abs = ext.MatchesFORALL(t) {
		params = append(params, dsl.BundleParam{Name: string(abs.Var().Name()), Type: abs.Var().Type()})
		t = abs.Body()
	}
	return declaredBundleSyntaxFor(decls, params)
}

// declaredBundleSyntaxFor is declaredBundleSyntax over binders already
// read — the equation text's, before the equation is built.
func declaredBundleSyntaxFor(decls []string, params []dsl.BundleParam) (*dsl.BundleSyntax, error) {
	index := map[string]int{}
	for i, p := range params {
		index[p.Name] = i
	}
	b := &dsl.BundleSyntax{Params: params, Subject: -1}
	mgr := GetConstMetaManager()
	for _, decl := range decls {
		structure, args, err := splitBundleDecl(decl)
		if err != nil {
			return nil, err
		}
		sub := mgr.ConstSyntax(structure)
		if sub == nil || sub.Bundle == nil || !sub.Bundle.Structure {
			return nil, fmt.Errorf("%q: %s is no structure", decl, structure)
		}
		if len(args) != len(sub.Bundle.Params) {
			return nil, fmt.Errorf("%q: %s has %d components, the declaration gives %d", decl, structure, len(sub.Bundle.Params), len(args))
		}
		slots := make([]int, len(args))
		var env []core.TypeSubst
		taken := false
		for k, a := range args {
			if a == "_" {
				slots[k] = -1
				continue
			}
			i, ok := index[a]
			if !ok {
				return nil, fmt.Errorf("%q: %s is not one of the definition's binders", decl, a)
			}
			want := sub.Bundle.Params[k].Type
			if !core.MatchTypeInto(want, params[i].Type, utils.FullPredicate[core.VarType], &env) {
				return nil, fmt.Errorf("%q: %s has type %s, where %s's component %s has %s",
					decl, a, ext.FormatType(params[i].Type), structure, sub.Bundle.Params[k].Name, ext.FormatType(want))
			}
			slots[k] = i
			taken = true
		}
		if !taken {
			return nil, fmt.Errorf("%q: the declaration fills no binder", decl)
		}
		b.Layouts = append(b.Layouts, dsl.BundleLayout{Structure: structure, Slots: slots})
	}
	return b, nil
}

// splitBundleDecl reads `S(a, b, _, …)`.
func splitBundleDecl(decl string) (string, []string, error) {
	open := strings.Index(decl, "(")
	if open <= 0 || !strings.HasSuffix(strings.TrimSpace(decl), ")") {
		return "", nil, fmt.Errorf("%q is not a structure applied to the binders it fills", decl)
	}
	structure := strings.TrimSpace(decl[:open])
	inner := strings.TrimSpace(decl)[open+1 : len(strings.TrimSpace(decl))-1]
	var args []string
	for _, a := range strings.Split(inner, ",") {
		args = append(args, strings.TrimSpace(a))
	}
	return structure, args, nil
}

// ProvisionalBundleSyntax registers, before a definition's equation is
// read, the bundle layouts its entry declares, so that the equation's
// body may pass its binders as bundles; RegisterConstSyntax replaces
// it with the full syntax once the equation is built.
func (m *ConstMetaManager) ProvisionalBundleSyntax(name core.TermName, b *dsl.BundleSyntax) {
	if _, loaded := m.syntax.LoadOrStore(name, &dsl.ConstSyntax{Bundle: b}); loaded {
		panic(fmt.Sprintf("constant %q: syntax registered twice", name))
	}
	m.provisional.Store(name, true)
}

// SetBundleSyntax records where a bundle goes among the parameters of
// name, on its registered syntax or on a syntax that says only that.
func (m *ConstMetaManager) SetBundleSyntax(name core.TermName, b *dsl.BundleSyntax) {
	if v, ok := m.syntax.Load(name); ok {
		v.Bundle = b
		return
	}
	m.syntax.Store(name, &dsl.ConstSyntax{Bundle: b})
}

var tupleNames struct {
	sync.Mutex
	order []string
}

// TupleNames is every tuple a family declared, in declaration order —
// dsl.SyntaxTable.
func (m *ConstMetaManager) TupleNames() []string {
	tupleNames.Lock()
	defer tupleNames.Unlock()
	return append([]string(nil), tupleNames.order...)
}

// Tuple declares a named list of terms that stands among an
// application's arguments and is spliced there: a constructed
// structure's components named once, `spec_sheaf(R)` for
// `zariski_topology(R), spec_section_ops(R), structure_restrict`. A
// parameter stands for a term where a term stands and for a type name
// where a type does (an instance annotation, a binder's type); the
// other names in the terms are read where the tuple is used, so a name
// the terms leave free is the one bound there. The chapter spelling
// writes a run of arguments the terms match back as the tuple. The
// name is the family's and no constant's; it is returned, for the
// chapter's package var that declares the tuple.
func (f *Family) Tuple(name string, params []string, terms ...string) string {
	if name == "" || len(terms) == 0 {
		panic("registry.Tuple: a name and at least one term are required")
	}
	mgr := GetConstMetaManager()
	if err := mgr.ClaimName(core.TermName(name)); err != nil {
		panic(fmt.Sprintf("registry.Tuple(%s): %v", name, err))
	}
	for _, p := range params {
		if p == "" || strings.ContainsAny(p, " ().,") {
			panic(fmt.Sprintf("registry.Tuple(%s): parameter %q is not a name", name, p))
		}
	}
	for _, t := range terms {
		if err := dsl.CheckTupleTerm(t); err != nil {
			panic(fmt.Sprintf("registry.Tuple(%s): %v", name, err))
		}
	}
	mgr.RegisterConstSyntax(core.TermName(name), &dsl.ConstSyntax{Tuple: &dsl.TupleSyntax{
		Params: append([]string(nil), params...), Terms: append([]string(nil), terms...)}})
	tupleNames.Lock()
	tupleNames.order = append(tupleNames.order, name)
	tupleNames.Unlock()
	return name
}
