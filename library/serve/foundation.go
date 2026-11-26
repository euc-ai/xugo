// Foundation closure computation for omega's self-circularity gate.
//
// Each *LemmaBundle struct (NatLemmaBundle / RealLemmaBundle / IntLemmaBundle)
// is a flat list of `*prop.PropWrapper` fields that bind to corpus
// theorems via either `fromEntry(e)` (direct) or `fromGeneral(g)` /
// `CurryIffConj(...)` / `defNorm(...)` (shape-adapted). At install time
// the install site knows each field's identity by construction; this
// file extracts it uniformly (regardless of binding style) by running
// `prop.Normalize` on each non-nil field's wrapped prop — the AlphaKey
// of the normalized form is the statement's OWN key, the identity a
// entry carries (registry.ProofEntry.Key) and the key
// PromiseForGeneral looks the corpus promise up by.
//
// The seed set (every field's key)
// is then BFS-closed over the corpus DAG (`library/integrity/dag`). The
// result is the transitive set of theorems the bundle depends on, in
// the DAG's key space — the EXACT set omega's self-circularity gate
// should refuse when proving any of them.
//
// Why this lives in corpus, not omega: the gate's correctness depends on
// "which theorems does this bundle reach", a fact only the corpus
// wiring layer can compute (omega itself has no library import, by
// design). corpus is also where each bundle's field list is written by
// hand — both contribute to a single "what does this bundle MEAN at the
// corpus level" answer, so they belong together.

package serve

import (
	"fmt"
	"reflect"
	"slices"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/integrity/dag"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// wrapperPtrType is the reflect.Type of *prop.PropWrapper, the
// universal bundle-field type. Computed once at first install.
var wrapperPtrType = reflect.TypeFor[*prop.PropWrapper]()

// computeBundleCapability returns emitted theorem roots and their closure,
// and notes the bundle as installed, for WarmBundles (warm.go) to force
// its fields.
func computeBundleCapability(b any, fieldOverrides ...map[string][]core.PropKey) ([]core.PropKey, map[core.PropKey]bool) {
	overrides := map[string][]core.PropKey{}
	if len(fieldOverrides) > 0 {
		overrides = fieldOverrides[0]
	}
	fields := bundleFields(b, overrides)
	if fields == nil {
		return nil, nil
	}
	noteInstalledBundle(b, overrides)
	var nodeSeeds []core.PropKey
	for _, f := range fields {
		nodeSeeds = append(nodeSeeds, f.roots...)
	}
	var roots []core.PropKey
	seen := map[core.PropKey]bool{}
	for _, k := range nodeSeeds {
		if dag.Has(k) && !seen[k] {
			seen[k] = true
			roots = append(roots, k)
		}
	}
	return roots, dag.Closure(nodeSeeds)
}

// installCapability installs a law table's capability, refusing a table
// that stands on a card. A member that closes through a law table
// records the capability and none of its laws, so a card beneath a law
// is in no dependency of the member and the card frontier
// (registry.CardFrontier) does not report it. A law table therefore
// holds proved theorems all the way down: every install in this package
// goes through here.
func installCapability(name string, roots []core.PropKey, foundation map[core.PropKey]bool) {
	refuseCardFoundation(name, roots, foundation)
	proof.InstallDependencyCapability(name, roots, foundation)
}

// refuseCardFoundation panics where a card is among the roots of a law
// table or in their closure, naming each card and the laws that reach
// it.
func refuseCardFoundation(name string, roots []core.PropKey, foundation map[core.PropKey]bool) {
	seen := map[*registry.ProofEntry]bool{}
	var cards []*registry.ProofEntry
	note := func(k core.PropKey) {
		if e, ok := registry.ByKey(string(k)); ok && e.IsCard() && !seen[e] {
			seen[e] = true
			cards = append(cards, e)
		}
	}
	for _, k := range roots {
		note(k)
	}
	for k := range foundation {
		note(k)
	}
	if len(cards) == 0 {
		return
	}
	sort.Slice(cards, func(i, j int) bool { return cards[i].Name < cards[j].Name })
	findings := make([]string, 0, len(cards))
	for _, card := range cards {
		var laws []string
		for _, k := range roots {
			if law, ok := registry.ByKey(string(k)); ok && slices.Contains(registry.CardFrontier(law), card.Name) {
				laws = append(laws, law.Name)
			}
		}
		sort.Strings(laws)
		laws = slices.Compact(laws)
		if len(laws) == 0 {
			findings = append(findings, card.Name+" (in the closure of the laws)")
			continue
		}
		findings = append(findings, card.Name+" (beneath "+strings.Join(laws, ", ")+")")
	}
	panic(fmt.Sprintf("serve: the law table of the capability %q stands on a card: %s — "+
		"a law table holds proved theorems all the way down, since a member that closes through it "+
		"records the capability and not the cards beneath its laws",
		name, strings.Join(findings, "; ")))
}

// bundleField is one bound field of an installed bundle with the entries
// a force of it reaches: the field's override where its install declared
// one (a shape adapter's or lift's sources; empty for a definition), else
// the entry whose own key its normalized statement carries — the entry
// PromiseForGeneral and fromEntry resolve to.
type bundleField struct {
	field   string
	wrapper *prop.PropWrapper
	roots   []core.PropKey
}

// bundleFields reflects over the bundle pointed to by `b` and resolves
// every non-nil field. A field with neither an override nor a corpus
// identity fails closed, and an override naming no field is a drift.
// nil for a nil bundle.
func bundleFields(b any, overrides map[string][]core.PropKey) []bundleField {
	v := reflect.ValueOf(b)
	if v.Kind() != reflect.Pointer || v.IsNil() {
		return nil
	}
	var seeds []bundleSeed
	collectBundleSeeds(v.Elem(), "", &seeds)
	usedOverrides := make(map[string]bool)
	fields := make([]bundleField, 0, len(seeds))
	var unknown []bundleSeed
	for _, seed := range seeds {
		if keys, ok := overrides[seed.field]; ok {
			usedOverrides[seed.field] = true
			// An empty slice explicitly declares a primitive/definition leaf.
			fields = append(fields, bundleField{field: seed.field, wrapper: seed.wrapper, roots: keys})
			continue
		}
		if !dag.Has(seed.key) {
			unknown = append(unknown, seed)
			continue
		}
		fields = append(fields, bundleField{field: seed.field, wrapper: seed.wrapper, roots: []core.PropKey{seed.key}})
	}
	for field := range overrides {
		if !usedOverrides[field] {
			panic(fmt.Sprintf("bundle dependency override names missing field %q", field))
		}
	}
	if len(unknown) > 0 {
		panic(fmt.Sprintf("bundle fields have unresolved theorem identities %v; add explicit source-key or primitive overrides", unknown))
	}
	return fields
}

type bundleSeed struct {
	field   string
	wrapper *prop.PropWrapper
	key     core.PropKey
}

func (s bundleSeed) String() string { return fmt.Sprintf("{%s %s}", s.field, s.key) }

func collectBundleSeeds(v reflect.Value, prefix string, out *[]bundleSeed) {
	if v.Kind() != reflect.Struct {
		return
	}
	t := v.Type()
	for i := 0; i < v.NumField(); i++ {
		f := v.Field(i)
		if !t.Field(i).IsExported() {
			continue
		}
		name := t.Field(i).Name
		if prefix != "" {
			name = prefix + "." + name
		}
		if f.Type() == wrapperPtrType {
			if f.IsNil() {
				continue
			}
			pw := f.Interface().(*prop.PropWrapper)
			normalized, _ := prop.Normalize(pw)
			*out = append(*out, bundleSeed{field: name, wrapper: pw, key: normalized.AlphaKey()})
			continue
		}
		if f.Kind() == reflect.Struct {
			collectBundleSeeds(f, name, out)
		}
	}
}
