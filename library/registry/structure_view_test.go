package registry_test

import (
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

func TestAtUniverseRecord(t *testing.T) {
	view := group.Group.AtUniverseRecord(group.GroupOn, group.GroupOnUniverse,
		"restrict_group(G, 𝕌)", set_basic.InUniv, set_order.SubsetUniv)
	body := "∀x y z:A. x * (y * z) = (x * y) * z"
	law := view.Law(body, group.AssocOn)
	require.Equal(t, headlineOf(t, group.Group.Statement(body)), law.Headline)
	var deps []*registry.ProofEntry
	for _, dep := range law.Deps {
		deps = append(deps, dep.Entry())
	}
	require.ElementsMatch(t, []*registry.ProofEntry{
		group.Group.Entry(), group.AssocOn.Entry(), group.GroupOnUniverse.Entry(), set_basic.InUniv.Entry(),
	}, deps)

	narrow := group.Group.AtUniverseRecord(group.GroupOn, group.GroupOnUniverse,
		"restrict_group(G, 𝕌)", set_basic.InUniv)
	require.Panics(t, func() {
		narrow.Law("∀h:set(A). subgroup(restrict_group(G, 𝕌), h) ⇒ h ⊆ 𝕌", group.SubgroupGroupOn)
	},
		"a subset guard needs its universe law")
	require.Panics(t, func() {
		group.Group.AtUniverseRecord(group.Group, group.GroupOnUniverse, "G", set_basic.InUniv)
	})
}

// TestAtUniverse: the view door checks that the carrier form is the
// carrier followed by the whole-type structure's components, reads each universe law's
// relation to 𝕌, and gives a view law the whole-type statement — its
// Headline the structure's own Statement — with the carrier law, the
// bridge, the universe laws its guards need and the definition as its
// deps by construction. The kernel build of a view is the corpus's: the
// group chapter's whole-type laws replay as views of their carrier laws.
func TestAtUniverse(t *testing.T) {
	fam := registry.NewFamily("zz_structure_view_test", nil)
	whole := fam.DefineStructure(registry.DefEntry{
		Name:  "Mon",
		Const: "zz_view_mon",
		Type:  "(A → A → A) → A → bool",
		Equations: []string{
			"∀op:(A → A → A). ∀e:A. zz_view_mon(op, e) ⇔ (∀x y:A. op(x, y) = op(y, x)) ∧ (∀x:A. op(e, x) = x)",
		},
	})
	carrier := fam.DefineStructure(registry.DefEntry{
		Name:  "MonOn",
		Const: "zz_view_mon_on",
		Type:  "set(A) → (A → A → A) → A → bool",
		Equations: []string{
			"∀c:set(A). ∀op:(A → A → A). ∀e:A. zz_view_mon_on(c, op, e) ⇔ " +
				"e ∈ c ∧ (∀x y:A. x ∈ c ∧ y ∈ c ⇒ op(x, y) = op(y, x)) ∧ (∀x:A. x ∈ c ⇒ op(e, x) = x)",
		},
	})
	bridge := fam.Add(registry.ProofEntry{Name: "Bridge", Build: whole.Axiom("∀x:A. op(e, x) = x")})
	commOn := fam.Add(registry.ProofEntry{Name: "CommOn", Build: carrier.Axiom("∀x y:A. x ∈ c ∧ y ∈ c ⇒ op(x, y) = op(y, x)")})
	squareOn := fam.Add(registry.ProofEntry{Name: "SquareOn",
		Build: carrier.Law("op(e, e) = e", func(a *proof.Argument, h proof.Fact) {})})
	subsetOn := fam.Add(registry.ProofEntry{Name: "SubsetOn",
		Build: carrier.Law("∀s:set(A). ∀x:A. s ⊆ c ∧ x ∈ s ⇒ op(e, x) = x", func(a *proof.Argument, h proof.Fact) {})})

	depsOf := func(e *registry.ProofEntry) []*registry.ProofEntry {
		out := make([]*registry.ProofEntry, 0, len(e.Deps))
		for _, d := range e.Deps {
			out = append(out, d.Entry())
		}
		return out
	}

	view := whole.AtUniverse(carrier, bridge, set_basic.InUniv, set_order.SubsetUniv)
	comm := fam.Add(registry.ProofEntry{Name: "Comm", Build: view.Law("∀x y:A. op(x, y) = op(y, x)", commOn)})
	require.Equal(t, headlineOf(t, whole.Statement("∀x y:A. op(x, y) = op(y, x)")), comm.Build.Headline,
		"a view law states the whole-type law")
	require.ElementsMatch(t, []*registry.ProofEntry{whole.ProofEntry, commOn, bridge, set_basic.InUniv.Entry()}, depsOf(comm),
		"a membership guard takes the membership law and nothing else")
	subset := fam.Add(registry.ProofEntry{Name: "Subset", Build: view.Law("∀s:set(A). ∀x:A. x ∈ s ⇒ op(e, x) = x", subsetOn)})
	require.ElementsMatch(t, []*registry.ProofEntry{whole.ProofEntry, subsetOn, bridge, set_order.SubsetUniv.Entry()}, depsOf(subset),
		"an inclusion guard takes the inclusion law; `x ∈ s` is no guard on the carrier")
	square := fam.Add(registry.ProofEntry{Name: "Square", Build: view.Law("op(e, e) = e", squareOn)})
	require.ElementsMatch(t, []*registry.ProofEntry{whole.ProofEntry, squareOn, bridge}, depsOf(square),
		"a law with no guard takes no universe law")

	// Declared with the membership law alone, the view refuses a law
	// with an inclusion guard, naming the missing universe law.
	narrow := whole.AtUniverse(carrier, bridge, set_basic.InUniv)
	require.Panics(t, func() { narrow.Law("∀s:set(A). ∀x:A. x ∈ s ⇒ op(e, x) = x", subsetOn) })

	// The carrier form must be the carrier followed by the whole's
	// components, and a universe law must state a relation to 𝕌.
	require.Panics(t, func() { whole.AtUniverse(whole, bridge, set_basic.InUniv) }, "the same arity is not a carrier form")
	other := fam.DefineStructure(registry.DefEntry{
		Name:  "OtherOn",
		Const: "zz_view_other_on",
		Type:  "set(A) → (A → A → A) → (A → A) → bool",
		Equations: []string{
			"∀c:set(A). ∀op:(A → A → A). ∀f:(A → A). zz_view_other_on(c, op, f) ⇔ (∀x:A. x ∈ c ⇒ op(x, f(x)) = x)",
		},
	})
	require.Panics(t, func() { whole.AtUniverse(other, bridge, set_basic.InUniv) }, "a different component after the carrier is not a carrier form")
	last := fam.DefineStructure(registry.DefEntry{
		Name:  "LastOn",
		Const: "zz_view_last_on",
		Type:  "(A → A → A) → A → set(A) → bool",
		Equations: []string{
			"∀op:(A → A → A). ∀e:A. ∀c:set(A). zz_view_last_on(op, e, c) ⇔ e ∈ c",
		},
	})
	require.Panics(t, func() { whole.AtUniverse(last, bridge, set_basic.InUniv) }, "a carrier form names its carrier first")
	require.Panics(t, func() { whole.AtUniverse(carrier, bridge, commOn) }, "a law stating no relation to 𝕌 is no universe law")
	require.Panics(t, func() { view.Law("∀x y:A. op(x, y) = op(y, x)", nil) }, "the carrier law is required")
}

// TestAtUniverseSubscriptedCarrier: a view over components bound with
// subscripts states its law with them as the printer spells them, and
// finds a guard on the carrier `c₀` whether the carrier law spells it
// `c₀` or `c_0`, the one identifier both read as.
func TestAtUniverseSubscriptedCarrier(t *testing.T) {
	fam := registry.NewFamily("zz_structure_view_subscript_test", nil)
	whole := fam.DefineStructure(registry.DefEntry{
		Name:  "Comm",
		Const: "zz_view_sub_comm",
		Type:  "(A → A → A) → A → bool",
		Equations: []string{
			"∀op:(A → A → A). ∀e₀:A. zz_view_sub_comm(op, e₀) ⇔ (∀x y:A. op(x, y) = op(y, x))",
		},
	})
	carrier := fam.DefineStructure(registry.DefEntry{
		Name:  "CommOn",
		Const: "zz_view_sub_comm_on",
		Type:  "set(A) → (A → A → A) → A → bool",
		Equations: []string{
			"∀c₀:set(A). ∀op:(A → A → A). ∀e₀:A. zz_view_sub_comm_on(c₀, op, e₀) ⇔ " +
				"e₀ ∈ c₀ ∧ (∀x y:A. x ∈ c₀ ∧ y ∈ c₀ ⇒ op(x, y) = op(y, x))",
		},
	})
	bridge := fam.Add(registry.ProofEntry{Name: "Bridge", Build: whole.Axiom("∀x y:A. op(x, y) = op(y, x)")})
	commOn := fam.Add(registry.ProofEntry{Name: "CommOnLaw",
		Build: carrier.Axiom("∀x y:A. x ∈ c₀ ∧ y ∈ c₀ ⇒ op(x, y) = op(y, x)")})
	require.Equal(t,
		"∀c₀:set(A). ∀op:(A → A → A). ∀e₀ x y:A. zz_view_sub_comm_on(c₀, op, e₀) ∧ x ∈ c₀ ∧ y ∈ c₀ ⇒ op(x, y) = op(y, x)",
		commOn.Build.Headline)
	commOnByHand := fam.Add(registry.ProofEntry{Name: "CommOnByHand",
		Build: fam.Theorem("∀c_0:set(A). ∀op:(A → A → A). ∀e_0:A. zz_view_sub_comm_on(c_0, op, e_0) ⇒ "+
			"∀x y:A. x ∈ c_0 ∧ y ∈ c_0 ⇒ op(x, y) = op(y, x)", proof.Unfold(carrier))})

	view := whole.AtUniverse(carrier, bridge, set_basic.InUniv)
	for _, onLaw := range []*registry.ProofEntry{commOn, commOnByHand} {
		comm := fam.Add(registry.ProofEntry{Name: "Comm" + onLaw.BareName(), Build: view.Law("∀x y:A. op(x, y) = op(y, x)", onLaw)})
		require.Equal(t, "∀op:(A → A → A). ∀e₀ x y:A. zz_view_sub_comm(op, e₀) ⇒ op(x, y) = op(y, x)", comm.Build.Headline)
		var deps []*registry.ProofEntry
		for _, d := range comm.Deps {
			deps = append(deps, d.Entry())
		}
		require.Contains(t, deps, set_basic.InUniv.Entry(), "%s: the guard `x ∈ c₀` takes the membership law", onLaw.Name)
	}
}

// headlineOf is a door statement's text, the Headline of the member it builds.
func headlineOf(t *testing.T, st dsl.Statement) string {
	t.Helper()
	text, err := st.Text()
	require.NoError(t, err)
	return text
}
