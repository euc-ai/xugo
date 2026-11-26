package typematch

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/ematch"
	"github.com/stretchr/testify/require"
)

// A set lemma read at FAMILIES: the goal's own point type sits inside
// the instance's image (`A ↦ A → bool`), and the sweep's by-name
// occurs-check drops that binding as recursive, committing nothing —
// the lemma's A is captured as the goal's. The retry renames the
// lemma's colliding letter apart and reaches the instance; at a goal
// letter that does not collide the first sweep already reaches it, and
// the adaptations agree.
func TestTryAdaptLemmaTypes_LetterInsideItsOwnImage(t *testing.T) {
	parse := func(text string) core.Prop {
		res := dsl.ParsePropTextInScope(text, &dsl.ParseScope{})
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Prop
	}
	lemma := parse("∀s t:(A → bool). ∀x:A. insert(x, s) ⊆ t ⇔ x ∈ t ∧ s ⊆ t")
	collides := parse("T:((A → bool) → bool), u:(A → bool), v:(A → bool) ⊢ insert(u, insert(v, ∅)) ⊆ T")
	apart := parse("T:((B → bool) → bool), u:(B → bool), v:(B → bool) ⊢ insert(u, insert(v, ∅)) ⊆ T")

	familyOf := func(goal core.Prop) core.HolType { return goalVarType(t, goal, "u") }
	check := func(goal core.Prop, adapted core.Prop) {
		require.NotNil(t, adapted, "no adaptation at %s", ext.FormatType(familyOf(goal)))
		binders, _ := ematch.StripGuardedForalls(adapted.Conclusion())
		require.Len(t, binders, 3)
		require.Equal(t, "x", string(binders[2].Name()))
		require.True(t, binders[2].Type().Equals(familyOf(goal)),
			"x must be read at the family's element type %s, got %s", ext.FormatType(familyOf(goal)), ext.FormatType(binders[2].Type()))
	}
	// The single adaptation reaches it at both: where the letters
	// collide, the sweep committed nothing and left the lemma's A
	// captured, and the retry binds it (see TryAdaptLemmaTypes).
	check(apart, TryAdaptLemmaTypes(lemma, apart))
	check(collides, TryAdaptLemmaTypes(lemma, collides))

	// The enumeration — an instance ADDED beside the rule at its own
	// letters — reaches it at the colliding goal too, and nothing else.
	out := EnumerateLemmaTypeAdaptations(lemma, collides)
	require.Len(t, out, 1)
	check(collides, out[0])
	apartOut := EnumerateLemmaTypeAdaptations(lemma, apart)
	require.Len(t, apartOut, 1)
	check(apart, apartOut[0])

	// No reserved letter escapes: the adapted lemma mentions only the
	// goal's letters.
	ext.TermAnyTypeVar(out[0].Conclusion(), func(v core.VarType) bool {
		require.NotContains(t, string(v.Name()), "?apart", "a renamed-apart letter escaped: %s", v.Name())
		return false
	})
}

func TestEnumerateLemmaTypeAdaptations_MixedLettersAndSelfContainingInstance(t *testing.T) {
	parse := func(text string) core.Prop {
		res := dsl.ParsePropTextInScope(text, &dsl.ParseScope{})
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Prop
	}
	lemma := parse("∀s t:(A → bool). ∀x:A. insert(x, s) ⊆ t ⇔ x ∈ t ∧ s ⊆ t")
	goal := parse("T:((A → bool) → bool), u:(A → bool), v:(A → bool), S:(B → bool), b:B ⊢ insert(u, insert(v, ∅)) ⊆ T ∧ insert(b, ∅) ⊆ S")
	instances := EnumerateLemmaTypeAdaptations(lemma, goal)
	for _, name := range []string{"u", "b"} {
		want := goalVarType(t, goal, name)
		found := false
		for _, instance := range instances {
			binders, _ := ematch.StripGuardedForalls(instance.Conclusion())
			found = found || binders[2].Type().Equals(want)
		}
		require.True(t, found, "missing instance at %s among %d adaptations", ext.FormatType(want), len(instances))
	}
}

// The enumeration is complete, independent of the finite target's width
// and of the anchor discovery order.
func TestEnumerateLemmaTypeAdaptations_CompletesFinitePins(t *testing.T) {
	fMeta := makeUnaryConst("allPinsF", core.TypeA())
	fA := core.MakeConstTerm(fMeta, core.MakeFun(core.TypeA(), core.TypeBool()))
	x := core.Var("x", core.TypeA())
	lemma := core.MakeProp(ext.ForAll(x)(ext.WrapTerm(core.Apply(fA, x))).Core())
	var terms []core.Term
	for i := 0; i < 24; i++ {
		ty := core.MakeVarType(core.TypeName(fmt.Sprintf("T%d", i)))
		f := core.MakeConstTerm(fMeta, core.MakeFun(ty, core.TypeBool()))
		terms = append(terms, core.Apply(f, core.Var("x", ty)))
	}
	var first map[core.PropKey]bool
	for _, reverse := range []bool{false, true} {
		var body core.Term
		for i := range terms {
			j := i
			if reverse {
				j = len(terms) - 1 - i
			}
			if body == nil {
				body = terms[j]
			} else {
				body = ext.And(body, terms[j]).Core()
			}
		}
		goal := core.MakeProp(body)
		got := EnumerateLemmaTypeAdaptations(lemma, goal)
		require.Len(t, got, len(terms))
		keys := map[core.PropKey]bool{}
		for _, instance := range got {
			keys[instance.AlphaKey()] = true
		}
		if first == nil {
			first = keys
		} else {
			require.Equal(t, first, keys)
		}
	}
}

// A law read at an instance that holds the goal's own letter, where the
// law spells that letter too: associativity of `∘` at (num → A). The
// sweep drops `A := num → A` as recursive by name and commits B, C, D,
// leaving the law's A unbound — captured as the goal's A — so the
// instance it commits occurs nowhere in the goal. The single adaptation
// then retries renamed apart and takes the retry's instance, which binds
// every letter; the enumeration lists that instance and not the
// captured one. At a goal letter that does not collide nothing changes.
func TestTryAdaptLemmaTypes_CapturedLetterRetriesApart(t *testing.T) {
	parse := func(text string) core.Prop {
		res := dsl.ParsePropTextInScope(text, &dsl.ParseScope{FreshenMetaLetters: true})
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Prop
	}
	lemma := parse("∀f:(C → D). ∀g:(B → C). ∀h:(A → B). f ∘ (g ∘ h) = (f ∘ g) ∘ h")
	for _, letter := range []string{"A", "E"} {
		goal := parse(fmt.Sprintf("f:((num → %[1]s) → (num → %[1]s)), g:((num → %[1]s) → (num → %[1]s)), h:((num → %[1]s) → (num → %[1]s)) ⊢ f ∘ (g ∘ h) = (f ∘ g) ∘ h", letter))
		want := goalVarType(t, goal, "f")
		atGoal := func(instance core.Prop) bool {
			binders, _ := ematch.StripGuardedForalls(instance.Conclusion())
			for _, b := range binders {
				if !b.Type().Equals(want) {
					return false
				}
			}
			return len(binders) == 3
		}
		adapted := TryAdaptLemmaTypes(lemma, goal)
		require.NotNil(t, adapted, "letter %s", letter)
		require.True(t, atGoal(adapted), "letter %s: the single adaptation is at the goal's instance, got %s", letter, prop.PrintProp(adapted))
		instances := EnumerateLemmaTypeAdaptations(lemma, goal)
		require.NotEmpty(t, instances, "letter %s", letter)
		for _, instance := range instances {
			require.True(t, atGoal(instance), "letter %s: an enumerated instance not at the goal's: %s", letter, prop.PrintProp(instance))
		}
	}
}
