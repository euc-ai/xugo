// definitions.go — the chapter's definitional layer: finiteness (by its
// two rules, through the inductive door), its negation, and the fold's
// stage relation.

package finite_set

import (
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// finite — finite is the smallest predicate holding at ∅ and closed
// under insert. The README tells what that decides for the chapter;
// the theorems the definition comes with are the four faces at the top
// of finite_set.go.
var finite = family.DefineInductive(registry.InductiveEntry{
	Name: "Finite",
	Keys: registry.InductiveKeys{
		Rules:        "prop_49ad15a85dc9d731",
		Induct:       "prop_57661b5806f2d762",
		Cases:        "prop_965790a1f633e0cc",
		InductStrong: "prop_2474a304b8f54154",
	},
	Const: "finite",
	Type:  "set(A) → bool",
	Rules: []string{
		"finite(∅)",
		"∀x:A. ∀s:set(A). finite(s) ⇒ finite(insert(x, s))",
	},
	Deps: []registry.EntryLike{set_basic.EmptySetDef, set_basic.InsertDef},
})

// InfiniteDef — not finite.
var InfiniteDef = infiniteDefThm{family.Define(registry.DefEntry{
	Name:      "InfiniteDef",
	Key:       "prop_9a280881c977c526",
	Const:     "infinite",
	Type:      "set(A) → bool",
	Equations: []string{"∀s:set(A). infinite(s) ⇔ ¬finite(s)"},
	Deps:      []registry.EntryLike{FiniteRules},
})}

// setFoldStageDef — the stages of a fold, by recursion on the step count:
// set_fold_stage(f, b, s, a, n) says that folding f from b over s in n steps
// can land on a. Stage 0 is the empty fold; stage suc n takes one
// element off and asks the stage before about the rest.
var setFoldStageDef = setFoldStageDefThm{family.Define(registry.DefEntry{
	Name:  "setFoldStageDef",
	Key:   "prop_c115a4476508ddc5",
	Const: "set_fold_stage",
	Type:  "(A → B → B) → B → set(A) → B → num → bool",
	Equations: []string{
		"∀f:(A → B → B). ∀b:B. ∀s:set(A). ∀a:B. set_fold_stage(f, b, s, a, 0) ⇔ s = ∅ ∧ a = b",
		"∀f:(A → B → B). ∀b:B. ∀s:set(A). ∀a:B. ∀n:num. " +
			"    set_fold_stage(f, b, s, a, suc(n)) ⇔ " +
			"    ∃x:A. ∃c:B. x ∈ s ∧ set_fold_stage(f, b, delete(s, x), c, n) ∧ a = f(x, c)",
	},
})}
