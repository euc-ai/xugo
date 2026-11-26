// vocab.go — the chapter's alphabet, declared once.
//
// This chapter's subject is a map, so its alphabet starts with the two
// combinators that name maps without naming any set: `identity_map`
// and composition `∘`. No member constructs a term over either one;
// every law about them is proved by UNFOLDING them, and `Unfold` takes
// the name and reads the scope the family's install populates.
//
// Both are this chapter's own definitions (functions.go: IdentityApply
// and ComposeApply ARE the definitions of `identity_map` and `o`), so each name's
// type is read off its mint through the Alphabet's fallback, like the
// set names — which are set_basic's definitions, declared here by name
// when a member states them. The text-DSL reads `∘` on its own and
// resolves the `o` it lowers to through the family's resolver to the
// mint's def-carrying meta, so the declaration is the chapter's
// statement of its alphabet, not what makes the unfold find a def.
//
// Each name binds at ONE type instance per Script. A statement naming a
// constant at a second instance says so in its own text, with the DSL's
// `⟨…⟩` annotation.
//
// The chapter's third definition is a predicate rather than a
// combinator: `injective_on(s, f)`, that `f` separates the points of
// `s` (functions.go: InjectiveOnDef). The corpus states injectivity
// through it, on a set or on `𝕌`. The fourth is a set term:
// `preimage_on(s, f, t)`, the points of `s` that `f` sends into `t`
// (functions.go: PreimageOnDef). Statements spell every preimage
// through it, restricted to a set or, at `𝕌`, whole; it is in the set
// driver's vocabulary, so `BySets` reads it as its membership condition.
// The fifth is a set term too: `fun_support(zero, f)`, the points where
// `f` is not `zero` (functions.go: FunSupportDef). The corpus spells
// every support through it, and it is in the set driver's vocabulary for
// the same reason.
// The chapter's other definitions — `inverse_on` and, in normalize.go,
// `junk` and `normalize_on` — are not declared here: their statements
// read them through their mints, at whatever letters they spell.
//
// Membership carries the restricted laws — a map from a set to a set is
// a condition on where points go, and `∈` is enough to say it. The other
// two set names are stated by fewer members: inclusion by `Cantor`'s
// diagonal set and by restricting injectivity to a part
// (`InjectiveOnSubset`), and `image` by the laws of the named inverse
// (`inverse_on.go`), which read a chosen point only where the map
// reaches.

package functions

import (
	"github.com/euc-ai/xugo/library/proofs/sets/internal/setvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data: the family installs it into
// every member's ParseScope (family.go's WithVocabSpec), and the vocab
// generator renders the build surface from it (zz_vocab_gen.go).
var vocab = registry.NewVocabSpec(setvocab.Table()).
	OpsName("functionsOps").
	// the set side: membership, inclusion, and the reach of a map
	Term("set_member").Term("subset").Term("image").
	Term("identity_map"). // the identity combinator
	Term("o").            // composition, `∘`
	Term("injective_on"). // separating the points of a set
	Term("preimage_on").  // pulling a set back into a source set
	Term("fun_support")   // the points where a map is not a given value

	// The chapter's set-side closer is `BySets`. Two notes on how this
	// chapter meets it:
	//
	// A statement mentioning `∘` needs `Unfold(ComposeApply)` FIRST — the driver's
	// vocabulary is the set constructors, so a function constant is opaque
	// to it and has to become an application before the residual is about
	// points at all.
	//
	// It unfolds the set constructors themselves, so a guard like
	// `x ∈ 𝕌` dissolves without a law being cited, where a `By` — whose
	// terminal is a refutation and does no unfolding — has to be handed
	// one: `InjectiveLeftInverse` reads its relativized sibling at `𝕌` by
	// a `By`, and is handed `set_basic.InUniv`.
	//
	// The mirror of that point is `Normalized` in a `By` premise
	// list: an implication brought to bear on a goal it entails still has
	// to be broken into clauses before a refutation meets it. It carries no
	// premise and says nothing about the mathematics.
