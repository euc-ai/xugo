// vocab.go — the chapter's statement vocabulary.
//
// The chapter's alphabet is four constants. Three are DEFINED HERE
// (well_founded.go opens with them): `wellfounded`, the well-foundedness
// predicate on a binary relation; `measure_less`, the relation a ℕ-valued
// measure induces; and `accessible`, well-foundedness read one point
// at a time. The fourth, `transitive_closure`, belongs to
// `relations/closure`; this chapter states what taking it does to
// well-foundedness. Everything else a statement
// here mentions is either bound by the statement itself (relations,
// measures and predicates are all ∀-bound with annotated types) or
// belongs to ℕ (`<` in the nat instance), whose type its surroundings
// pin. No domain table applies — the chapter is not ℕ's — and none is
// needed: a defined constant's one authoritative type is its mint, so
// the rows below name the constants and say nothing about their types.
//
// Every constant is declared at its abstract letters; each
// occurrence in a statement instantiates independently (the parser
// freshens a meta's letters per occurrence), which is what lets one
// statement use `wellfounded` at two instances — the inverse-image law is wellfounded at
// the target type implying wellfounded at the source — with no explicit ties:
// the binder annotations anchor every letter. The family installs the
// rows into each member's ParseScope (family.go's WithVocabSpec), and
// the build surface members take with `v := ops(a.Ctx())` is rendered
// from the same rows (zz_vocab_gen.go).

package well_founded

import (
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name, each
// typed by its mint.
var vocab = registry.NewVocabSpec(nil).
	OpsName("wfOps").
	Term("wellfounded").  // (A → A → bool) → bool
	Term("measure_less"). // (A → num) → A → A → bool
	Term("accessible").   // (A → A → bool) → A → bool
	// (A → A → bool) → A → A → bool — relations/closure's.
	Term("transitive_closure").As("TransitiveClosure")
