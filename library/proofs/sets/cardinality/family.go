// family.go — the cardinality family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// The dependency direction is one-way and load-bearing: `cardinality`
// imports `finite_set` for the entries it cites, so `finite_set` must never
// import back. That is why this package's blank import lives in
// `sets/sets.go` and not in the parent — the reverse would be a cycle.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=<cardinality.MEMBER> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=sets/cardinality go test -run TestRecordFamilyCNF ./library/integrity/gates/

package cardinality

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed cardinality.cnf.pb
var familyCNF []byte

// The registered name is the full path; `registry.Family` takes
// `path.Base` of it for the member prefix, so members read
// `cardinality.X` and the nesting costs no depth in any DepNames string.
var family = registry.NewFamily("sets/cardinality", familyCNF).WithVocabSpec(
	vocab).WithAbbrev(Abbrev{
	{Name: "funspaceWhole", Text: "{h:(A → B) | (∀x:A. x ∈ s ⇒ h(x) ∈ t) ∧ (∀x:A. x ∉ s ⇒ h(x) = d)}"},
	{Name: "funspaceSized", Text: "has_size(«funspaceWhole», nat_pow(card(t), card(s)))"},
})
