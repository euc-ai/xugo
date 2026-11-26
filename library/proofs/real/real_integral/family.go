// family.go — the real_integral family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=real_integral.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/real_integral go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// Note the two spellings: RECORD_CNF takes the registered member name,
// which carries the family's BASE name; CNF_GC takes the family's FULL
// domain path.

package real_integral

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_integral.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates real/real_integral/real_integral.cnf.pb from it, and the registered
// entry prefix is the name's last segment (`real_integral.<Member>`). Its
// numbers are reals: an `&` no operand anchors is ℝ's embedding, by
// the declaration on the handle.
var family = registry.NewFamily("real/real_integral", familyCNF).WithCoerceDomain(
	RealDomain).WithAbbrev(Abbrev{
	{Name: "partition", Text: "λa:real. λb:real. λn:num. λp:(num → real). " +
		"    p(0) = a ∧ p(n + 1) = b ∧ (∀i:num. i ≤ n ⇒ p(i) ≤ p(i + 1))"},
	{Name: "finePartition", Text: "λa:real. " +
		"λb:real. " +
		"λδ:real. " +
		"λn:num. " +
		"λp:(num → real). " +
		"λt:(num → real). " +
		"    p(0) = a ∧ " +
		"    p(n + 1) = b ∧ " +
		"    (∀i:num. i ≤ n ⇒ p(i) ≤ t(i) ∧ t(i) ≤ p(i + 1) ∧ p(i + 1) - p(i) < δ)"},
	{Name: "riemannSum", Text: "λf:(real → real). λn:num. λp:(num → real). λt:(num → real). " +
		"    Σ_{i∈0 .. n} f(t(i)) * (p(i + 1) - p(i))"},
	{Name: "sumsWithin", Text: "λf:(real → real). " +
		"λa:real. " +
		"λb:real. " +
		"λδ:real. " +
		"λε:real. " +
		"∀n:num. " +
		"∀p t:(num → real). " +
		"∀m:num. " +
		"∀q s:(num → real). " +
		"    «finePartition»(a, b, δ, n, p, t) ∧ «finePartition»(a, b, δ, m, q, s) ⇒ " +
		"    |«riemannSum»(f, n, p, t) - «riemannSum»(f, m, q, s)| < ε"},
})
