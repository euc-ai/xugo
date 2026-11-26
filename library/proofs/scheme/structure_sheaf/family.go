// family.go — the structure_sheaf family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=structure_sheaf.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/structure_sheaf go test -run TestRecordFamilyCNF ./library/integrity/gates/

package structure_sheaf

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed structure_sheaf.cnf.pb
var familyCNF []byte

// _Section is the Go type of a section of the structure sheaf,
// set(A) → set(prod(A, A)): at each point of its open set a fraction
// class, a set of numerator–denominator pairs, and ∅ elsewhere.
type _Section = Fun[Set[A], Set[Prod[A, A]]]

// _Germ is the Go type of an element of a stalk of the structure sheaf: a
// germ, the class of the (open set, section) pairs that agree near the point.
type _Germ = Set[Prod[Set[Set[A]], _Section]]

// family is the family handle. The recorder derives structure_sheaf/structure_sheaf.cnf.pb
// from the name's basename, and the registered entry prefix is
// `structure_sheaf.<Member>`.
var family = registry.NewFamily("scheme/structure_sheaf", familyCNF).WithAbbrev(Abbrev{
	// The coefficient section of a over U: the fraction section a / 1.
	{Name: "coefficientSection", Text: "λR:ring_ops(A). λU:set(set(A)). λa:A. " +
		"    fraction_section(R, U, a, R.one)"},
	// The coefficient germ of a at the prime p: the germ at p of the coefficient section of a over the whole spectrum.
	{Name: "coefficientGerm", Text: "λR:ring_ops(A). λp:set(A). λa:A. " +
		"    sheaf_germ(zariski_topology(R), " +
		"        structure_sections(R), " +
		"        structure_restrict, " +
		"        p, " +
		"        prime_spectrum(R), " +
		"        «coefficientSection»(R, prime_spectrum(R), a))"},
	// hⁿ / 1 kills the section s at every prime of V: hⁿ / 1 times s(q) is the zero fraction.
	{Name: "powerKills", Text: "λR:ring_ops(A). " +
		"λh:A. " +
		"λs:(set(A) → set(prod(A, A))). " +
		"λn:num. " +
		"λV:set(set(A)). " +
		"∀q:set(A). " +
		"    q ∈ V ⇒ " +
		"    fraction_mul(R.mul, " +
		"        R.carrier, " +
		"        R.carrier ∖ q, " +
		"        fraction_class(R.mul, R.carrier, R.carrier ∖ q, monoid_pow(R.mul, R.one, h, n), R.one), " +
		"        s(q)) = " +
		"    fraction_zero(R.zero, R.mul, R.one, R.carrier, R.carrier ∖ q)"},
})
