// family.go — the lattice_pair_sequence family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=lattice_pair_sequence.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/lattice_pair_sequence go test -run TestRecordFamilyCNF ./library/integrity/gates/

package lattice_pair_sequence

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed lattice_pair_sequence.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// lattice_pair_sequence/lattice_pair_sequence.cnf.pb from the name's basename, and
// the registered entry prefix is `lattice_pair_sequence.<Member>`.
var family = registry.NewFamily("scheme/lattice_pair_sequence", familyCNF).WithOuterAbbrev(
	lattice_pair.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "waQuotientPairs", Text: "set_cross(left_cosets(V.add, fst(M), fst(M')), " +
		"    left_cosets(V.add, snd(M), snd(M')))"},
	{Name: "waQ0", Text: "quotient_module(restrict_module(V, fst(M)), fst(M'))"},
	{Name: "waQ1", Text: "quotient_module(restrict_module(V, snd(M)), snd(M'))"},
	{Name: "waAmbientModSubSum", Text: "quotient_module( " +
		"    restrict_module(V, lattice_pair_ambient(R, V, M)), set_mul(V.add, fst(M'), snd(M')))"},
	{Name: "waQ01", Text: "quotient_module(restrict_module(V, lattice_pair_ambient(R, V, M)), " +
		"    lattice_pair_ambient(R, V, M'))"},
	{Name: "waQ01Carrier", Text: "left_cosets(V.add, " +
		"    lattice_pair_ambient(R, V, M), " +
		"    lattice_pair_ambient(R, V, M'))"},
	{Name: "waKernelModule", Text: "lattice_pair_quotient_kernel(R, V, M, M')"},
	{Name: "waKernelPairs", Text: "group_kernel(lattice_pair_ambient(R, V, M'), " +
		"    «waQuotientPairs», " +
		"    lattice_pair_quotient_difference(R, V, M'))"},
	{Name: "waH1Map", Text: "λx:set(B). set_mul(V.add, x, set_mul(V.add, fst(M), snd(M)))"},
})
