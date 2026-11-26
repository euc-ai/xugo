// family.go — the signed_word family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// The chapter is the TERM-LEVEL signed reading — the permanent home of
// the mathematics the type-level words/signed_word chapter carries — and it
// lives under words/machine_word only while that chapter still occupies
// words/signed_word. The registered entry prefix is the name's LAST
// segment, so entries are `signed_word.<Member>` from day one (the
// type-level family stepped aside to words/signed_legacy); when the
// legacy chapter retires, this directory moves to words/signed_word and
// every registered name, key and pb byte stays put.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=signed_word.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=words/signed_word go test -run TestRecordFamilyCNF ./library/integrity/gates/

package signed_word

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed signed_word.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates words/signed_word/signed_word.cnf.pb from it. The
// statement vocabulary — the chapter's minted constants and the ℤ
// alphabet the signed reading is stated in — is declared in vocab.go,
// beside the mints.
var family = registry.NewFamily("words/signed_word", familyCNF).WithVocabSpec(vocab)
