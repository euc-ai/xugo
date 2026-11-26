// family.go — the set_category family manifest: the registry handle
// every member registers into, and the family's one shared recorded
// CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=set_category.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=category/set_category go test -run TestRecordFamilyCNF ./library/integrity/gates/

package set_category

import (
	// functions mints junk, normalize_on, composition and injective_on,
	// set_basic and set_image the set vocabulary and the image: the
	// constants this family's members spell, initialized before they
	// are parsed.
	_ "github.com/euc-ai/xugo/library/proofs/sets/functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_image"

	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed set_category.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// set_category/set_category.cnf.pb from the name's basename, and the
// registered entry prefix is `set_category.<Member>`.
var family = registry.NewFamily("category/set_category", familyCNF)
