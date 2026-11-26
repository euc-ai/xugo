// family.go — the simplex_category family manifest: the registry handle
// every member registers into, and the family's one shared recorded
// CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=simplex_category.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=simplicial/simplex_category go test -run TestRecordFamilyCNF ./library/integrity/gates/

package simplex_category

import (
	// functions mints normalize_on and composition, num_segment the
	// interval `0 .. n`: constants this family's definitions spell,
	// initialized before they are parsed.
	_ "github.com/euc-ai/xugo/library/proofs/sets/functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/num_segment"

	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed simplex_category.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// simplex_category/simplex_category.cnf.pb from the name's basename,
// and the registered entry prefix is `simplex_category.<Member>`.
var family = registry.NewFamily("simplicial/simplex_category", familyCNF)
