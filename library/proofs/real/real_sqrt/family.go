// family.go — the real_sqrt family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=real_sqrt.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/real_sqrt go test -run TestRecordFamilyCNF ./library/integrity/gates/

package real_sqrt

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_sqrt.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates real/real_sqrt/real_sqrt.cnf.pb from it,
// and the registered entry prefix is the name's last segment
// (`real_sqrt.<Member>`).
var family = registry.NewFamily("real/real_sqrt", familyCNF).WithCoerceDomain(RealDomain)
