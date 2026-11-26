// family.go — the simplicial_module family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=simplicial_module.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=simplicial/simplicial_module go test -run TestRecordFamilyCNF ./library/integrity/gates/

package simplicial_module

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed simplicial_module.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// simplicial_module/simplicial_module.cnf.pb from the name's basename, and the
// registered entry prefix is `simplicial_module.<Member>`. Its table
// names the two face iterates of a bisimplicial module D:
// «rowLastFaces»(q, k, r, y) removes the last face r times from y in
// horizontal degree k on the row q, «columnZerothFaces»(c, k, r, y) the
// 0-th face r times from y in vertical degree k in the column c; and
// «degree module»(q) is the module M(q) the simplices of degree q cut
// out of V.
var family = registry.NewFamily("simplicial/simplicial_module", familyCNF).WithAbbrev(Abbrev{
	{Name: "rowLastFaces", Text: "λq:num. λk:num. λr:num. λy:B. " +
		"    face_iterate_top(λm:num. λi:num. D.dh(m, q, i), k, r, y)"},
	{Name: "columnZerothFaces", Text: "λc:num. λk:num. λr:num. λy:B. " +
		"    face_iterate_bottom(λm:num. λj:num. D.dv(c, m, j), k, r, y)"},
	{Name: "degree module", Text: "λq:num. restrict_module(V, M.simplices(q))"},
})
