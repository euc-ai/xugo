package int_lattice

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed int_lattice.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/module/int_lattice", familyCNF).WithAbbrev(Abbrev{
	{Name: "ℤⁿ", Text: "free_module_record(int_ring, {i:num | i < n})"},
})
