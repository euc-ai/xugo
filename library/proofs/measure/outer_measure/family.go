package outer_measure

import (
	// extended_nonneg_real mints the value type and extended_series, and
	// set_basic the set operations, that the definition here spells: the
	// imports initialize those mints before it is parsed.
	_ "github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"

	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed outer_measure.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("measure/outer_measure", familyCNF).WithCoerceDomain(RealDomain)
