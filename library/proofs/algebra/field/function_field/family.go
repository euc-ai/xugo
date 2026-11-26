package function_field

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed function_field.cnf.pb
var familyCNF []byte

// family is the family handle. «constants» is the field of constants of
// L over k: the elements of L algebraic over k, read over the binders
// M, k, L the chapter's statements share.
var family = registry.NewFamily("algebra/field/function_field", familyCNF).WithAbbrev(Abbrev{
	{Name: "constants", Text: "{x:A | x ∈ L ∧ algebraic_over(M, k, x)}"},
})
