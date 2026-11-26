package algebra_point_bounds

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed algebra_point_bounds.cnf.pb
var familyCNF []byte

var family = registry.NewFamily(
	"algebra/ring/algebra_point_bounds", familyCNF).WithAbbrev(Abbrev{
	{Name: "algebraModule", Text: "scalar_restriction(i, regular_module(S))"},
	{Name: "dual", Text: "hom_module(field_ring(K), «algebraModule», regular_module(field_ring(K)))"},
	{Name: "points", Text: "{f:B → A | " +
		"    f ∈ algebra_points(S, field_ring(K), ∅, λb:B. K.zero) ∧ (∀a:A. a ∈ K.carrier ⇒ f(i(a)) = a)}"},
})
