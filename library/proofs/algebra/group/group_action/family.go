package group_action

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed group_action.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/group/group_action", familyCNF).WithAbbrev(Abbrev{
	{Name: "residues", Text: "λn:num. " +
		"    mk_group(λi:num. λj:num. rem(i + j, n), 0, λi:num. rem(n - i, n), {i:num | i < n})"},
	{Name: "tuples", Text: "λn:num. " +
		"    {l:list(A) | " +
		"        list_length(l) = n ∧ " +
		"        (∀y:A. list_member(y, l) ⇒ y ∈ G.carrier) ∧ " +
		"        list_fold(G.mul, l, G.one) = G.one}"},
	{Name: "orbits", Text: "image(λx:B. group_orbit(G, act, x), X)"},
	{Name: "rotate", Text: "λn:num. λk:num. λl:list(A). εm:list(A). " +
		"    list_length(m) = n ∧ (∀i:num. i < n ⇒ list_nth(m, i) = list_nth(l, rem(i + k, n)))"},
})
