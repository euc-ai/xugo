package main

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/library/index"
	"github.com/euc-ai/xugo/library/visualize"
)

func queryGraph(t *testing.T, body string) any {
	t.Helper()
	out, err := rpcQuery([]byte(`{"cmd":"query","what":"graph",` + body + `}`))
	if err != nil {
		t.Fatalf("query graph %s: %v", body, err)
	}
	return out
}

// `query graph` names its scope by field: the corpus's families, or a
// member's proof, the member named as every question names one.
func TestQueryGraph_Scopes(t *testing.T) {
	families := queryGraph(t, `"scope":"families"`).(*visualize.FamilyGraph)
	overview, err := rpcQuery([]byte(`{"cmd":"query","what":"overview"}`))
	if err != nil {
		t.Fatal(err)
	}
	count := 0
	for _, d := range overview.(*index.Overview).Domains {
		count += len(d.Families)
	}
	if len(families.Nodes) != count || families.Layers == 0 {
		t.Errorf("families: %d nodes on %d rows for the overview's %d families", len(families.Nodes), families.Layers, count)
	}

	proof := queryGraph(t, `"scope":"proof","member":"elliptic_hasse_weil.HasseTheorem"`).(*visualize.ProofGraph)
	if proof.Target != "scheme/elliptic_hasse_weil.HasseTheorem" || proof.Name != "HasseTheorem" || len(proof.Grains) != 3 {
		t.Errorf("proof: target %q, name %q, %d grains", proof.Target, proof.Name, len(proof.Grains))
	}
	byID := queryGraph(t, `"scope":"proof","member":"scheme/elliptic_hasse_weil.HasseTheorem"`).(*visualize.ProofGraph)
	if len(byID.Grains) != 3 || len(byID.Grains[1].Nodes) != len(proof.Grains[1].Nodes) {
		t.Errorf("a member named by id and by registered name draw two graphs")
	}
}

// A field the scope does not take is refused by name, and so is a
// missing scope or argument.
func TestQueryGraph_RefusesMisplacedFields(t *testing.T) {
	for body, want := range map[string]string{
		`"scope":"families","member":"peano.Induction"`:        "query graph families takes no `member`",
		`"scope":"proof","member":"peano.Induction","depth":2`: "query graph proof takes no `depth`",
		`"scope":"proof"`:            "query graph proof requires `member`",
		`"member":"peano.Induction"`: "query graph requires `scope`",
		`"scope":"orbit"`:            "unknown scope",
		`"scope":"proof","member":"no_such_family.NoSuchMember"`: "names no corpus member",
	} {
		_, err := rpcQuery([]byte(`{"cmd":"query","what":"graph",` + body + `}`))
		if err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("%s: error %v, want one saying %q", body, err, want)
		}
	}
	if _, err := rpcQuery([]byte(`{"cmd":"query","what":"family","family":"sets/set_basic","scope":"proof"}`)); err == nil || !strings.Contains(err.Error(), "query family takes no `scope`") {
		t.Errorf("a graph field on another question: %v", err)
	}
}

// The CLI reads a scope's words into the same fields.
func TestQueryGraph_CLIWords(t *testing.T) {
	var in QueryRPCInput
	in.graphArgs([]string{"families"})
	if in.Scope != "families" || in.Member != "" {
		t.Errorf("families words: scope %q, member %q", in.Scope, in.Member)
	}
	in = QueryRPCInput{}
	in.graphArgs([]string{"proof", "a.X"})
	if in.Scope != "proof" || in.Member != "a.X" {
		t.Errorf("proof words: scope %q, member %q", in.Scope, in.Member)
	}
}
