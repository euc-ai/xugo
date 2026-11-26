package main

import (
	"encoding/json"
	"os"
	"path"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/library/index"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/stretchr/testify/require"
)

func queryMember(t *testing.T, member string) *QueryMemberOutput {
	t.Helper()
	out, err := rpcQuery([]byte(`{"cmd":"query","what":"member","member":"` + member + `"}`))
	if err != nil {
		t.Fatalf("query member %s: %v", member, err)
	}
	return out.(*QueryMemberOutput)
}

// `query member` is the door that shows a member, and it serves the
// member's two texts: the chapter's as `statement`, the one that reads
// with nothing declared as `statement_typed`. The rows are the shapes a
// kernel print once showed through — a set-builder (its comprehension
// spelled with the GEN%PVAR binder where the constant carries a type
// annotation), a chapter notation over an implicit structure, a
// definition door's computed statement, a door's induction principle.
func TestQueryMember_TwoTexts(t *testing.T) {
	rows := []struct{ member, statement, typed string }{
		{"monoidal.Fibres",
			"iterated_op(op, image(f, s), λy:C. iterated_op(op, {x | x ∈ s ∧ f(x) = y}, g))",
			"{x:A | x ∈ s ∧ f(x) = y}"},
		{"set_image.SimpleImageGen", "{f(x) | x:A | P(x)} = image(f, {x:A | P(x)})", "{f(x):B | x:A | P(x)} = image(f, {x:A | P(x)})"},
		{"euclidean.NormTriangle", "∀n:num. ∀u v:(num → real). ‖u + v‖_n ≤ ‖u‖_n + ‖v‖_n", "‖u + v‖_n"},
		{"set_basic.UnionDef", "s ∪ t = {x:A | x ∈ s ∨ x ∈ t}", "s ∪ t = {x:A | x ∈ s ∨ x ∈ t}"},
		{"list.Induction",
			"∀P:(list(A) → bool). ∀x:list(A). P(nil) ∧ (∀a0:A. ∀a1:list(A). P(a1) ⇒ P(cons(a0, a1))) ⇒ P(x)",
			"∀P:(list(A) → bool). ∀x:list(A). P(nil) ∧ (∀a0:A. ∀a1:list(A). P(a1) ⇒ P(cons(a0, a1))) ⇒ P(x)"},
	}
	for _, row := range rows {
		m := queryMember(t, row.member)
		if !strings.Contains(m.Statement, row.statement) {
			t.Errorf("%s: statement %q does not read %q", row.member, m.Statement, row.statement)
		}
		if !strings.Contains(m.StatementTyped, row.typed) {
			t.Errorf("%s: statement_typed %q does not read %q", row.member, m.StatementTyped, row.typed)
		}
		for _, text := range []string{m.Statement, m.StatementTyped} {
			if strings.Contains(text, "GEN%PVAR") || strings.Contains(text, "set_comprehension") {
				t.Errorf("%s: a served text spells the comprehension's machine form: %s", row.member, text)
			}
		}
		out, err := rpcQuery([]byte(`{"cmd":"query","what":"dossier","member":"` + row.member + `"}`))
		if err != nil {
			t.Fatalf("query dossier %s: %v", row.member, err)
		}
		d := out.(*QueryDossierOutput)
		if d.Member.Statement != m.Statement || d.StatementTyped != m.StatementTyped {
			t.Errorf("%s: the dossier reads the member otherwise\n  statement      : %s\n  statement_typed: %s",
				row.member, d.Member.Statement, d.StatementTyped)
		}
	}
}

// A member is named by its index id, its registered name or its own
// key, and all three answer with the one member — what it cites and
// the cards it stands on by index id, itself by both names.
func TestQueryMember_NamesAndCitations(t *testing.T) {
	entry, ok := registry.ByName("real_sequences.BoundedClusterPoint")
	if !ok {
		t.Fatal("real_sequences.BoundedClusterPoint is not registered")
	}
	byName := queryMember(t, entry.Name)
	if byName.ID != "real/real_sequences.BoundedClusterPoint" || byName.Entry != entry.Name || byName.Key != entry.Key {
		t.Fatalf("id %q, entry %q, key %q", byName.ID, byName.Entry, byName.Key)
	}
	for _, ref := range []string{byName.ID, entry.Key} {
		if got := queryMember(t, ref); got.ID != byName.ID {
			t.Errorf("%q answers with %s", ref, got.ID)
		}
	}
	if len(byName.Deps) != len(entry.DepEntries()) {
		t.Fatalf("deps %v against %d declared", byName.Deps, len(entry.DepEntries()))
	}
	for i, dep := range entry.DepEntries() {
		if byName.Deps[i] != index.MemberID(dep) {
			t.Errorf("dep %d is %q, the declared one is %s", i, byName.Deps[i], index.MemberID(dep))
		}
	}

	// A card, the first the registry lists, whichever that is: a card
	// named here would be a proved member the day its proof landed.
	for _, e := range registry.All() {
		if !e.IsCard() {
			continue
		}
		card := queryMember(t, e.Name)
		if !card.Card || card.Kind != "card" || card.Note == "" {
			t.Errorf("the card %s answers card=%v kind=%q note=%q", e.Name, card.Card, card.Kind, card.Note)
		}
		if !slices.Contains(card.Cards, card.ID) {
			t.Errorf("the frontier %v of the card %s does not hold the card itself", card.Cards, e.Name)
		}
		return
	}
	t.Log("the corpus has no card: a card's answer goes unchecked")
}

// The registered name a session cites is the index id from its last
// `/` on: an id read off a `query` answer is cited by dropping the
// family's directory.
func TestQueryMember_IDCarriesTheRegisteredName(t *testing.T) {
	for _, e := range registry.All() {
		id := index.MemberID(e)
		if name := id[strings.LastIndex(id, "/")+1:]; name != e.Name {
			t.Errorf("%s: the id %s ends in %q", e.Name, id, name)
		}
	}
}

// `query member` and `query dossier` take one member as `member` and
// several as `members`. Several are answered by one answer holding each
// member's, in the order given — the answer the member gets asked alone
// — with the names no member carries listed apart under the refusal the
// question of one gives. Both fields at once, and `members` on a
// question that takes none, are refused by name.
func TestQueryMember_OneOrSeveral(t *testing.T) {
	const several = `["real/real_sequences.CauchyConverges","zz_no_family.NoSuchMember","nat_num/nat_arith.Add"]`
	known := []string{"real/real_sequences.CauchyConverges", "nat_num/nat_arith.Add"}
	asJSON := func(v any) string {
		data, err := json.Marshal(v)
		require.NoError(t, err)
		return string(data)
	}
	for _, what := range []string{"member", "dossier"} {
		out, err := rpcQuery([]byte(`{"cmd":"query","what":"` + what + `","members":` + several + `}`))
		require.NoError(t, err, what)
		var answers []any
		var unknown []UnknownName
		switch batch := out.(type) {
		case *QueryMembersOutput:
			for _, m := range batch.Members {
				answers = append(answers, m)
			}
			unknown = batch.Unknown
		case *QueryDossiersOutput:
			for _, d := range batch.Dossiers {
				answers = append(answers, d)
			}
			unknown = batch.Unknown
		default:
			t.Fatalf("query %s of several members answered a %T", what, out)
		}
		require.Len(t, answers, len(known), what)
		for i, ref := range known {
			alone, err := rpcQuery([]byte(`{"cmd":"query","what":"` + what + `","member":"` + ref + `"}`))
			require.NoError(t, err, "%s %s", what, ref)
			require.Equal(t, asJSON(alone), asJSON(answers[i]), "%s %s: the answer among several is the answer alone", what, ref)
		}
		_, refusal := rpcQuery([]byte(`{"cmd":"query","what":"` + what + `","member":"zz_no_family.NoSuchMember"}`))
		require.Error(t, refusal)
		require.Equal(t, []UnknownName{{Name: "zz_no_family.NoSuchMember", Reason: refusal.Error()}}, unknown, what)

		_, err = rpcQuery([]byte(`{"cmd":"query","what":"` + what + `","member":"nat_num/nat_arith.Add","members":` + several + `}`))
		require.ErrorContains(t, err, "query "+what+" takes `member` or `members`, not both")
	}
	_, err := rpcQuery([]byte(`{"cmd":"query","what":"between","from":"nat_num/nat_arith.Add","to":"nat_num/nat_arith.Add","members":` + several + `}`))
	require.ErrorContains(t, err, "query between takes no `members`")
}

// On the command line one name asks with `member` and two or more with
// `members`.
func TestQueryMember_CommandLine(t *testing.T) {
	stdout := os.Stdout
	os.Stdout, _ = os.Open(os.DevNull)
	defer func() { os.Stdout = stdout }()

	resetTrace()
	cmdQuery([]string{"member", "nat_num/nat_arith.Add"})
	require.Equal(t, "nat_num/nat_arith.Add", traceEntry.Output.(*QueryMemberOutput).ID)

	resetTrace()
	cmdQuery([]string{"member", "nat_num/nat_arith.Add", "real/real_sequences.CauchyConverges"})
	members := traceEntry.Output.(*QueryMembersOutput)
	require.Len(t, members.Members, 2)
	require.Equal(t, "nat_num/nat_arith.Add", members.Members[0].ID)
	require.Equal(t, "real/real_sequences.CauchyConverges", members.Members[1].ID)
	require.Empty(t, members.Unknown)

	resetTrace()
	cmdQuery([]string{"dossier", "nat_num/nat_arith.Add", "real/real_sequences.CauchyConverges"})
	dossiers := traceEntry.Output.(*QueryDossiersOutput)
	require.Len(t, dossiers.Dossiers, 2)
	require.Empty(t, dossiers.Unknown)
}

// `query family`, `query deps` and `query dependents` take several
// names as `query member` does: one answer holding each name's, in the
// order given — the answer the name gets asked alone — and the names
// nothing carries apart, under the refusal the question of one gives.
// A family's short name asks what its path asks. A neighborhood's
// `depth` is every member's.
func TestQueryFamilyAndNeighborhoods_OneOrSeveral(t *testing.T) {
	asJSON := func(v any) string {
		data, err := json.Marshal(v)
		require.NoError(t, err)
		return string(data)
	}
	ask := func(body string) any {
		out, err := rpcQuery([]byte(body))
		require.NoError(t, err, body)
		return out
	}

	families := ask(`{"cmd":"query","what":"family","families":["real/real_sequences","zz_no_domain/zz_no_family","nat_num/nat_arith"]}`).(*QueryFamiliesOutput)
	require.Len(t, families.Families, 2)
	for i, name := range []string{"real/real_sequences", "nat_num/nat_arith"} {
		alone := ask(`{"cmd":"query","what":"family","family":"` + name + `"}`)
		require.Equal(t, asJSON(alone), asJSON(families.Families[i]), "family %s: the answer among several is the answer alone", name)
	}
	byShort := ask(`{"cmd":"query","what":"family","families":["real_sequences","nat_arith"]}`).(*QueryFamiliesOutput)
	require.Empty(t, byShort.Unknown)
	require.Equal(t, asJSON(families.Families), asJSON(byShort.Families), "a family's short name asks what its path asks")
	_, refusal := rpcQuery([]byte(`{"cmd":"query","what":"family","family":"zz_no_domain/zz_no_family"}`))
	require.Error(t, refusal)
	require.Equal(t, []UnknownName{{Name: "zz_no_domain/zz_no_family", Reason: refusal.Error()}}, families.Unknown)
	_, err := rpcQuery([]byte(`{"cmd":"query","what":"family","family":"nat_num/nat_arith","families":["real/real_sequences"]}`))
	require.ErrorContains(t, err, "query family takes `family` or `families`, not both")
	_, err = rpcQuery([]byte(`{"cmd":"query","what":"member","member":"nat_num/nat_arith.Add","families":["real/real_sequences"]}`))
	require.ErrorContains(t, err, "query member takes no `families`")

	const several = `["real/real_sequences.CauchyConverges","zz_no_family.NoSuchMember","nat_num/nat_arith.Add"]`
	known := []string{"real/real_sequences.CauchyConverges", "nat_num/nat_arith.Add"}
	for _, what := range []string{"deps", "dependents"} {
		for _, depth := range []string{``, `,"depth":2`} {
			batch := ask(`{"cmd":"query","what":"` + what + `","members":` + several + depth + `}`).(*QueryNeighborhoodsOutput)
			require.Len(t, batch.Neighborhoods, len(known), what)
			for i, ref := range known {
				alone := ask(`{"cmd":"query","what":"` + what + `","member":"` + ref + `"` + depth + `}`)
				require.Equal(t, asJSON(alone), asJSON(batch.Neighborhoods[i]), "%s %s%s: the answer among several is the answer alone", what, ref, depth)
			}
			require.Len(t, batch.Unknown, 1)
			require.Equal(t, "zz_no_family.NoSuchMember", batch.Unknown[0].Name)
		}
		_, err := rpcQuery([]byte(`{"cmd":"query","what":"` + what + `","member":"nat_num/nat_arith.Add","members":` + several + `}`))
		require.ErrorContains(t, err, "query "+what+" takes `member` or `members`, not both")
		_, err = rpcQuery([]byte(`{"cmd":"query","what":"` + what + `","members":` + several + `,"depth":-1}`))
		require.ErrorContains(t, err, "depth must be 0 (the whole reach) or positive", "a failure that is no unknown name is the question's")
	}
}

// On the command line two or more names ask with `families` and
// `members`, and --depth is every member's.
func TestQueryFamilyAndNeighborhoods_CommandLine(t *testing.T) {
	stdout := os.Stdout
	os.Stdout, _ = os.Open(os.DevNull)
	defer func() { os.Stdout = stdout }()

	resetTrace()
	cmdQuery([]string{"family", "nat_num/nat_arith"})
	require.Equal(t, "nat_num/nat_arith", traceEntry.Output.(*index.Family).Name)

	resetTrace()
	cmdQuery([]string{"family", "nat_arith"})
	require.Equal(t, "nat_num/nat_arith", traceEntry.Output.(*index.Family).Name, "a short name names its family on the command line too")

	resetTrace()
	cmdQuery([]string{"family", "nat_num/nat_arith", "real/real_sequences"})
	families := traceEntry.Output.(*QueryFamiliesOutput)
	require.Len(t, families.Families, 2)
	require.Equal(t, "real/real_sequences", families.Families[1].Name)

	resetTrace()
	cmdQuery([]string{"deps", "real/real_sequences.CauchyConverges", "nat_num/nat_arith.Add", "--depth", "2"})
	deps := traceEntry.Output.(*QueryNeighborhoodsOutput)
	require.Len(t, deps.Neighborhoods, 2)
	require.Equal(t, 2, deps.Neighborhoods[0].Depth)
	require.Equal(t, index.Deps, deps.Neighborhoods[0].Direction)

	resetTrace()
	cmdQuery([]string{"dependents", "nat_num/nat_arith.Add", "real/real_sequences.CauchyConverges"})
	require.Len(t, traceEntry.Output.(*QueryNeighborhoodsOutput).Neighborhoods, 2)
}

// `query cards` names its families as `query family` does, by path or
// short name, and spells each card's statement typed, as `query member`
// serves it; a name naming no family refuses the question, and the
// families go in `family` or `families`, not both.
func TestQueryCards_OfFamilies(t *testing.T) {
	asJSON := func(v any) string {
		data, err := json.Marshal(v)
		require.NoError(t, err)
		return string(data)
	}
	ask := func(body string) any {
		out, err := rpcQuery([]byte(body))
		require.NoError(t, err, body)
		return out
	}
	name := ""
	for _, d := range ask(`{"cmd":"query","what":"overview"}`).(*index.Overview).Domains {
		for _, f := range d.Families {
			if f.Counts.Cards > 0 && name == "" {
				name = f.Family
			}
		}
	}
	require.NotEmpty(t, name, "the corpus has a family holding cards")
	short := path.Base(name)

	v := ask(`{"cmd":"query","what":"cards","family":"` + short + `"}`).(*index.CardsView)
	require.NotEmpty(t, v.Cards)
	spelled := 0
	for _, card := range v.Cards {
		require.Equal(t, name, card.Member.Family)
		require.Equal(t, queryMember(t, card.Member.ID).StatementTyped, card.StatementTyped, "%s: the cards view spells the card as query member does", card.Member.ID)
		if card.StatementTyped != "" {
			spelled++
		}
	}
	require.Positive(t, spelled)
	require.Equal(t, asJSON(v), asJSON(ask(`{"cmd":"query","what":"cards","families":["`+name+`"]}`)), "by short name or path, one view")

	_, err := rpcQuery([]byte(`{"cmd":"query","what":"cards","family":"zz_no_family"}`))
	require.ErrorContains(t, err, `"zz_no_family" names no family`)
	_, err = rpcQuery([]byte(`{"cmd":"query","what":"cards","family":"` + name + `","families":["` + name + `"]}`))
	require.ErrorContains(t, err, "query cards takes `family` or `families`, not both")

	stdout := os.Stdout
	os.Stdout, _ = os.Open(os.DevNull)
	defer func() { os.Stdout = stdout }()
	resetTrace()
	cmdQuery([]string{"cards", short})
	require.Equal(t, asJSON(v), asJSON(traceEntry.Output), "the command line names the families as arguments")
}

// A bare name asks of every member under it, and the answer is a list
// however many it holds: of one name the several-member answer, each
// member's answer the one its id gets alone; among several names, each
// bare name's members in its place. A name naming nothing is unknown.
// `between` and `graph proof`, asked of one member each, refuse a bare
// name several members share. The names are picked at run time.
func TestQueryMember_BareName(t *testing.T) {
	asJSON := func(v any) string {
		data, err := json.Marshal(v)
		require.NoError(t, err)
		return string(data)
	}
	ask := func(body string) any {
		out, err := rpcQuery([]byte(body))
		require.NoError(t, err, body)
		return out
	}
	mod, err := moduleRoot()
	require.NoError(t, err)
	corpus, err := index.Load(filepath.Join(mod, "library", "proofs"))
	require.NoError(t, err)
	shared, alone := "", ""
	for _, m := range corpus.Members {
		bare := m.ID[strings.LastIndex(m.ID, ".")+1:]
		switch n := len(corpus.ResolveBare(bare)); {
		case n > 1 && shared == "":
			shared = bare
		case n == 1 && alone == "":
			alone = bare
		}
	}
	require.NotEmpty(t, shared)
	require.NotEmpty(t, alone)
	var sharedIDs []string
	for _, m := range corpus.ResolveBare(shared) {
		sharedIDs = append(sharedIDs, m.ID)
	}

	members := ask(`{"cmd":"query","what":"member","member":"` + shared + `"}`).(*QueryMembersOutput)
	require.Len(t, members.Members, len(sharedIDs))
	for i, id := range sharedIDs {
		require.Equal(t, asJSON(ask(`{"cmd":"query","what":"member","member":"`+id+`"}`)), asJSON(members.Members[i]), "%s among the bare name's members is %s alone", id, id)
	}
	lone := ask(`{"cmd":"query","what":"member","member":"` + alone + `"}`).(*QueryMembersOutput)
	require.Len(t, lone.Members, 1, "a bare name one member has answers a list all the same")
	dossiers := ask(`{"cmd":"query","what":"dossier","member":"` + shared + `"}`).(*QueryDossiersOutput)
	require.Len(t, dossiers.Dossiers, len(sharedIDs))
	deps := ask(`{"cmd":"query","what":"deps","member":"` + shared + `","depth":2}`).(*QueryNeighborhoodsOutput)
	require.Len(t, deps.Neighborhoods, len(sharedIDs))
	require.Equal(t, 2, deps.Neighborhoods[0].Depth)

	batch := ask(`{"cmd":"query","what":"member","members":["` + sharedIDs[0] + `","` + shared + `","ZzNoSuchMember"]}`).(*QueryMembersOutput)
	require.Len(t, batch.Members, 1+len(sharedIDs))
	require.Equal(t, sharedIDs[0], batch.Members[1].Member.ID, "the bare name's members stand in its place")
	require.Len(t, batch.Unknown, 1)
	require.Equal(t, "ZzNoSuchMember", batch.Unknown[0].Name)
	_, err = rpcQuery([]byte(`{"cmd":"query","what":"member","member":"ZzNoSuchMember"}`))
	require.ErrorContains(t, err, `"ZzNoSuchMember" names no corpus member`)

	_, err = rpcQuery([]byte(`{"cmd":"query","what":"between","from":"` + shared + `","to":"` + sharedIDs[0] + `"}`))
	require.ErrorContains(t, err, `"`+shared+`" is the bare name of`)
	_, err = rpcQuery([]byte(`{"cmd":"query","what":"graph","scope":"proof","member":"` + shared + `"}`))
	require.ErrorContains(t, err, `"`+shared+`" is the bare name of`)

	stdout := os.Stdout
	os.Stdout, _ = os.Open(os.DevNull)
	defer func() { os.Stdout = stdout }()
	resetTrace()
	cmdQuery([]string{"member", shared})
	require.Len(t, traceEntry.Output.(*QueryMembersOutput).Members, len(sharedIDs))
}
