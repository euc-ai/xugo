package emit

// Tests for the rendering of a bare auto-match close — a KnownThm step
// whose payload resolves to a NAMED registry entry. With Cite's
// normalize-tier gate (prover/proof/fact.go citeNormalizedClose) the
// consolidated verb reproduces the close, so the member renders
// `Cite(<the entry's var>)` — `Cite("N")` for a name no landed entry
// carries — and never the lint-banned CiteKnown(ctx.Dep(…)).

import (
	"strings"
	"testing"

	"go.uber.org/goleak"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

func TestEmit_AutoMatchClose(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))
	goal := prop.MakeProp(ext.ForAll(x)(R.Apply(x)).Core())

	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{{
		Goal: pb.PropRef(goal),
		Step: &proof.StepProto_KnownThm{
			KnownThm: &proof.KnownThmProto{StrongerGoal: pb.PropRef(goal)},
		},
	}}
	goalKey := goal.AlphaKey()
	normalized, _ := proof.Normalize(goal)
	normalizedKey := normalized.AlphaKey()
	resolve := func(key core.PropKey) (ExternalLeaf, bool) {
		if key == goalKey || key == normalizedKey {
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "IN_DELETE_LIKE"}, true
		}
		return ExternalLeaf{}, false
	}

	// The consolidated verb, and the dep surfaces in DepNames.
	res := emitMember(t, env, EmitOptions{
		FuncName:            "BuildKnownClose",
		ResolveExternalLeaf: resolve,
	}, detailed(pb, steps...))
	src := res.Source
	if !strings.Contains(src, `Cite("IN_DELETE_LIKE"),`) {
		t.Errorf("auto-match close did not render Cite(\"N\")\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "CiteKnown(") {
		t.Errorf("member output still renders the internal CiteKnown spelling\n--- source: ---\n%s", src)
	}
	if len(res.DepNames) != 1 || res.DepNames[0] != "IN_DELETE_LIKE" {
		t.Errorf("DepNames = %v, want [IN_DELETE_LIKE]", res.DepNames)
	}

	// A landed entry is cited as its var — the spelling the Deps list
	// gives the same name — with its package's import.
	landed := emitMember(t, env, EmitOptions{
		FuncName:            "BuildKnownClose",
		ResolveExternalLeaf: resolve,
		FamilyDepEntry: func(name string, _ core.PropKey) (FamilyDepRef, bool) {
			return FamilyDepRef{Expr: "set_basic.InDeleteLike", ImportPath: "github.com/euc-ai/xugo/library/proofs/sets/set_basic"}, name == "IN_DELETE_LIKE"
		},
	}, detailed(pb, steps...))
	for _, want := range []string{
		"Cite(set_basic.InDeleteLike),",
		`"github.com/euc-ai/xugo/library/proofs/sets/set_basic"`,
	} {
		if !strings.Contains(landed.Source, want) {
			t.Errorf("a close on a landed entry lacks %q\n--- source: ---\n%s", want, landed.Source)
		}
	}
	if strings.Contains(unspaced(landed.Source), `Cite("`) {
		t.Errorf("a landed entry is cited by its quoted name\n--- source: ---\n%s", landed.Source)
	}
	if len(landed.DepNames) != 1 || landed.DepNames[0] != "IN_DELETE_LIKE" {
		t.Errorf("DepNames = %v, want [IN_DELETE_LIKE]", landed.DepNames)
	}
}
