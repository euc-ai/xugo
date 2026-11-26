package module_test

// typed_fact_test.go — the carrier refinement of the structure laws
// (prover/proof/holds.go, member.go; library/registry/typedgen's
// structure_phantoms.go), observed at the two families that state it:
// what a law's closure binds as a typed structure fact and as members,
// what the binding refuses, and what the compiler refuses at a reading;
// and at a bundle binder, the field chapters' `∀L:field_on(A).`, whose
// fact binds at the letter of its own name (ext/on's L).

import (
	"bytes"
	"context"
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"io"
	"os"
	"os/exec"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve/testenv"
	"github.com/euc-ai/xugo/prover/proof"
)

// runLaw runs a law's or a theorem's Build in a test environment
// holding the cited laws as given theorems, and fails the test when it
// yields no certificate.
func runLaw(t *testing.T, spec registry.BuildSpec, cited ...registry.EntryLike) {
	t.Helper()
	env := testenv.MakeT(t)
	for _, c := range cited {
		e := c.Entry()
		stmt := e.Statement().Prop
		hyps := make([]core.Term, stmt.NumHyps())
		for i := range hyps {
			hyps[i] = stmt.Hyp(i)
		}
		env.LibraryThms[e.Name] = core.TestThm(stmt.Conclusion(), hyps...)
	}
	env.Scope = proof.NewProofScope("test_typed_fact")
	top, _ := spec.Fn(env)
	cert, _ := core.ForceWithBoundary(context.Background(), top, func(core.Prop) bool { return false })
	if cert.IsZero() {
		t.Fatal("the law yielded no certificate")
	}
}

func mustPanicContaining(t *testing.T, want string, f func()) {
	t.Helper()
	defer func() {
		got := recover()
		if got == nil {
			t.Fatalf("expected a panic containing %q", want)
		}
		if !strings.Contains(fmt.Sprint(got), want) {
			t.Fatalf("the panic does not contain %q:\n%s", want, got)
		}
	}()
	f()
}

// The door binds the hypothesis as the structure's typed fact and each
// guarded point as a member of its carrier, the guard their evidence;
// the cite reads the member as that evidence.
func TestTypedLaw_BindsTheFactAndItsMembers(t *testing.T) {
	runLaw(t, group.GroupOn.Law("∀x:A. x ∈ G.carrier ⇒ G.one * x = x",
		func(a *Argument, g group.GroupFact[on.G], x *Member[A, on.G]) {
			content, ok := g.AsFact().BoundContent()
			if !ok || !strings.HasPrefix(ext.PrintTerm(content), "group_on(") {
				t.Fatalf("the structure fact is bound to %v", ext.PrintTerm(content))
			}
			guard, ok := x.AsFact().BoundContent()
			if !ok || !strings.Contains(ext.PrintTerm(guard), "∈") {
				t.Fatalf("the member's evidence is bound to %v", ext.PrintTerm(guard))
			}
			a.Show(
				"the identity, from the left",
				By(group.LeftIdentityOn, g, x))
		}), group.LeftIdentityOn)
}

// A two-carrier structure binds its fact at both carriers, and a member
// of each.
func TestTypedLaw_BindsBothCarriersOfAModule(t *testing.T) {
	runLaw(t, module.ModuleOn.Law("∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ M.carrier ⇒ c • u ∈ M.carrier",
		func(a *Argument, m module.ModuleFact[on.R, on.M], c *Member[A, on.R], u *Member[B, on.M]) {
			a.Show(
				"the carrier is closed under scaling",
				By(module.SmulIn, m, c, u))
		}), module.SmulIn)
}

// A member whose phantom names another carrier than its guard's set is
// refused when the guard binds.
func TestTypedLaw_RefusesAMemberOfAnotherCarrier(t *testing.T) {
	mustPanicContaining(t, "its parameter's carrier phantom names R", func() {
		runLaw(t, module.ModuleOn.Law("∀u:B. u ∈ M.carrier ⇒ R.zero • u = M.zero",
			func(a *Argument, m module.ModuleFact[on.R, on.M], u *Member[B, on.R]) {}))
	})
}

// A structure fact whose carrier phantoms name its carriers in the
// wrong order is refused when the hypothesis binds.
func TestTypedLaw_RefusesSwappedCarriers(t *testing.T) {
	mustPanicContaining(t, "which is not the binder M the parameter's phantom names", func() {
		runLaw(t, module.ModuleOn.Law("∀u:B. u ∈ M.carrier ⇒ R.zero • u = M.zero",
			func(a *Argument, m module.ModuleFact[on.M, on.R], u *Member[B, on.M]) {}))
	})
}

// A member takes its membership as its evidence; a hypothesis beside
// it that is no membership stays in the goal, for the body to assume.
func TestTypedLaw_MembersLeaveTheOtherHypothesesInTheGoal(t *testing.T) {
	runLaw(t, group.GroupOn.Law("∀e:A. e ∈ G.carrier ∧ e * e = e ⇒ e = G.one",
		func(a *Argument, g group.GroupFact[on.G], e *Member[A, on.G]) {
			idempotent := a.Assume()
			a.Show(
				"an idempotent of a group is its identity",
				By(idempotent, group.IdempotentIsOneOn.Read(g).At(e)))
		}), group.IdempotentIsOneOn)
}

// A fact of another structure is refused at the plan.
func TestTypedLaw_RefusesAFactOfAnotherStructure(t *testing.T) {
	mustPanicContaining(t, "is a fact of comm_ring_on, "+
		"but no hypothesis of the statement is one", func() {
		runLaw(t, group.GroupOn.Law("∀x:A. x ∈ G.carrier ⇒ G.one * x = x",
			func(a *Argument, h comm_ring.CommRingFact[on.C], x *Member[A, on.G]) {}))
	})
}

// bundles is the family the bundle-binder tests state their theorems
// in: a structure's own laws bind its carrier under the definition's
// name, so a statement under a bundle binder is a theorem of its own.
var bundles = registry.NewFamily("zz_typed_fact_bundle_test", nil)

// A bundle binder binds its fact at the letter of its own name, and the
// points a guard states in it as members of that carrier: a law read at
// the fact takes them.
func TestTypedBundle_BindsAFieldAndItsMembersAtL(t *testing.T) {
	runLaw(t, bundles.Theorem("∀L:field_on(A). ∀x y:A. "+
		"    x ∈ L.carrier ∧ y ∈ L.carrier ⇒ x / y ∈ L.carrier",
		func(a *Argument, L field.FieldFact[on.L], x, y *Member[A, on.L]) {
			content, ok := L.AsFact().BoundContent()
			if !ok || !strings.HasPrefix(ext.PrintTerm(content), "field_on(") {
				t.Fatalf("the structure fact is bound to %v", ext.PrintTerm(content))
			}
			a.Show(
				"L is closed under division",
				By(field.DivIn.Read(L).At(x, y)))
		}), field.DivIn)
}

// A point the body shows in the field is paired at L by hand, and the
// reading at the fact takes it.
func TestTypedBundle_PairsAPointOfL(t *testing.T) {
	runLaw(t, bundles.Theorem("∀L:field_on(A). ∀E:set(A). ∀x:A. "+
		"    E ⊆ L.carrier ∧ x ∈ E ⇒ L.inv(x) ∈ L.carrier",
		func(a *Argument, L field.FieldFact[on.L], E *Expr[Set[A]], x *Expr[A], h Fact) {
			inE := a.Conjuncts(
				h,
				"E lies inside L",
				"x lies in E")
			inL := a.Have(
				"x lies in L",
				"x ∈ L.carrier",
				BySets(inE[0], inE[1]))
			a.Show(
				"L is closed under inverses",
				By(field.InvIn.Read(L).At(a.MemberOf[on.L](x, inL))))
		}), field.InvIn)
}

// A membership in another set is refused at L, naming both sets.
func TestTypedBundle_RefusesAPointOfAnotherSetAtL(t *testing.T) {
	mustPanicContaining(t, "x₀ lies in E₀, but the carrier L names is field_carrier(L₀)", func() {
		runLaw(t, bundles.Theorem("∀L:field_on(A). ∀E:set(A). ∀x:A. "+
			"    E ⊆ L.carrier ∧ x ∈ E ⇒ L.inv(x) ∈ L.carrier",
			func(a *Argument, L field.FieldFact[on.L], E *Expr[Set[A]], x *Expr[A], h Fact) {
				inE := a.Conjuncts(
					h,
					"E lies inside L",
					"x lies in E")
				a.MemberOf[on.L](x, inE[1])
			}))
	})
}

// The compile-time half: a reading at a typed fact takes members of its
// carrier alone, a law reads at its own structure's facts alone, and
// the untyped call sites still compile. Each snippet is type-checked
// against the packages' export data.
func TestTypedReading_CompileWalls(t *testing.T) {
	cases := []struct {
		name, expr, want string
	}{
		{
			"control: typed reads at their own carriers",
			`group.AssocOn.Read(g).At(x, x, x), group.AssocOn.Read(module.AddGroupOn.Read(m)).At(u, u, u), group.InvIn.Read(g).At(x)`,
			"",
		},
		{
			"control: an untyped instance reads as before",
			`group.AssocOn.Read(f).At(proof.MemberOf(e, f), proof.MemberOf(e, f), proof.MemberOf(e, f))`,
			"",
		},
		{"a member of another carrier", `group.AssocOn.Read(g).At(u, u, u)`, "does not match"},
		{"a group law read at a module fact", `group.AssocOn.Read(m)`, "cannot infer"},
		{"a module law read at a group fact", `module.AddGroupOn.Read(g)`, "cannot infer"},
		{"a typed member at an untyped reading", `group.AssocOn.Read(f).At(x, x, x)`, "does not match"},
		{
			"a closure law's member keeps its carrier",
			`group.AssocOn.Read(module.AddGroupOn.Read(m)).At(group.InvIn.Read(g).At(x), x, x)`,
			"does not match",
		},
		{
			"control: a reading at a bundle's fact takes its members",
			`field.InvIn.Read(L).At(l), field.DivIn.Read(L).At(l, field.InvIn.Read(L).At(l))`,
			"",
		},
		{"a member of c at a bundle's fact", `field.InvIn.Read(L).At(x)`, "does not match"},
		{
			"an untyped member at a bundle's fact",
			`field.InvIn.Read(L).At(proof.MemberOf(e, f))`,
			"does not match",
		},
	}
	lookup := exportLookup(t)
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			src := `package snippet

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/prover/proof"
)

func use(g group.GroupFact[on.C], m module.ModuleFact[on.R, on.M], L field.FieldFact[on.L], f proof.Fact, x *Member[A, on.C], u *Member[B, on.M], l *Member[A, on.L], e *Expr[A]) {
	_, _, _, _, _, _, _, _ = g, m, L, f, x, u, l, e
	_ = []any{` + tc.expr + `}
}
`
			errs := typeCheck(t, src, lookup)
			if tc.want == "" {
				if len(errs) > 0 {
					t.Fatalf("the snippet must compile:\n%s", strings.Join(errs, "\n"))
				}
				return
			}
			joined := strings.Join(errs, "\n")
			if !strings.Contains(joined, tc.want) {
				t.Fatalf("want a type error containing %q, got:\n%s", tc.want, joined)
			}
		})
	}
}

// exportLookup reads the export data of the snippets' imports, and of
// everything they import, off `go list -export`.
func exportLookup(t *testing.T) func(string) (io.ReadCloser, error) {
	t.Helper()
	cmd := exec.Command("go", "list", "-export", "-deps", "-f", "{{.ImportPath}}\t{{.Export}}",
		"github.com/euc-ai/xugo/ext/on",
		"github.com/euc-ai/xugo/library/authoring",
		"github.com/euc-ai/xugo/library/proofs/algebra/group/group",
		"github.com/euc-ai/xugo/library/proofs/algebra/module/module",
		"github.com/euc-ai/xugo/library/proofs/algebra/field/field",
		"github.com/euc-ai/xugo/prover/proof")
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	out, err := cmd.Output()
	if err != nil {
		t.Fatalf("go list -export: %v\n%s", err, stderr.String())
	}
	files := map[string]string{}
	for _, line := range strings.Split(strings.TrimSpace(string(out)), "\n") {
		if path, file, ok := strings.Cut(line, "\t"); ok && file != "" {
			files[path] = file
		}
	}
	return func(path string) (io.ReadCloser, error) {
		file, ok := files[path]
		if !ok {
			return nil, fmt.Errorf("no export data for %s", path)
		}
		return os.Open(file)
	}
}

// typeCheck type-checks one file and returns its type errors.
func typeCheck(t *testing.T, src string, lookup func(string) (io.ReadCloser, error)) []string {
	t.Helper()
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "snippet.go", src, 0)
	if err != nil {
		t.Fatalf("the snippet must parse: %v", err)
	}
	var errs []string
	conf := types.Config{
		Importer: importer.ForCompiler(fset, "gc", lookup),
		Error:    func(err error) { errs = append(errs, err.Error()) },
	}
	_, _ = conf.Check("snippet", fset, []*ast.File{file}, nil)
	return errs
}
