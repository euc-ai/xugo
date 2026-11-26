package typedgen

// vec_fun_slots_test.go — the dimension refinement of a statement's MAP
// binders (dimension_slots.go), read off a fixture family whose
// constants declare a vector's dimension and a map's two: what the
// generated At takes, which binders leave its parameter list, and what
// the compiler refuses at a call of it.

import (
	"bytes"
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
	"sync"
	"testing"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

const vecFunFixturePackage = "zz_typedgen_vec_funs"

// vecFunFixture renders the fixture family once: a membership at one
// dimension, a predicate of a map between two, a predicate of two maps
// of one space into itself, two predicates that read no dimension —
// what a law's hypothesis is — and the statements over them.
var vecFunFixture = sync.OnceValues(func() (string, error) {
	fam := registry.NewFamily(vecFunFixturePackage, nil)
	const vector, linear = "(num → A)", "((num → A) → num → A)"
	fam.Define(registry.DefEntry{
		Name:      "PointDef",
		Const:     "zz_typedgen_point",
		Type:      "num → " + vector + " → bool",
		Dim:       "n",
		Equations: []string{"∀n:num. ∀u:" + vector + ". zz_typedgen_point⟨n⟩(u) ⇔ n = n ∧ u = u"},
	})
	fam.Define(registry.DefEntry{
		Name:      "CarriesDef",
		Const:     "zz_typedgen_carries",
		Type:      "num → num → " + linear + " → bool",
		SourceDim: "n",
		TargetDim: "m",
		Equations: []string{"∀n m:num. ∀f:" + linear + ". zz_typedgen_carries⟨n, m⟩(f) ⇔ n = m ∧ f = f"},
	})
	fam.Define(registry.DefEntry{
		Name:      "UndoesDef",
		Const:     "zz_typedgen_undoes",
		Type:      "num → " + linear + " → " + linear + " → bool",
		SourceDim: "n",
		TargetDim: "n",
		Equations: []string{"∀n:num. ∀L K:" + linear + ". zz_typedgen_undoes⟨n⟩(L, K) ⇔ n = n ∧ L = K"},
	})
	fam.Define(registry.DefEntry{
		Name:      "HeldDef",
		Const:     "zz_typedgen_held",
		Type:      vector + " → bool",
		Equations: []string{"∀u:" + vector + ". zz_typedgen_held(u) ⇔ u = u"},
	})
	fam.Define(registry.DefEntry{
		Name:      "KeptDef",
		Const:     "zz_typedgen_kept",
		Type:      linear + " → bool",
		Equations: []string{"∀f:" + linear + ". zz_typedgen_kept(f) ⇔ f = f"},
	})
	for _, e := range []struct{ name, stmt string }{
		// Laws whose component is the vector, or the map, that anchors a
		// dimension the reading still binds.
		{"HeldAt", "∀u:" + vector + ". zz_typedgen_held(u) ⇒ ∀n:num. zz_typedgen_point⟨n⟩(u) ⇒ zz_typedgen_point⟨n⟩(u)"},
		{"KeptBetween", "∀f:" + linear + ". zz_typedgen_kept(f) ⇒ ∀n m:num. zz_typedgen_carries⟨n, m⟩(f) ⇒ zz_typedgen_carries⟨n, m⟩(f)"},
		{"KeptImage", "∀f:" + linear + ". zz_typedgen_kept(f) ⇒ ∀n m:num. ∀u:" + vector + ". zz_typedgen_carries⟨n, m⟩(f) ∧ zz_typedgen_point⟨n⟩(u) ⇒ zz_typedgen_point⟨m⟩(f(u))"},
		// A map between two dimensions, beside a vector at its source.
		{"Image", "∀n m:num. ∀f:" + linear + ". ∀u:" + vector + ". zz_typedgen_carries⟨n, m⟩(f) ∧ zz_typedgen_point⟨n⟩(u) ⇒ zz_typedgen_point⟨m⟩(f(u))"},
		// Two maps sharing the middle dimension.
		{"Chain", "∀n m k:num. ∀f g:" + linear + ". zz_typedgen_carries⟨n, m⟩(f) ∧ zz_typedgen_carries⟨m, k⟩(g) ⇒ zz_typedgen_carries⟨n, k⟩(λx:" + vector + ". g(f(x)))"},
		// Maps of one space into itself: one binder is both dimensions.
		{"Swap", "∀n:num. ∀L K:" + linear + ". zz_typedgen_undoes⟨n⟩(L, K) ⇒ zz_typedgen_undoes⟨n⟩(K, L)"},
		// Read at two targets, the map keeps its plain slot, and so do
		// the dimensions only it would have written.
		{"TwoTargets", "∀n m k:num. ∀f:" + linear + ". zz_typedgen_carries⟨n, m⟩(f) ∧ zz_typedgen_carries⟨n, k⟩(f) ⇒ m = k"},
		// Read on a dimension that is no binder, likewise.
		{"NoBinder", "∀n m:num. ∀f:" + linear + ". zz_typedgen_carries⟨suc(n), m⟩(f) ⇒ zz_typedgen_carries⟨suc(n), m⟩(f)"},
	} {
		fam.Add(registry.ProofEntry{
			Name:  e.name,
			Build: registry.BuildSpec{Headline: e.stmt, Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
		})
	}
	// The fixture has no proof file: its package directory is empty.
	dir, err := os.MkdirTemp("", vecFunFixturePackage)
	if err != nil {
		return "", err
	}
	defer os.RemoveAll(dir)
	rendered, err := Render(fam, vecFunFixturePackage, dir, "a fixture chapter")
	if err != nil {
		return "", err
	}
	return string(rendered.Source), nil
})

// A map binder every map-declared constant reads at ONE source binder
// and ONE target binder is a VecFun at both phantoms, and the two binders
// are written off it; a binder read at two, or at a term that is no
// binder, keeps its plain slot and elides nothing.
func TestRender_VecFunSlots(t *testing.T) {
	src, err := vecFunFixture()
	if err != nil {
		t.Fatalf("Render: %v", err)
	}
	for _, want := range []string{
		// The definition's own cite: both dimensions off the map.
		"func (th carriesDefThm) At[Type0 TypePhantom, DimN, DimM DimPhantom](f *VecFun[Type0, DimN, DimM]) Fact {\n" +
			"\treturn th.Inst[Type0]().At(proof.SameDimension(f.Source()), proof.SameDimension(f.Target()), f)\n}\n",
		// A map and a vector at its source: one dimension, two anchors.
		"func (th imageThm) At[Type0 TypePhantom, DimN, DimM DimPhantom](f *VecFun[Type0, DimN, DimM], u *Inhabited[Type0, DimN]) proof.PremiseGroup {\n" +
			"\treturn GroupPremises(u, th.Inst[Type0]().At(proof.SameDimension(f.Source(), u.Dim()), proof.SameDimension(f.Target()), f, u))\n}\n",
		// Two maps through a middle dimension: the first's target is
		// the second's source.
		"func (th chainThm) At[Type0 TypePhantom, DimN, DimM, DimK DimPhantom](f *VecFun[Type0, DimN, DimM], g *VecFun[Type0, DimM, DimK]) Fact {\n" +
			"\treturn th.Inst[Type0]().At(proof.SameDimension(f.Source()), proof.SameDimension(f.Target(), g.Source()), proof.SameDimension(g.Target()), f, g)\n}\n",
		// A space into itself: one phantom twice, one binder, four anchors.
		"func (th swapThm) At[Type0 TypePhantom, DimN DimPhantom](L, K *VecFun[Type0, DimN, DimN]) Fact {\n" +
			"\treturn th.Inst[Type0]().At(proof.SameDimension(L.Source(), L.Target(), K.Source(), K.Target()), L, K)\n}\n",
		// Nothing is elided the statement does not determine.
		"func (th twoTargetsThm) At[Type0 TypePhantom](n, m, k Typed[Nat], f Typed[Fun2[Fun[Nat, Type0], Nat, Type0]]) Fact {\n" +
			"\treturn th.Inst[Type0]().At(n, m, k, f)\n}\n",
		"func (th noBinderThm) At[Type0 TypePhantom](n, m Typed[Nat], f Typed[Fun2[Fun[Nat, Type0], Nat, Type0]]) Fact {\n" +
			"\treturn th.Inst[Type0]().At(n, m, f)\n}\n",
	} {
		if !strings.Contains(src, want) {
			t.Errorf("the rendered file lacks\n%s\n--- source: ---\n%s", want, src)
		}
	}
}

// The compile-time half: the rendered cites take maps and vectors whose
// phantoms agree and no others, a map at SomeDim cites like one at
// letters, and a VecFun still passes to a plain typed slot. Each snippet
// is type-checked with the rendered file, against the packages' export
// data.
func TestRender_VecFunSlotCompileWalls(t *testing.T) {
	src, err := vecFunFixture()
	if err != nil {
		t.Fatalf("Render: %v", err)
	}
	cases := []struct {
		name, expr, want string
	}{
		{"control: maps and vectors at agreeing phantoms", `image.At(f, u), chain.At(f, g), swap.At(e, e), carries.At(g)`, ""},
		{"control: SomeDim cites as a letter does", `image.At(s, t), chain.At(s, s), swap.At(s, s)`, ""},
		{"control: the image of a vector is a vector at the target", `image.At(g, proof.Inhabit(f.Apply(u.Vec), fact)), g.Apply(f.Apply(u.Vec))`, ""},
		{"control: a VecFun passes to a plain typed slot", `twoTargets.At(n, n, n, f), noBinder.At(n, n, e)`, ""},
		{"a vector at the map's target, where its source is read", `image.At(f, w)`, "does not match"},
		{"two maps composed the wrong way round", `chain.At(g, f)`, "does not match"},
		{"a map between two dimensions, where a space maps into itself", `swap.At(f, f)`, "does not match"},
		{"a map at letters beside one at SomeDim", `swap.At(e, s)`, "does not match"},
		{"a plain arrow at a VecFun slot", `carries.At(arrow)`, "does not match"},
		{"a vector of another dimension under a map", `f.Apply(w.Vec)`, "cannot use"},
		{"a matrix at a VecFun slot", `carries.At(matrix)`, "does not match"},
	}
	lookup := vecFunExportLookup(t)
	if errs := typeCheckWith(t, src, "package "+vecFunFixturePackage+"\n", lookup); len(errs) > 0 {
		t.Fatalf("the rendered file must compile on its own:\n%s", strings.Join(errs, "\n"))
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			snippet := `package ` + vecFunFixturePackage + `

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/prover/proof"
)

var _ = proof.SameDimension

func use(image imageThm, chain chainThm, swap swapThm, carries carriesDefThm, twoTargets twoTargetsThm, noBinder noBinderThm,
	f *VecFun[A, DimN, DimM], g *VecFun[A, DimM, DimK], e *VecFun[A, DimN, DimN], s *VecFun[A, SomeDim, SomeDim],
	u *Inhabited[A, DimN], w *Inhabited[A, DimM], t *Inhabited[A, SomeDim],
	arrow *Arrow[Fun[Nat, A], Fun[Nat, A]], matrix *Mat[A, DimN, DimM], n *Expr[Nat], fact Fact) {
	_ = []any{` + tc.expr + `}
}
`
			errs := typeCheckWith(t, src, snippet, lookup)
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
			t.Logf("refused: %s", joined)
		})
	}
}

// vecFunExportLookup reads the export data of the packages the rendered
// file and the snippets import, and of everything those import, off
// `go list -export`.
func vecFunExportLookup(t *testing.T) func(string) (io.ReadCloser, error) {
	t.Helper()
	cmd := exec.Command("go", "list", "-export", "-deps", "-f", "{{.ImportPath}}\t{{.Export}}",
		"github.com/euc-ai/xugo/library/authoring",
		"github.com/euc-ai/xugo/library/registry",
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

// typeCheckWith type-checks the rendered file and one more file of its
// package together and returns the type errors.
func typeCheckWith(t *testing.T, rendered, snippet string, lookup func(string) (io.ReadCloser, error)) []string {
	t.Helper()
	fset := token.NewFileSet()
	var files []*ast.File
	for name, src := range map[string]string{File: rendered, "snippet.go": snippet} {
		file, err := parser.ParseFile(fset, name, src, 0)
		if err != nil {
			t.Fatalf("%s must parse: %v", name, err)
		}
		files = append(files, file)
	}
	var errs []string
	conf := types.Config{
		Importer: importer.ForCompiler(fset, "gc", lookup),
		Error:    func(err error) { errs = append(errs, err.Error()) },
	}
	_, _ = conf.Check(vecFunFixturePackage, fset, files, nil)
	return errs
}

// A reading drops the law's components, and a vector or a map among
// them takes its dimension's anchor with it. The reading still binds
// that dimension, so with no carrier of its own to write it off, the
// dimension is a parameter again; one a remaining slot anchors stays
// written off that slot. The law's own At, which holds the component,
// elides as ever.
func TestRender_ReadingKeepsADimensionOnlyAComponentAnchors(t *testing.T) {
	src, err := vecFunFixture()
	if err != nil {
		t.Fatalf("Render: %v", err)
	}
	for _, want := range []string{
		"func (th heldAtThm) At[Type0 TypePhantom, DimN DimPhantom](u *Vec[Type0, DimN]) Fact {\n" +
			"\treturn th.Inst[Type0]().At(u, proof.SameDimension(u.Dim()))\n}\n",
		"func (th heldAtReading) At(n Typed[Nat]) Fact {\n" +
			"\treturn th.fact.At(n)\n}\n",
		"func (th keptBetweenThm) At[Type0 TypePhantom, DimN, DimM DimPhantom](f *VecFun[Type0, DimN, DimM]) Fact {\n" +
			"\treturn th.Inst[Type0]().At(f, proof.SameDimension(f.Source()), proof.SameDimension(f.Target()))\n}\n",
		"func (th keptBetweenReading) At(n, m Typed[Nat]) Fact {\n" +
			"\treturn th.fact.At(n, m)\n}\n",
		// n is anchored by the vector the reading keeps, m by the map it
		// dropped alone.
		"func (th keptImageReading) At[Type0 TypePhantom, DimN DimPhantom](m Typed[Nat], u *Inhabited[Type0, DimN]) proof.PremiseGroup {\n" +
			"\treturn WithMembers(th.fact.At(proof.SameDimension(u.Dim()), m, u), u)\n}\n",
	} {
		if !strings.Contains(src, want) {
			t.Errorf("the rendered file lacks\n%s\n--- source: ---\n%s", want, src)
		}
	}
	if strings.Contains(src, "proof.SameDimension()") {
		t.Errorf("a cite writes a dimension off no carrier\n--- source: ---\n%s", src)
	}
}
