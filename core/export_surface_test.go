package core_test

// TestExportSurface reads the package's declarations and holds the shape
// that keeps a kernel object out of an importer's reach: no exported
// variable, no pointer to a kernel type and no unexported type in
// anything an importer can name, every kernel object a one-word handle
// over a node, no handle of one underlying type with another declared
// type, every interface the kernel reads its inputs through closed
// by an unexported method, and no exported method on Thm beyond Prop's,
// since a force asked of the value is answered by whatever type embeds
// it. It checks declarations, so it is a guard against a slip in this
// package, not a defense against one.

import (
	"go/ast"
	"go/build"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"io/fs"
	"os/exec"
	"sort"
	"strings"
	"testing"
)

const corePackagePath = "github.com/euc-ai/xugo/core"

func loadCore(t *testing.T) *types.Package {
	t.Helper()
	fset := token.NewFileSet()
	parsed, err := parser.ParseDir(fset, ".", func(info fs.FileInfo) bool {
		return !strings.HasSuffix(info.Name(), "_test.go")
	}, 0)
	if err != nil {
		t.Fatalf("parsing the package: %v", err)
	}
	var files []*ast.File
	for _, pkg := range parsed {
		for _, f := range pkg.Files {
			files = append(files, f)
		}
	}
	// The source importer finds the standard library and the module's
	// packages through build.Default's GOROOT, which a test binary built
	// under -trimpath leaves empty; the go command running the test knows
	// it.
	if build.Default.GOROOT == "" {
		out, err := exec.Command("go", "env", "GOROOT").Output()
		if err != nil {
			t.Fatalf("finding GOROOT: %v", err)
		}
		build.Default.GOROOT = strings.TrimSpace(string(out))
	}
	conf := types.Config{Importer: importer.ForCompiler(fset, "source", nil)}
	pkg, err := conf.Check(corePackagePath, fset, files, nil)
	if err != nil {
		t.Fatalf("type-checking the package: %v", err)
	}
	return pkg
}

// fromCore is the named type t when core declares it, aliases resolved.
func fromCore(t types.Type) (*types.Named, bool) {
	n, ok := types.Unalias(t).(*types.Named)
	if !ok || n.Obj().Pkg() == nil || n.Obj().Pkg().Path() != corePackagePath {
		return nil, false
	}
	return n, true
}

// unreachable is what in t an importer must not be able to name: a
// pointer to a type core declares, or a type core does not export.
func unreachable(t types.Type, seen map[types.Type]bool) []string {
	if t == nil || seen[t] {
		return nil
	}
	seen[t] = true
	var out []string
	walk := func(u types.Type) { out = append(out, unreachable(u, seen)...) }
	switch t := types.Unalias(t).(type) {
	case *types.Named:
		if n, ok := fromCore(t); ok && !n.Obj().Exported() {
			out = append(out, "the unexported type "+n.Obj().Name())
		}
		for i := range t.TypeArgs().Len() {
			walk(t.TypeArgs().At(i))
		}
	case *types.Pointer:
		if n, ok := fromCore(t.Elem()); ok {
			out = append(out, "a pointer to "+n.Obj().Name())
			return out
		}
		walk(t.Elem())
	case *types.Slice:
		walk(t.Elem())
	case *types.Array:
		walk(t.Elem())
	case *types.Map:
		walk(t.Key())
		walk(t.Elem())
	case *types.Chan:
		walk(t.Elem())
	case *types.Signature:
		walk(t.Params())
		walk(t.Results())
	case *types.Tuple:
		for i := range t.Len() {
			walk(t.At(i).Type())
		}
	case *types.Struct:
		for i := range t.NumFields() {
			walk(t.Field(i).Type())
		}
	case *types.Interface:
		for i := range t.NumMethods() {
			if m := t.Method(i); m.Exported() {
				walk(m.Type())
			}
		}
	}
	return out
}

// isHandle reports whether s is one word over a node: a single embedded
// field, unexported, of pointer type.
func isHandle(s *types.Struct) bool {
	if s.NumFields() != 1 || !s.Field(0).Embedded() || s.Field(0).Exported() {
		return false
	}
	_, isPointer := s.Field(0).Type().(*types.Pointer)
	return isPointer
}

func TestExportSurface(t *testing.T) {
	pkg := loadCore(t)
	scope := pkg.Scope()
	names := scope.Names()
	sort.Strings(names)

	var findings []string
	report := func(where string, what []string) {
		for _, w := range what {
			findings = append(findings, where+" names "+w)
		}
	}
	signature := func(where string, f *types.Func) {
		sig := f.Type().(*types.Signature)
		report(where, unreachable(sig.Params(), map[types.Type]bool{}))
		report(where, unreachable(sig.Results(), map[types.Type]bool{}))
	}

	sealed := map[string]bool{"Term": false, "HolType": false, "Prop": false, "Thm": false}
	var readThrough []*types.Interface
	handles := 0

	for _, name := range names {
		switch obj := scope.Lookup(name).(type) {
		case *types.Var:
			if obj.Exported() {
				findings = append(findings, "the exported variable "+name+": any importer can assign it")
			}
		case *types.Func:
			if obj.Exported() {
				signature("func "+name, obj)
			}
		case *types.TypeName:
			if obj.IsAlias() {
				if obj.Exported() {
					report("type "+name, unreachable(obj.Type(), map[types.Type]bool{}))
				}
				continue
			}
			named := obj.Type().(*types.Named)
			// Every exported method, of an exported type or not: a method of
			// an unexported type is called through whatever embeds it.
			for _, recv := range []types.Type{named, types.NewPointer(named)} {
				set := types.NewMethodSet(recv)
				for i := range set.Len() {
					if f, ok := set.At(i).Obj().(*types.Func); ok && f.Exported() {
						signature("method "+name+"."+f.Name(), f)
					}
				}
			}
			switch under := named.Underlying().(type) {
			case *types.Interface:
				if _, tracked := sealed[name]; tracked {
					for i := range under.NumMethods() {
						if !under.Method(i).Exported() {
							sealed[name] = true
						}
					}
					readThrough = append(readThrough, under)
				}
				if name == "Thm" {
					for i := range under.NumExplicitMethods() {
						if m := under.ExplicitMethod(i); m.Exported() {
							findings = append(findings, "interface Thm declares the exported method "+m.Name()+
								": a type that embeds a Thm answers it in the kernel's place")
						}
					}
				}
			case *types.Struct:
				if !obj.Exported() {
					continue
				}
				if isHandle(under) {
					handles++
					continue
				}
				for i := range under.NumFields() {
					f := under.Field(i)
					if !f.Exported() {
						findings = append(findings, "type "+name+" is neither a handle over one node nor a struct of exported fields: field "+f.Name())
					}
					report("field "+name+"."+f.Name(), unreachable(f.Type(), map[types.Type]bool{}))
				}
			default:
				if obj.Exported() {
					report("type "+name, unreachable(under, map[types.Type]bool{}))
				}
			}
		}
	}

	for name, has := range sealed {
		if !has {
			findings = append(findings, "interface "+name+" has no unexported method: a type outside the package can implement it outright")
		}
	}
	// A node is reached only through its handle: a pointer to one that
	// satisfied an interface could be handed out inside it.
	for _, name := range names {
		obj, ok := scope.Lookup(name).(*types.TypeName)
		if !ok || obj.Exported() || obj.IsAlias() {
			continue
		}
		under, isStruct := obj.Type().Underlying().(*types.Struct)
		if !isStruct || isHandle(under) {
			continue // a pointer to a handle points at a holder's copy of it
		}
		for _, iface := range readThrough {
			if types.Implements(types.NewPointer(obj.Type()), iface) {
				findings = append(findings, "a pointer to "+name+" satisfies an interface the kernel hands out")
			}
		}
	}
	// Go converts a struct type to any other of the same underlying type,
	// and a pointer to the one to a pointer to the other; reflect makes
	// the conversion for a type its caller cannot name. A handle is the
	// one type over its node, exported or not: a second would be made
	// from the first.
	for _, to := range names {
		target, ok := scope.Lookup(to).(*types.TypeName)
		if !ok || target.IsAlias() {
			continue
		}
		if under, isStruct := target.Type().Underlying().(*types.Struct); !isStruct || !isHandle(under) {
			continue
		}
		for _, from := range names {
			source, ok := scope.Lookup(from).(*types.TypeName)
			if !ok || source.IsAlias() || from == to {
				continue
			}
			if types.ConvertibleTo(source.Type(), target.Type()) ||
				types.ConvertibleTo(types.NewPointer(source.Type()), types.NewPointer(target.Type())) {
				findings = append(findings, "type "+from+" converts to the handle "+to+": reflect makes one from the other")
			}
		}
	}
	if handles != 11 {
		findings = append(findings, "the package declares 11 handle types — four terms, the constant's meta, three types, the certificate, the promise and the forcer — and the reading found a different number")
	}

	sort.Strings(findings)
	for i, f := range findings {
		if i == 0 || f != findings[i-1] {
			t.Error(f)
		}
	}
}
