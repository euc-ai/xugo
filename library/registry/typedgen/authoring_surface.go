package typedgen

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/library/registry/aliasgen"
)

const authoringImportPath = "github.com/euc-ai/xugo/library/authoring"

// bareAuthoring uses the existing authoring aliases for framework names.
// Carrier letters and chapter phantoms retain their owners. A parameter
// shadowing an alias also keeps the qualified spelling in its method.
// The import decision reads the resulting unresolved names, so a file
// carrying only bare wrappers acquires no unused dot import.
func bareAuthoring(pkg, declarations string) (string, bool, error) {
	prefix := "package " + pkg + "\n\n"
	parse := func(src string) (*token.FileSet, *ast.File, error) {
		fset := token.NewFileSet()
		file, err := parser.ParseFile(fset, File, prefix+src, 0)
		if err != nil {
			return nil, nil, fmt.Errorf("typedgen: rendered declarations do not parse (generator bug): %w", err)
		}
		return fset, file, nil
	}
	fset, file, err := parse(declarations)
	if err != nil {
		return "", false, err
	}
	type span struct{ start, end int }
	var edits []span
	for _, decl := range file.Decls {
		shadowed := map[string]bool{}
		if fn, ok := decl.(*ast.FuncDecl); ok {
			for _, fields := range []*ast.FieldList{fn.Recv, fn.Type.TypeParams, fn.Type.Params, fn.Type.Results} {
				if fields != nil {
					for _, field := range fields.List {
						for _, name := range field.Names {
							shadowed[name.Name] = true
						}
					}
				}
			}
		}
		ast.Inspect(decl, func(node ast.Node) bool {
			sel, ok := node.(*ast.SelectorExpr)
			if !ok || shadowed[sel.Sel.Name] {
				return true
			}
			owner, ok := sel.X.(*ast.Ident)
			if !ok {
				return true
			}
			if !aliasgen.OnSurfaceFrom(owner.Name, sel.Sel.Name) {
				return true
			}
			switch owner.Name {
			case "ext", "dsl", "dimtypes", "proof":
				edits = append(edits, span{fset.Position(sel.Pos()).Offset - len(prefix), fset.Position(sel.Sel.Pos()).Offset - len(prefix)})
			}
			return true
		})
	}
	sort.Slice(edits, func(i, j int) bool { return edits[i].start < edits[j].start })
	var bare strings.Builder
	bare.Grow(len(declarations))
	end := 0
	for _, edit := range edits {
		bare.WriteString(declarations[end:edit.start])
		end = edit.end
	}
	bare.WriteString(declarations[end:])
	declarations = bare.String()
	_, file, err = parse(declarations)
	if err != nil {
		return "", false, err
	}
	for _, ident := range file.Unresolved {
		if aliasgen.OnSurface(ident.Name) {
			return declarations, true, nil
		}
	}
	return declarations, false, nil
}
