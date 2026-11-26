// struct.go — the fields of a record type (dsl.StructSyntax): which
// projection reads each part off a value, under which name a text
// writes it after the dot, and the operator symbol an operation
// carries.
//
// A record (DefineData with one constructor and Fields) whose fields
// name a dot name (DataField.Field) declares them here at
// registration; the parser then reads `R.add` and `c + d` under a
// binder of the type, and the chapter spelling writes them back
// (ext/dsl/struct_fields.go).

package registry

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
)

// declareStruct records the fields of the record type typeName. Each
// projection's type takes a value of the type first; a field carrying
// a symbol yields an operation or a map (two operands or one), and two
// fields never carry one symbol at one signature.
func declareStruct(typeName string, fields []dsl.StructField) error {
	mgr := GetConstMetaManager()
	syntax := &dsl.StructSyntax{}
	claimed := map[string]string{}
	for _, fd := range fields {
		meta, ok := mgr.LoadConstMeta(core.TermName(fd.Const))
		if !ok {
			return fmt.Errorf("field %s: no constant %s", fd.Name, fd.Const)
		}
		dom, cod, ok := funTypeParts(meta.AbsType())
		if !ok || metaTypeName(dom) != typeName {
			return fmt.Errorf("field %s: %s reads no value of %s — its type is %s",
				fd.Name, fd.Const, typeName, ext.FormatType(meta.AbsType()))
		}
		if fd.Symbol != "" {
			arity := 0
			for t := cod; ; arity++ {
				_, next, ok := funTypeParts(t)
				if !ok {
					break
				}
				t = next
			}
			if arity != 1 && arity != 2 {
				return fmt.Errorf("field %s ↦ %s: a symbol is carried by an operation or a map, not a field of type %s",
					fd.Name, fd.Symbol, ext.FormatType(cod))
			}
			if !dsl.OperatorSymbolOK(fd.Symbol, arity) {
				return fmt.Errorf("field %s ↦ %s: not a symbol the DSL parses at arity %d", fd.Name, fd.Symbol, arity)
			}
			key := fmt.Sprintf("%s/%d/%s", fd.Symbol, arity, ext.FormatType(cod))
			if prev, dup := claimed[key]; dup {
				return fmt.Errorf("%s and %s both carry %s at arity %d on %s", prev, fd.Name, fd.Symbol, arity, ext.FormatType(cod))
			}
			claimed[key] = fd.Name
			fd.Arity = arity
		}
		syntax.Fields = append(syntax.Fields, fd)
	}
	return mgr.registerStructSyntax(typeName, syntax)
}

// metaTypeName is the constructor name of a composite type, "" for a
// type variable.
func metaTypeName(t core.HolType) string {
	c, ok := t.(core.CompositeType)
	if !ok {
		return ""
	}
	return string(c.Meta().Name())
}
