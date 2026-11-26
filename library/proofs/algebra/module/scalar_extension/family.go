package scalar_extension

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed scalar_extension.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("algebra/module/scalar_extension", familyCNF).WithAbbrev(Abbrev{
	{Name: "kRing", Text: "restrict_ring(field_ring(L), k)"},
	{Name: "extendedV", Text: "scalar_extension(«kRing», field_ring(L), V)"},
	{Name: "extendedW", Text: "scalar_extension(«kRing», field_ring(L), W)"},
	{Name: "mapF", Text: "scalar_extension_map(«kRing», field_ring(L), V, W, f)"},
	{Name: "kernelModule", Text: "restrict_module(V, group_kernel(W.zero, V.carrier, f))"},
	{Name: "extendedKernel", Text: "scalar_extension(«kRing», field_ring(L), «kernelModule»)"},
	{Name: "kernelOfMapF", Text: "group_kernel(«extendedW».zero, «extendedV».carrier, «mapF»)"},
	{Name: "targetKernel", Text: "restrict_module(«extendedV», «kernelOfMapF»)"},
	{Name: "cokernel", Text: "quotient_module(W, image(f, V.carrier))"},
	{Name: "extendedCokernel", Text: "scalar_extension(«kRing», field_ring(L), «cokernel»)"},
	{Name: "targetCokernel", Text: "quotient_module(«extendedW», image(«mapF», «extendedV».carrier))"},
	{Name: "tensorS", Text: "tensor_module(restrict_ring(R, S), regular_module(R), V)"},
	{Name: "pureS", Text: "tensor(restrict_ring(R, S), regular_module(R), V)"},
	{Name: "unitS", Text: "λv:B. «pureS»(R.one, v)"},
	{Name: "actionS", Text: "tensor_scalar_action(restrict_ring(R, S), R, V)"},
	{Name: "tensorSW", Text: "tensor_module(restrict_ring(R, S), regular_module(R), W)"},
	{Name: "extension", Text: "scalar_extension(restrict_ring(R, S), R, V)"},
	{Name: "extensionW", Text: "scalar_extension(restrict_ring(R, S), R, W)"},
	{Name: "mapExtF", Text: "scalar_extension_map(restrict_ring(R, S), R, V, W, f)"},
	{Name: "mapExtG", Text: "scalar_extension_map(restrict_ring(R, S), R, V, W, g)"},
	{Name: "pureSW", Text: "tensor(restrict_ring(R, S), regular_module(R), W)"},
})
