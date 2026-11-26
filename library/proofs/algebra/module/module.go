// Package module is the aggregator for modules over a commutative ring
// on a set: the module structure with its finite sums, the submodules
// and quotient modules, the homomorphisms with kernels, images and
// exactness and the five lemma, the indexed products of varying modules,
// the free modules on a set, the chain complexes with their
// homology and long exact sequence, the projective resolutions, the
// tensor product and the module of homomorphisms, the derived functors
// Tor and Ext, the extensions of a module by a module and their
// classification by Ext¹, and the flat modules. Each is one family.
package module

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/flat_module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/free_complex_duality"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_extension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/resolution"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/tensor_product"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/tor_ext"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/yoneda_ext"
)
