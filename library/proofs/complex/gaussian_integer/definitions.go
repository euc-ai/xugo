package gaussian_integer

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// GaussianIntegersDef — ℤ[i]: the complex numbers whose real and
// imaginary parts are integers.
var GaussianIntegersDef = gaussianIntegersDefThm{family.Define(registry.DefEntry{
	Name:  "GaussianIntegersDef",
	Key:   "prop_851c4e1836d5b3d4",
	Const: "gaussian_integers",
	Type:  "set(complex)",
	Equations: []string{
		"gaussian_integers = {z:complex | ∃a b:int. z = complex(real_of_int(a), real_of_int(b))}",
	},
})}

// GaussianRingDef — ℤ[i] as a ring: ℂ's operations on the Gaussian
// integers.
var GaussianRingDef = gaussianRingDefThm{family.Define(registry.DefEntry{
	Name:      "GaussianRingDef",
	Key:       "prop_8afcdc715ae2fca8",
	Const:     "gaussian_ring",
	Type:      "ring_ops(complex)",
	Equations: []string{"gaussian_ring = restrict_ring(complex_ring, gaussian_integers)"},
	Deps:      []registry.EntryLike{GaussianIntegersDef},
})}

// GaussianNormDef — the norm a² + b² of a + bi, read as a natural number.
var GaussianNormDef = gaussianNormDefThm{family.Define(registry.DefEntry{
	Name:  "GaussianNormDef",
	Key:   "prop_a73511052b4fd9bb",
	Const: "gaussian_norm",
	Type:  "complex → num",
	Equations: []string{
		"∀z:complex. gaussian_norm(z) = num_of_int(int_of_real(re(z) * re(z) + im(z) * im(z)))",
	},
})}
