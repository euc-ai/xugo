// definitions.go — the complex numbers: the type with its two parts,
// the operations, each spelled on the parts, and the finite product, the
// fold at multiplication.

package complex_field

import (
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ComplexData — a complex number is a pair of reals: complex(x, y) is
// the number whose real part is x and whose imaginary part is y. The
// datatype door mints the type and its one constructor and registers
// what a record comes with: every complex number is complex(x, y) for
// some reals (Induction — a case analysis, there being no recursive
// argument), a function on ℂ is determined by its values at the
// complex(x, y) (Recursion), two pairs are equal exactly when their
// entries are (ComplexInjective); and the two parts — the real part
// `complex_re`, written `re(z)`, and the imaginary part `complex_im`,
// written `im(z)` (each word declared on its constant, so the parser
// picks it wherever the argument is complex) — with the law that makes a
// complex number its parts (ComplexEq).
var ComplexData = family.DefineData(registry.DataEntry{
	Name: "Complex",
	Type: "complex",
	Constructors: []proof.DataConstructorSpec{
		{Name: "complex", Args: []string{"real", "real"}},
	},
	Fields: []registry.DataField{
		{Name: "ComplexReDef", Const: "complex_re", Overload: "re"},
		{Name: "ComplexImDef", Const: "complex_im", Overload: "im"},
	},
	Principles: registry.DataPrinciples{
		Induction:      "Induction",
		Recursion:      "Recursion",
		Injective:      "ComplexInjective",
		Extensionality: "ComplexEq",
	},
	// The recursive-type universe's rows the derivations read, and the
	// pair rows a two-part payload needs.
	Deps: []registry.EntryLike{
		datatype_universe.Recursion,
		datatype_universe.FamilyCons,
		datatype_universe.NodeInjective,
		pairs.PairEq,
		pairs.Fst,
		pairs.Snd,
	},
})

// What the door registered, under chapter names. The two projection
// equations, ComplexReDef (re(complex(a, b)) = a) and ComplexImDef
// (im(complex(a, b)) = b), are named by the generated file under the
// names their fields register.
var (
	Induction        = inductionThm{ComplexData.Induct}
	Recursion        = recursionThm{ComplexData.Recursion}
	ComplexInjective = complexInjectiveThm{ComplexData.Inj}
	// ComplexEq — two complex numbers are equal exactly when their real
	// parts are and their imaginary parts are.
	ComplexEq = complexEqThm{ComplexData.Ext}
)

// Parts — the chapter's working move as one rule set: an equation
// between complex numbers becomes the two equations between their parts
// (ComplexEq), and each part of complex(a, b) reads back as a or b. A
// member names it beside the definitions of the operations it computes —
// `Simp(Parts, Fwd(ComplexMulDef))` — and what is left is arithmetic of
// ℝ.
var Parts = ComplexData.Parts

// ComplexAddDef — addition, part by part.
var ComplexAddDef = complexAddDefThm{family.Define(registry.DefEntry{
	Name:      "ComplexAddDef",
	Key:       "prop_47c4d85e280b410a",
	Const:     "complex_add",
	Type:      "complex → complex → complex",
	Notation:  "z + w",
	Equations: []string{"∀z w:complex. complex_add(z, w) = complex(re(z) + re(w), im(z) + im(w))"},
	Deps:      []registry.EntryLike{ComplexReDef, ComplexImDef},
})}

// ComplexNegDef — negation, part by part.
var ComplexNegDef = complexNegDefThm{family.Define(registry.DefEntry{
	Name:      "ComplexNegDef",
	Key:       "prop_dacb242ceba10a44",
	Const:     "complex_neg",
	Type:      "complex → complex",
	Notation:  "-z",
	Equations: []string{"∀z:complex. complex_neg(z) = complex(-re(z), -im(z))"},
	Deps:      []registry.EntryLike{ComplexReDef, ComplexImDef},
})}

// ComplexSubDef — subtraction, as addition of the negation.
var ComplexSubDef = complexSubDefThm{family.Define(registry.DefEntry{
	Name:      "ComplexSubDef",
	Key:       "prop_fd3a8e21e7ee86f3",
	Const:     "complex_sub",
	Type:      "complex → complex → complex",
	Notation:  "z - w",
	Equations: []string{"∀z w:complex. complex_sub(z, w) = z + -w"},
	Deps:      []registry.EntryLike{ComplexAddDef, ComplexNegDef},
})}

// ComplexMulDef — multiplication: (x + iy)(u + iv) = (xu − yv) + i(xv + yu),
// the product that makes i² = −1.
var ComplexMulDef = complexMulDefThm{family.Define(registry.DefEntry{
	Name:     "ComplexMulDef",
	Key:      "prop_c34ab59c14e09861",
	Const:    "complex_mul",
	Type:     "complex → complex → complex",
	Notation: "z * w",
	Equations: []string{"∀z w:complex. " +
		"    complex_mul(z, w) = complex(re(z) * re(w) - im(z) * im(w), re(z) * im(w) + im(z) * re(w))"},
	Deps: []registry.EntryLike{ComplexReDef, ComplexImDef},
})}

// ComplexInvDef — the inverse: the conjugate's parts, each divided by
// the sum of the squares of the parts. It is total, as ℝ's is: at zero
// the sum is zero, every quotient by it is zero, and the inverse of
// zero is zero.
var ComplexInvDef = complexInvDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexInvDef",
	Key:   "prop_9f050d6f47ccc98f",
	Const: "complex_inv",
	Type:  "complex → complex",
	Equations: []string{"∀z:complex. " +
		"    complex_inv(z) = " +
		"    complex(re(z) / (re(z) * re(z) + im(z) * im(z)), (-im(z)) / (re(z) * re(z) + im(z) * im(z)))"},
	Deps: []registry.EntryLike{ComplexReDef, ComplexImDef},
})}

// ComplexDivDef — division, as multiplication by the inverse.
var ComplexDivDef = complexDivDefThm{family.Define(registry.DefEntry{
	Name:      "ComplexDivDef",
	Key:       "prop_259919db496b5d85",
	Const:     "complex_div",
	Type:      "complex → complex → complex",
	Notation:  "z / w",
	Equations: []string{"∀z w:complex. complex_div(z, w) = z * complex_inv(w)"},
	Deps:      []registry.EntryLike{ComplexMulDef, ComplexInvDef},
})}

// ComplexProductDef — Π over ℂ is the fold at complex multiplication;
// `Π_{i<n} f(i)` at a complex body is `complex_product({i:num | i < n}, λi:num. f(i))`.
var ComplexProductDef = complexProductDefThm{family.Define(registry.DefEntry{
	Name:      "ComplexProductDef",
	Key:       "prop_a8ed1d41ad029034",
	Const:     "complex_product",
	Type:      "set(A) → (A → complex) → complex",
	Overload:  "product",
	BigOp:     "Π",
	Equations: []string{"complex_product = iterated_op⟨A:A, B:complex⟩(complex_mul)"},
	Deps:      []registry.EntryLike{ComplexMulDef},
})}

// ComplexOfRealDef — a real seen in ℂ: its imaginary part is zero.
var ComplexOfRealDef = complexOfRealDefThm{family.Define(registry.DefEntry{
	Name:      "ComplexOfRealDef",
	Key:       "prop_6f2d3ad439a168d",
	Const:     "complex_of_real",
	Type:      "real → complex",
	Coercion:  true,
	Equations: []string{"∀x:real. complex_of_real(x) = complex(x, &0)"},
	// The constructor's door: the equation spells `complex`, which the
	// datatype mints, and the reference initializes the door first.
	Deps: []registry.EntryLike{Induction},
})}

// ComplexIDef — the imaginary unit.
var ComplexIDef = complexIDefThm{family.Define(registry.DefEntry{
	Name:      "ComplexIDef",
	Key:       "prop_b851ffe3811b5a20",
	Const:     "complex_i",
	Type:      "complex",
	Equations: []string{"complex_i = complex(&0, &1)"},
	Deps:      []registry.EntryLike{Induction},
})}

// ComplexConjDef — the conjugate: the imaginary part negated. Written
// `conj(z)`.
var ComplexConjDef = complexConjDefThm{family.Define(registry.DefEntry{
	Name:      "ComplexConjDef",
	Key:       "prop_94dc60edb780e669",
	Const:     "complex_conj",
	Type:      "complex → complex",
	Overload:  "conj",
	Equations: []string{"∀z:complex. complex_conj(z) = complex(re(z), -im(z))"},
	Deps:      []registry.EntryLike{ComplexReDef, ComplexImDef},
})}

// ComplexRingDef — complex ring operations and its whole-type carrier.
var ComplexRingDef = complexRingDefThm{family.Define(registry.DefEntry{
	Name: "ComplexRingDef",
	Key:  "prop_60e4a6104750fbb8", Const: "complex_ring", Type: "ring_ops(complex)",
	Equations: []string{
		"complex_ring = " +
			"mk_ring(complex_add, " +
			"    complex_of_real(&0), " +
			"    complex_neg, " +
			"    complex_mul, " +
			"    complex_of_real(&1), " +
			"    complex_sub, " +
			"    𝕌)",
	},
	Deps: []registry.EntryLike{
		ComplexAddDef,
		ComplexNegDef,
		ComplexSubDef,
		ComplexMulDef,
		ComplexOfRealDef,
	},
})}

// ComplexFieldOpsDef — complex field operations and its whole-type carrier.
var ComplexFieldOpsDef = complexFieldOpsDefThm{family.Define(registry.DefEntry{
	Name: "ComplexFieldOpsDef",
	Key:  "prop_f6ecf6112e610255", Const: "complex_field_ops", Type: "field_ops(complex)",
	Equations: []string{
		"complex_field_ops = " +
			"mk_field(complex_add, " +
			"    complex_of_real(&0), " +
			"    complex_neg, " +
			"    complex_mul, " +
			"    complex_of_real(&1), " +
			"    complex_sub, " +
			"    complex_inv, " +
			"    complex_div, " +
			"    𝕌)",
	},
	Deps: []registry.EntryLike{ComplexRingDef, ComplexInvDef, ComplexDivDef},
})}
