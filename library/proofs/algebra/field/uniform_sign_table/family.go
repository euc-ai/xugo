package uniform_sign_table

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/field/parametric_sign_table"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed uniform_sign_table.cnf.pb
var familyCNF []byte

// family is the family handle. It reads the parametric_sign_table table,
// for «model», and through it the polynomial_formula table, for
// «parameterRing», «overParameters», «specialized» and «value»;
// parametric_sign_table's handle says what each names.
//
// The ring operations on parameter polynomials are spelled two ways here:
// as integer_polynomial_ring's projections (integer_polynomial_ring.add,
// .zero, .mul, .one) and as the polynomial algebra's operations
// (fun_add(int_add), fun_zero(int_of_num(0)), polynomial_algebra_mul(int_ring),
// polynomial_algebra_one(int_ring)). A proof whose leaves meet both reads the
// equation between them, polynomial_formula.IntegerPolynomialRingOperations,
// once as its `operations`, and lists it wherever a leaf mixes the spellings.
var family = registry.NewFamily("algebra/field/uniform_sign_table", familyCNF).WithOuterAbbrev(
	parametric_sign_table.ChapterAbbrev)
