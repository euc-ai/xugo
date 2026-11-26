// family.go — the algebraically_closed_quantifier_elimination family
// manifest: the registry handle every member registers into, the family's
// one shared recorded CNF cache, and the chapter's table of abbreviations.
//
//	XUGO_RECORD_FAMILY_CNF=algebraically_closed_quantifier_elimination.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/

package algebraically_closed_quantifier_elimination

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed algebraically_closed_quantifier_elimination.cnf.pb
var familyCNF []byte

// family is the family handle. It reads the polynomial_division table, for
// «fieldPolynomials», and the polynomial_formula table, for the parameter
// ring, the univariate polynomials over the parameter polynomials and the
// value of a specialized polynomial, and declares the terms the chapter's
// statements share: the systems that value enters, and the models a
// decision ranges over.
var family = registry.NewFamily(
	"algebra/field/algebraically_closed_quantifier_elimination", familyCNF).WithOuterAbbrev(
	polynomial_division.ChapterAbbrev, polynomial_formula.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "nonzeroSomewhere", Text: "λp:(num → ((num → num) → int)). " +
		"λF:field_ops(A). " +
		"λρ:(num → A). " +
		"∃x:A. " +
		"    x ∈ F.carrier ∧ «value»(F, ρ, p, x) ≠ F.zero"},
	{Name: "system", Text: "λn:num. " +
		"λg:(num → num → ((num → num) → int)). " +
		"λh:(num → ((num → num) → int)). " +
		"λF:field_ops(A). " +
		"λρ:(num → A). " +
		"∃x:A. " +
		"    x ∈ F.carrier ∧ " +
		"    (∀j:num. j < n ⇒ «value»(F, ρ, g(j), x) = F.zero) ∧ " +
		"    «value»(F, ρ, h, x) ≠ F.zero"},
	{Name: "models", Text: "λF:field_ops(A). λρ:(num → A). " +
		"    algebraically_closed_field_on(F) ∧ fo_env_ok(F.carrier, U, ρ)"},
	{Name: "vanishes", Text: "λc:((num → num) → int). λF:field_ops(A). λρ:(num → A). " +
		"    «models»(F, ρ) ∧ integer_polynomial_eval(field_ring(F), ρ, c) = F.zero"},
	{Name: "survives", Text: "λc:((num → num) → int). λF:field_ops(A). λρ:(num → A). " +
		"    «models»(F, ρ) ∧ integer_polynomial_eval(field_ring(F), ρ, c) ≠ F.zero"},
})
