package parametric_sign_table

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed parametric_sign_table.cnf.pb
var familyCNF []byte

// family is the family handle. It reads the polynomial_formula table, for
// «parameterRing»(U), the parameter ring, for «overParameters»(g), that g
// is a polynomial over the parameter polynomials, for «specialized», the
// specialization of a coefficient sequence at an environment ρ of a ring,
// here F's ring, «specialized»(field_ring(F), ρ, g), and «value», the value
// at a point x of F of a specialized polynomial. Its own table names the
// model a uniform table is read in, «model»(U, C, F, lt, ρ): a real closed
// field F ordered by lt and an environment ρ of the parameters U in its
// carrier, meeting the condition C; and the sign rules of the step, each a
// function of the table it reads:
//   - «vanishing»(m, k, t, l): l is one of the k cuts of a table with rows
//     t, and one of its first m members, with a nonzero sign on cell 0,
//     vanishes there;
//   - «coarse»(t, e): the rows of t on the cells of the cuts e lists;
//   - «below»(l, r), «above»(l, r) and «split»(l, r): the signs of a
//     polynomial below, above and at the one point that splits an interval
//     whose ends give it the signs l and r;
//   - «leftSign»(P, L, a) and «rightSign»(q, P, R, a): the signs at the two
//     ends of the open cell a of q cuts, P(a) at the cut a and L and R far
//     out;
//   - «refined»(q, t, P, L, R): the rows t of q cuts refined by one split
//     point in each open cell, for the polynomial p of signs P at the cuts
//     and L and R far out; p is the new member 0 and the others shift by one.
var family = registry.NewFamily("algebra/field/parametric_sign_table", familyCNF).WithOuterAbbrev(
	polynomial_formula.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "model", Text: "λU:set(num). " +
		"λC:(field_ops(A) → (A → A → bool) → (num → A) → bool). " +
		"λF:field_ops(A). " +
		"λlt:(A → A → bool). " +
		"λρ:(num → A). " +
		"    real_closed_field(F, lt) ∧ fo_env_ok(F.carrier, U, ρ) ∧ C(F, lt, ρ)"},
	{Name: "vanishing", Text: "λm:num. λk:num. λt:(num → num → int). λl:num. " +
		"    l < k ∧ ∃i:num. i < m ∧ ¬(t(0, i) = &0) ∧ t(2 * l + 1, i) = &0"},
	{Name: "coarse", Text: "λt:(num → num → int). λe:(num → num). λj:num. λi:num. " +
		"    COND(nat_mod(j, 2) = 1, " +
		"        t(2 * e(nat_div(j, 2)) + 1, i), " +
		"        t(COND(j = 0, 0, 2 * e(nat_div(j, 2) - 1) + 2), i))"},
	{Name: "below", Text: "λl:int. λr:int. COND(l = &0, r, l)"},
	{Name: "above", Text: "λl:int. λr:int. COND(r = &0, l, r)"},
	{Name: "split", Text: "λl:int. λr:int. COND(l = -r ∧ ¬(l = &0), int_of_num(0), «below»(l, r))"},
	{Name: "leftSign", Text: "λP:(num → int). λL:int. λa:num. COND(a = 0, L, P(a - 1))"},
	{Name: "rightSign", Text: "λq:num. λP:(num → int). λR:int. λa:num. COND(a = q, R, P(a))"},
	{Name: "refined", Text: "λq:num. " +
		"λt:(num → num → int). " +
		"λP:(num → int). " +
		"λL:int. " +
		"λR:int. " +
		"λj:num. " +
		"λi:num. " +
		"    COND(i = 0, " +
		"        COND(nat_mod(j, 4) = 0, " +
		"            «below»(«leftSign»(P, L, nat_div(j, 4)), «rightSign»(q, P, R, nat_div(j, 4))), " +
		"            COND(nat_mod(j, 4) = 1, " +
		"                «split»(«leftSign»(P, L, nat_div(j, 4)), «rightSign»(q, P, R, nat_div(j, 4))), " +
		"                COND(nat_mod(j, 4) = 2, " +
		"                    «above»(«leftSign»(P, L, nat_div(j, 4)), " +
		"                        «rightSign»(q, P, R, nat_div(j, 4))), " +
		"                    P(nat_div(j, 4))))), " +
		"        t(2 * nat_div(j, 4) + nat_div(nat_mod(j, 4), 3), i - 1))"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
