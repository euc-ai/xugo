// formal_exp.go — the formal exponential over ℝ: the ring of reals has
// characteristic zero, so a real series with a counting sequence is the formal
// exponential of its counts over their indices.

package real_formal_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/formal_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

// RealCharacteristicZero — ℝ has characteristic zero: n ones sum to the numeral
// n, nonzero for n positive.
var RealCharacteristicZero = realCharacteristicZeroThm{family.Add(registry.ProofEntry{
	Name: "RealCharacteristicZero",
	Key:  "prop_9f70b1e440ce6ef5",
	Build: family.Theorem("characteristic_zero(real_ring)",
		func(arg *Argument) {
			arg.Show(
				"the sum of n ones is the numeral n",
				Unfold(comm_ring.CharacteristicZeroDef),
				Simp(Fwd(real_ring.AddPowOne)),
				ByArith())
		}),
})}

// RealFormalExpOfCounts — a real series with counting sequence m is the formal
// exponential of m(n)/n, the count of index zero read as zero: the law over a
// field, read at ℝ, whose ring is the ring of reals and whose index n is the
// numeral.
var RealFormalExpOfCounts = realFormalExpOfCountsThm{family.Add(registry.ProofEntry{
	Name: "RealFormalExpOfCounts",
	Key:  "prop_7cf2fb6c9f6c6dc0",
	Build: family.Theorem(Statement{
		Binders:    "∀a m:(num → real).",
		Hypotheses: []string{"series_recurrence(real_ring, a, m)"},
		Conclusion: "a = formal_exp_zero(real_ring, λn:num. COND(n = 0, &0, m(n) / &n))",
	}, func(arg *Argument, a, m *Arrow[Nat, Real], recurrence Fact) {
		realField := arg.Have(
			"ℝ is a field on the whole of ℝ",
			"field_on(restrict_field(real_field_ops, 𝕌))",
			By(real_field.Field, field.FieldOnUniverse))
		realRing := arg.Have(
			"its ring is the ring of reals",
			"field_ring(restrict_field(real_field_ops, 𝕌)) = real_ring",
			Simp(
				Fwd(field.FieldRingDef),
				Fwd(field.RestrictFieldDef),
				Fwd(real_field.RealFieldOpsDef),
				Fwd(real_ring.RealRingDef)),
			Refl())
		atReals := arg.Simplified(
			formal_series.FormalExpOfCounts.Read(realField).At(a, m),
			Fwd(realRing),
			Fwd(real_ring.AddPowOne))
		arg.Show(
			"over ℝ the recurrence gives the exponential, the index reading as the numeral",
			By(atReals, RealCharacteristicZero, recurrence))
	}),
})}
