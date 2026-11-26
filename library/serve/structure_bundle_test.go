package serve

import (
	"reflect"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/stretchr/testify/require"
)

// TestStructureBundle_CarrierLawsAndBridges checks that leaves read
// carrier laws, with explicit whole-to-universe bridges beside them.
func TestStructureBundle_CarrierLawsAndBridges(t *testing.T) {
	InstallNatBundle()
	InstallStructureRingBundle()
	t.Cleanup(func() {
		omega.SetStructureRingLaws(nil)
		omega.SetStructureInstances(nil)
		omega.SetModulusLaws(nil)
		omega.SetNatLemmaBundle(nil)
	})
	laws := omega.InstalledStructureRingLaws()
	require.NotNil(t, laws)
	clauses := map[string]bool{"PowZeroClause": true, "PowSucClause": true, "InUniv": true}
	v := reflect.ValueOf(laws).Elem()
	for i := 0; i < v.NumField(); i++ {
		f := v.Type().Field(i)
		if !f.IsExported() {
			continue
		}
		if v.Field(i).Kind() == reflect.Func {
			require.False(t, v.Field(i).IsNil(), "%s is not installed", f.Name)
			continue
		}
		law, ok := v.Field(i).Interface().(*prop.PropWrapper)
		require.True(t, ok, "%s is not a law", f.Name)
		require.NotNil(t, law, "%s is not installed", f.Name)
		if clauses[f.Name] {
			continue
		}
		body, _ := law.StripConclForAll()
		if f.Name == "RingOnUniverse" || f.Name == "FieldOnUniverse" {
			whole, carrier, ok := prop.MatchesIFF(body.Conclusion())
			require.True(t, ok, "%s is not an equivalence", f.Name)
			wh, wa := ext.MatchesApply(whole)
			ch, ca := ext.MatchesApply(carrier)
			wc, ok := wh.AsConst()
			require.True(t, ok)
			cc, ok := ch.AsConst()
			require.True(t, ok)
			require.Equal(t, string(wc.Name())+"_on", string(cc.Name()))
			require.Len(t, wa, 1)
			require.Len(t, ca, 1)
			rh, ra := ext.MatchesApply(ca[0])
			rc, ok := rh.AsConst()
			require.True(t, ok)
			expected := "restrict_ring"
			if f.Name == "FieldOnUniverse" {
				expected = "restrict_field"
			}
			require.Equal(t, expected, string(rc.Name()))
			require.Len(t, ra, 2)
			require.True(t, ra[0].AlphaEquals(wa[0]))
			continue
		}
		structure, _, isLaw := prop.MatchesIMPLY(body.Conclusion())
		require.True(t, isLaw, "%s has no structure hypothesis: %s", f.Name, ext.PrintTerm(law.Conclusion()))
		head, _ := ext.MatchesApply(structure)
		c, isConst := head.AsConst()
		require.True(t, isConst)
		name := string(c.Name())
		require.True(t, strings.HasSuffix(name, "_on"), "%s is read at the whole-type structure %s: the table holds carrier laws only", f.Name, name)
	}
}

// TestStructureBundle_InstancesAreTheirOwnCapability: the laws'
// capability roots hold no instance, and the instances' capability holds
// ℂ's three — the field, its numeral bridge and the injectivity of its
// copy of ℝ — so a chapter over a ring of its own depends on no instance.
func TestStructureBundle_InstancesAreTheirOwnCapability(t *testing.T) {
	InstallNatBundle()
	InstallStructureRingBundle()
	t.Cleanup(func() {
		omega.SetStructureRingLaws(nil)
		omega.SetStructureInstances(nil)
		omega.SetModulusLaws(nil)
		omega.SetNatLemmaBundle(nil)
	})
	specs := proof.DependencyCapabilitySnapshot()
	laws, ok := specs[proof.CapabilityArithStructure]
	require.True(t, ok)
	instances, ok := specs[proof.CapabilityArithStructureInstances]
	require.True(t, ok)
	instanceKeys := entryKeys(complex_field.Field, complex_field.AddPowOne, complex_field.OfRealInjective)
	for _, k := range instanceKeys {
		require.NotContains(t, laws.Roots, k, "the laws' capability names an instance as its root")
		require.Contains(t, instances.Roots, k)
		require.False(t, laws.Foundation[k], "an instance lies in the laws' foundation")
	}
}

// A field's ring projection and division law compute at the same record,
// while division on a proper carrier still requires its denominator.
func TestStructureBundle_FieldRecordGuards(t *testing.T) {
	InstallNatBundle()
	InstallStructureRingBundle()
	t.Cleanup(func() {
		omega.SetStructureRingLaws(nil)
		omega.SetStructureInstances(nil)
		omega.SetModulusLaws(nil)
		omega.SetNatLemmaBundle(nil)
	})
	scope := corpusParseScope()
	for _, complete := range []bool{true, false} {
		prefix := "F:field_ops(A), x:A, y:A, z:A, field_on(F), x ∈ F.carrier, y ∈ F.carrier"
		if complete {
			prefix += ", z ∈ F.carrier"
		}
		parsed := dsl.ParsePropTextInScope(prefix+" ⊢ F.div(F.add(x, y), z) = F.add(F.mul(x, F.inv(z)), F.mul(y, F.inv(z)))", scope)
		require.Empty(t, parsed.Errors)
		closed := omega.NewArithCtxWithPolicy(parsed.Prop.Hyps(), omega.ArithPolicy{Nat: true, Structure: true}, nil).Decide(parsed.Prop.Conclusion())
		if complete {
			require.NotNil(t, closed)
			require.True(t, prop.Rhs(closed).AlphaEquals(prop.T))
		} else {
			require.Nil(t, closed)
		}
	}
}

// Whole records ignore their stored carrier and reach the same guarded
// laws through the chapter bridges; the installed complex field does too.
func TestStructureBundle_WholeRecordsAndComplexInstance(t *testing.T) {
	InstallNatBundle()
	InstallStructureRingBundle()
	t.Cleanup(func() {
		omega.SetStructureRingLaws(nil)
		omega.SetStructureInstances(nil)
		omega.SetModulusLaws(nil)
		omega.SetNatLemmaBundle(nil)
	})
	scope := corpusParseScope()
	for _, text := range []string{
		"R:ring_ops(A), x:A, y:A, comm_ring(R) ⊢ R.mul(R.sub(x, y), R.add(x, y)) = R.sub(R.mul(x, x), R.mul(y, y))",
		"F:field_ops(A), x:A, y:A, field(F) ⊢ F.div(F.add(x, y), y) = F.add(F.mul(x, F.inv(y)), F.mul(y, F.inv(y)))",
		"R:ring_ops(A), x:A, y:A, comm_ring(restrict_ring(R, ∅)) ⊢ R.add(x, y) = R.add(y, x)",
		"F:field_ops(A), x:A, y:A, field(restrict_field(F, ∅)) ⊢ F.div(F.add(x, y), y) = F.add(F.mul(x, F.inv(y)), F.mul(y, F.inv(y)))",
		"z:complex, w:complex ⊢ complex_mul(complex_sub(z, w), complex_add(z, w)) = complex_sub(complex_mul(z, z), complex_mul(w, w))",
	} {
		parsed := dsl.ParsePropTextInScope(text, scope)
		require.Empty(t, parsed.Errors)
		closed := omega.NewArithCtxWithPolicy(parsed.Prop.Hyps(), omega.ArithPolicy{Nat: true, Structure: true, StructureInstances: true}, nil).Decide(parsed.Prop.Conclusion())
		require.NotNil(t, closed, text)
		require.True(t, prop.Rhs(closed).AlphaEquals(prop.T))
	}
}

// A field fact on a record literal the goal spells out of normal form
// — `mk_field(field_ring(K).add, …)`, a session's own claim — builds
// its ring as the fact spelled `mk_field(K.add, …)` does: the ring
// holds the fact and its records in the instance normal form, so the
// field-ring and monoid laws instantiated at the records discharge
// their hypotheses from the derived facts — the shape a session's own
// claim leaves resident, which `inspect` reads at every equation.
func TestStructureBundle_FieldFactOnARecordLiteralOutOfNormalForm(t *testing.T) {
	InstallNatBundle()
	InstallStructureRingBundle()
	t.Cleanup(func() {
		omega.SetStructureRingLaws(nil)
		omega.SetStructureInstances(nil)
		omega.SetModulusLaws(nil)
		omega.SetNatLemmaBundle(nil)
	})
	scope := corpusParseScope()
	for _, literal := range []string{
		"mk_field(field_ring(K).add, field_ring(K).zero, field_ring(K).neg, field_ring(K).mul, field_ring(K).one, field_ring(K).sub, K.inv, K.div, field_ring(K).carrier)",
		"mk_field(K.add, K.zero, K.neg, K.mul, K.one, K.sub, K.inv, K.div, K.carrier)",
	} {
		text := "K:field_ops(A), x:A, field_on(" + literal + "), x ∈ K.carrier ⊢ K.mul(x, K.one) = x"
		parsed := dsl.ParsePropTextInScope(text, scope)
		require.Empty(t, parsed.Errors, text)
		require.True(t, omega.IsStructureRingContent(parsed.Prop.Hyps(), parsed.Prop.Conclusion()), text)
		closed := omega.NewArithCtxWithPolicy(parsed.Prop.Hyps(), omega.ArithPolicy{Nat: true, Structure: true}, nil).Decide(parsed.Prop.Conclusion())
		require.NotNil(t, closed, text)
		require.True(t, prop.Rhs(closed).AlphaEquals(prop.T))
	}
}

// TestStructureBundle_ComplexUnitFacts: over ℂ a factor and its inverse
// cancel wherever they stand in a monomial, on the evidence that the
// factor is not zero — the field's left inverse law read at the installed
// instance (omega structure_unit_facts.go). The evidence is the context's,
// or, for an embedded real, ℝ's: ℂ's instance names complex_of_real as
// its copy of ℝ, so the primitive αz + βz²/2 of a linear function
// differentiates back with no premise, and so do the cube's third and a
// quotient by an embedded real of resident sign. With ℝ's arithmetic
// withheld by the policy a literal is a premise again, and an abstract
// field reads the same law, whole or on a carrier set with the
// memberships named, with no literal nonzero without such evidence.
func TestStructureBundle_ComplexUnitFacts(t *testing.T) {
	InstallNatBundle()
	InstallRealBundle()
	InstallStructureRingBundle()
	t.Cleanup(func() {
		omega.SetStructureRingLaws(nil)
		omega.SetStructureInstances(nil)
		omega.SetModulusLaws(nil)
		omega.SetRealLemmaBundle(nil)
		omega.SetNatLemmaBundle(nil)
	})
	scope := corpusParseScope()
	withReal := omega.ArithPolicy{Nat: true, Real: true, Structure: true, StructureInstances: true}
	withoutReal := omega.ArithPolicy{Nat: true, Structure: true, StructureInstances: true}
	decides := func(policy omega.ArithPolicy, text string) bool {
		t.Helper()
		parsed := dsl.ParsePropTextInScope(text, scope)
		require.Empty(t, parsed.Errors, text)
		closed := omega.NewArithCtxWithPolicy(parsed.Prop.Hyps(), policy, nil).Decide(parsed.Prop.Conclusion())
		if closed == nil || !prop.Rhs(closed).AlphaEquals(prop.T) {
			return false
		}
		theorem := closed.EqSym().EqMP(prop.DerivesTrue)
		require.True(t, prop.IsStronger(theorem, parsed.Prop), "the close carries a hypothesis the goal lacks: %s", text)
		return true
	}
	two := "¬(complex_of_real(&2) = complex_of_real(&0))"
	primitive := "complex_add(complex_mul(α, complex_of_real(&1)), complex_mul(complex_div(β, complex_of_real(&2)), complex_add(complex_mul(complex_of_real(&1), u), complex_mul(u, complex_of_real(&1))))) = complex_add(α, complex_mul(β, u))"
	third := "complex_mul(complex_div(β, complex_of_real(&3)), complex_add(complex_add(complex_mul(u, u), complex_mul(u, u)), complex_mul(u, u))) = complex_mul(β, complex_mul(u, u))"
	byRadius := "complex_mul(complex_div(x, complex_of_real(r)), complex_of_real(r)) = x"
	for _, text := range []string{
		"α:complex, β:complex, u:complex, " + two + " ⊢ " + primitive,
		"α:complex, β:complex, u:complex, ¬(complex_of_real(&0) = complex_of_real(&2)) ⊢ " + primitive,
		"β:complex, u:complex, ¬(complex_of_real(&3) = complex_of_real(&0)) ⊢ " + third,
		"x:complex, y:complex, ¬(y = complex_of_real(&0)) ⊢ complex_mul(complex_div(x, y), y) = x",
		"f:complex, p:complex, z:complex, c:complex, ¬(z = c) ⊢ complex_mul(complex_div(complex_sub(f, p), complex_sub(z, c)), complex_sub(z, c)) = complex_sub(f, p)",
		// An abstract field on a carrier set: the fact and the memberships named.
		"F:field_ops(A), x:A, y:A, field_on(F), x ∈ F.carrier, y ∈ F.carrier, ¬(y = F.zero) ⊢ F.mul(F.div(x, y), y) = x",
		"F:field_ops(A), x:A, y:A, field(F), ¬(y = F.zero) ⊢ F.mul(F.div(x, y), y) = x",
	} {
		require.True(t, decides(withoutReal, text), "declined: %s", text)
	}
	// ℂ's embedded reals: ℝ's arithmetic is the evidence.
	for _, text := range []string{
		"α:complex, β:complex, u:complex ⊢ " + primitive,
		"β:complex, u:complex ⊢ " + third,
		"x:complex ⊢ complex_mul(complex_div(x, complex_of_real(-&2)), complex_of_real(-&2)) = x",
		"x:complex, r:real, &0 < r ⊢ " + byRadius,
		"x:complex, r:real, s:real, r < s ⊢ complex_mul(complex_div(x, complex_of_real(s - r)), complex_of_real(s - r)) = x",
	} {
		require.True(t, decides(withReal, text), "declined: %s", text)
	}
	for _, text := range []string{
		"x:complex, y:complex ⊢ complex_mul(complex_div(x, y), y) = x",
		"x:complex, y:complex, w:complex, ¬(w = complex_of_real(&0)) ⊢ complex_mul(complex_div(x, y), y) = x",
		"x:complex, r:real ⊢ " + byRadius,
		"x:complex ⊢ complex_mul(complex_div(x, complex_of_real(&0)), complex_of_real(&0)) = x",
		"F:field_ops(A), x:A, y:A, field_on(F), x ∈ F.carrier, ¬(y = F.zero) ⊢ F.mul(F.div(x, y), y) = x",
		"F:field_ops(A), x:A, field(F) ⊢ F.mul(F.div(x, F.add(F.one, F.one)), F.add(F.one, F.one)) = x",
	} {
		require.False(t, decides(withReal, text), "cancelled a factor with no evidence that it is nonzero, or no membership: %s", text)
	}
	require.False(t, decides(withoutReal, "α:complex, β:complex, u:complex ⊢ "+primitive),
		"cancelled the literal 2 with ℝ's arithmetic withheld")
}
