package serve

import (
	"fmt"
	"math/big"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/integrity/dag"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/euc-ai/xugo/prover/tactic"
)

// InstallStructureRingBundle binds omega's structure ring to the algebra
// chapters' carrier laws as stated. Ring, field and additive-group laws
// take records; the commutative-monoid laws retain their operation,
// identity and carrier parameters. Record projections compute in the
// instance normal form, and membership guards are discharged at the
// record's carrier. Whole-type facts read through their chapter bridges
// to records on 𝕌, where set_basic.InUniv discharges the guards.
//
// The laws and installed instances have separate dependency capabilities:
// arith:structure and arith:structure-instances. A proof depends on the
// roots it reads, and a capability's foundation cannot use that capability.
// The installed ℂ field supplies its literal spelling complex_of_real(&n)
// through the canonical-numeral bridge complex_field.AddPowOne, and its
// copy of ℝ, complex_of_real, injective by complex_field.OfRealInjective:
// an embedded real is not zero where ℝ's arithmetic shows the real is
// not, so a literal divisor over ℂ needs no premise.
func InstallStructureRingBundle() {
	InstallRecordNormal()
	// monoid_pow's definition: (∀op e x. pow(op, e, x, 0) = e) ∧
	// (∀op e x n. pow(op, e, x, suc n) = op(x, pow(op, e, x, n))).
	powDef := fromEntryAsStated(comm_monoid.MonoidPowDef)
	zeroPart, sucPart, ok := prop.MatchesAND(powDef.Conclusion())
	if !ok {
		panic("InstallStructureRingBundle: monoid_pow's definition is not a top-level conjunction")
	}
	// Each law keeps its structure hypothesis and carrier guard.
	laws := &omega.StructureRingLaws{
		MulMonoid: fromEntryAsStated(comm_ring.MulMonoidOn),
		AddMonoid: fromEntryAsStated(comm_ring.AddMonoidOn),
		AddGroup:  fromEntryAsStated(comm_ring.AddGroupOn),

		Group:  fromEntryAsStated(abelian_group.GroupOn),
		NegAdd: fromEntryAsStated(abelian_group.NegAddOn),

		Comm:          fromEntryAsStated(comm_monoid.CommOn),
		Assoc:         fromEntryAsStated(comm_monoid.AssocOn),
		LeftIdentity:  fromEntryAsStated(comm_monoid.LeftIdentityOn),
		RightIdentity: fromEntryAsStated(comm_monoid.RightIdentityOn),
		PowOne:        fromEntryAsStated(comm_monoid.PowOneOn),
		PowAdd:        fromEntryAsStated(comm_monoid.PowAddOn),
		PowIn:         fromEntryAsStated(comm_monoid.PowIn),
		PowZeroClause: powDef.DeriveTrans(prop.HypAND0(zeroPart, sucPart)),
		PowSucClause:  powDef.DeriveTrans(prop.HypAND1(zeroPart, sucPart)),

		InvInv:      fromEntryAsStated(group.InvInvOn),
		InvOne:      fromEntryAsStated(group.InvOneOn),
		LeftInverse: fromEntryAsStated(group.LeftInverseOn),
		RightCancel: fromEntryAsStated(group.RightCancelOn),

		LeftDistrib:  fromEntryAsStated(comm_ring.LeftDistribOn),
		RightDistrib: fromEntryAsStated(comm_ring.RightDistribOn),
		MulLeftZero:  fromEntryAsStated(comm_ring.MulLeftZeroOn),
		MulRightZero: fromEntryAsStated(comm_ring.MulRightZeroOn),
		SubAddNeg:    fromEntryAsStated(comm_ring.SubAddNegOn),
		MulRightNeg:  fromEntryAsStated(comm_ring.MulRightNegOn),
		AddPowMul:    fromEntryAsStated(comm_ring.AddPowMulOn),

		ZeroIn: fromEntryAsStated(comm_ring.ZeroIn),
		OneIn:  fromEntryAsStated(comm_ring.OneIn),
		AddIn:  fromEntryAsStated(comm_ring.AddIn),
		NegIn:  fromEntryAsStated(comm_ring.NegIn),
		MulIn:  fromEntryAsStated(comm_ring.MulIn),
		SubIn:  fromEntryAsStated(comm_ring.SubIn),

		RingOnUniverse:  fromEntryAsStated(comm_ring.CommRingOnUniverse),
		FieldOnUniverse: fromEntryAsStated(field.FieldOnUniverse),
		InUniv:          fromEntryAsStated(set_basic.InUniv),

		FieldRing: fromEntryAsStated(field.RingOn),
		DivMulInv: fromEntryAsStated(field.DivMulInvOn),
		InvMul:    fromEntryAsStated(field.InvMulOn),
		InvIn:     fromEntryAsStated(field.InvIn),
		DivIn:     fromEntryAsStated(field.DivIn),

		MulLeftInverse: fromEntryAsStated(field.MulLeftInverseOn),
		OneNotZero:     fromEntryAsStated(field.OneNotZeroOn),
		PowEqZero:      fromEntryAsStated(field.PowEqZeroOn),

		NormalizeWith: func(read omega.LibraryRead) prop.Rewrite { return tactic.InstanceNormal(tactic.LibraryRead(read)) },
		NormalizeTerm: tactic.InstanceNormalTerm,
	}
	omega.SetStructureRingLaws(laws)

	// ℂ: the field instance (its projection is the ring), with the
	// carrier's literal `complex_of_real(&n)` read and bridged.
	complexOfRealMeta, ok := registry.GetConstMetaManager().LoadConstMeta("complex_of_real")
	if !ok {
		panic("InstallStructureRingBundle: complex_of_real is not a registered constant")
	}
	complexOfReal := complexOfRealMeta.Term()
	complexLiteral := func(t core.Term) (*big.Int, bool, bool) {
		app, isApp := t.AsAppliedTerm()
		if !isApp || !app.Fun().Equals(complexOfReal) {
			return nil, false, false
		}
		inner, isReal := omega.MatchesRealOfNum(app.Arg())
		if !isReal {
			return nil, false, false
		}
		n, isNumeral := ext.NumeralValue(inner)
		if !isNumeral {
			return nil, false, false // `&x` for a symbolic x: an atom
		}
		return n, true, ext.IsCanonicalNumeral(inner)
	}
	addPowOne := fromEntryAsStated(complex_field.AddPowOne)
	complexBridge := func(t core.Term, n *big.Int) *prop.PropWrapper {
		w := addPowOne.ConclForAllInsts(ext.MakeNumeral(n)).EqSym() // ⊢ complex_of_real(&n) = monoid_pow(complex_add, &0, &1, n)
		if !prop.Lhs(w).AlphaEquals(t) {
			panic(fmt.Sprintf("InstallStructureRingBundle: the ℂ literal %s is not the numeral AddPowOne reads at %s (%s)",
				ext.PrintTerm(t), n, ext.PrintTerm(prop.Lhs(w))))
		}
		return w
	}
	instances := []omega.StructureInstance{{
		Fact:          fromEntryAsStated(complex_field.Field),
		Literal:       complexLiteral,
		LiteralBridge: complexBridge,
		RealEmbedding: &omega.RealEmbedding{
			Map:       complexOfReal,
			Injective: fromEntryAsStated(complex_field.OfRealInjective),
		},
	}}
	omega.SetStructureInstances(instances)

	roots, foundation := computeBundleCapability(laws, map[string][]core.PropKey{
		// The two clauses are projections of monoid_pow's definition
		// entry: that entry is what their force runs, so it is their
		// provenance (as real_pow.Pow is PowZero's and PowSuc's in the
		// real bundle) — and the warm-up leaves them cold while the
		// comm_monoid family itself is replayed.
		"PowZeroClause": entryKeys(comm_monoid.MonoidPowDef),
		"PowSucClause":  entryKeys(comm_monoid.MonoidPowDef),
	})
	omega.SetStructureBundleFoundation(foundation)
	installCapability(proof.CapabilityArithStructure, roots, foundation)

	// The instances are their own capability: a proof depends on ℂ only
	// where ℂ's instance may read its carrier.
	instanceEntries := entryKeys(complex_field.Field, complex_field.AddPowOne, complex_field.OfRealInjective)
	var instanceRoots []core.PropKey
	for _, k := range instanceEntries {
		if dag.Has(k) {
			instanceRoots = append(instanceRoots, k)
		}
	}
	instanceFoundation := dag.Closure(instanceEntries)
	omega.SetStructureInstanceFoundation(instanceFoundation)
	installCapability(proof.CapabilityArithStructureInstances, instanceRoots, instanceFoundation)

	// ℂ's modulus, a third capability: read by the real layer, where a
	// modulus is a number.
	installModulus()
}
