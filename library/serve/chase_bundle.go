package serve

// chase_bundle.go — the laws the diagram-chase closer reads
// (prover/solver/chase), bound from the algebra and set chapters: the
// module's additive group and its commutativity, the group's carrier
// laws, the abelian group's definition and its law for the negation of
// a sum, the homomorphism's image and additivity, the definitions that
// read exactness, images, kernels, submodules, subsets and injectivity
// on a set, record constructor and projection equations, and set
// extensionality, by which a set equation the closer decides is two
// memberships. Every
// law is a proved theorem of its chapter — a card is refused, so no
// proof the closer finishes rests on an axiom its dependencies do not name —
// and the bundle is one capability (proof.CapabilityChase) whose
// foundation is the closure of those entries.

import (
	"fmt"
	"github.com/euc-ai/xugo/ext/prop"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/chase"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/euc-ai/xugo/prover/tactic"
)

// InstallChaseBundle binds the chase closer's laws from the chapters
// and installs its capability. Idempotent.
func InstallChaseBundle() {
	InstallRecordNormal()
	if !omega.StructureRingEnabled() {
		InstallStructureRingBundle()
	}
	entries := map[string]registry.EntryLike{
		"AddGroupOn":           module.AddGroupOn,
		"Scalars.RingOn":       module.RingOn,
		"Scalars.SmulAddLeft":  module.SmulAddLeft,
		"Scalars.SmulAddRight": module.SmulAddRight,
		"Scalars.SmulMul":      module.SmulMul,
		"Scalars.SmulOne":      module.SmulOne,
		"Scalars.ZeroSmul":     module.ZeroSmul,
		"Scalars.SmulZero":     module.SmulZero,
		"Scalars.HomSmul":      module_homomorphism.HomSmul,
		"AddComm":              module.AddComm,
		"SmulIn":               module.SmulIn,
		"HomSource":            module_homomorphism.HomSource,
		"HomTarget":            module_homomorphism.HomTarget,
		"AbelianGroupOnDef":    abelian_group.AbelianGroupOn,
		"NegAdd":               abelian_group.NegAddOn,
		"OneIn":                group.OneIn,
		"MulIn":                group.MulIn,
		"InvIn":                group.InvIn,
		"Assoc":                group.AssocOn,
		"LeftIdentity":         group.LeftIdentityOn,
		"RightIdentity":        group.RightIdentityOn,
		"LeftInverse":          group.LeftInverseOn,
		"RightInverse":         group.RightInverseOn,
		"InvInv":               group.InvInvOn,
		"InvOne":               group.InvOneOn,
		"IdempotentIsOne":      group.IdempotentIsOneOn,
		"InvUnique":            group.InvUniqueOn,
		"LeftCosetEq":          group.LeftCosetEqOn,
		"HomIn":                module_homomorphism.HomIn,
		"HomAdd":               module_homomorphism.HomAdd,
		"ExactAtDef":           module_homomorphism.ExactAtDef,
		"InImage":              set_basic.InImage,
		"InKernel":             group_homomorphism.InKernel,
		"SubmoduleSubgroup":    submodule.SubmoduleSubgroup,
		"SubgroupSubset":       group.SubgroupSubset,
		"SubsetDef":            set_basic.SubsetDef,
		"InjectiveOnDef":       functions.InjectiveOnDef,
		"Extension":            set_basic.Extension,
	}
	for name, entry := range map[string]registry.EntryLike{
		"Rewrites.RingAdd":             module_record.RingAddDef,
		"Rewrites.RingZero":            module_record.RingZeroDef,
		"Rewrites.RingNeg":             module_record.RingNegDef,
		"Rewrites.RingMul":             module_record.RingMulDef,
		"Rewrites.RingOne":             module_record.RingOneDef,
		"Rewrites.RingSub":             module_record.RingSubDef,
		"Rewrites.RingCarrier":         module_record.RingCarrierDef,
		"Rewrites.ModuleAdd":           module_record.ModAddDef,
		"Rewrites.ModuleZero":          module_record.ModZeroDef,
		"Rewrites.ModuleNeg":           module_record.ModNegDef,
		"Rewrites.ModuleSmul":          module_record.ModSmulDef,
		"Rewrites.ModuleCarrier":       module_record.ModCarrierDef,
		"Rewrites.ComplexAdd":          chain_complex.ComplexAddDef,
		"Rewrites.ComplexZero":         chain_complex.ComplexZeroDef,
		"Rewrites.ComplexNeg":          chain_complex.ComplexNegDef,
		"Rewrites.ComplexSmul":         chain_complex.ComplexSmulDef,
		"Rewrites.ComplexTerms":        chain_complex.ComplexTermsDef,
		"Rewrites.ComplexDifferential": chain_complex.ComplexDifferentialDef,
		"Rewrites.RestrictModule":      module_record.RestrictModuleDef,
		"Rewrites.QuotientModule":      submodule.QuotientModuleDef,
		"Rewrites.ComplexModule":       chain_complex.ComplexModuleDef,
		"Rewrites.HomologyModule":      chain_complex.HomologyModuleDef,
		"Rewrites.HomologyCarrier":     chain_complex.HomologyDef,
		"Rewrites.CohomologyModule":    chain_complex.CohomologyModuleDef,
		"Rewrites.CohomologyCarrier":   chain_complex.CohomologyDef,
	} {
		entries[name] = entry
	}
	for name, e := range entries {
		if pe := e.Entry(); pe.ServedAsAxiom() {
			panic(fmt.Sprintf("InstallChaseBundle: the law %s (%s) is stated without a proof; the closer's laws are proved theorems", name, pe.Name))
		}
	}
	laws := &chase.Laws{
		NormalizeWith: func(read omega.LibraryRead) prop.Rewrite { return tactic.RecordProjections(tactic.LibraryRead(read)) },
		Scalars: chase.ScalarLaws{
			RingOn:      fromEntryAsStated(module.RingOn),
			SmulAddLeft: fromEntryAsStated(module.SmulAddLeft), SmulAddRight: fromEntryAsStated(module.SmulAddRight),
			SmulMul: fromEntryAsStated(module.SmulMul), SmulOne: fromEntryAsStated(module.SmulOne),
			ZeroSmul: fromEntryAsStated(module.ZeroSmul), SmulZero: fromEntryAsStated(module.SmulZero),
			HomSmul: fromEntryAsStated(module_homomorphism.HomSmul),
			Ring:    *omega.InstalledStructureRingLaws(),
		},
		AddGroupOn: fromEntryAsStated(module.AddGroupOn),
		AddComm:    fromEntryAsStated(module.AddComm),
		SmulIn:     fromEntryAsStated(module.SmulIn),
		HomSource:  fromEntryAsStated(module_homomorphism.HomSource),
		HomTarget:  fromEntryAsStated(module_homomorphism.HomTarget),
		Rewrites: chase.RecordRewrites{
			RingAdd:             fromEntryAsStated(module_record.RingAddDef),
			RingZero:            fromEntryAsStated(module_record.RingZeroDef),
			RingNeg:             fromEntryAsStated(module_record.RingNegDef),
			RingMul:             fromEntryAsStated(module_record.RingMulDef),
			RingOne:             fromEntryAsStated(module_record.RingOneDef),
			RingSub:             fromEntryAsStated(module_record.RingSubDef),
			RingCarrier:         fromEntryAsStated(module_record.RingCarrierDef),
			ModuleAdd:           fromEntryAsStated(module_record.ModAddDef),
			ModuleZero:          fromEntryAsStated(module_record.ModZeroDef),
			ModuleNeg:           fromEntryAsStated(module_record.ModNegDef),
			ModuleSmul:          fromEntryAsStated(module_record.ModSmulDef),
			ModuleCarrier:       fromEntryAsStated(module_record.ModCarrierDef),
			ComplexAdd:          fromEntryAsStated(chain_complex.ComplexAddDef),
			ComplexZero:         fromEntryAsStated(chain_complex.ComplexZeroDef),
			ComplexNeg:          fromEntryAsStated(chain_complex.ComplexNegDef),
			ComplexSmul:         fromEntryAsStated(chain_complex.ComplexSmulDef),
			ComplexTerms:        fromEntryAsStated(chain_complex.ComplexTermsDef),
			ComplexDifferential: fromEntryAsStated(chain_complex.ComplexDifferentialDef),
			RestrictModule:      fromEntryAsStated(module_record.RestrictModuleDef),
			QuotientModule:      fromEntryAsStated(submodule.QuotientModuleDef),
			ComplexModule:       fromEntryAsStated(chain_complex.ComplexModuleDef),
			HomologyModule:      fromEntryAsStated(chain_complex.HomologyModuleDef),
			HomologyCarrier:     fromEntryAsStated(chain_complex.HomologyDef),
			CohomologyModule:    fromEntryAsStated(chain_complex.CohomologyModuleDef),
			CohomologyCarrier:   fromEntryAsStated(chain_complex.CohomologyDef),
		},
		AbelianGroupOnDef: fromEntryAsStated(abelian_group.AbelianGroupOn),
		NegAdd:            fromEntryAsStated(abelian_group.NegAddOn),
		OneIn:             fromEntryAsStated(group.OneIn),
		MulIn:             fromEntryAsStated(group.MulIn),
		InvIn:             fromEntryAsStated(group.InvIn),
		Assoc:             fromEntryAsStated(group.AssocOn),
		LeftIdentity:      fromEntryAsStated(group.LeftIdentityOn),
		RightIdentity:     fromEntryAsStated(group.RightIdentityOn),
		LeftInverse:       fromEntryAsStated(group.LeftInverseOn),
		RightInverse:      fromEntryAsStated(group.RightInverseOn),
		InvInv:            fromEntryAsStated(group.InvInvOn),
		InvOne:            fromEntryAsStated(group.InvOneOn),
		IdempotentIsOne:   fromEntryAsStated(group.IdempotentIsOneOn),
		InvUnique:         fromEntryAsStated(group.InvUniqueOn),
		LeftCosetEq:       fromEntryAsStated(group.LeftCosetEqOn),
		HomIn:             fromEntryAsStated(module_homomorphism.HomIn),
		HomAdd:            fromEntryAsStated(module_homomorphism.HomAdd),
		ExactAtDef:        fromEntryAsStated(module_homomorphism.ExactAtDef),
		InImage:           fromEntryAsStated(set_basic.InImage),
		InKernel:          fromEntryAsStated(group_homomorphism.InKernel),
		SubmoduleSubgroup: fromEntryAsStated(submodule.SubmoduleSubgroup),
		SubgroupSubset:    fromEntryAsStated(group.SubgroupSubset),
		SubsetDef:         fromEntryAsStated(set_basic.SubsetDef),
		InjectiveOnDef:    fromEntryAsStated(functions.InjectiveOnDef),
		Extension:         fromEntryAsStated(set_basic.Extension),
	}
	chase.SetLaws(laws)
	roots, foundation := computeBundleCapability(laws, map[string][]core.PropKey{
		"Scalars.Ring.PowZeroClause": entryKeys(comm_monoid.MonoidPowDef),
		"Scalars.Ring.PowSucClause":  entryKeys(comm_monoid.MonoidPowDef),
	})
	chase.SetFoundation(foundation)
	installCapability(proof.CapabilityChase, roots, foundation)
}
