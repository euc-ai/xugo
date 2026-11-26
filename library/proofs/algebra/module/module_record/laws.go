// laws.go — what the record constructors satisfy: a module or a ring
// restricted to its own carrier is itself, a ring or a module restricted
// twice is restricted once, to the second set, the regular module of a
// restricted ring is the regular module restricted, the additive group of a
// restricted module is the additive group restricted, and a module read
// along the identity of its scalars is itself.

package module_record

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/registry"
)

// RestrictModuleCarrier — restricting a module to its own carrier gives
// the module back: the restriction packs M's four operations with M's
// carrier, and a module record packed from its own parts is the record.
var RestrictModuleCarrier = restrictModuleCarrierThm{family.Add(registry.ProofEntry{
	Name: "RestrictModuleCarrier",
	Key:  "prop_8aa89d9c7c8094b7",
	Build: family.Theorem("∀M:module_ops(A, B). restrict_module(M, M.carrier) = M",
		func(a *Argument, M *Expr[ModuleOps[A, B]]) {
			a.Show(
				"the restriction is M packed from its own parts, which is M",
				Simp(Fwd(RestrictModuleDef)),
				By(ModuleOpsData.Ext))
		}),
})}

// RestrictModuleTwice — restricting a module twice is restricting it once,
// to the second set: both restrictions keep M's four operations, and the
// second carrier replaces the first.
var RestrictModuleTwice = restrictModuleTwiceThm{family.Add(registry.ProofEntry{
	Name: "RestrictModuleTwice",
	Key:  "prop_3cfe96372d133d9a",
	Build: family.Theorem("∀M:module_ops(A, B). ∀S T:set(B). "+
		"    restrict_module(restrict_module(M, S), T) = restrict_module(M, T)",
		func(a *Argument) {
			a.Show(
				"restricting twice keeps the same operations and the final carrier",
				Simp(Fwd(RestrictModuleDef)),
				Basic())
		}),
})}

// RestrictRingCarrier — restricting a ring to its own carrier gives the
// ring back: the restriction packs R's six operations with R's carrier,
// and a ring record packed from its own parts is the record.
var RestrictRingCarrier = restrictRingCarrierThm{family.Add(registry.ProofEntry{
	Name: "RestrictRingCarrier",
	Key:  "prop_b856626d41c2eab6",
	Build: family.Theorem("∀R:ring_ops(A). restrict_ring(R, R.carrier) = R",
		func(a *Argument, R *Expr[RingOps[A]]) {
			a.Show(
				"the restriction is R packed from its own parts, which is R",
				Simp(Fwd(RestrictRingDef)),
				By(RingOpsData.Ext))
		}),
})}

// RestrictRingTwice — restricting a ring twice is restricting it once, to
// the second carrier: the outer restriction packs the inner one's
// operations, which are R's, with the second carrier.
var RestrictRingTwice = restrictRingTwiceThm{family.Add(registry.ProofEntry{
	Name: "RestrictRingTwice",
	Key:  "prop_492944ca1fe70137",
	Build: family.Theorem("∀R:ring_ops(A). ∀S T:set(A). "+
		"    restrict_ring(restrict_ring(R, S), T) = restrict_ring(R, T)",
		func(a *Argument) {
			a.Show(
				"both sides pack R's six operations with the carrier T",
				Simp(Fwd(RestrictRingDef)),
				Basic())
		}),
})}

// RegularModuleRestrict — the regular module of a restricted ring is the
// regular module restricted to the same set: restriction keeps R's
// operations, so both sides pack R's addition, zero, negation and product
// with the carrier S.
var RegularModuleRestrict = regularModuleRestrictThm{family.Add(registry.ProofEntry{
	Name: "RegularModuleRestrict",
	Key:  "prop_b5715efe87bceb35",
	Build: family.Theorem("∀R:ring_ops(A). ∀S:set(A). "+
		"    regular_module(restrict_ring(R, S)) = restrict_module(regular_module(R), S)",
		func(a *Argument) {
			a.Show(
				"both sides pack R's module operations with the carrier S",
				Simp(Fwd(RegularModuleDef), Fwd(RestrictRingDef), Fwd(RestrictModuleDef)),
				Basic())
		}),
})}

// ModuleAdditiveGroupRestrict — restriction commutes with taking the
// additive group: restricting a module keeps its addition, zero and
// negation, and restricting a group keeps its operations, so both sides
// pack M's addition, zero and negation with the carrier N.
var ModuleAdditiveGroupRestrict = moduleAdditiveGroupRestrictThm{family.Add(registry.ProofEntry{
	Name: "ModuleAdditiveGroupRestrict",
	Key:  "prop_34eac6ee797bcbc7",
	Build: family.Theorem("∀M:module_ops(A, B). ∀N:set(B). "+
		"    module_additive_group(restrict_module(M, N)) = restrict_group(module_additive_group(M), N)",
		func(a *Argument) {
			a.Show(
				"both sides pack M's addition, zero and negation with the carrier N",
				Simp(Fwd(ModuleAdditiveGroupDef), Fwd(RestrictModuleDef), Fwd(group.RestrictGroupDef)),
				Basic())
		}),
})}

// ScalarRestrictionIdentity — a module read over its own scalars along the
// identity is the module: each scalar acts as itself, and the record keeps
// M's addition, zero, negation and carrier.
var ScalarRestrictionIdentity = scalarRestrictionIdentityThm{family.Add(registry.ProofEntry{
	Name: "ScalarRestrictionIdentity",
	Key:  "prop_acd005eaa2b9a049",
	Build: family.Theorem("∀M:module_ops(A, B). scalar_restriction(λa:A. a, M) = M",
		func(a *Argument, M *Expr[ModuleOps[A, B]]) {
			a.Show(
				"the restriction is M packed from its own parts, which is M",
				Simp(Fwd(ScalarRestrictionDef)),
				By(ModuleOpsData.Ext))
		}),
})}
