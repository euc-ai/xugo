// family.go — the tensor_product family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=tensor_product.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/tensor_product go test -run TestRecordFamilyCNF ./library/integrity/gates/

package tensor_product

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed tensor_product.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// tensor_product/tensor_product.cnf.pb from the name's basename, and the
// registered entry prefix is `tensor_product.<Member>`.
var family = registry.NewFamily("algebra/module/tensor_product", familyCNF).WithAbbrev(Abbrev{
	{Name: "pairRecord", Text: "free_module_record(R, set_cross(M.carrier, N.carrier))"},
	{Name: "pairFree", Text: "finite_supp(R.zero, R.carrier, set_cross(M.carrier, N.carrier))"},
	{Name: "additiveLeftRelation", Text: "λu:B. λu':B. λv:C. " +
		"    fun_add⟨D:prod(B, C)⟩(R.add, " +
		"        delta_at(R.zero, R.one, (u + u', v)), " +
		"        fun_neg⟨D:prod(B, C)⟩(R.neg, " +
		"            fun_add⟨D:prod(B, C)⟩(R.add, " +
		"                delta_at(R.zero, R.one, (u, v)), " +
		"                delta_at(R.zero, R.one, (u', v)))))"},
	{Name: "additiveRightRelation", Text: "λu:B. λv:C. λv':C. " +
		"    fun_add⟨D:prod(B, C)⟩(R.add, " +
		"        delta_at(R.zero, R.one, (u, v + v')), " +
		"        fun_neg⟨D:prod(B, C)⟩(R.neg, " +
		"            fun_add⟨D:prod(B, C)⟩(R.add, " +
		"                delta_at(R.zero, R.one, (u, v)), " +
		"                delta_at(R.zero, R.one, (u, v')))))"},
	{Name: "scaledLeftRelation", Text: "λc:A. λu:B. λv:C. " +
		"    fun_add⟨D:prod(B, C)⟩(R.add, " +
		"        delta_at(R.zero, R.one, (c • u, v)), " +
		"        fun_neg⟨D:prod(B, C)⟩(R.neg, " +
		"            fun_smul⟨D:prod(B, C)⟩(R.mul, c, delta_at(R.zero, R.one, (u, v)))))"},
	{Name: "scaledRightRelation", Text: "λc:A. λu:B. λv:C. " +
		"    fun_add⟨D:prod(B, C)⟩(R.add, " +
		"        delta_at(R.zero, R.one, (u, c • v)), " +
		"        fun_neg⟨D:prod(B, C)⟩(R.neg, " +
		"            fun_smul⟨D:prod(B, C)⟩(R.mul, c, delta_at(R.zero, R.one, (u, v)))))"},
	{Name: "additiveLeftRelations", Text: "{r:(prod(B, C) → A) | " +
		"    ∃u u':B. ∃v:C. " +
		"        u ∈ M.carrier ∧ u' ∈ M.carrier ∧ v ∈ N.carrier ∧ r = «additiveLeftRelation»(u, u', v)}"},
	{Name: "additiveRightRelations", Text: "{r:(prod(B, C) → A) | " +
		"    ∃u:B. ∃v v':C. " +
		"        u ∈ M.carrier ∧ v ∈ N.carrier ∧ v' ∈ N.carrier ∧ r = «additiveRightRelation»(u, v, v')}"},
	{Name: "scaledLeftRelations", Text: "{r:(prod(B, C) → A) | " +
		"    ∃c:A. ∃u:B. ∃v:C. " +
		"        c ∈ R.carrier ∧ u ∈ M.carrier ∧ v ∈ N.carrier ∧ r = «scaledLeftRelation»(c, u, v)}"},
	{Name: "scaledRightRelations", Text: "{r:(prod(B, C) → A) | " +
		"    ∃c:A. ∃u:B. ∃v:C. " +
		"        c ∈ R.carrier ∧ u ∈ M.carrier ∧ v ∈ N.carrier ∧ r = «scaledRightRelation»(c, u, v)}"},
	{Name: "relationElements", Text: "«additiveLeftRelations» ∪ " +
		"«additiveRightRelations» ∪ " +
		"«scaledLeftRelations» ∪ " +
		"«scaledRightRelations»"},
	{Name: "projection", Text: "coset_map(fun_add⟨D:prod(B, C)⟩(R.add), tensor_relations(R, M, N))"},
	{Name: "pureTensors", Text: "{t:set(prod(B, C) → A) | " +
		"    ∃u:B. ∃v:C. u ∈ M.carrier ∧ v ∈ N.carrier ∧ t = tensor(R, M, N, u, v)}"},
	{Name: "bilinearLift", Text: "free_lift(R.zero, " +
		"    L.add, " +
		"    L.zero, " +
		"    L.smul, " +
		"    λp:prod(B, C). phi(fst(p), snd(p)))"},
})
