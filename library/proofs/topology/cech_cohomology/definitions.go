package cech_cohomology

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	_ "github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	_ "github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_chain"
	_ "github.com/euc-ai/xugo/library/proofs/topology/presheaf"
	"github.com/euc-ai/xugo/library/registry"
)

// cechIndicesDef — A degree-n tuple has n+1 active entries and zero tail.
var cechIndicesDef = cechIndicesDefThm{family.Define(registry.DefEntry{
	Name:  "cechIndicesDef",
	Key:   "prop_969889cd29a05237",
	Const: "cech_indices",
	Type:  "num → set(prod(num, num → num))",
	Equations: []string{
		"∀n:num. cech_indices(n) = {t:prod(num, num → num) | fst(t) = n ∧ (∀k:num. n < k ⇒ snd(t, k) = 0)}",
	},
	Reading: "A degree-n tuple has n+1 active entries and zero tail.",
})}

// cechMeetDef — The intersection over the nonempty finite tuple of cover indices.
var cechMeetDef = cechMeetDefThm{family.Define(registry.DefEntry{
	Name:  "cechMeetDef",
	Key:   "prop_a6560426ccf57a27",
	Const: "cech_meet",
	Type:  "(num → set(A)) → prod(num, num → num) → set(A)",
	Equations: []string{
		"∀U:(num → set(A)). ∀t:prod(num, num → num). " +
			"    cech_meet(U, t) = ⋂image(λi:num. U(snd(t, i)), 0 .. fst(t))",
	},
	Reading: "The intersection over the nonempty finite tuple of cover indices.",
})}

// cechDeleteDef — Delete one tuple entry, reducing its degree and normalizing the tail; read only in positive degree with i at most the degree.
var cechDeleteDef = cechDeleteDefThm{family.Define(registry.DefEntry{
	Name:  "cechDeleteDef",
	Key:   "prop_379991944075a4e4",
	Const: "cech_delete",
	Type:  "prod(num, num → num) → num → prod(num, num → num)",
	Equations: []string{
		"∀t:prod(num, num → num). ∀i:num. " +
			"    cech_delete(t, i) = (fst(t) - 1, λk:num. COND(k < fst(t), snd(t, COND(k < i, k, k + 1)), 0))",
	},
	Reading: "Delete one tuple entry, reducing its degree and normalizing " +
		"the tail; read only in positive degree with i at most the degree.",
})}

// cechRefineTupleDef — Apply the refinement index map to active tuple entries only.
var cechRefineTupleDef = cechRefineTupleDefThm{family.Define(registry.DefEntry{
	Name:  "cechRefineTupleDef",
	Key:   "prop_4d589c07a9bd5676",
	Const: "cech_refine_tuple",
	Type:  "(num → num) → prod(num, num → num) → prod(num, num → num)",
	Equations: []string{
		"∀r:(num → num). ∀t:prod(num, num → num). " +
			"    cech_refine_tuple(r, t) = (fst(t), λk:num. COND(k ≤ fst(t), r(snd(t, k)), 0))",
	},
	Reading: "Apply the refinement index map to active tuple entries only.",
})}

// modulePresheafDef — The existing set-valued presheaf has module sections and linear restriction maps.
var modulePresheafDef = modulePresheafDefThm{family.Define(registry.DefEntry{
	Name:  "modulePresheafDef",
	Key:   "prop_8ec0fdb75cc06af",
	Const: "module_presheaf",
	Type: "ring_ops(B) → " +
		"set(set(A)) → " +
		"(set(A) → module_ops(B, C)) → " +
		"(set(A) → set(A) → C → C) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(B). ∀T:set(set(A)). ∀F:(set(A) → module_ops(B, C)). ∀res:(set(A) → set(A) → C → C). " +
			"    module_presheaf(R, T, F, res) ⇔ " +
			"    presheaf(T, λu:set(A). F(u).carrier, res) ∧ " +
			"    (∀u:set(A). u ∈ T ⇒ module_on(R, F(u))) ∧ " +
			"    (∀u v:set(A). u ∈ T ∧ v ∈ T ∧ v ⊆ u ⇒ module_homomorphism(R, F(u), F(v), res(u, v)))",
	},
	Reading: "The existing set-valued presheaf has module sections and linear restriction maps.",
})}

// cechDatumDef — All finite-intersection section groups are countable; the ambient section type need not be countable.
var cechDatumDef = cechDatumDefThm{family.Define(registry.DefEntry{
	Name:  "cechDatumDef",
	Key:   "prop_b11ba9bca6520b5c",
	Const: "cech_datum",
	Type: "ring_ops(B) → " +
		"set(set(A)) → " +
		"(set(A) → module_ops(B, C)) → " +
		"(set(A) → set(A) → C → C) → " +
		"(num → set(A)) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(B). " +
			"∀T:set(set(A)). " +
			"∀F:(set(A) → module_ops(B, C)). " +
			"∀res:(set(A) → set(A) → C → C). " +
			"∀U:(num → set(A)). " +
			"    cech_datum(R, T, F, res, U) ⇔ " +
			"    module_presheaf(R, T, F, res) ∧ " +
			"    (∀i:num. U(i) ∈ T) ∧ " +
			"    ⋃image(U, 𝕌) = ⋃T ∧ " +
			"    (∀t:prod(num, num → num). countable(F(cech_meet(U, t)).carrier))",
	},
	Deps: []registry.EntryLike{cechMeetDef, modulePresheafDef},
	Reading: "All finite-intersection section groups are " +
		"countable; the ambient section type need not be countable.",
})}

// cechZeroDef — The zero cochain is the section zero at each tuple intersection.
var cechZeroDef = cechZeroDefThm{family.Define(registry.DefEntry{
	Name:  "cechZeroDef",
	Key:   "prop_6f6a0c1754a12694",
	Const: "cech_zero",
	Type:  "(set(A) → module_ops(B, C)) → (num → set(A)) → prod(num, num → num) → C",
	Equations: []string{
		"∀F:(set(A) → module_ops(B, C)). ∀U:(num → set(A)). ∀t:prod(num, num → num). " +
			"    cech_zero(F, U, t) = F(cech_meet(U, t)).zero",
	},
	Deps:    []registry.EntryLike{cechMeetDef},
	Reading: "The zero cochain is the section zero at each tuple intersection.",
})}

// cechTermsDef — The degree carrier consists of section assignments on its tuples, with coordinate zero outside that degree.
var cechTermsDef = cechTermsDefThm{family.Define(registry.DefEntry{
	Name:  "cechTermsDef",
	Key:   "prop_b06fe854a7ffdbb2",
	Const: "cech_terms",
	Type:  "(set(A) → module_ops(B, C)) → (num → set(A)) → num → set(prod(num, num → num) → C)",
	Equations: []string{
		"∀F:(set(A) → module_ops(B, C)). ∀U:(num → set(A)). ∀n:num. " +
			"    cech_terms(F, U, n) = " +
			"    indexed_functions(cech_indices(n), " +
			"        cech_zero(F, U), " +
			"        λt:prod(num, num → num). F(cech_meet(U, t)).carrier)",
	},
	Deps: []registry.EntryLike{cechIndicesDef, cechMeetDef, cechZeroDef},
	Reading: "The degree carrier consists of section assignments " +
		"on its tuples, with coordinate zero outside that degree.",
})}

// cechDifferentialDef — The alternating restriction sum has n+2 terms and is normalized outside the target degree.
var cechDifferentialDef = cechDifferentialDefThm{family.Define(registry.DefEntry{
	Name:  "cechDifferentialDef",
	Key:   "prop_f153fb570fe310ee",
	Const: "cech_differential",
	Type: "ring_ops(B) → " +
		"(set(A) → module_ops(B, C)) → " +
		"(set(A) → set(A) → C → C) → " +
		"(num → set(A)) → " +
		"num → " +
		"(prod(num, num → num) → C) → " +
		"prod(num, num → num) → " +
		"C",
	Equations: []string{
		"∀R:ring_ops(B). " +
			"∀F:(set(A) → module_ops(B, C)). " +
			"∀res:(set(A) → set(A) → C → C). " +
			"∀U:(num → set(A)). " +
			"∀n:num. " +
			"∀w:(prod(num, num → num) → C). " +
			"∀t:prod(num, num → num). " +
			"    cech_differential(R, F, res, U, n, w, t) = " +
			"    COND(t ∈ cech_indices(n + 1), " +
			"        module_sum(F(cech_meet(U, t)).add, " +
			"            F(cech_meet(U, t)).zero, " +
			"            0 .. n + 1, " +
			"            λi:num. " +
			"                F(cech_meet(U, t)).smul(alternating_sign(R.one, R.neg, i), " +
			"                    res(cech_meet(U, cech_delete(t, i)), " +
			"                        cech_meet(U, t), " +
			"                        w(cech_delete(t, i))))), " +
			"        cech_zero(F, U, t))",
	},
	Deps: []registry.EntryLike{cechDeleteDef, cechIndicesDef, cechMeetDef, cechZeroDef},
	Reading: "The alternating restriction sum has n+2 " +
		"terms and is normalized outside the target degree.",
})}

// CechComplexDef — One complex record holds every degree on the normalized tuple-function host.
var CechComplexDef = cechComplexDefThm{family.Define(registry.DefEntry{
	Name:  "CechComplexDef",
	Key:   "prop_de527a57739b133c",
	Const: "cech_complex",
	Type: "ring_ops(B) → " +
		"(set(A) → module_ops(B, C)) → " +
		"(set(A) → set(A) → C → C) → " +
		"(num → set(A)) → " +
		"complex_ops(B, prod(num, num → num) → C)",
	Equations: []string{
		"∀R:ring_ops(B). " +
			"∀F:(set(A) → module_ops(B, C)). " +
			"∀res:(set(A) → set(A) → C → C). " +
			"∀U:(num → set(A)). " +
			"    cech_complex(R, F, res, U) = " +
			"    pack_complex(λv:(prod(num, num → num) → C). " +
			"        λw:(prod(num, num → num) → C). " +
			"        λt:prod(num, num → num). " +
			"            F(cech_meet(U, t)).add(v(t), w(t)), " +
			"        cech_zero(F, U), " +
			"        λw:(prod(num, num → num) → C). λt:prod(num, num → num). F(cech_meet(U, t)).neg(w(t)), " +
			"        λa:B. λw:(prod(num, num → num) → C). λt:prod(num, num → num). " +
			"            F(cech_meet(U, t)).smul(a, w(t)), " +
			"        cech_terms(F, U), " +
			"        cech_differential(R, F, res, U))",
	},
	Deps:    []registry.EntryLike{cechDifferentialDef, cechMeetDef, cechTermsDef, cechZeroDef},
	Reading: "One complex record holds every degree on the normalized tuple-function host.",
})}

// cechTopologiesDef — A countable product of discrete section groups, with prescribed inactive coordinates.
var cechTopologiesDef = cechTopologiesDefThm{family.Define(registry.DefEntry{
	Name:  "cechTopologiesDef",
	Key:   "prop_682acb91ce0fb24b",
	Const: "cech_topologies",
	Type: "(set(A) → module_ops(B, C)) → " +
		"(num → set(A)) → " +
		"num → " +
		"set(set(prod(num, num → num) → C))",
	Equations: []string{
		"∀F:(set(A) → module_ops(B, C)). ∀U:(num → set(A)). ∀n:num. " +
			"    cech_topologies(F, U, n) = " +
			"    indexed_discrete_topology(cech_indices(n), " +
			"        cech_zero(F, U), " +
			"        λt:prod(num, num → num). F(cech_meet(U, t)).carrier)",
	},
	Deps:    []registry.EntryLike{cechIndicesDef, cechMeetDef, cechZeroDef},
	Reading: "A countable product of discrete section groups, with prescribed inactive coordinates.",
})}

// cechRefinementMapDef — A refined output coordinate reads one old coordinate and restricts it to the refined intersection.
var cechRefinementMapDef = cechRefinementMapDefThm{family.Define(registry.DefEntry{
	Name:  "cechRefinementMapDef",
	Key:   "prop_4d0f63b786652758",
	Const: "cech_refinement_map",
	Type: "(set(A) → module_ops(B, C)) → " +
		"(set(A) → set(A) → C → C) → " +
		"(num → set(A)) → " +
		"(num → set(A)) → " +
		"(num → num) → " +
		"num → " +
		"(prod(num, num → num) → C) → " +
		"prod(num, num → num) → " +
		"C",
	Equations: []string{
		"∀F:(set(A) → module_ops(B, C)). " +
			"∀res:(set(A) → set(A) → C → C). " +
			"∀U V:(num → set(A)). " +
			"∀r:(num → num). " +
			"∀n:num. " +
			"∀w:(prod(num, num → num) → C). " +
			"∀t:prod(num, num → num). " +
			"    cech_refinement_map(F, res, U, V, r, n, w, t) = " +
			"    COND(t ∈ cech_indices(n), " +
			"        res(cech_meet(U, cech_refine_tuple(r, t)), " +
			"            cech_meet(V, t), " +
			"            w(cech_refine_tuple(r, t))), " +
			"        cech_zero(F, V, t))",
	},
	Deps: []registry.EntryLike{cechIndicesDef, cechMeetDef, cechRefineTupleDef, cechZeroDef},
	Reading: "A refined output coordinate reads one old " +
		"coordinate and restricts it to the refined intersection.",
})}
