// family.go — the biaffine_deformation family manifest: the registry
// handle every member registers into, and the family's ONE shared
// recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=biaffine_deformation.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/biaffine_deformation go test -run TestRecordFamilyCNF ./library/integrity/gates/

package biaffine_deformation

import (
	_ "embed"

	// The chapters whose constants the definitions spell, initialized
	// before them.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/algebra_deformation"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/square_zero_classification"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/transitivity"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_extension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/square_zero_extension"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed biaffine_deformation.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// biaffine_deformation/biaffine_deformation.cnf.pb from the name's
// basename, and the registered entry prefix is
// `biaffine_deformation.<Member>`.
var family = registry.NewFamily("scheme/biaffine_deformation", familyCNF).WithAbbrev(Abbrev{
	{Name: "wg3Derivations", Text: "biaffine_overlap_derivations(P, h, A₀₁, V, M)"},
	{Name: "wg3Pair", Text: "biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)"},
	{Name: "wg3Module0", Text: "restrict_module(V, fst(M))"},
	{Name: "wg3Module1", Text: "restrict_module(V, snd(M))"},
	{Name: "wg3Overlap", Text: "restrict_module(V, lattice_pair_ambient(A₀₁, V, M))"},
	{Name: "wg3LocalClass", Text: "biaffine_local_class⟨U:U⟩(P, h, A₀₁, A₀, A₁, V, M)"},
	{Name: "wg3Restriction0", Text: "cotangent_cohomology_restriction(P, " +
		"    restrict_ring(A₀₁, A₀), " +
		"    h, " +
		"    A₀₁, " +
		"    λc:C. c, " +
		"    «wg3Overlap», " +
		"    λv:D. v, " +
		"    1)"},
	{Name: "wg3Restriction1", Text: "cotangent_cohomology_restriction(P, " +
		"    restrict_ring(A₀₁, A₁), " +
		"    h, " +
		"    A₀₁, " +
		"    λc:C. c, " +
		"    «wg3Overlap», " +
		"    λv:D. v, " +
		"    1)"},
	{Name: "wg3LocalObstruction", Text: "biaffine_local_obstruction⟨U:U⟩(R, " +
		"    R₀, " +
		"    f, " +
		"    g, " +
		"    A₀₁, " +
		"    A₀, " +
		"    A₁, " +
		"    V, " +
		"    M, " +
		"    ι)"},
	{Name: "wg3SecondZero0", Text: "cotangent_cohomology(R₀, " +
		"    restrict_ring(A₀₁, A₀), " +
		"    g, " +
		"    restrict_ring(A₀₁, A₀), " +
		"    λc:C. c, " +
		"    restrict_module(V, fst(M)), " +
		"    2).zero"},
	{Name: "wg3SecondZero1", Text: "cotangent_cohomology(R₀, " +
		"    restrict_ring(A₀₁, A₁), " +
		"    g, " +
		"    restrict_ring(A₀₁, A₁), " +
		"    λc:C. c, " +
		"    restrict_module(V, snd(M)), " +
		"    2).zero"},
	{Name: "wg3LocalZero", Text: "(«wg3SecondZero0», «wg3SecondZero1»)"},
	{Name: "wg3ThickeningRestriction0", Text: "cotangent_cohomology_restriction(R, " +
		"    restrict_ring(A₀₁, A₀), " +
		"    λa:A. g(f(a)), " +
		"    A₀₁, " +
		"    λc:C. c, " +
		"    «wg3Overlap», " +
		"    λv:D. v, " +
		"    1)"},
	{Name: "wg3ThickeningRestriction1", Text: "cotangent_cohomology_restriction(R, " +
		"    restrict_ring(A₀₁, A₁), " +
		"    λa:A. g(f(a)), " +
		"    A₀₁, " +
		"    λc:C. c, " +
		"    «wg3Overlap», " +
		"    λv:D. v, " +
		"    1)"},
	{Name: "wg3OverReduced", Text: "mk_module(V.add, V.zero, V.neg, λb:B. λm:D. V.smul(g(b), m))"},
	{Name: "wg3Cokernel", Text: "biaffine_gluing_cokernel(R₀, g, A₀₁, A₀, A₁, V, M)"},
	{Name: "wg3GluingObstruction", Text: "biaffine_gluing_obstruction(R, R₀, f, g, A₀₁, A₀, A₁, V, M)"},
	{Name: "wg3Deformation", Text: "biaffine_deformation(R, R₀, f, g, A₀₁, A₀, A₁, t, s, V, M, ι)"},
})
