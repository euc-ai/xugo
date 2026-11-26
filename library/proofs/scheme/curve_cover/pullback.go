// pullback.go — the chapter's pullback statements.

package curve_cover

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_sequence"
	"github.com/euc-ai/xugo/library/registry"
)

// CoverDegreeCharts — Both extension bases have the positive cover degree as their size.
var CoverDegreeCharts = coverDegreeChartsThm{family.Add(registry.ProofEntry{
	Name: "CoverDegreeCharts",
	Key:  "prop_cc18ddf4a30512bc",
	Deps: []registry.EntryLike{CurveCoverDef, module_dimension.DimBasis, module_dimension.DimZero},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁ E₀ E₁:set(A).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"finite(E₀)",
			"finite(E₁)",
			"module_basis(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), E₀)",
			"module_basis(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), E₁)",
		},
		Conclusion: "card(E₀) = cover_degree(field_ring(L), K) ∧ " +
			"card(E₁) = cover_degree(field_ring(L), K) ∧ " +
			"0 < cover_degree(field_ring(L), K)",
	},
		"Both finite bases measure dim_K L. The field is nonzero, so that dimension is positive."),
})}

// CoverOverlapBasis — A chart-zero extension basis remains a basis on the overlap.
var CoverOverlapBasis = coverOverlapBasisThm{family.Add(registry.ProofEntry{
	Name: "CoverOverlapBasis",
	Key:  "prop_9ce686b74ca97f89",
	Deps: []registry.EntryLike{
		CurveCoverDef,
		ring_away.RingAwayDef,
		linear_independence.ModuleBasisDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁ E:set(A).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"finite(E)",
			"module_basis(restrict_ring(field_ring(L), A₀), " +
				"    restrict_module(regular_module(field_ring(L)), B₀), " +
				"    E)",
			"module_basis(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), E)",
		},
		Conclusion: "module_basis(restrict_ring(field_ring(L), A₀₁), " +
			"    restrict_module(regular_module(field_ring(L)), B₀₁), " +
			"    E)",
	},
		"Localize the chart-zero basis at t. Both overlaps are the corresponding "+
			"chart localizations; independence follows by clearing a common denominator."),
})}

// CoverPullbackDirectSum — A pulled-back chart module has unique coefficients along the extension basis.
var CoverPullbackDirectSum = coverPullbackDirectSumThm{family.Add(registry.ProofEntry{
	Name: "CoverPullbackDirectSum",
	Key:  "prop_c998274a7c525526",
	Deps: []registry.EntryLike{
		linear_independence.IndependentUniqueCoefficients,
		linear_independence.SpanMembership,
		fractional_ideal.FractionalMulDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁ S B E N:set(A).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"S ⊆ K",
			"S ⊆ B",
			"subring(field_ring(L), B)",
			"finite(E)",
			"module_basis(restrict_ring(field_ring(L), S), " +
				"    restrict_module(regular_module(field_ring(L)), B), " +
				"    E)",
			"module_basis(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), E)",
			"submodule(restrict_ring(field_ring(L), S), restrict_module(regular_module(field_ring(L)), K), N)",
		},
		Conclusion: "(∀z:A. " +
			"    z ∈ fractional_mul(field_ring(L), B, N, B) ⇔ " +
			"    ∃a:(A → A). (∀e:A. e ∈ E ⇒ a(e) ∈ N) ∧ z = module_sum(L.add, L.zero, E, λe:A. a(e) * e)) ∧ " +
			"(∀a b:(A → A). " +
			"    (∀e:A. e ∈ E ⇒ a(e) ∈ N ∧ b(e) ∈ N) ∧ " +
			"    module_sum(L.add, L.zero, E, λe:A. a(e) * e) = " +
			"    module_sum(L.add, L.zero, E, λe:A. b(e) * e) ⇒ " +
			"    ∀e:A. e ∈ E ⇒ a(e) = b(e))",
	},
		"Expand the B-factor in its S-basis and collect the N-coefficients. K-independence "+
			"of E gives uniqueness; the finite sum is the internal direct sum of N·e."),
})}

// CoverPullbackLattice — Pullback is a lattice pair with the scalar-extended overlap ambient.
var CoverPullbackLattice = coverPullbackLatticeThm{family.Add(registry.ProofEntry{
	Name: "CoverPullbackLattice",
	Key:  "prop_9167bbf9a0c4dfc3",
	Deps: []registry.EntryLike{CoverOverlapBasis, CoverPullbackDirectSum, lattice_pair.LatticePairDef},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"lattice_pair(restrict_ring(field_ring(L), A₀₁), " +
				"    A₀, " +
				"    A₁, " +
				"    restrict_module(regular_module(field_ring(L)), K), " +
				"    M)",
		},
		Conclusion: "lattice_pair(restrict_ring(field_ring(L), B₀₁), " +
			"    B₀, " +
			"    B₁, " +
			"    regular_module(field_ring(L)), " +
			"    cover_pullback(field_ring(L), B₀, B₁, M)) ∧ " +
			"lattice_pair_ambient(restrict_ring(field_ring(L), B₀₁), " +
			"    regular_module(field_ring(L)), " +
			"    cover_pullback(field_ring(L), B₀, B₁, M)) = " +
			"cover_pullback_ambient(field_ring(L), " +
			"    B₀₁, " +
			"    lattice_pair_ambient(restrict_ring(field_ring(L), A₀₁), " +
			"        restrict_module(regular_module(field_ring(L)), K), " +
			"        M))",
	},
		"Scalar extension carries each chart submodule into L. The two localized "+
			"spans agree by CoverOverlapBasis and the base lattice equality."),
})}

// CoverPullbackStructure — Pullback carries the base structure pair to the source structure pair.
var CoverPullbackStructure = coverPullbackStructureThm{family.Add(registry.ProofEntry{
	Name: "CoverPullbackStructure",
	Key:  "prop_bd621b15c21a71fe",
	Deps: []registry.EntryLike{CurveCoverDef, fractional_ideal.FractionalMulDef},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
		},
		Conclusion: "cover_pullback(field_ring(L), B₀, B₁, (A₀, A₁)) = (B₀, B₁)",
	},
		"The inclusions of chart rings and the common unit give B_i A_i=B_i."),
})}

// CoverPullbackMul — Pullback preserves products of lattice pairs.
var CoverPullbackMul = coverPullbackMulThm{family.Add(registry.ProofEntry{
	Name: "CoverPullbackMul",
	Key:  "prop_7e479791c7fb8dd2",
	Deps: []registry.EntryLike{
		fractional_ideal.FractionalMulAssoc,
		fractional_ideal.FractionalMulComm,
		CoverPullbackLattice,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"lattice_pair(restrict_ring(field_ring(L), A₀₁), " +
				"    A₀, " +
				"    A₁, " +
				"    restrict_module(regular_module(field_ring(L)), K), " +
				"    M)",
			"lattice_pair(restrict_ring(field_ring(L), A₀₁), " +
				"    A₀, " +
				"    A₁, " +
				"    restrict_module(regular_module(field_ring(L)), K), " +
				"    N)",
		},
		Conclusion: "cover_pullback(field_ring(L), " +
			"    B₀, " +
			"    B₁, " +
			"    lattice_pair_mul(restrict_ring(field_ring(L), K), A₀, A₁, M, N)) = " +
			"lattice_pair_mul(field_ring(L), " +
			"    B₀, " +
			"    B₁, " +
			"    cover_pullback(field_ring(L), B₀, B₁, M), " +
			"    cover_pullback(field_ring(L), B₀, B₁, N))",
	},
		"Associate finite products chartwise: B_i(M_iN_i)=(B_iM_i)(B_iN_i)."),
})}

// CoverPullbackInvertible — Pullback preserves invertibility and its inverse.
var CoverPullbackInvertible = coverPullbackInvertibleThm{family.Add(registry.ProofEntry{
	Name: "CoverPullbackInvertible",
	Key:  "prop_8d0dfb0581d8de5d",
	Deps: []registry.EntryLike{
		CoverPullbackMul,
		CoverPullbackStructure,
		CoverPullbackLattice,
		invertible_lattice_pair.InvertibleLatticeInverse,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"invertible_lattice_pair(restrict_ring(field_ring(L), K), A₀, A₁, A₀₁, M)",
		},
		Conclusion: "invertible_lattice_pair(field_ring(L), " +
			"    B₀, " +
			"    B₁, " +
			"    B₀₁, " +
			"    cover_pullback(field_ring(L), B₀, B₁, M)) ∧ " +
			"lattice_pair_inverse(field_ring(L), B₀, B₁, cover_pullback(field_ring(L), B₀, B₁, M)) = " +
			"cover_pullback(field_ring(L), " +
			"    B₀, " +
			"    B₁, " +
			"    lattice_pair_inverse(restrict_ring(field_ring(L), K), A₀, A₁, M))",
	},
		"Pull back M M^-1=O and use multiplicativity and the structure identity. "+
			"The pulled-back inverse witnesses invertibility on both charts."),
})}

// CoverPullbackQuotientDim — Pullback multiplies each finite quotient dimension by the cover degree.
var CoverPullbackQuotientDim = coverPullbackQuotientDimThm{family.Add(registry.ProofEntry{
	Name: "CoverPullbackQuotientDim",
	Key:  "prop_3bca439cb07b190e",
	Deps: []registry.EntryLike{CoverPullbackDirectSum, CoverDegreeCharts, module_dimension.DimBasis},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K k:set(A). ∀t:A. ∀A₀ A₁ A₀₁ B₀ B₁ B₀₁ S B E N N₂:set(A).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"S ⊆ K",
			"k ⊆ S",
			"S ⊆ B",
			"subring(field_ring(L), B)",
			"finite(E)",
			"module_basis(restrict_ring(field_ring(L), S), " +
				"    restrict_module(regular_module(field_ring(L)), B), " +
				"    E)",
			"module_basis(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), E)",
			"submodule(restrict_ring(field_ring(L), S), restrict_module(regular_module(field_ring(L)), K), N)",
			"submodule(restrict_ring(field_ring(L), S), restrict_module(regular_module(field_ring(L)), K), N₂)",
			"N₂ ⊆ N",
			"finite_dimensional(restrict_ring(field_ring(L), k), " +
				"    quotient_module(restrict_module(regular_module(field_ring(L)), N), N₂))",
		},
		Conclusion: "finite_dimensional(restrict_ring(field_ring(L), k), " +
			"    quotient_module( " +
			"        restrict_module(regular_module(field_ring(L)), fractional_mul(field_ring(L), B, N, B)), " +
			"        fractional_mul(field_ring(L), B, N₂, B))) ∧ " +
			"module_dim(restrict_ring(field_ring(L), k), " +
			"    quotient_module( " +
			"        restrict_module(regular_module(field_ring(L)), fractional_mul(field_ring(L), B, N, B)), " +
			"        fractional_mul(field_ring(L), B, N₂, B))) = " +
			"cover_degree(field_ring(L), K) * " +
			"module_dim(restrict_ring(field_ring(L), k), " +
			"    quotient_module(restrict_module(regular_module(field_ring(L)), N), N₂))",
	},
		"The coefficient expansion identifies the quotient with a finite direct sum of card(E) copies "+
			"of N/N′ over k. A finite basis of N/N′ in each E-coordinate gives its basis and dimension."),
})}

// CoverPullbackSubpairFinite — Finiteness descends to a subpair and its pullback through finite chart quotients.
var CoverPullbackSubpairFinite = coverPullbackSubpairFiniteThm{family.Add(registry.ProofEntry{
	Name: "CoverPullbackSubpairFinite",
	Key:  "prop_d10f66d87036d554",
	Deps: []registry.EntryLike{
		CoverPullbackQuotientDim,
		CoverPullbackLattice,
		lattice_pair_sequence.EulerSubpairFinite,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"lattice_pair(restrict_ring(field_ring(L), A₀₁), " +
				"    A₀, " +
				"    A₁, " +
				"    restrict_module(regular_module(field_ring(L)), K), " +
				"    M)",
			"lattice_pair(restrict_ring(field_ring(L), A₀₁), " +
				"    A₀, " +
				"    A₁, " +
				"    restrict_module(regular_module(field_ring(L)), K), " +
				"    N)",
			"fst(N) ⊆ fst(M)",
			"snd(N) ⊆ snd(M)",
			"finite_dimensional(restrict_ring(field_ring(L), k), " +
				"    quotient_module(restrict_module(regular_module(field_ring(L)), fst(M)), fst(N)))",
			"finite_dimensional(restrict_ring(field_ring(L), k), " +
				"    quotient_module(restrict_module(regular_module(field_ring(L)), snd(M)), snd(N)))",
			"lattice_pair_finite(restrict_ring(field_ring(L), A₀₁), " +
				"    k, " +
				"    restrict_module(regular_module(field_ring(L)), K), " +
				"    M)",
			"lattice_pair_finite(restrict_ring(field_ring(L), B₀₁), " +
				"    k, " +
				"    regular_module(field_ring(L)), " +
				"    cover_pullback(field_ring(L), B₀, B₁, M))",
		},
		Conclusion: "lattice_pair_finite(restrict_ring(field_ring(L), A₀₁), " +
			"    k, " +
			"    restrict_module(regular_module(field_ring(L)), K), " +
			"    N) ∧ " +
			"lattice_pair_finite(restrict_ring(field_ring(L), B₀₁), " +
			"    k, " +
			"    regular_module(field_ring(L)), " +
			"    cover_pullback(field_ring(L), B₀, B₁, N))",
	},
		"Apply EulerSubpairFinite to N⊆M and to their pullbacks. CoverPullbackQuotientDim supplies "+
			"finite chart quotients on the source curve. This works even when N is not invertible."),
})}

// CoverPullbackEuler — Pullback multiplies a finite subpair Euler difference by the cover degree.
var CoverPullbackEuler = coverPullbackEulerThm{family.Add(registry.ProofEntry{
	Name: "CoverPullbackEuler",
	Key:  "prop_84eb625b10f9015f",
	Deps: []registry.EntryLike{
		CoverPullbackQuotientDim,
		CoverOverlapBasis,
		CoverPullbackLattice,
		lattice_pair_sequence.EulerAdditive,
		lattice_pair.QuotientDimLocalizes,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀M N:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"lattice_pair(restrict_ring(field_ring(L), A₀₁), " +
				"    A₀, " +
				"    A₁, " +
				"    restrict_module(regular_module(field_ring(L)), K), " +
				"    M)",
			"lattice_pair(restrict_ring(field_ring(L), A₀₁), " +
				"    A₀, " +
				"    A₁, " +
				"    restrict_module(regular_module(field_ring(L)), K), " +
				"    N)",
			"fst(N) ⊆ fst(M)",
			"snd(N) ⊆ snd(M)",
			"finite_dimensional(restrict_ring(field_ring(L), k), " +
				"    quotient_module(restrict_module(regular_module(field_ring(L)), fst(M)), fst(N)))",
			"finite_dimensional(restrict_ring(field_ring(L), k), " +
				"    quotient_module(restrict_module(regular_module(field_ring(L)), snd(M)), snd(N)))",
			"lattice_pair_finite(restrict_ring(field_ring(L), A₀₁), " +
				"    k, " +
				"    restrict_module(regular_module(field_ring(L)), K), " +
				"    N)",
			"lattice_pair_finite(restrict_ring(field_ring(L), B₀₁), " +
				"    k, " +
				"    regular_module(field_ring(L)), " +
				"    cover_pullback(field_ring(L), B₀, B₁, N))",
		},
		Conclusion: "lattice_pair_euler(restrict_ring(field_ring(L), B₀₁), " +
			"    k, " +
			"    regular_module(field_ring(L)), " +
			"    cover_pullback(field_ring(L), B₀, B₁, M)) - " +
			"lattice_pair_euler(restrict_ring(field_ring(L), B₀₁), " +
			"    k, " +
			"    regular_module(field_ring(L)), " +
			"    cover_pullback(field_ring(L), B₀, B₁, N)) = " +
			"int_of_num(cover_degree(field_ring(L), K)) * " +
			"(lattice_pair_euler(restrict_ring(field_ring(L), A₀₁), " +
			"        k, " +
			"        restrict_module(regular_module(field_ring(L)), K), " +
			"        M) - " +
			"    lattice_pair_euler(restrict_ring(field_ring(L), A₀₁), " +
			"        k, " +
			"        restrict_module(regular_module(field_ring(L)), K), " +
			"        N))",
	},
		"QuotientDimLocalizes supplies finite overlap quotients from the finite chart "+
			"quotients. CoverPullbackQuotientDim multiplies all three quotient dimensions by the "+
			"cover degree, and EulerAdditive on both curves gives the Euler difference formula."),
})}

// CoverPullbackFinite — An invertible pair has finite cohomology after pullback.
var CoverPullbackFinite = coverPullbackFiniteThm{family.Add(registry.ProofEntry{
	Name: "CoverPullbackFinite",
	Key:  "prop_712a42a16521fe00",
	Deps: []registry.EntryLike{CoverPullbackInvertible, algebraic_curve.InvertibleFinite},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"invertible_lattice_pair(restrict_ring(field_ring(L), K), A₀, A₁, A₀₁, M)",
		},
		Conclusion: "lattice_pair_finite(restrict_ring(field_ring(L), B₀₁), " +
			"    k, " +
			"    regular_module(field_ring(L)), " +
			"    cover_pullback(field_ring(L), B₀, B₁, M))",
	},
		"The pullback is invertible by CoverPullbackInvertible; apply InvertibleFinite on X."),
})}

// CoverDegreeMultiplicative — Pullback multiplies the degree of an invertible pair by the cover degree.
var CoverDegreeMultiplicative = coverDegreeMultiplicativeThm{family.Add(registry.ProofEntry{
	Name: "CoverDegreeMultiplicative",
	Key:  "prop_b088187cda6ff48f",
	Reading: "The meet N=M∩O need not be invertible on a singular curve. Its finiteness comes " +
		"from the finite quotient interface, so the proof does not silently narrow to smooth curves.",
	Deps: []registry.EntryLike{
		CoverPullbackEuler,
		CoverPullbackSubpairFinite,
		CoverPullbackFinite,
		CoverPullbackStructure,
		algebraic_curve.InvertibleMeetStructure,
		algebraic_curve.StructureFinite,
		curve_degree.CurveDegreeDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). " +
			"∀K k:set(A). " +
			"∀t:A. " +
			"∀A₀ A₁ A₀₁ B₀ B₁ B₀₁:set(A). " +
			"∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_cover(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)",
			"invertible_lattice_pair(restrict_ring(field_ring(L), K), A₀, A₁, A₀₁, M)",
		},
		Conclusion: "curve_degree(field_ring(L), " +
			"    k, " +
			"    B₀, " +
			"    B₁, " +
			"    B₀₁, " +
			"    cover_pullback(field_ring(L), B₀, B₁, M)) = " +
			"int_of_num(cover_degree(field_ring(L), K)) * " +
			"curve_degree(restrict_ring(field_ring(L), K), k, A₀, A₁, A₀₁, M)",
	},
		"Compare M and O with N=(M₀∩A₀,M₁∩A₁). InvertibleMeetStructure gives "+
			"finite quotients, and CoverPullbackSubpairFinite gives finite cohomology "+
			"for N and its pullback from O. Subtract CoverPullbackEuler at N⊆M and N⊆O."),
})}
