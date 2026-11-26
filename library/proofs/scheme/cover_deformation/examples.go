package cover_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/derived_limit"
	"github.com/euc-ai/xugo/library/registry"
)

var nodalChainCoverDef = nodalChainCoverDefThm{family.Define(registry.DefEntry{
	Name:  "nodalChainCoverDef",
	Key:   "prop_bc687fc4b1b5509",
	Const: "nodal_chain_cover",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(num)) → " +
		"(set(num) → A → num) → " +
		"(set(num) → set(num) → num → num) → " +
		"(set(num) → set(num) → num) → " +
		"(num → num) → " +
		"(num → num) → " +
		"(num → num) → " +
		"(num → set(num) → num) → " +
		"bool",
	Equations: []string{
		"∀K:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(num)). " +
			"∀f:(set(num) → A → num). " +
			"∀g:(set(num) → set(num) → num → num). " +
			"∀t:(set(num) → set(num) → num). " +
			"∀a b:(num → num). " +
			"∀φ₀:(num → num). " +
			"∀φ:(num → set(num) → num). " +
			"    nodal_chain_cover(K, S, f, g, t, a, b, φ₀, φ) ⇔ " +
			"    cover_datum(K, S, f, λσ:set(num). regular_module(S(σ)), g, g, t) ∧ " +
			"    ring_isomorphism(universe_algebra_ring⟨U:num⟩(K, {0}), S({0}), φ₀) ∧ " +
			"    a(0) = φ₀(universe_algebra_var⟨U:num⟩(K, 0)) ∧ " +
			"    b(0) = a(0) ∧ " +
			"    (∀r:A. r ∈ K.carrier ⇒ φ₀(universe_algebra_const⟨U:num⟩(K, r)) = f({0}, r)) ∧ " +
			"    (∀n:num. " +
			"        ring_isomorphism(ideal_quotient_ring(universe_algebra_ring⟨U:num⟩(K, {0, 1}), " +
			"                ideal_span(universe_algebra_ring⟨U:num⟩(K, {0, 1}), " +
			"                    {universe_algebra_ring⟨U:num⟩(K, {0, 1}).mul( " +
			"                            universe_algebra_var⟨U:num⟩(K, 0), " +
			"                            universe_algebra_var⟨U:num⟩(K, 1))})), " +
			"            S({n + 1}), " +
			"            φ(n)) ∧ " +
			"        a(n + 1) = " +
			"        φ(n, " +
			"            ideal_quotient_projection(universe_algebra_ring⟨U:num⟩(K, {0, 1}), " +
			"                ideal_span(universe_algebra_ring⟨U:num⟩(K, {0, 1}), " +
			"                    {universe_algebra_ring⟨U:num⟩(K, {0, 1}).mul( " +
			"                            universe_algebra_var⟨U:num⟩(K, 0), " +
			"                            universe_algebra_var⟨U:num⟩(K, 1))}))( " +
			"                universe_algebra_var⟨U:num⟩(K, 0))) ∧ " +
			"        b(n + 1) = " +
			"        φ(n, " +
			"            ideal_quotient_projection(universe_algebra_ring⟨U:num⟩(K, {0, 1}), " +
			"                ideal_span(universe_algebra_ring⟨U:num⟩(K, {0, 1}), " +
			"                    {universe_algebra_ring⟨U:num⟩(K, {0, 1}).mul( " +
			"                            universe_algebra_var⟨U:num⟩(K, 0), " +
			"                            universe_algebra_var⟨U:num⟩(K, 1))}))( " +
			"                universe_algebra_var⟨U:num⟩(K, 1))) ∧ " +
			"        (∀r:A. " +
			"            r ∈ K.carrier ⇒ " +
			"            φ(n, " +
			"                ideal_quotient_projection(universe_algebra_ring⟨U:num⟩(K, {0, 1}), " +
			"                    ideal_span(universe_algebra_ring⟨U:num⟩(K, {0, 1}), " +
			"                        {universe_algebra_ring⟨U:num⟩(K, {0, 1}).mul( " +
			"                                universe_algebra_var⟨U:num⟩(K, 0), " +
			"                                universe_algebra_var⟨U:num⟩(K, 1))}))( " +
			"                    universe_algebra_const⟨U:num⟩(K, r))) = " +
			"            f({n + 1}, r))) ∧ " +
			"    (∀n:num. " +
			"        t({n}, {n, n + 1}) = b(n) ∧ " +
			"        t({n + 1}, {n, n + 1}) = a(n + 1) ∧ " +
			"        S({n, n + 1}).mul(g({n}, {n, n + 1}, b(n)), g({n + 1}, {n, n + 1}, a(n + 1))) = " +
			"        S({n, n + 1}).one) ∧ " +
			"    (∀i j:num. i + 1 < j ⇒ S({i, j}).one = S({i, j}).zero)",
	},
	Deps: []registry.EntryLike{coverDatumDef},
	Reading: "An affine line at the left end and countably many node charts K[x,y]/(xy), " +
		"adjacent branches glued by reciprocal coordinates; nonadjacent overlaps are empty. " +
		"This is the affine-cover datum of a one-sided infinite chain of projective lines."})}

var NodalChainCoverExists = nodalChainCoverExistsThm{family.Add(registry.ProofEntry{
	Name: "NodalChainCoverExists",
	Key:  "prop_ab009e5a65efdddf",
	Build: family.Card(
		Statement{
			Binders: "∀K:ring_ops(A).",
			Hypotheses: []string{
				"∃F:field_ops(A). field_on(F) ∧ field_ring(F) = K",
				"countable(K.carrier)",
				"cotangent_universe(K, 𝕌⟨A:num⟩)",
			},
			Conclusion: "∃S:(set(num) → ring_ops(num)). " +
				"∃f:(set(num) → A → num). " +
				"∃g:(set(num) → set(num) → num → num). " +
				"∃t:(set(num) → set(num) → num). " +
				"∃a b:(num → num). " +
				"∃φ₀:(num → num). " +
				"∃φ:(num → set(num) → num). " +
				"    nodal_chain_cover(K, S, f, g, t, a, b, φ₀, φ)",
		},
		"Use the displayed node and affine-line rings, Laurent overlaps on adjacent "+
			"charts and the zero ring elsewhere. Enumerate the countable rings into num and "+
			"transport the maps; the reciprocal formulas make all intersection maps strict."),
	Deps: []registry.EntryLike{nodalChainCoverDef},
	Reading: "Use the displayed node and affine-line rings, Laurent overlaps on adjacent " +
		"charts and the zero ring elsewhere. Enumerate the countable rings into num and " +
		"transport the maps; the reciprocal formulas make all intersection maps strict.",
})}

var NodalChainAQCalibration = nodalChainAQCalibrationThm{family.Add(registry.ProofEntry{
	Name: "NodalChainAQCalibration",
	Key:  "prop_3a752a7d75a4c287",
	Build: family.Card(
		Statement{
			Binders: "∀K:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(num)). " +
				"∀f:(set(num) → A → num). " +
				"∀g:(set(num) → set(num) → num → num). " +
				"∀t:(set(num) → set(num) → num). " +
				"∀a b:(num → num). " +
				"∀φ₀:(num → num). " +
				"∀φ:(num → set(num) → num).",
			Hypotheses: []string{
				"∃F:field_ops(A). field_on(F) ∧ field_ring(F) = K",
				"countable(K.carrier)",
				"cotangent_universe(K, 𝕌⟨A:num⟩)",
				"nodal_chain_cover(K, S, f, g, t, a, b, φ₀, φ)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ cotangent_universe(S(σ), 𝕌⟨A:num⟩)",
			},
			Conclusion: "(∀n:num. ∃h:(set(num → num) → A). " +
				"    module_isomorphism(K, " +
				"        cover_aq_module⟨U:num⟩(K, S, f, λσ:set(num). regular_module(S(σ)), 1)({n + 1}), " +
				"        regular_module(K), " +
				"        h)) ∧ " +
				"(∀σ:set(num). " +
				"    σ ∈ intersection_indices ∧ ¬(∃n:num. σ = {n + 1}) ⇒ " +
				"    cover_aq_module⟨U:num⟩(K, S, f, λσ:set(num). regular_module(S(σ)), 1)(σ).carrier = " +
				"    {cover_aq_module⟨U:num⟩(K, S, f, λσ:set(num). regular_module(S(σ)), 1)(σ).zero}) ∧ " +
				"cohomology(intersection_cech_complex(K, " +
				"        cover_aq_module⟨U:num⟩(K, S, f, λσ:set(num). regular_module(S(σ)), 1), " +
				"        cover_aq_restriction⟨U:num⟩(K, S, f, λσ:set(num). regular_module(S(σ)), g, g, 1)), " +
				"    1) = " +
				"{coboundaries(intersection_cech_complex(K, " +
				"            cover_aq_module⟨U:num⟩(K, S, f, λσ:set(num). regular_module(S(σ)), 1), " +
				"            cover_aq_restriction⟨U:num⟩(K, S, f, λσ:set(num). regular_module(S(σ)), g, g, 1)), " +
				"        1)} ∧ " +
				"cohomology(intersection_cech_complex(K, " +
				"        cover_derivation_module(K, S, f, λσ:set(num). regular_module(S(σ))), " +
				"        cover_derivation_restriction(K, S, f, λσ:set(num). regular_module(S(σ)), g, g)), " +
				"    2) = " +
				"{coboundaries(intersection_cech_complex(K, " +
				"            cover_derivation_module(K, S, f, λσ:set(num). regular_module(S(σ))), " +
				"            cover_derivation_restriction(K, S, f, λσ:set(num). regular_module(S(σ)), g, g)), " +
				"        2)} ∧ " +
				"(∃h:(set(prod(num, num → num) → set(num → num)) → num → A). " +
				"    module_isomorphism(K, " +
				"        cohomology_module(intersection_cech_complex(K, " +
				"                cover_aq_module⟨U:num⟩(K, S, f, λσ:set(num). regular_module(S(σ)), 1), " +
				"                cover_aq_restriction⟨U:num⟩(K, " +
				"                    S, " +
				"                    f, " +
				"                    λσ:set(num). regular_module(S(σ)), " +
				"                    g, " +
				"                    g, " +
				"                    1)), " +
				"            0), " +
				"        sequence_module(λn:num. regular_module(K)), " +
				"        h))",
		},
		"For a node, the hypersurface relation xy gives T1=K[x,y]/(xy,x,y)=K. The "+
			"affine line and Laurent overlaps are smooth, and triple overlaps are "+
			"empty. Thus the T1 Cech complex has only its vertex term, the full "+
			"product over nodes; the Der complex has no nonzero terms above degree one."),
	Deps: []registry.EntryLike{nodalChainCoverDef, AQPresheaf, CoverExtensionExactSequence},
	Reading: "Every finite collection of chart indices misses a node with nonzero " +
		"T1, so the chart datum is genuinely infinite. The compatible local smoothing " +
		"parameters form an infinite product; H1(T1) vanishes in this calibration.",
})}

var projectivePlaneCoverDef = projectivePlaneCoverDefThm{family.Define(registry.DefEntry{
	Name:  "projectivePlaneCoverDef",
	Key:   "prop_9ec3b921326f9051",
	Const: "projective_plane_cover",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(num)) → " +
		"(set(num) → A → num) → " +
		"(set(num) → set(num) → num → num) → " +
		"(set(num) → set(num) → num) → " +
		"(num → num → num) → " +
		"(num → num → num) → " +
		"bool",
	Equations: []string{
		"∀K:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(num)). " +
			"∀f:(set(num) → A → num). " +
			"∀g:(set(num) → set(num) → num → num). " +
			"∀t:(set(num) → set(num) → num). " +
			"∀a:(num → num → num). " +
			"∀φ:(num → num → num). " +
			"    projective_plane_cover(K, S, f, g, t, a, φ) ⇔ " +
			"    cover_datum(K, S, f, λσ:set(num). regular_module(S(σ)), g, g, t) ∧ " +
			"    cover_repeated(S, f, λσ:set(num). regular_module(S(σ)), g, g, λi:num. COND(i < 3, i, 0)) ∧ " +
			"    (∀i:num. " +
			"        i < 3 ⇒ " +
			"        ring_isomorphism(universe_algebra_ring⟨U:num⟩(K, {j:num | j < 3 ∧ ¬(j = i)}), " +
			"            S({i}), " +
			"            φ(i)) ∧ " +
			"        (∀r:A. r ∈ K.carrier ⇒ φ(i, universe_algebra_const⟨U:num⟩(K, r)) = f({i}, r)) ∧ " +
			"        (∀j:num. " +
			"            j < 3 ⇒ " +
			"            a(i, j) = COND(j = i, S({i}).one, φ(i, universe_algebra_var⟨U:num⟩(K, j))))) ∧ " +
			"    (∀i:num. ∀σ:set(num). " +
			"        σ ∈ intersection_indices ∧ σ ⊆ {0, 1, 2} ∧ i ∈ σ ⇒ " +
			"        t({i}, σ) = " +
			"        S({i}).mul(COND(0 ∈ σ, a(i, 0), S({i}).one), " +
			"            S({i}).mul(COND(1 ∈ σ, a(i, 1), S({i}).one), COND(2 ∈ σ, a(i, 2), S({i}).one)))) ∧ " +
			"    (∀i j k:num. " +
			"        i < 3 ∧ j < 3 ∧ k < 3 ⇒ " +
			"        g({i}, {i, j}, a(i, k)) = " +
			"        S({i, j}).mul(g({i}, {i, j}, a(i, j)), g({j}, {i, j}, a(j, k))))",
	},
	Deps: []registry.EntryLike{coverDatumDef, coverRepeatedDef},
	Reading: "The three polynomial standard charts of projective " +
		"two-space, localized at the omitted homogeneous coordinate ratios and " +
		"glued by their ratio identities. Higher indices repeat chart zero."})}

var ProjectivePlaneCoverExists = projectivePlaneCoverExistsThm{family.Add(registry.ProofEntry{
	Name: "ProjectivePlaneCoverExists",
	Key:  "prop_8075cbd85ff7bce0",
	Build: family.Card(
		Statement{
			Binders: "∀K:ring_ops(A).",
			Hypotheses: []string{
				"∃F:field_ops(A). field_on(F) ∧ field_ring(F) = K",
				"countable(K.carrier)",
				"cotangent_universe(K, 𝕌⟨A:num⟩)",
			},
			Conclusion: "∃S:(set(num) → ring_ops(num)). " +
				"∃f:(set(num) → A → num). " +
				"∃g:(set(num) → set(num) → num → num). " +
				"∃t:(set(num) → set(num) → num). " +
				"∃a:(num → num → num). " +
				"∃φ:(num → num → num). " +
				"    projective_plane_cover(K, S, f, g, t, a, φ)",
		},
		"Take the degree-zero parts of the homogeneous localizations of K[X0,X1,X2], one "+
			"for each nonempty subset of the three coordinates, and transport their countable "+
			"carriers to num. The inclusions are strict and satisfy the displayed ratios."),
	Deps: []registry.EntryLike{projectivePlaneCoverDef},
	Reading: "Take the degree-zero parts of the homogeneous localizations of K[X0,X1,X2], " +
		"one for each nonempty subset of the three coordinates, and transport their countable " +
		"carriers to num. The inclusions are strict and satisfy the displayed ratios.",
})}

var ProjectivePlaneTripleCalibration = projectivePlaneTripleCalibrationThm{family.Add(registry.ProofEntry{
	Name: "ProjectivePlaneTripleCalibration",
	Key:  "prop_ac0bd083714cd79b",
	Build: family.Card(
		Statement{
			Binders: "∀K:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(num)). " +
				"∀f:(set(num) → A → num). " +
				"∀g:(set(num) → set(num) → num → num). " +
				"∀t:(set(num) → set(num) → num). " +
				"∀a:(num → num → num). " +
				"∀φ:(num → num → num).",
			Hypotheses: []string{
				"∃F:field_ops(A). field_on(F) ∧ field_ring(F) = K",
				"countable(K.carrier)",
				"cotangent_universe(K, 𝕌⟨A:num⟩)",
				"projective_plane_cover(K, S, f, g, t, a, φ)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ cotangent_universe(S(σ), 𝕌⟨A:num⟩)",
			},
			Conclusion: "(∀σ:set(num). " +
				"    σ ∈ intersection_indices ⇒ " +
				"    cover_aq_module⟨U:num⟩(K, S, f, λσ:set(num). regular_module(S(σ)), 1)(σ).carrier = " +
				"    {cover_aq_module⟨U:num⟩(K, S, f, λσ:set(num). regular_module(S(σ)), 1)(σ).zero} ∧ " +
				"    cover_aq_module⟨U:num⟩(K, S, f, λσ:set(num). regular_module(S(σ)), 2, σ).carrier = " +
				"    {cover_aq_module⟨U:num⟩(K, S, f, λσ:set(num). regular_module(S(σ)), 2, σ).zero}) ∧ " +
				"¬(intersection_cech_complex(K, " +
				"        cover_derivation_module(K, S, f, λσ:set(num). regular_module(S(σ))), " +
				"        cover_derivation_restriction(K, S, f, λσ:set(num). regular_module(S(σ)), g, g)).terms( " +
				"        2) = " +
				"    {intersection_cech_complex(K, " +
				"            cover_derivation_module(K, S, f, λσ:set(num). regular_module(S(σ))), " +
				"            cover_derivation_restriction(K, " +
				"                S, " +
				"                f, " +
				"                λσ:set(num). regular_module(S(σ)), " +
				"                g, " +
				"                g)).zero}) ∧ " +
				"cohomology(intersection_cech_complex(K, " +
				"        cover_derivation_module(K, S, f, λσ:set(num). regular_module(S(σ))), " +
				"        cover_derivation_restriction(K, S, f, λσ:set(num). regular_module(S(σ)), g, g)), " +
				"    2) = " +
				"{coboundaries(intersection_cech_complex(K, " +
				"            cover_derivation_module(K, S, f, λσ:set(num). regular_module(S(σ))), " +
				"            cover_derivation_restriction(K, S, f, λσ:set(num). regular_module(S(σ)), g, g)), " +
				"        2)}",
		},
		"Polynomial charts and their localizations have T1=T2=0. The triple overlap is a "+
			"two-variable Laurent ring with nonzero derivations, so degree-two cochains are present. A "+
			"Laurent-monomial Cech computation, equivalently the Euler sequence and the degree-zero and "+
			"degree-one line-bundle computation on P2, shows H2 of the tangent derivation sheaf is zero."),
	Deps: []registry.EntryLike{
		projectivePlaneCoverDef,
		DerivationPresheaf,
		AQPresheaf,
		SmoothCoverDeformationObstruction,
	},
	Reading: "The triple cocycle equation is genuinely tested even though this particular smooth " +
		"cover has vanishing final obstruction group. Smoothness alone is not the reason H2 vanishes.",
})}
