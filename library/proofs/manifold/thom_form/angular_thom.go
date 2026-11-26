package thom_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/riemannian"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/registry"
)

var AngularRepresentativeExistsUnique = angularRepresentativeExistsUniqueThm{family.Add(registry.ProofEntry{
	Name: "AngularRepresentativeExistsUnique",
	Key:  "prop_3a0a025e312f9573",
	Deps: []registry.EntryLike{
		localAngularDef,
		riemannian.PositiveFrameExists,
		differential_form.FormAtlasExtension,
		vec_form.PfaffianCurvatureClosed,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
				"∀m:num.",
			Hypotheses: []string{
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"riemannian_metric⟨n⟩(T, 𝒜, g)",
				"n = 2 * m + 2",
			},
			Conclusion: "∃ψ:(prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
				"            prod(A, prod(set(A), A → num → real) → num → real) → num → real) → " +
				"        (num → real) → " +
				"        (num → num → real) → " +
				"        real). " +
				"    riemannian_angular_representative⟨n⟩(T, 𝒜, g, ψ) ∧ " +
				"    (∀χ:(prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
				"                prod(A, prod(set(A), A → num → real) → num → real) → num → real) → " +
				"            (num → real) → " +
				"            (num → num → real) → " +
				"            real). " +
				"        riemannian_angular_representative⟨n⟩(T, 𝒜, g, χ) ⇒ χ = ψ)",
		},
		"In positive orthonormal tangent charts form B + tα and apply K to its "+
			"normalized curvature Pfaffian. Gauge covariance and restriction compatibility "+
			"glue these local forms; chartwise form extensionality gives uniqueness."),
})}

var AngularFormDerivative = angularFormDerivativeThm{family.Add(registry.ProofEntry{
	Name: "AngularFormDerivative",
	Key:  "prop_a6c1f781406e507d",
	Deps: []registry.EntryLike{
		AngularRepresentativeExistsUnique,
		vec_form.PfaffianCurvatureClosed,
		vec_form.PfaffianUnitKernel,
		de_rham.HomotopyOperator,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
				"∀m:num.",
			Hypotheses: []string{
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"riemannian_metric⟨n⟩(T, 𝒜, g)",
				"n = 2 * m + 2",
			},
			Conclusion: "manifold_exterior_derivative⟨2 * n⟩(«punctured topology», " +
				"    «punctured atlas», " +
				"    n - 1, " +
				"    riemannian_angular_form⟨n⟩(T, 𝒜, g)) = " +
				"(λc:prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
				"        prod(A, prod(set(A), A → num → real) → num → real) → num → real). " +
				"λy:(num → real). " +
				"λP:(num → num → real). " +
				"    -manifold_form_pullback⟨2 * n, n⟩(«punctured topology», " +
				"        «punctured atlas», " +
				"        T, " +
				"        𝒜, " +
				"        n, " +
				"        (λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p)), " +
				"        riemannian_euler_form⟨n⟩(T, 𝒜, g))(c, y, P))",
		},
		"The homotopy formula gives the endpoint Pfaffian difference. The initial endpoint is π * "+
			"e; at the final endpoint u is parallel, hence curvature kills u and its Pfaffian vanishes."),
})}

var AngularFormFiberIntegral = angularFormFiberIntegralThm{family.Add(registry.ProofEntry{
	Name: "AngularFormFiberIntegral",
	Key:  "prop_fb83ee0bcbe08420",
	Deps: []registry.EntryLike{AngularRepresentativeExistsUnique, angularVolumeDef},
	Reading: "This is the explicit fiber identity, stronger than a sphere-integral assertion. " +
		"The first matrix column is radial; for rank two it gives (y₀dy₁−y₁dy₀)/(2π|y|²).",
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
				"∀m:num. " +
				"∀c:prod(set(A), A → num → real). " +
				"∀E:((num → real) → num → num → real). " +
				"∀x:A.",
			Hypotheses: []string{
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"riemannian_metric⟨n⟩(T, 𝒜, g)",
				"n = 2 * m + 2",
				"positive_manifold_chart⟨n⟩(T, 𝒜, c)",
				"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
				"x ∈ fst(c)",
			},
			Conclusion: "manifold_form_pullback⟨n, 2 * n⟩( " +
				"    subtopology(euclidean_topology(n), {y:(num → real) | vec⟨n⟩(y) ∧ y ≠ (λi:num. &0)}), " +
				"    euclidean_atlas({y:(num → real) | vec⟨n⟩(y) ∧ y ≠ (λi:num. &0)}), " +
				"    «punctured topology», " +
				"    «punctured atlas», " +
				"    n - 1, " +
				"    thom_frame_fiber⟨n⟩(T, 𝒜, c, E, x), " +
				"    riemannian_angular_form⟨n⟩(T, 𝒜, g))( " +
				"    ({y:(num → real) | vec⟨n⟩(y) ∧ y ≠ (λi:num. &0)}, λy:(num → real). y)) = " +
				"even_angular_volume(m)",
		},
		"On a fiber B vanishes and α=u(du)^T−(du)u^T. Expanding the matching Pfaffian of tα and "+
			"integrating its dt coefficient gives factorial(m)/(2π^(m + 1)) times det[y, P]/|y|^(2m + 2)."),
})}

var RadialCutoffExists = radialCutoffExistsThm{family.Add(registry.ProofEntry{
	Name: "RadialCutoffExists",
	Key:  "prop_c51e637611a06385",
	Deps: []registry.EntryLike{radialCutoffDef},
	Build: family.Card(
		Statement{
			Binders:    "∀a b:real.",
			Hypotheses: []string{"&0 < a", "a < b"},
			Conclusion: "∃ρ:(real → real). thom_radial_cutoff(a, b, ρ)",
		},
		"A smooth step between the two radii, shifted by minus one, is constant near zero and beyond b."),
})}

var ThomRepresentativeExistsUnique = thomRepresentativeExistsUniqueThm{family.Add(registry.ProofEntry{
	Name: "ThomRepresentativeExistsUnique",
	Key:  "prop_3172d6eb3a3ce2ae",
	Deps: []registry.EntryLike{AngularFormDerivative, differential_form.FormAtlasExtension},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
				"∀m:num. " +
				"∀a b:real. " +
				"∀ρ:(real → real).",
			Hypotheses: []string{
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"riemannian_metric⟨n⟩(T, 𝒜, g)",
				"n = 2 * m + 2",
				"thom_radial_cutoff(a, b, ρ)",
			},
			Conclusion: "∃U:(prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
				"            prod(A, prod(set(A), A → num → real) → num → real) → num → real) → " +
				"        (num → real) → " +
				"        (num → num → real) → " +
				"        real). " +
				"    riemannian_thom_representative⟨n⟩(T, 𝒜, g, a, ρ, U) ∧ " +
				"    (∀V:(prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
				"                prod(A, prod(set(A), A → num → real) → num → real) → num → real) → " +
				"            (num → real) → " +
				"            (num → num → real) → " +
				"            real). " +
				"        riemannian_thom_representative⟨n⟩(T, 𝒜, g, a, ρ, V) ⇒ V = U)",
		},
		"On the overlap ρ=-1, so d(ρψ)=−dψ=π*e. Glue across the zero section; "+
			"the punctured bundle and the inner disk cover the total space."),
})}

var ThomClosed = thomClosedThm{family.Add(registry.ProofEntry{
	Name: "ThomClosed",
	Key:  "prop_18c2d9b2ad95d637",
	Deps: []registry.EntryLike{
		ThomRepresentativeExistsUnique,
		riemannian.EulerClosed,
		differential_form.ExteriorDerivativeSquareZero,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
				"∀m:num. " +
				"∀a b:real. " +
				"∀ρ:(real → real).",
			Hypotheses: []string{
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"riemannian_metric⟨n⟩(T, 𝒜, g)",
				"n = 2 * m + 2",
				"thom_radial_cutoff(a, b, ρ)",
			},
			Conclusion: "riemannian_thom_form⟨n⟩(T, 𝒜, g, a, ρ) ∈ " +
				"cocycles(de_rham_complex⟨2 * n⟩(tangent_topology⟨n⟩(T, 𝒜), tangent_atlas⟨n⟩(T, 𝒜)), n)",
		},
		"Away from the zero section d²=0; on the inner disk use closedness "+
			"of e and pullback. Locality supplies the global closed form."),
})}

var ThomSupport = thomSupportThm{family.Add(registry.ProofEntry{
	Name: "ThomSupport",
	Key:  "prop_b1aef9fa5651e790",
	Deps: []registry.EntryLike{ThomRepresentativeExistsUnique, differential_form.SupportDef},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
				"∀m:num. " +
				"∀a b:real. " +
				"∀ρ:(real → real).",
			Hypotheses: []string{
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"riemannian_metric⟨n⟩(T, 𝒜, g)",
				"n = 2 * m + 2",
				"thom_radial_cutoff(a, b, ρ)",
			},
			Conclusion: "manifold_form_support⟨2 * n⟩(tangent_topology⟨n⟩(T, 𝒜), " +
				"    tangent_atlas⟨n⟩(T, 𝒜), " +
				"    riemannian_thom_form⟨n⟩(T, 𝒜, g, a, ρ)) ⊆ " +
				"{p:prod(A, prod(set(A), A → num → real) → num → real) | " +
				"    p ∈ tangent_bundle⟨n⟩(T, 𝒜) ∧ riemannian_pairing⟨n⟩(T, 𝒜, g, fst(p), snd(p), snd(p)) ≤ b}",
		},
		"Outside the outer squared radius both ρ and dρ vanish. "+
			"The closed disk contains the closure of the nonzero set."),
})}

var ThomCompactSupport = thomCompactSupportThm{family.Add(registry.ProofEntry{
	Name: "ThomCompactSupport",
	Key:  "prop_6bd1ef99ebf2bef9",
	Deps: []registry.EntryLike{ThomSupport, riemannian.PairingDef},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
				"∀m:num. " +
				"∀a b:real. " +
				"∀ρ:(real → real).",
			Hypotheses: []string{
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"riemannian_metric⟨n⟩(T, 𝒜, g)",
				"n = 2 * m + 2",
				"thom_radial_cutoff(a, b, ρ)",
				"compact_in(T, ⋃T)",
			},
			Conclusion: "compact_in(tangent_topology⟨n⟩(T, 𝒜), " +
				"    manifold_form_support⟨2 * n⟩(tangent_topology⟨n⟩(T, 𝒜), " +
				"        tangent_atlas⟨n⟩(T, 𝒜), " +
				"        riemannian_thom_form⟨n⟩(T, 𝒜, g, a, ρ)))",
		},
		"A finite cover by relatively compact bundle charts and positive definiteness bound "+
			"the metric disk in each trivialization. Its closed subset supporting U is compact."),
})}

var ThomFiberIntegral = thomFiberIntegralThm{family.Add(registry.ProofEntry{
	Name: "ThomFiberIntegral",
	Key:  "prop_86fb7bae9dfbf0cd",
	Deps: []registry.EntryLike{
		AngularFormFiberIntegral,
		ThomRepresentativeExistsUnique,
		vec_integral.EvenRadialIntegral,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
				"∀m:num. " +
				"∀a b:real. " +
				"∀ρ:(real → real). " +
				"∀c:prod(set(A), A → num → real). " +
				"∀E:((num → real) → num → num → real). " +
				"∀x:A.",
			Hypotheses: []string{
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"riemannian_metric⟨n⟩(T, 𝒜, g)",
				"n = 2 * m + 2",
				"thom_radial_cutoff(a, b, ρ)",
				"positive_manifold_chart⟨n⟩(T, 𝒜, c)",
				"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
				"x ∈ fst(c)",
			},
			Conclusion: "manifold_form_integral⟨n⟩(euclidean_topology(n), " +
				"    euclidean_atlas({y:(num → real) | vec⟨n⟩(y)}), " +
				"    manifold_form_pullback⟨n, 2 * n⟩(euclidean_topology(n), " +
				"        euclidean_atlas({y:(num → real) | vec⟨n⟩(y)}), " +
				"        tangent_topology⟨n⟩(T, 𝒜), " +
				"        tangent_atlas⟨n⟩(T, 𝒜), " +
				"        n, " +
				"        thom_frame_fiber⟨n⟩(T, 𝒜, c, E, x), " +
				"        riemannian_thom_form⟨n⟩(T, 𝒜, g, a, ρ))) = " +
				"&1",
		},
		"Insert the angular fiber identity into dρ∧ψ. EvenRadialIntegral cancels the radial "+
			"power and sphere-volume coefficient, leaving the endpoint difference ρ(∞)−ρ(0)=1."),
})}

var ThomZeroSection = thomZeroSectionThm{family.Add(registry.ProofEntry{
	Name: "ThomZeroSection",
	Key:  "prop_a275123aee9ea596",
	Deps: []registry.EntryLike{ThomRepresentativeExistsUnique, differential_form.PullbackCompose},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
				"∀m:num. " +
				"∀a b:real. " +
				"∀ρ:(real → real).",
			Hypotheses: []string{
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"riemannian_metric⟨n⟩(T, 𝒜, g)",
				"n = 2 * m + 2",
				"thom_radial_cutoff(a, b, ρ)",
			},
			Conclusion: "manifold_form_pullback⟨n, 2 * n⟩(T, " +
				"    𝒜, " +
				"    tangent_topology⟨n⟩(T, 𝒜), " +
				"    tangent_atlas⟨n⟩(T, 𝒜), " +
				"    n, " +
				"    tangent_zero_section, " +
				"    riemannian_thom_form⟨n⟩(T, 𝒜, g, a, ρ)) = " +
				"riemannian_euler_form⟨n⟩(T, 𝒜, g)",
		},
		"The zero section lies in the inner disk, where U=π*e and π∘s₀=id."),
})}

var ThomSupportInEmbeddedDisk = thomSupportInEmbeddedDiskThm{family.Add(registry.ProofEntry{
	Name: "ThomSupportInEmbeddedDisk",
	Key:  "prop_e25b98353af26cbb",
	Deps: []registry.EntryLike{ThomSupport, riemannian.PairingDef},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
				"∀m:num. " +
				"∀N:num. " +
				"∀i:(A → num → real). " +
				"∀δ:real.",
			Hypotheses: []string{
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"riemannian_metric⟨n⟩(T, 𝒜, g)",
				"n = 2 * m + 2",
				"compact_in(T, ⋃T)",
				"smooth_manifold_map⟨n, N⟩(T, " +
					"    𝒜, " +
					"    euclidean_topology(N), " +
					"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
					"    i)",
				"&0 < δ",
			},
			Conclusion: "∃a b:real. " +
				"    &0 < a ∧ " +
				"    a < b ∧ " +
				"    (∀ρ:(real → real). " +
				"        thom_radial_cutoff(a, b, ρ) ⇒ " +
				"        manifold_form_support⟨2 * n⟩(tangent_topology⟨n⟩(T, 𝒜), " +
				"            tangent_atlas⟨n⟩(T, 𝒜), " +
				"            riemannian_thom_form⟨n⟩(T, 𝒜, g, a, ρ)) ⊆ " +
				"        embedded_tangent_disk⟨n, N⟩(T, 𝒜, i, δ))",
		},
		"Compactness gives a uniform positive upper bound for |di(v)|² relative to g(v, v). "+
			"Choose b strictly below δ² divided by this bound, then any a between zero and b works."),
})}
