// Closed forms represent cohomology classes, with exact differences and pointwise quotient operations.

package de_rham

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/registry"
)

var Complex = complexThm{family.Add(registry.ProofEntry{
	Name: "Complex",
	Key:  "prop_e4afe71d114cc467",
	Reading: "The complex is indexed by nonnegative degrees. Its degree-zero carrier is " +
		"the zero-form module, and no artificial negative-degree form space is introduced.",
	Deps: []registry.EntryLike{
		ComplexDef,
		differential_form.FormModule,
		differential_form.ExteriorDerivativeLinear,
		differential_form.ExteriorDerivativeSquareZero,
		chain_complex.CochainComplex,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "cochain_complex(real_ring, de_rham_complex⟨n⟩(T, 𝒜))",
	},
		"Identify each complex_module with the existing degree-k manifold form module, whose "+
			"operations are the same pointwise operations. ExteriorDerivativeLinear gives each "+
			"coboundary homomorphism and ExteriorDerivativeSquareZero gives its square zero."),
})}

var CohomologyModule = cohomologyModuleThm{family.Add(registry.ProofEntry{
	Name: "CohomologyModule",
	Key:  "prop_f1a68a2cea1cfede",
	Deps: []registry.EntryLike{Complex, CohomologyModuleDef, chain_complex.CohomologyModuleOn},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num.",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "module_on(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, k))",
	},
		"Apply the generic cohomology-module theorem to the de Rham "+
			"cochain complex and unfold its named cohomology module."),
})}

// CocycleClosedForm — the degree-k cocycles of the de Rham complex are exactly
// the closed k-forms. The complex is packed with the k-forms as its degree-k
// terms, the exterior derivative as its differential and the zero family as its
// zero, so the cocycle set, read at ω, is the two conditions.
var CocycleClosedForm = cocycleClosedFormThm{family.Add(registry.ProofEntry{
	Name: "CocycleClosedForm",
	Key:  "prop_d361f23cd9b0266d",
	Build: family.Theorem("∀n:num. "+
		"∀T:set(set(A)). "+
		"∀𝒜:set(prod(set(A), A → num → real)). "+
		"∀k:num. "+
		"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). "+
		"    ω ∈ cocycles(de_rham_complex⟨n⟩(T, 𝒜), k) ⇔ "+
		"    manifold_form_on⟨n⟩(T, 𝒜, k, ω) ∧ manifold_exterior_derivative⟨n⟩(T, 𝒜, k, ω) = «zero family»",
		func(a *Argument,
			n *Expr[Nat],
			T *Expr[Set[Set[A]]],
			𝒜 *Expr[Set[Prod[Set[A], Fun2[A, Nat, Real]]]],
			k *Expr[Nat],
			ω *Expr[Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]],
		) {
			a.Show(
				"the cocycle set of the packed complex, read at ω",
				Simp(Fwd(ComplexDef), Fwd(chain_complex.CocyclesDef)),
				SetTacMembership())
		}),
})}

var ClassMember = classMemberThm{family.Add(registry.ProofEntry{
	Name: "ClassMember",
	Key:  "prop_af3b1e0299a96fe6",
	Reading: "The form predicate includes smooth-manifold membership. Closedness is " +
		"required: a coset of an arbitrary nonclosed form is not asserted to lie in cohomology.",
	Deps: []registry.EntryLike{
		Complex,
		CohomologyModuleDef,
		ClassDef,
		chain_complex.CocyclesDef,
		chain_complex.InCohomology,
		chain_complex.CohomologyModuleDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, k, ω)",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, k, ω) = «zero family»",
		},
		Conclusion: "de_rham_class⟨n⟩(T, 𝒜, k, ω) ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, k).carrier",
	},
		"The form and closedness hypotheses make ω a cocycle of the de Rham complex. InCohomology "+
			"places its coset in cohomology, which is the carrier of the named quotient module."),
})}

var ClassRepresentative = classRepresentativeThm{family.Add(registry.ProofEntry{
	Name: "ClassRepresentative",
	Key:  "prop_865e4006aad62527",
	Deps: []registry.EntryLike{
		Complex,
		CohomologyModuleDef,
		ClassDef,
		chain_complex.InCohomology,
		chain_complex.CocyclesDef,
		chain_complex.CohomologyModuleDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀s:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"s ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, k).carrier",
		},
		Conclusion: "∃ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    manifold_form_on⟨n⟩(T, 𝒜, k, ω) ∧ " +
			"    manifold_exterior_derivative⟨n⟩(T, 𝒜, k, ω) = «zero family» ∧ " +
			"    s = de_rham_class⟨n⟩(T, 𝒜, k, ω)",
	},
		"Unfold the named quotient module and use InCohomology to choose a cocycle representative. "+
			"Expanding the degree carrier and cocycle condition gives a closed normalized manifold form."),
})}

var ClassAdd = classAddThm{family.Add(registry.ProofEntry{
	Name: "ClassAdd",
	Key:  "prop_ccc6a231edc98c18",
	Reading: "Both representatives are closed, so their cosets lie in the cohomology module whose " +
		"addition is used. All sums use the pointwise operations of the normalized form host type.",
	Deps: []registry.EntryLike{
		Complex,
		ClassDef,
		CohomologyModuleDef,
		chain_complex.CocyclesSubmodule,
		chain_complex.CoboundariesSubsetCocycles,
		chain_complex.CoboundariesDef,
		chain_complex.CochainCoboundaryHom,
		module_homomorphism.ImageSubmodule,
		submodule.SubmoduleRestrict,
		submodule.ZeroSubmodule,
		submodule.QuotientModuleDef,
		quotient_group.LeftCosetMulOn,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, k, α)",
			"manifold_form_on⟨n⟩(T, 𝒜, k, β)",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, k, α) = «zero family»",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, k, β) = «zero family»",
		},
		Conclusion: "de_rham_cohomology_module⟨n⟩(T, 𝒜, k).add(de_rham_class⟨n⟩(T, 𝒜, k, α), " +
			"    de_rham_class⟨n⟩(T, 𝒜, k, β)) = " +
			"de_rham_class⟨n⟩(T, " +
			"    𝒜, " +
			"    k, " +
			"    λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"        α(c, y, P) + β(c, y, P))",
	},
		"Coboundaries form an additive subgroup of cocycles. The quotient addition is setwise addition "+
			"of cosets, so LeftCosetMulOn in the additive cocycle group gives the coset of the sum."),
})}

var ClassScale = classScaleThm{family.Add(registry.ProofEntry{
	Name: "ClassScale",
	Key:  "prop_1069b101d2d0fc22",
	Deps: []registry.EntryLike{
		Complex,
		ClassDef,
		CohomologyModuleDef,
		chain_complex.CocyclesSubmodule,
		chain_complex.CoboundariesSubsetCocycles,
		chain_complex.CoboundariesDef,
		chain_complex.CochainCoboundaryHom,
		module_homomorphism.ImageSubmodule,
		submodule.SubmoduleRestrict,
		submodule.ZeroSubmodule,
		submodule.QuotientSmulCoset,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀a:real.",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, k, ω)",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, k, ω) = «zero family»",
		},
		Conclusion: "de_rham_cohomology_module⟨n⟩(T, 𝒜, k).smul(a, de_rham_class⟨n⟩(T, 𝒜, k, ω)) = " +
			"de_rham_class⟨n⟩(T, " +
			"    𝒜, " +
			"    k, " +
			"    λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). a * ω(c, y, P))",
	},
		"Apply QuotientSmulCoset to the cocycle module and its coboundary submodule. "+
			"The inherited scalar action is pointwise multiplication of the form by a."),
})}

var ClassEqualSucc = classEqualSuccThm{family.Add(registry.ProofEntry{
	Name: "ClassEqualSucc",
	Key:  "prop_d409aa6b9a95c641",
	Reading: "Successor degree keeps the primitive in degree k and avoids truncated subtraction at " +
		"degree zero. The primitive is a whole normalized form, not just locally defined coordinate data.",
	Deps: []registry.EntryLike{
		Complex,
		ClassDef,
		chain_complex.CoboundariesSucc,
		chain_complex.CocyclesSubmodule,
		chain_complex.CoboundariesSubsetCocycles,
		chain_complex.CoboundariesDef,
		chain_complex.CochainCoboundaryHom,
		module_homomorphism.ImageSubmodule,
		submodule.SubmoduleRestrict,
		submodule.ZeroSubmodule,
		submodule.SubmoduleCosetEq,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, k + 1, α)",
			"manifold_form_on⟨n⟩(T, 𝒜, k + 1, β)",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, k + 1, α) = «zero family»",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, k + 1, β) = «zero family»",
		},
		Conclusion: "(de_rham_class⟨n⟩(T, 𝒜, k + 1, α) = de_rham_class⟨n⟩(T, 𝒜, k + 1, β) ⇔ " +
			"    ∃η:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"        manifold_form_on⟨n⟩(T, 𝒜, k, η) ∧ " +
			"        manifold_exterior_derivative⟨n⟩(T, 𝒜, k, η) = " +
			"        λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"            α(c, y, P) - β(c, y, P))",
	},
		"Two cocycle cosets agree exactly when their difference is a coboundary. "+
			"In degree k+1, CoboundariesSucc identifies coboundaries with the image "+
			"of the degree-k exterior derivative, yielding the asserted primitive."),
})}

// ClassAddExact — adding an exact form dθ to a closed (k + 1)-form α does
// not change its de Rham class: α + dθ is a (k + 1)-form, closed since
// d(α + dθ) = dα + d(dθ) = 0, and it differs from α by dθ, a derivative
// of the k-form θ.
var ClassAddExact = classAddExactThm{family.Add(registry.ProofEntry{
	Name: "ClassAddExact",
	Key:  "prop_daba544e912867a0",
	Build: family.Theorem(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀α θ:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, k + 1, α)",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, k + 1, α) = «zero family»",
			"manifold_form_on⟨n⟩(T, 𝒜, k, θ)",
		},
		Conclusion: "de_rham_class⟨n⟩(T, " +
			"    𝒜, " +
			"    k + 1, " +
			"    λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"        α(c, y, P) + manifold_exterior_derivative⟨n⟩(T, 𝒜, k, θ, c, y, P)) = " +
			"de_rham_class⟨n⟩(T, 𝒜, k + 1, α)",
	},
		func(
			a *Argument,
			n, k *Expr[Nat],
			T *Expr[Set[Set[A]]],
			𝒜 *Expr[Set[Prod[Set[A], Fun2[A, Nat, Real]]]],
			α, θ *Expr[Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]],
			αForm, αClosed, θForm Fact,
		) {
			shifted := a.TermAs[Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]](
				"λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
					"    α(c, y, P) + manifold_exterior_derivative⟨n⟩(T, 𝒜, k, θ, c, y, P)")
			dθ := a.TermAs[Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]](
				"manifold_exterior_derivative⟨n⟩(T, 𝒜, k, θ)")
			dθForm := a.Have(
				"dθ is a (k + 1)-form",
				"manifold_form_on⟨n⟩(T, 𝒜, k + 1, manifold_exterior_derivative⟨n⟩(T, 𝒜, k, θ))",
				By(θForm, differential_form.ExteriorDerivativeForm))
			squareZero := a.Have(
				"d(dθ) = 0",
				"manifold_exterior_derivative⟨n⟩(T, 𝒜, k + 1, manifold_exterior_derivative⟨n⟩(T, 𝒜, k, θ)) = "+
					"«zero family»",
				By(θForm, differential_form.ExteriorDerivativeSquareZero))
			shiftedForm := a.Have(
				"α + dθ is a (k + 1)-form",
				"manifold_form_on⟨n⟩(T, "+
					"    𝒜, "+
					"    k + 1, "+
					"    λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). "+
					"        α(c, y, P) + manifold_exterior_derivative⟨n⟩(T, 𝒜, k, θ, c, y, P))",
				By(αForm, dθForm, differential_form.FormAdd))
			additive := a.Have(
				"d(α + dθ) = dα + d(dθ)",
				"manifold_exterior_derivative⟨n⟩(T, "+
					"    𝒜, "+
					"    k + 1, "+
					"    λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). "+
					"        α(c, y, P) + manifold_exterior_derivative⟨n⟩(T, 𝒜, k, θ, c, y, P)) = "+
					"(λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). "+
					"    manifold_exterior_derivative⟨n⟩(T, 𝒜, k + 1, α, c, y, P) + "+
					"    manifold_exterior_derivative⟨n⟩(T, "+
					"        𝒜, "+
					"        k + 1, "+
					"        manifold_exterior_derivative⟨n⟩(T, 𝒜, k, θ), "+
					"        c, "+
					"        y, "+
					"        P))",
				By(
					αForm,
					dθForm,
					differential_form.ExteriorDerivativeAdd.At(n, a.TermAs[Nat]("k + 1"), T, 𝒜, α, dθ)))
			closed := a.Have(
				"α + dθ is closed: d(α + dθ) = dα + d(dθ) = 0 + 0",
				"manifold_exterior_derivative⟨n⟩(T, "+
					"    𝒜, "+
					"    k + 1, "+
					"    λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). "+
					"        α(c, y, P) + manifold_exterior_derivative⟨n⟩(T, 𝒜, k, θ, c, y, P)) = "+
					"«zero family»",
				additive.Rw(),
				αClosed.Rw(),
				squareZero.Rw(),
				ByArith())
			difference := a.Have(
				"dθ is the difference of α + dθ and α",
				"manifold_exterior_derivative⟨n⟩(T, 𝒜, k, θ) = "+
					"(λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). "+
					"    (α(c, y, P) + manifold_exterior_derivative⟨n⟩(T, 𝒜, k, θ, c, y, P)) - α(c, y, P))",
				Funext(),
				ByArith())
			primitive := a.Have(
				"θ is a primitive of the difference",
				"∃ζ:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). "+
					"    manifold_form_on⟨n⟩(T, 𝒜, k, ζ) ∧ "+
					"    manifold_exterior_derivative⟨n⟩(T, 𝒜, k, ζ) = "+
					"    (λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). "+
					"        (α(c, y, P) + manifold_exterior_derivative⟨n⟩(T, 𝒜, k, θ, c, y, P)) - α(c, y, P))",
				Derive(func(b *Argument) {
					b.Take(θ)
					b.Show(
						"θ is a k-form whose derivative is the difference",
						By(θForm, difference))
				}))
			a.Show(
				"two closed forms differing by an exact form have one class",
				By(shiftedForm, αForm, closed, αClosed, primitive, ClassEqualSucc.At(n, T, 𝒜, k, shifted, α)))
		}),
})}

var ClassEqualZero = classEqualZeroThm{family.Add(registry.ProofEntry{
	Name: "ClassEqualZero",
	Key:  "prop_54c322b405452fe5",
	Reading: "Degree-zero coboundaries are the singleton containing the " +
		"whole zero form. Thus class equality is equality of the closed " +
		"normalized forms themselves; no degree-minus-one primitive is introduced.",
	Deps: []registry.EntryLike{
		Complex,
		ClassDef,
		chain_complex.CoboundariesDef,
		chain_complex.CocyclesSubmodule,
		submodule.SubmoduleCosetEq,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, 0, α)",
			"manifold_form_on⟨n⟩(T, 𝒜, 0, β)",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, 0, α) = «zero family»",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, 0, β) = «zero family»",
		},
		Conclusion: "(de_rham_class⟨n⟩(T, 𝒜, 0, α) = de_rham_class⟨n⟩(T, 𝒜, 0, β) ⇔ α = β)",
	},
		"In degree zero the coboundary submodule is exactly the singleton zero "+
			"form. Equality of the two cocycle cosets therefore says their pointwise "+
			"difference is zero, which is equality of the normalized forms."),
})}

var CohomologyAboveDimension = cohomologyAboveDimensionThm{family.Add(registry.ProofEntry{
	Name: "CohomologyAboveDimension",
	Key:  "prop_3073ef3d6bbcead3",
	Reading: "This is a carrier statement, including empty and zero-dimensional manifolds. " +
		"It does not assert that the entire host type of sets of forms is a singleton.",
	Deps: []registry.EntryLike{
		Complex,
		CohomologyModule,
		CohomologyModuleDef,
		ClassRepresentative,
		differential_form.FormAboveDimension,
		chain_complex.CohomologyModuleDef,
		submodule.QuotientModuleDef,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num.",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "n < k"},
		Conclusion: "de_rham_cohomology_module⟨n⟩(T, 𝒜, k).carrier = " +
			"{de_rham_cohomology_module⟨n⟩(T, 𝒜, k).zero}",
	},
		"Every degree-k form is zero when k exceeds the ambient dimension, "+
			"so every cohomology class has the zero representative. The module "+
			"law supplies its zero class, giving exactly the singleton carrier."),
})}
