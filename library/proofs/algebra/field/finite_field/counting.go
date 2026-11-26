// counting.go — counting over a finite field: the q^n vectors of an
// n-dimensional space, the q^d points of an extension of degree d, the
// lines through the origin of a space, and the local finiteness of a field
// algebraic over a finite subfield, each of whose finite sets generates a
// finite extension of it.

package finite_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// finiteFieldFacts — what every count below reads off finite_field(F): F
// is a field, and its carrier has field_size(F) elements.
func finiteFieldFacts(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders:    "∀F:field_ops(A).",
		Hypotheses: []string{"finite_field(F)"},
		Conclusion: "field_on(F) ∧ has_size(F.carrier, field_size(F))",
	}, func(a *Argument, F *Expr[FieldOps[A]], finiteF Fact) {
		definition := a.Conjuncts(
			a.Unfolded(finiteF, FiniteFieldDef),
			"F is a field",
			"the carrier is finite")
		fieldOn, finiteCarrier := definition[0], definition[1]
		carrier := a.TermAs[Set[A]]("F.carrier")
		a.Show(
			"a finite carrier has its cardinality as its size",
			By(Normalized, fieldOn, finiteCarrier, cardinality.FiniteHasSize.At(carrier), FieldSizeDef.At(F)))
	})
}

// FiniteDimensionalSpaceSize — a finite-dimensional module over a finite
// field has q^n vectors: its basis coordinates identify its carrier with
// the scalar-valued functions on a finite basis, zero off that basis.
var FiniteDimensionalSpaceSize = finiteDimensionalSpaceSizeThm{family.Add(registry.ProofEntry{
	Name: "FiniteDimensionalSpaceSize",
	Key:  "prop_8466a1ab5fa8d4cb",
	Reading: "Finite dimensionality determines the otherwise total choice " +
		"module_dim. In dimension zero the carrier has its single zero vector.",
	Build: family.Sections(Statement{
		Binders: "∀F:field_ops(A). ∀M:module_ops(A, B).",
		Hypotheses: []string{
			"finite_field(F)",
			"module_on(field_ring(F), M)",
			"finite_dimensional(field_ring(F), M)",
		},
		Conclusion: "has_size(M.carrier, field_size(F) ^ module_dim(field_ring(F), M))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		finiteField := finiteFieldFacts(ctx)

		synthesisIn := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀E:set(B). ∀c:(B → A).",
			Hypotheses: []string{
				"module_on(R, M)",
				"finite(E)",
				"module_basis(R, M, E)",
				"∀e:B. e ∈ E ⇒ c(e) ∈ R.carrier",
			},
			Conclusion: "module_sum(M.add, M.zero, E, λe:B. c(e) • e) ∈ M.carrier",
		}, func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			moduleOn module.ModuleFact[on.R, on.M],
			E *Expr[Set[B]],
			c *Arrow[B, A],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"the basis is finite",
				"E is a basis",
				"the coefficients are scalars on E")
			finiteE, basisE, scalars := given[0], given[1], given[2]
			summands := a.Have(
				"each scalar multiple of a basis vector lies in the carrier",
				"∀e:B. e ∈ E ⇒ c(e) • e ∈ M.carrier",
				By(
					module.SmulIn.Read(moduleOn),
					scalars,
					basisE,
					linear_independence.BasisInCarrier.At(R, M, E),
					set_basic.SubsetDef))
			summand := a.TermAs[Fun[B, B]]("λe:B. c(e) • e")
			a.Show(
				"the finite sum of these vectors lies in the carrier",
				By(summands, moduleOn, finiteE, module.ModuleSumIn.At(R, M, E, summand)))
		})

		coordinatesInjective := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀E:set(B).",
			Hypotheses: []string{
				"module_on(R, M)",
				"finite(E)",
				"module_basis(R, M, E)",
			},
			Conclusion: "injective_on(M.carrier, module_basis_coordinates(R, M, E))",
		}, func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			moduleOn module.ModuleFact[on.R, on.M],
			E *Expr[Set[B]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"the basis is finite",
				"E is a basis")
			finiteE, basisE := given[0], given[1]
			a.Do(Unfold(functions.InjectiveOnDef))
			x := a.FixAs[B]("x")
			y := a.FixAs[B]("y")
			same := a.Assume()
			a.Show(
				"equal coordinate functions reconstruct equal vectors",
				By(
					finiteE,
					moduleOn,
					same,
					basisE,
					module_dimension.BasisCoordinatesSpec.At(R, M, E, x),
					module_dimension.BasisCoordinatesSpec.At(R, M, E, y)))
		})

		coordinatesImage := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀E:set(B).",
			Hypotheses: []string{
				"module_on(R, M)",
				"finite(E)",
				"module_basis(R, M, E)",
			},
			Conclusion: "image(module_basis_coordinates(R, M, E), M.carrier) = " +
				"{c:(B → A) | (∀e:B. e ∈ E ⇒ c(e) ∈ R.carrier) ∧ (∀e:B. e ∉ E ⇒ c(e) = R.zero)}",
		}, func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			moduleOn module.ModuleFact[on.R, on.M],
			E *Expr[Set[B]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"the basis is finite",
				"E is a basis")
			finiteE, basisE := given[0], given[1]
			a.Do(Simp(Fwd(set_basic.Extension)))
			c := a.FixAs[Fun[B, A]]("c")
			a.Iff()
			a.Forward(
				"a vector's coordinates are scalars on E and zero off E",
				func(b *Argument, inImage Fact) {
					v, source := b.ObtainAs[B](
						"c is the coordinate function of a vector of the carrier",
						"∃v:B. v ∈ M.carrier ∧ c = module_basis_coordinates(R, M, E, v)",
						BySets(inImage))
					b.Show(
						"the coordinate specification gives both support conditions",
						BySets(source, moduleOn, finiteE, basisE, module_dimension.BasisCoordinatesSpec.At(R, M, E, v)))
				})
			a.Backward(
				"synthesize a vector from the supported scalar coefficients",
				func(b *Argument, supported Fact) {
					support := b.Conjuncts(
						supported,
						"c is scalar on E",
						"c is zero off E")
					scalarOnE, zeroOffE := support[0], support[1]
					v := b.TermAs[B]("module_sum(M.add, M.zero, E, λe:B. c(e) • e)")
					synthesized := b.Have(
						"the synthesized vector lies in the carrier",
						"module_sum(M.add, M.zero, E, λe:B. c(e) • e) ∈ M.carrier",
						By(moduleOn, finiteE, basisE, scalarOnE, At(synthesisIn, R, M, E, c)))
					recovered := b.Have(
						"uniqueness of coordinates recovers the coefficients",
						"module_basis_coordinates(R, M, E, module_sum(M.add, M.zero, E, λe:B. c(e) • e)) = c",
						By(
							moduleOn,
							finiteE,
							basisE,
							synthesized,
							scalarOnE,
							zeroOffE,
							module_dimension.BasisCoordinatesUnique.At(R, M, E, v, c)))
					b.Show(
						"the synthesized vector is a source of c",
						BySets(synthesized, recovered))
				})
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			F *Expr[FieldOps[A]],
			M *Expr[ModuleOps[A, B]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"F is a finite field",
				"M is a module over its ring",
				"M is finite-dimensional")
			moduleOn, finiteDimensional := given[1], given[2]
			fieldFacts := a.Conjuncts(
				GroupPremises(given[0], At(finiteField, F)),
				"F is a field",
				"the scalar carrier has q elements")
			fieldOn, scalarSize := fieldFacts[0], fieldFacts[1]
			S, basis := a.UnpackAs[Set[B]](
				a.Unfolded(finiteDimensional, module_dimension.FiniteDimensionalDef), "S")
			R := a.TermAs[RingOps[A]]("field_ring(F)")
			inverse := a.TermAs[Fun[A, A]]("F.inv")
			dimension := a.TermAs[Nat]("module_dim(field_ring(F), M)")
			basisSize := a.Have(
				"a finite basis has as many vectors as the dimension",
				"has_size(S, module_dim(field_ring(F), M))",
				By(
					field.FieldRingSubfield.Read(fieldOn),
					moduleOn,
					basis,
					module_dimension.DimBasis.At(R, M, inverse, S),
					cardinality.HasSizeDef.At(S, dimension)))
			scalarCarrier := a.TermAs[Set[A]]("F.carrier")
			q := a.TermAs[Nat]("field_size(F)")
			scalarZero := a.TermAs[A]("F.zero")
			coefficientCount := a.Have(
				"the coefficient functions have q choices at each basis vector",
				"has_size({c:(B → A) | (∀e:B. e ∈ S ⇒ c(e) ∈ F.carrier) ∧ (∀e:B. e ∉ S ⇒ c(e) = F.zero)}, "+
					"    field_size(F) ^ module_dim(field_ring(F), M))",
				By(
					scalarSize,
					basisSize,
					cardinality.HasSizeFunspace.At(S, scalarCarrier, dimension, q, scalarZero)))
			coordinateMap := a.TermAs[Fun[B, Fun[B, A]]]("module_basis_coordinates(field_ring(F), M, S)")
			vectorCarrier := a.TermAs[Set[B]]("M.carrier")
			expectedSize := a.TermAs[Nat]("field_size(F) ^ module_dim(field_ring(F), M)")
			a.Show(
				"the coordinate bijection transfers this count to the module carrier",
				By(
					coefficientCount,
					moduleOn,
					basis,
					At(coordinatesInjective, R, M, S),
					At(coordinatesImage, R, M, S),
					cardinality.HasSizeImageInjEq.At(coordinateMap, vectorCarrier, expectedSize)))
		})
	}),
})}

// FiniteExtensionSize — a finite extension of degree d of a finite subfield of
// q elements has q^d elements: it is a vector space of dimension d over the
// restricted finite field.
var FiniteExtensionSize = finiteExtensionSizeThm{family.Add(registry.ProofEntry{
	Name: "FiniteExtensionSize",
	Key:  "prop_73cb570df31b7a3c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"K ⊆ M",
			"finite(K)",
			"finite_extension(L, K, M)",
		},
		Conclusion: "has_size(M, card(K) ^ extension_degree(L, K, M))",
	}, func(a *Argument, L field.FieldFact[on.L], K, M *Expr[Set[A]], given Fact) {
		fieldL := a.TermAs[FieldOps[A]]("L")
		F, Fdef := a.LetAs[FieldOps[A]]("F", "restrict_field(L, K)")
		V, Vdef := a.LetAs[ModuleOps[A, A]]("V", "restrict_module(regular_module(field_ring(L)), M)")
		scalarData := a.Have(
			"restrict to the finite scalar field",
			"finite_field(F) ∧ field_ring(F) = restrict_ring(field_ring(L), K)",
			Simp(
				Fwd(Fdef),
				Fwd(FiniteFieldDef),
				Fwd(field.RestrictFieldRing),
				Fwd(field.RestrictFieldDef),
				Fwd(field.FieldCarrierDef)),
			By(L, given, field.SubfieldFieldOn.At(fieldL, K), field.RestrictFieldDef.At(fieldL, K)))
		scalarSize := a.Have(
			"the scalar field has as many points as K",
			"field_size(F) = card(K)",
			Simp(Fwd(Fdef), Fwd(FieldSizeDef), Fwd(field.RestrictFieldDef), Fwd(field.FieldCarrierDef)),
			Basic())
		spaceCarrier := a.Have(
			"the restricted module has carrier M",
			"V.carrier = M",
			Simp(Fwd(Vdef), Fwd(module_record.RestrictModuleDef), Fwd(module_record.ModCarrierDef)),
			Basic())
		moduleData := a.Have(
			"the extension is a finite dimensional module",
			"module_on(field_ring(F), V) ∧ finite_dimensional(field_ring(F), V)",
			By(
				Normalized,
				Vdef,
				scalarData,
				given,
				field_extension.ExtensionModuleOn.Read(L).At(K, M),
				field_extension.FiniteExtensionDef.At(fieldL, K, M)))
		a.Show(
			"M has as many points as a vector space of dimension [M:K] over K",
			By(
				Normalized,
				Vdef,
				moduleData,
				scalarData,
				scalarSize,
				spaceCarrier,
				FiniteDimensionalSpaceSize.At(F, V),
				field_extension.ExtensionDegreeDef.At(fieldL, K, M)))
	}),
})}

// FiniteSubfieldSize — a finite subfield E above k is a finite extension of
// k, with card(k)^[E:k] points: E is a vector space over k, its finite
// carrier holds a basis, and FiniteExtensionSize counts it.
var FiniteSubfieldSize = finiteSubfieldSizeThm{family.Add(registry.ProofEntry{
	Name: "FiniteSubfieldSize",
	Key:  "prop_96e2ddbdd154102c",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k E:set(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, E)",
			"k ⊆ E",
			"finite(E)",
		},
		Conclusion: "finite_extension(M, k, E) ∧ card(E) = card(k) ^ extension_degree(M, k, E)",
		Abbrev: Abbrev{
			{Name: "scalars", Text: "restrict_ring(field_ring(M), k)"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(M)), E)"},
		},
	}, func(a *Argument, M field.FieldFact[on.M], k, E *Expr[Set[A]], h Fact) {
		given := a.Conjuncts(
			h,
			"k is a subfield",
			"E is a subfield",
			"k lies in E",
			"E is finite")
		subK, subE, kInE, finiteE := given[0], given[1], given[2], given[3]
		R := a.TermAs[RingOps[A]]("«scalars»")
		V := a.TermAs[ModuleOps[A, A]]("«vectors»")
		inverse := a.TermAs[Fun[A, A]]("M.inv")
		space := a.Have(
			"E is a vector space over k",
			"module_on(«scalars», «vectors»)",
			By(subK, subE, kInE, field_extension.ExtensionModuleOn.Read(M).At(k, E)))
		scalarField := a.Have(
			"k is a field of scalars, with the inverse of M",
			"ring_subfield(«scalars», M.inv, k)",
			By(subK, field.SubfieldRingSubfield.Read(M).At(k, k)))
		B, basis := a.ObtainAs[Set[A]](
			"choose a basis of E over k",
			"∃B:set(A). module_basis(«scalars», «vectors», B)",
			By(space, scalarField, linear_independence.BasisExists.At(R, V, inverse)))
		finiteB := a.Have(
			"the basis lies in the finite set E",
			"finite(B)",
			By(
				basis,
				finiteE,
				linear_independence.BasisInCarrier.At(R, V, B),
				finite_set.FiniteSubset.At(B, E)))
		extension := a.Have(
			"so E is finite over k",
			"finite_extension(M, k, E)",
			By(subK, subE, kInE, finiteB, basis, field_extension.BasisDegree.Read(M).At(k, E, B)))
		finiteK := a.Have(
			"k lies in E, so it is finite",
			"finite(k)",
			By(finiteE, kInE, finite_set.FiniteSubset.At(k, E)))
		count := a.Have(
			"a finite extension of a finite subfield has card(k)^[E:k] points",
			"has_size(E, card(k) ^ extension_degree(M, k, E))",
			By(subK, subE, kInE, finiteK, extension, FiniteExtensionSize.Read(M).At(k, E)))
		a.Show(
			"so E is finite over k and has card(k)^[E:k] points",
			By(
				extension,
				count,
				cardinality.CardOfSized.At(E, a.TermAs[Nat]("card(k) ^ extension_degree(M, k, E)"))))
	}),
})}

// AlgebraicOverFiniteLocallyFinite — a field algebraic over a finite
// subfield k is locally finite: a finite set S of its elements, each
// algebraic over k, generates over k a finite extension k(S), and a finite
// extension of the finite field k is finite.
var AlgebraicOverFiniteLocallyFinite = algebraicOverFiniteLocallyFiniteThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicOverFiniteLocallyFinite",
	Key:  "prop_2625b182e8c75b59",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A).",
		Hypotheses: []string{
			"subfield(L, k)",
			"finite(k)",
			"∀x:A. x ∈ L.carrier ⇒ algebraic_over(L, k, x)",
		},
		Conclusion: "locally_finite_field(L)",
	}, func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], subfieldK, finiteK, algebraic Fact) {
		generated := a.Have(
			"a finite set S of elements of L lies in k(S), the subfield it generates over k, which is finite",
			"∀S:set(A). finite(S) ∧ S ⊆ L.carrier ⇒ ∃K:set(A). subfield(L, K) ∧ finite(K) ∧ S ⊆ K",
			Derive(func(b *Argument) {
				S := b.FixAs[Set[A]]("S")
				given := b.Conjuncts(
					b.Assume(),
					"S is finite",
					"S lies in L")
				finiteS, inL := given[0], given[1]
				adjoined := b.TermAs[Set[A]]("field_adjoin(L, k, S)")
				extension := b.Have(
					"every element of S is algebraic over k, so k(S) is a finite extension of k",
					"finite_extension(L, k, field_adjoin(L, k, S))",
					By(
						algebraic,
						subfieldK,
						finiteS,
						inL,
						set_basic.SubsetDef,
						algebraic_element.FiniteAlgebraicAdjoin.Read(L).At(k, S)))
				between := b.Have(
					"k(S) is a subfield of L containing k and S",
					"subfield(L, field_adjoin(L, k, S)) ∧ k ⊆ field_adjoin(L, k, S) ∧ S ⊆ field_adjoin(L, k, S)",
					By(
						subfieldK,
						inL,
						field.SubfieldSubset.At(b.TermAs[FieldOps[A]]("L"), k),
						algebraic_element.AdjoinSubfield.Read(L).At(k, S)))
				b.Take(adjoined)
				b.Show(
					"a finite extension of the finite field k is finite",
					By(
						finiteK,
						subfieldK,
						between,
						extension,
						FiniteExtensionSize.Read(L).At(k, adjoined),
						cardinality.HasSizeDef))
			}))
		a.Show(
			"L is a field, and every finite set of its elements lies in a finite subfield",
			By(L, generated, LocallyFiniteFieldDef))
	}),
})}

// ProjectiveCount — deleting zero from each line through the origin leaves
// a punctured line of q−1 vectors, and the punctured lines partition the
// nonzero vectors.
var ProjectiveCount = projectiveCountThm{family.Add(registry.ProofEntry{
	Name: "ProjectiveCount",
	Key:  "prop_4f0e77cc5575d213",
	Reading: "The subspaces include their zero vector, but the indexing vectors are " +
		"nonzero. In dimension zero the line set is empty and the multiplied equation is 0=0.",
	Build: family.Sections(Statement{
		Binders: "∀F:field_ops(A). ∀M:module_ops(A, B).",
		Hypotheses: []string{
			"finite_field(F)",
			"module_on(field_ring(F), M)",
			"finite_dimensional(field_ring(F), M)",
		},
		Conclusion: "finite(«lines») ∧ " +
			"card(«lines») * (field_size(F) - 1) = field_size(F) ^ module_dim(field_ring(F), M) - 1",
		Abbrev: Abbrev{
			{Name: "line", Text: "λv:B. image(λc:A. M.smul(c, v), F.carrier)"},
			{Name: "lines", Text: "{«line»(v) | v:B | v ∈ M.carrier ∧ v ≠ M.zero}"},
			{Name: "puncture", Text: "λl:set(B). delete(l, M.zero)"},
			{Name: "punctured", Text: "image(«puncture», «lines»)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		finiteField := finiteFieldFacts(ctx)

		inverseScalar := ctx.Lemma(Statement{
			Binders: "∀F:field_ops(A). ∀M:module_ops(A, B). ∀c:A. ∀v:B.",
			Hypotheses: []string{
				"field_on(F)",
				"module_on(field_ring(F), M)",
				"c ∈ F.carrier",
				"c ≠ F.zero",
				"v ∈ M.carrier",
			},
			Conclusion: "M.smul(F.inv(c), M.smul(c, v)) = v",
		}, func(
			a *Argument,
			F *Expr[FieldOps[A]],
			fieldOn field.FieldFact[on.F],
			M *Expr[ModuleOps[A, B]],
			c *Expr[A],
			v *Expr[B],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"M is a module over F",
				"c is a scalar",
				"c is nonzero",
				"v lies in the module carrier")
			moduleOn := given[0]
			a.Show(
				"multiplication by the inverse scalar undoes multiplication by c",
				Simp(
					Rev(module.SmulMul.Read(moduleOn)),
					Fwd(field.MulLeftInverseOn.Read(fieldOn)),
					Fwd(module.SmulOne.Read(moduleOn)),
					Fwd(field.InvIn.Read(fieldOn))),
				Refl())
		})

		zeroMultiple := ctx.Lemma(Statement{
			Binders: "∀F:field_ops(A). ∀M:module_ops(A, B). ∀c:A. ∀v:B.",
			Hypotheses: []string{
				"field_on(F)",
				"module_on(field_ring(F), M)",
				"c ∈ F.carrier",
				"v ∈ M.carrier",
				"v ≠ M.zero",
			},
			Conclusion: "M.smul(c, v) = M.zero ⇔ c = F.zero",
		}, func(
			a *Argument,
			F *Expr[FieldOps[A]],
			fieldOn field.FieldFact[on.F],
			M *Expr[ModuleOps[A, B]],
			c *Expr[A],
			v *Expr[B],
			h Fact,
		) {
			R := a.TermAs[RingOps[A]]("field_ring(F)")
			inverseC := a.TermAs[A]("F.inv(c)")
			a.Show(
				"a multiple of a nonzero vector vanishes exactly at scalar zero",
				By(
					Normalized,
					fieldOn,
					h,
					At(inverseScalar, F, M, c, v),
					field.InvIn.At(F, c),
					module.SmulZero.At(R, M, inverseC),
					module.ZeroSmul.At(R, M, v)))
		})

		scalarInjective := ctx.Lemma(Statement{
			Binders: "∀F:field_ops(A). ∀M:module_ops(A, B). ∀v:B.",
			Hypotheses: []string{
				"field_on(F)",
				"module_on(field_ring(F), M)",
				"v ∈ M.carrier",
				"v ≠ M.zero",
			},
			Conclusion: "injective_on(F.carrier, λc:A. M.smul(c, v))",
		}, func(
			a *Argument,
			F *Expr[FieldOps[A]],
			fieldOn field.FieldFact[on.F],
			M *Expr[ModuleOps[A, B]],
			v *Expr[B],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"M is a module over F",
				"v lies in the module carrier",
				"v is nonzero")
			moduleOn, vIn, vNonzero := given[0], given[1], given[2]
			ring := field.RingOn.Read(fieldOn)
			additive := module.AddGroupOn.Read(moduleOn)
			a.Do(Unfold(functions.InjectiveOnDef))
			x := a.FixAs[A]("x")
			y := a.FixAs[A]("y")
			same := a.Assume()
			negativeY := a.TermAs[A]("F.neg(y)")
			difference := a.TermAs[A]("F.add(x, F.neg(y))")
			multipleY := a.TermAs[B]("M.smul(y, v)")
			differenceMultiple := a.Have(
				"the difference of the scalars annihilates v",
				"M.smul(F.add(x, F.neg(y)), v) = M.zero",
				By(
					vIn,
					same,
					module.SmulAddRight.Read(moduleOn).AsFact().At(x, negativeY, v),
					module.NegSmul.Read(moduleOn).AsFact().At(y, v),
					group.RightInverseOn.Read(additive).AsFact().At(multipleY),
					module.SmulIn.Read(moduleOn).AsFact().At(y, v),
					comm_ring.NegIn.Read(ring).AsFact().At(y)))
			differenceIn := a.Have(
				"the difference lies in the scalar carrier",
				"F.add(x, F.neg(y)) ∈ F.carrier",
				By(
					same,
					comm_ring.AddIn.Read(ring).AsFact().At(x, negativeY),
					comm_ring.NegIn.Read(ring).AsFact().At(y)))
			differenceZero := a.Have(
				"the difference must therefore be zero",
				"F.add(x, F.neg(y)) = F.zero",
				By(
					fieldOn,
					vNonzero,
					differenceMultiple,
					moduleOn,
					differenceIn,
					vIn,
					At(zeroMultiple, F, M, difference, v)))
			a.Show(
				"the two scalar coefficients agree",
				ByArith(fieldOn, differenceZero, same))
		})

		rescaleLine := ctx.Lemma(Statement{
			Binders: "∀F:field_ops(A). ∀M:module_ops(A, B). ∀t:A. ∀v:B.",
			Hypotheses: []string{
				"field_on(F)",
				"module_on(field_ring(F), M)",
				"t ∈ F.carrier",
				"t ≠ F.zero",
				"v ∈ M.carrier",
			},
			Conclusion: "«line»(M.smul(t, v)) = «line»(v)",
		}, func(
			a *Argument,
			F *Expr[FieldOps[A]],
			fieldOn field.FieldFact[on.F],
			M *Expr[ModuleOps[A, B]],
			t *Expr[A],
			v *Expr[B],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"M is a module over F",
				"t is a scalar",
				"t is nonzero",
				"v lies in the module carrier")
			moduleOn, tIn, tNonzero, vIn := given[0], given[1], given[2], given[3]
			ring := field.RingOn.Read(fieldOn)
			inverseT := a.TermAs[A]("F.inv(t)")
			scaled := a.TermAs[B]("M.smul(t, v)")
			forwardMap := a.Have(
				"multiplication by t carries scalar coefficients forward",
				"∀c:A. c ∈ F.carrier ⇒ F.mul(c, t) ∈ F.carrier ∧ M.smul(c, M.smul(t, v)) = M.smul(F.mul(c, t), v)",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					cIn := b.Assume()
					b.Show(
						"the product is a scalar and associativity gives the same vector",
						By(
							tIn,
							cIn,
							vIn,
							comm_ring.MulIn.Read(ring).At(b.MemberOf[on.F](c, cIn), b.MemberOf[on.F](t, tIn)),
							module.SmulMul.Read(moduleOn).AsFact().At(c, t, v)))
				}))
			reverseMap := a.Have(
				"multiplication by the inverse scalar gives coefficients in the other direction",
				Statement{
					Binders:    "∀c:A.",
					Hypotheses: []string{"c ∈ F.carrier"},
					Conclusion: "F.mul(c, F.inv(t)) ∈ F.carrier ∧ " +
						"M.smul(F.mul(c, F.inv(t)), M.smul(t, v)) = M.smul(c, v)",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					cIn := b.Assume()
					b.Show(
						"inverse rescaling stays in the field and recovers the vector",
						By(
							tNonzero,
							tIn,
							cIn,
							vIn,
							field.InvIn.Read(fieldOn).AsFact().At(t),
							comm_ring.MulIn.Read(ring).AsFact().At(c, inverseT),
							module.SmulIn.Read(moduleOn).AsFact().At(t, v),
							module.SmulMul.Read(moduleOn).AsFact().At(c, inverseT, scaled),
							At(inverseScalar, F, M, t, v)))
				}))
			a.Show(
				"the two scalar images are equal",
				Simp(Fwd(set_basic.Extension)),
				BySets(forwardMap, reverseMap))
		})

		lineFromNonzeroPoint := ctx.Lemma(Statement{
			Binders: "∀F:field_ops(A). ∀M:module_ops(A, B). ∀v w:B.",
			Hypotheses: []string{
				"field_on(F)",
				"module_on(field_ring(F), M)",
				"v ∈ M.carrier",
				"w ∈ «line»(v)",
				"w ≠ M.zero",
			},
			Conclusion: "«line»(w) = «line»(v)",
		}, func(
			a *Argument,
			F *Expr[FieldOps[A]],
			fieldOn field.FieldFact[on.F],
			M *Expr[ModuleOps[A, B]],
			v, w *Expr[B],
			h Fact,
		) {
			R := a.TermAs[RingOps[A]]("field_ring(F)")
			scalarMap := a.TermAs[Fun[A, B]]("λc:A. M.smul(c, v)")
			scalarCarrier := a.TermAs[Set[A]]("F.carrier")
			c, represented := a.ObtainAs[A](
				"a scalar represents w on the line through v",
				"∃c:A. c ∈ F.carrier ∧ w = M.smul(c, v)",
				By(Normalized, fieldOn, h, set_basic.InImage.At(scalarMap, scalarCarrier, w)))
			cNonzero := a.Have(
				"the representing scalar is nonzero",
				"c ≠ F.zero",
				By(Normalized, represented, fieldOn, h, module.ZeroSmul.At(R, M, v)))
			a.Show(
				"a nonzero point generates the same line",
				By(cNonzero, represented, fieldOn, h, At(rescaleLine, F, M, c, v)))
		})

		lineCarrier := ctx.Lemma(Statement{
			Binders: "∀F:field_ops(A). ∀M:module_ops(A, B). ∀v:B.",
			Hypotheses: []string{
				"field_on(F)",
				"module_on(field_ring(F), M)",
				"v ∈ M.carrier",
			},
			Conclusion: "M.zero ∈ «line»(v) ∧ v ∈ «line»(v) ∧ «line»(v) ⊆ M.carrier",
		}, func(
			a *Argument,
			F *Expr[FieldOps[A]],
			fieldOn field.FieldFact[on.F],
			M *Expr[ModuleOps[A, B]],
			v *Expr[B],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"M is a module over F",
				"v lies in the module carrier")
			moduleOn, vIn := given[0], given[1]
			ring := field.RingOn.Read(fieldOn)
			a.Show(
				"the scalar image contains zero and v and stays in the module carrier",
				BySets(
					module.SmulIn.Read(moduleOn),
					comm_ring.ZeroIn.Read(ring),
					comm_ring.OneIn.Read(ring),
					vIn,
					module.ZeroSmul.Read(moduleOn).AsFact().At(v),
					module.SmulOne.Read(moduleOn).AsFact().At(v)))
		})

		puncturedLineSize := ctx.Lemma(Statement{
			Binders: "∀F:field_ops(A). ∀M:module_ops(A, B). ∀v:B.",
			Hypotheses: []string{
				"finite_field(F)",
				"module_on(field_ring(F), M)",
				"v ∈ M.carrier",
				"v ≠ M.zero",
			},
			Conclusion: "has_size(delete(«line»(v), M.zero), field_size(F) - 1)",
		}, func(a *Argument, F *Expr[FieldOps[A]], M *Expr[ModuleOps[A, B]], v *Expr[B], h Fact) {
			given := a.Conjuncts(
				h,
				"F is a finite field",
				"M is a module over F",
				"v lies in the module carrier",
				"v is nonzero")
			moduleOn, vIn, vNonzero := given[1], given[2], given[3]
			fieldFacts := a.Conjuncts(
				GroupPremises(given[0], At(finiteField, F)),
				"F is a field",
				"the scalar carrier has q elements")
			fieldOn, scalarSize := fieldFacts[0], fieldFacts[1]
			scalarCarrier := a.TermAs[Set[A]]("F.carrier")
			q := a.TermAs[Nat]("field_size(F)")
			scalarMap := a.TermAs[Fun[A, B]]("λc:A. M.smul(c, v)")
			line := a.TermAs[Set[B]]("«line»(v)")
			lineCount := a.Have(
				"injective scalar multiplication gives q points on the line",
				"has_size(«line»(v), field_size(F))",
				By(
					fieldOn,
					vNonzero,
					scalarSize,
					moduleOn,
					vIn,
					At(scalarInjective, F, M, v),
					cardinality.HasSizeImageInj.At(scalarMap, scalarCarrier, q)))
			zero := a.TermAs[B]("M.zero")
			punctured := a.TermAs[Set[B]]("delete(«line»(v), M.zero)")
			puncturedSize := a.TermAs[Nat]("field_size(F) - 1")
			a.Show(
				"deleting zero, which lies on the line, leaves q−1 vectors",
				By(
					lineCount,
					fieldOn,
					moduleOn,
					vIn,
					At(lineCarrier, F, M, v),
					cardinality.HasSizeDef.At(line, q),
					cardinality.HasSizeDef.At(punctured, puncturedSize),
					finite_set.FiniteDelete.At(line, zero),
					cardinality.CardDelete.At(line, zero)))
		})

		linesDisjointOrEqual := ctx.Lemma(Statement{
			Binders: "∀F:field_ops(A). ∀M:module_ops(A, B). ∀v w:B.",
			Hypotheses: []string{
				"field_on(F)",
				"module_on(field_ring(F), M)",
				"v ∈ M.carrier",
				"w ∈ M.carrier",
			},
			Conclusion: "«line»(v) = «line»(w) ∨ " +
				"disjoint(delete(«line»(v), M.zero), delete(«line»(w), M.zero))",
		}, func(
			a *Argument,
			F *Expr[FieldOps[A]],
			fieldOn field.FieldFact[on.F],
			M *Expr[ModuleOps[A, B]],
			v, w *Expr[B],
			h Fact,
		) {
			neither := a.SupposeNot()
			z, shared := a.ObtainAs[B](
				"failure of disjointness supplies a shared nonzero point",
				"∃z:B. z ∈ «line»(v) ∧ z ∈ «line»(w) ∧ z ≠ M.zero",
				BySets(neither))
			a.Show(
				"both lines are the line generated by that point",
				By(
					neither,
					shared,
					fieldOn,
					h,
					At(lineFromNonzeroPoint, F, M, v, z),
					At(lineFromNonzeroPoint, F, M, w, z)))
		})

		partition := ctx.Lemma(Statement{
			Binders: "∀F:field_ops(A). ∀M:module_ops(A, B).",
			Hypotheses: []string{
				"finite_field(F)",
				"module_on(field_ring(F), M)",
			},
			Conclusion: "(∀X:set(B). X ∈ «punctured» ⇒ has_size(X, field_size(F) - 1)) ∧ " +
				"(∀X Y:set(B). X ∈ «punctured» ∧ Y ∈ «punctured» ∧ X ≠ Y ⇒ disjoint(X, Y)) ∧ " +
				"⋃«punctured» = delete(M.carrier, M.zero)",
		}, func(a *Argument, F *Expr[FieldOps[A]], M *Expr[ModuleOps[A, B]], h Fact) {
			given := a.Conjuncts(
				h,
				"F is a finite field",
				"M is a module over F")
			finiteF, moduleOn := given[0], given[1]
			fieldOn := a.Conjuncts(
				GroupPremises(given[0], At(finiteField, F)),
				"F is a field",
				"the scalar carrier has q elements")[0]
			generated := a.Have(
				"each punctured line is the line of a nonzero vector with zero deleted",
				"∀X:set(B). X ∈ «punctured» ⇒ ∃v:B. v ∈ M.carrier ∧ v ≠ M.zero ∧ X = delete(«line»(v), M.zero)",
				BySets())
			sizes := a.Have(
				"every punctured line has q−1 vectors",
				"∀X:set(B). X ∈ «punctured» ⇒ has_size(X, field_size(F) - 1)",
				Derive(func(b *Argument) {
					X := b.FixAs[Set[B]]("X")
					xInImage := b.Assume()
					v, source := b.UnpackAs[B](GroupPremises(xInImage, generated.At(X)), "v")
					generator := b.Conjuncts(
						source,
						"v lies in the carrier",
						"v is nonzero",
						"X is the line through v with zero deleted")
					b.Show(
						"the line through v has q−1 nonzero vectors",
						generator[2].Rw(),
						By(generator[0], generator[1], finiteF, moduleOn, At(puncturedLineSize, F, M, v)))
				}))
			disjoint := a.Have(
				"distinct punctured lines are disjoint",
				"∀X Y:set(B). X ∈ «punctured» ∧ Y ∈ «punctured» ∧ X ≠ Y ⇒ disjoint(X, Y)",
				Derive(func(b *Argument) {
					X := b.FixAs[Set[B]]("X")
					Y := b.FixAs[Set[B]]("Y")
					distinct := b.Assume()
					v, sourceV := b.UnpackAs[B](GroupPremises(distinct, generated.At(X)), "v")
					w, sourceW := b.UnpackAs[B](GroupPremises(distinct, generated.At(Y)), "w")
					generatorV := b.Conjuncts(
						sourceV,
						"v lies in the carrier",
						"v is nonzero",
						"X is the line through v with zero deleted")
					generatorW := b.Conjuncts(
						sourceW,
						"w lies in the carrier",
						"w is nonzero",
						"Y is the line through w with zero deleted")
					b.Show(
						"distinct punctured lines come from distinct lines, which share only zero",
						generatorV[2].Rw(),
						generatorW[2].Rw(),
						By(distinct, generatorV[0], generatorW[0], fieldOn, moduleOn, At(linesDisjointOrEqual, F, M, v, w)))
				}))
			covered := a.Have(
				"the punctured lines cover exactly the nonzero vectors",
				"⋃«punctured» = delete(M.carrier, M.zero)",
				BySets(fieldOn, moduleOn, At(lineCarrier, F, M)))
			a.Show(
				"the punctured lines partition the nonzero vectors",
				By(sizes, disjoint, covered))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			F *Expr[FieldOps[A]],
			M *Expr[ModuleOps[A, B]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"F is a finite field",
				"M is a module over F",
				"M is finite-dimensional")
			moduleOn := given[1]
			fieldOn := a.Conjuncts(
				GroupPremises(given[0], At(finiteField, F)),
				"F is a field",
				"the scalar carrier has q elements")[0]
			line := a.TermAs[Fun[B, Set[B]]]("«line»")
			lines := a.TermAs[Set[Set[B]]]("«lines»")
			puncture := a.TermAs[Fun[Set[B], Set[B]]]("«puncture»")
			punctured := a.TermAs[Set[Set[B]]]("«punctured»")
			nonzero := a.TermAs[Set[B]]("delete(M.carrier, M.zero)")
			puncturedSize := a.TermAs[Nat]("field_size(F) - 1")
			nonzeroTotal := a.TermAs[Nat]("field_size(F) ^ module_dim(field_ring(F), M) - 1")
			nonzeroCount := a.Have(
				"deleting zero leaves q^n−1 vectors",
				"has_size(delete(M.carrier, M.zero), field_size(F) ^ module_dim(field_ring(F), M) - 1)",
				Derive(func(b *Argument) {
					carrier := b.TermAs[Set[B]]("M.carrier")
					zero := b.TermAs[B]("M.zero")
					total := b.TermAs[Nat]("field_size(F) ^ module_dim(field_ring(F), M)")
					vectorCount := b.Have(
						"the module carrier has q^n vectors",
						"has_size(M.carrier, field_size(F) ^ module_dim(field_ring(F), M))",
						By(h, FiniteDimensionalSpaceSize.At(F, M)))
					zeroIn := b.Have(
						"module zero lies in the carrier",
						"M.zero ∈ M.carrier",
						By(group.OneIn.Read(module.AddGroupOn.Read(moduleOn))))
					b.Show(
						"deleting a member of a finite set lowers its count by one",
						By(
							vectorCount,
							zeroIn,
							cardinality.HasSizeDef.At(carrier, total),
							cardinality.HasSizeDef.At(nonzero, nonzeroTotal),
							finite_set.FiniteDelete.At(carrier, zero),
							cardinality.CardDelete.At(carrier, zero)))
				}))
			finiteLines := a.Have(
				"the lines are the image of the finitely many nonzero vectors",
				"finite(«lines»)",
				Derive(func(b *Argument) {
					comprehension := b.Have(
						"the nonzero vectors are the comprehension the line set ranges over",
						"delete(M.carrier, M.zero) = {v:B | v ∈ M.carrier ∧ v ≠ M.zero}",
						BySets())
					nonzeroCondition := b.TermAs[Fun[B, Bool]]("λv:B. v ∈ M.carrier ∧ v ≠ M.zero")
					image := b.Have(
						"the line set is the image of the nonzero vectors",
						"«lines» = image(«line», delete(M.carrier, M.zero))",
						By(comprehension, set_image.SimpleImageGen.At(line, nonzeroCondition)))
					b.Show(
						"the image of a finite set is finite",
						By(
							nonzeroCount,
							image,
							finite_set.FiniteImage.At(line, nonzero),
							cardinality.HasSizeDef.At(nonzero, nonzeroTotal)))
				}))
			sameCount := a.Have(
				"there are as many punctured lines as lines",
				"card(«punctured») = card(«lines»)",
				Derive(func(b *Argument) {
					containsZero := b.Have(
						"every line contains zero",
						"∀l:set(B). l ∈ «lines» ⇒ M.zero ∈ l",
						Derive(func(c *Argument) {
							c.FixAs[Set[B]]("l")
							inLines := c.Assume()
							v, source := c.ObtainAs[B](
								"a nonzero vector spans l",
								"∃v:B. v ∈ M.carrier ∧ v ≠ M.zero ∧ l = «line»(v)",
								BySets(inLines))
							generator := c.Conjuncts(
								source,
								"v lies in the carrier",
								"v is nonzero",
								"l is the line through v")
							c.Show(
								"the line through v contains zero",
								generator[2].Rw(),
								By(generator[0], fieldOn, moduleOn, At(lineCarrier, F, M, v)))
						}))
					injective := b.Have(
						"deleting the common zero keeps distinct lines apart",
						"injective_on(«lines», «puncture»)",
						Derive(func(c *Argument) {
							c.Do(Unfold(functions.InjectiveOnDef))
							x := c.FixAs[Set[B]]("x")
							y := c.FixAs[Set[B]]("y")
							same := c.Assume()
							c.Show(
								"putting zero back into both gives equality",
								BySets(containsZero.At(x), containsZero.At(y), same))
						}))
					b.Show(
						"an injective map keeps the count",
						By(finiteLines, injective, cardinality.CardImageInj.At(puncture, lines)))
				}))
			partitionCount := a.Have(
				"the nonzero vectors number q−1 per punctured line",
				"has_size(delete(M.carrier, M.zero), (field_size(F) - 1) * card(«punctured»))",
				Derive(func(b *Argument) {
					partitioned := b.Conjuncts(
						GroupPremises(given[0], given[1], At(partition, F, M)),
						"every punctured line has q−1 vectors",
						"distinct punctured lines are disjoint",
						"the punctured lines cover the nonzero vectors")
					b.Show(
						"a finite disjoint union of equally sized sets has the product size",
						partitioned[2].RwRev(),
						By(
							partitioned[0],
							partitioned[1],
							finiteLines,
							finite_set.FiniteImage.At(puncture, lines),
							cardinality.HasSizeUnions.At(punctured, puncturedSize)))
				}))
			lineCount := a.TermAs[Nat]("card(«lines»)")
			partitionTotal := a.TermAs[Nat]("(field_size(F) - 1) * card(«punctured»)")
			a.Show(
				"comparing the two counts of the nonzero vectors gives the projective formula",
				By(
					finiteLines,
					sameCount,
					partitionCount,
					nonzeroCount,
					cardinality.CardOfSized.At(nonzero, partitionTotal),
					cardinality.CardOfSized.At(nonzero, nonzeroTotal),
					nat_arith.MulSym.At(lineCount, puncturedSize)))
		})
	}),
})}
