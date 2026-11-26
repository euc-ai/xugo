package linear_pairing

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// NondegeneratePairingDualityIso — a finite-dimensional left-nondegenerate
// bilinear pairing identifies its module with the dual: the pairing map
// is linear, its kernel is zero, and its image has the dual's dimension.
var NondegeneratePairingDualityIso = nondegeneratePairingDualityIsoThm{family.Add(registry.ProofEntry{
	Name: "NondegeneratePairingDualityIso",
	Key:  "prop_d7150d03b82c5ab8",
	Build: family.Theorem(Statement{
		Binders: "∀K:field_on(A). ∀M:module_ops(A, B). ∀b:(B → B → A).",
		Hypotheses: []string{
			"module_on(field_ring(K), M)",
			"finite_dimensional(field_ring(K), M)",
			"bilinear_pairing(field_ring(K), M, b)",
			"pairing_nondegenerate(field_ring(K), M, b)",
		},
		Conclusion: "module_isomorphism(field_ring(K), " +
			"    M, " +
			"    hom_module(field_ring(K), M, regular_module(field_ring(K))), " +
			"    λx:B. λy:B. COND(y ∈ M.carrier, b(x, y), K.zero))",
	}, func(
		a *Argument,
		K field.FieldFact[on.K],
		M *Expr[ModuleOps[A, B]],
		b *Arrow2[B, B, A],
		data Fact,
	) {
		given := a.Conjuncts(
			data,
			"M is a module",
			"M has finite dimension",
			"the pairing is bilinear",
			"the pairing is left-nondegenerate")
		moduleM, finiteM, bilinear, nondegenerate := given[0], given[1], given[2], given[3]
		R := a.TermAs[RingOps[A]]("field_ring(K)")
		T := a.TermAs[ModuleOps[A, A]]("regular_module(field_ring(K))")
		D, dualDef := a.LetAs[ModuleOps[A, Fun[B, A]]](
			"D", "hom_module(field_ring(K), M, regular_module(field_ring(K)))")
		F, mapDef := a.LetAs[Fun2[B, B, A]]("F", "λx:B. λy:B. COND(y ∈ M.carrier, b(x, y), K.zero)")
		dual := a.Have(
			"the dual is a module",
			"module_on(field_ring(K), D)",
			By(
				Normalized,
				dualDef,
				module.RegularModuleOn.Read(field.RingOn.Read(K)),
				moduleM,
				hom_module.HomSetModuleOn.At(R, M, T)))
		columns := a.Have(
			"each normalized pairing functional is linear",
			"∀x:B. x ∈ M.carrier ⇒ module_homomorphism(field_ring(K), M, regular_module(field_ring(K)), F(x))",
			Derive(func(q *Argument) {
				q.FixAs[B]("x")
				xIn := q.Assume()
				q.Show(
					"normalization preserves the functional on M",
					By(
						Normalized,
						mapDef,
						xIn,
						bilinear,
						BilinearPairingDef.At(R, M, b),
						module_homomorphism.HomCongruence.At(
							R, M, T, q.TermAs[Fun[B, A]]("b(x)"), q.TermAs[Fun[B, A]]("F(x)"))))
			}))
		dualCarrier := a.Have(
			"the dual consists of normalized linear maps",
			"D.carrier = hom_set(field_ring(K), M, regular_module(field_ring(K)))",
			Simp(Fwd(dualDef), Fwd(hom_module.HomModuleDef), Fwd(module_record.ModCarrierDef)),
			Basic())
		lands := a.Have(
			"the pairing map takes values in the dual",
			"∀x:B. x ∈ M.carrier ⇒ F(x) ∈ D.carrier",
			By(
				Normalized,
				columns,
				mapDef,
				dualCarrier,
				hom_module.InHomSet.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B](), TypeBinder.BindC[A]()).At(
					R, M, T)))
		dualOps := a.Have(
			"dual addition and scaling are pointwise",
			"D.add = (λf:(B → A). λg:(B → A). λy:B. K.add(f(y), g(y))) ∧ "+
				"D.smul = (λc:A. λf:(B → A). λy:B. K.mul(c, f(y)))",
			Simp(
				Fwd(dualDef),
				Fwd(module_record.RegularModuleDef),
				Fwd(field.FieldRingDef),
				Fwd(module_record.RingAddDef),
				Fwd(module_record.RingMulDef),
				Fwd(hom_module.HomModuleDef),
				Fwd(module_record.ModAddDef),
				Fwd(module_record.ModSmulDef),
				Fwd(function_module.FunAddDef),
				Fwd(function_module.FunSmulDef)),
			Basic())
		rows := a.Have(
			"the pairing is linear in its first variable",
			Statement{
				Binders: "∀y:B.",
				Hypotheses: []string{
					"y ∈ M.carrier",
				},
				Conclusion: "module_homomorphism(field_ring(K), M, regular_module(field_ring(K)), λx:B. b(x, y))",
			},
			By(bilinear, BilinearPairingDef.At(R, M, b)))

		additive := a.Have(
			"the pairing map preserves addition",
			"∀u v:B. u ∈ M.carrier ∧ v ∈ M.carrier ⇒ F(M.add(u, v)) = D.add(F(u), F(v))",
			Derive(func(q *Argument) {
				q.FixAs[B]("u")
				q.FixAs[B]("v")
				q.Assume()
				// Compare the two functionals at an arbitrary argument.
				q.Do(Funext())
				y := q.FixAs[B]("y")
				q.Cases(q.Term("y ∈ M.carrier"))
				q.When(
					"on M, additivity is the linearity of a pairing slice",
					func(r *Argument, yIn Fact) {
						slice := r.Have(
							"fix the second pairing argument",
							"module_homomorphism(field_ring(K), M, regular_module(field_ring(K)), λx:B. b(x, y))",
							By(rows.At(y), yIn))
						r.Show(
							"the slice preserves the sum",
							Simp(
								Fwd(mapDef),
								Fwd(dualOps),
								Fwd(module_homomorphism.HomAdd.Read(slice)),
								Fwd(module_record.RegularModuleDef),
								Fwd(module_record.ModAddDef),
								Fwd(field.FieldRingDef),
								Fwd(module_record.RingAddDef)),
							Basic())
					})
				q.Otherwise(
					"outside M the functionals vanish",
					func(r *Argument, outside Fact) {
						r.Do(Simp(Fwd(mapDef), Fwd(dualOps)))
						r.Show(
							"zero plus zero is zero",
							ByArith(K))
					})
			}))
		scaled := a.Have(
			"the pairing map preserves scalar multiplication",
			"∀c:A. ∀u:B. c ∈ field_ring(K).carrier ∧ u ∈ M.carrier ⇒ F(M.smul(c, u)) = D.smul(c, F(u))",
			Derive(func(q *Argument) {
				c := q.FixAs[A]("c")
				u := q.FixAs[B]("u")
				inM := q.Assume()
				// Equality of the functionals follows by evaluation.
				q.Do(Funext())
				y := q.FixAs[B]("y")
				q.Cases(q.Term("y ∈ M.carrier"))
				q.When(
					"on M, the pairing slice preserves scaling",
					func(r *Argument, yIn Fact) {
						slice := r.Have(
							"fix the second pairing argument",
							"module_homomorphism(field_ring(K), M, regular_module(field_ring(K)), λx:B. b(x, y))",
							By(rows.At(y), yIn))
						scalarLaw := r.Have(
							"apply the slice to a scalar multiple",
							"b(M.smul(c, u), y) = regular_module(field_ring(K)).smul(c, b(u, y))",
							By(inM, module_homomorphism.HomSmul.Read(slice).AsFact().At(c, u)))
						r.Show(
							"normalization respects the scalar action",
							Simp(
								Fwd(mapDef),
								Fwd(dualOps),
								Fwd(scalarLaw),
								Fwd(module_record.RegularModuleDef),
								Fwd(module_record.ModSmulDef),
								Fwd(field.FieldRingDef),
								Fwd(module_record.RingMulDef)),
							Basic())
					})
				q.Otherwise(
					"outside M scalar multiples still vanish",
					func(r *Argument, outside Fact) {
						r.Do(Simp(Fwd(mapDef), Fwd(dualOps)))
						cIn := r.Have(
							"the scalar belongs to the field",
							"c ∈ K.carrier",
							By(inM, field.FieldRingDef.At(a.TermAs[FieldOps[A]]("K")), module_record.RingCarrierDef))
						r.Show(
							"a scalar times zero is zero",
							ByArith(K, cIn))
					})
			}))
		linear := a.Have(
			"the pairing map is linear",
			"module_homomorphism(field_ring(K), M, D, F)",
			By(
				scaled,
				additive,
				lands,
				moduleM,
				dual,
				module_homomorphism.ModuleHomomorphismDef.At(R, M, D, F)))

		dualZero := a.Have(
			"the zero functional vanishes everywhere",
			"D.zero = (λy:B. K.zero)",
			Simp(
				Fwd(dualDef),
				Fwd(hom_module.HomModuleDef),
				Fwd(module_record.ModZeroDef),
				Fwd(function_module.FunZeroDef),
				Fwd(module_record.RegularModuleDef),
				Fwd(field.FieldRingDef),
				Fwd(module_record.RingZeroDef)),
			Basic())
		separates := a.Have(
			"every nonzero vector has a nonzero pairing",
			"∀z:B. z ∈ M.carrier ∧ z ≠ M.zero ⇒ ∃y:B. y ∈ M.carrier ∧ b(z, y) ≠ K.zero",
			By(nondegenerate, PairingNondegenerateDef.At(R, M, b)))
		zeroKernel := a.Have(
			"nondegeneracy makes the kernel zero",
			"∀x:B. x ∈ M.carrier ∧ F(x) = D.zero ⇒ x = M.zero",
			Derive(func(q *Argument) {
				x := q.FixAs[B]("x")
				killed := q.Assume()
				annihilates := q.Have(
					"the zero functional pairs to zero",
					"∀y:B. y ∈ M.carrier ⇒ b(x, y) = K.zero",
					By(Normalized, killed, mapDef, dualZero))
				q.Show(
					"left nondegeneracy kills the vector",
					By(Normalized, separates.At(x), killed, annihilates))
			}))
		injective := a.Have(
			"equal pairing functionals have equal vectors",
			"injective_on(M.carrier, F)",
			Unfold(functions.InjectiveOnDef),
			Derive(func(q *Argument) {
				q.FixAs[B]("x")
				q.FixAs[B]("y")
				equalMaps := q.Assume()
				d, difference := q.LetAs[B]("d", "M.add(M.neg(x), y)")
				killed := q.Have(
					"their difference lies in the kernel",
					"d ∈ M.carrier ∧ F(d) = D.zero",
					ByChase(Depth(0), linear, equalMaps, difference))
				zero := q.Have(
					"the difference is zero",
					"d = M.zero",
					By(zeroKernel.At(d), killed))
				q.Show(
					"the two vectors agree",
					ByChase(Depth(0), moduleM, equalMaps, difference, zero))
			}))

		// The dimension laws read the field through its ring and inverse.
		inv := a.TermAs[Fun[A, A]]("K.inv")
		scalarsField := field.FieldRingSubfield.Read(K)
		image := a.TermAs[Set[Fun[B, A]]]("image(F, M.carrier)")
		subImage := a.Have(
			"the pairing image is a submodule of the dual",
			"submodule(field_ring(K), D, image(F, M.carrier))",
			By(module_homomorphism.ImageSubmodule.Read(linear)))
		dualDimension := a.Have(
			"the dual has M's finite dimension",
			"finite_dimensional(field_ring(K), D) ∧ "+
				"module_dim(field_ring(K), D) = module_dim(field_ring(K), M)",
			By(Normalized, dualDef, moduleM, finiteM, scalarsField, module_dimension.DualDim.At(R, M, inv)))
		imageDimension := a.Have(
			"the injective image has M's dimension",
			"finite_dimensional(field_ring(K), restrict_module(D, image(F, M.carrier))) ∧ "+
				"module_dim(field_ring(K), restrict_module(D, image(F, M.carrier))) = module_dim(field_ring(K), M)",
			By(
				scalarsField,
				linear,
				injective,
				finiteM,
				module_dimension.InjectiveImageDim.At(R, inv, M, D, F)))
		onto := a.Have(
			"the pairing image fills the dual",
			"image(F, M.carrier) = D.carrier",
			Derive(func(q *Argument) {
				equalDimension := q.Have(
					"the image and dual dimensions agree",
					"module_dim(field_ring(K), restrict_module(D, image(F, M.carrier))) = module_dim(field_ring(K), D)",
					By(dualDimension, imageDimension))
				q.Show(
					"a submodule of full finite dimension is the whole dual",
					By(
						dual,
						scalarsField,
						subImage,
						dualDimension,
						equalDimension,
						module_dimension.SubmoduleDimEq.At(R, D, inv, image)))
			}))
		a.Show(
			"linearity, injectivity and the full image give the isomorphism",
			By(linear, injective, onto, module_homomorphism.ModuleIsomorphismDef.At(R, M, D, F)))
	}),
})}

// NondegeneratePairingDualBasis — a left-nondegenerate bilinear pairing
// on M with a finite basis E has a unique dual basis d(e), b(d(e), f) =
// δ(e, f) on E, and expands every x as Σ_{e∈E} b(x, e) • d(e). E makes M
// finite-dimensional of dimension card(E), so the pairing identifies M
// with its dual (NondegeneratePairingDualityIso above), and d(e) is the
// vector it carries to the coordinate functional at e. Expanding b(x, -)
// along E shows that x and its expansion pair alike with E, hence agree;
// so the d(e) span M, and being card(E) many they are a basis.
var NondegeneratePairingDualBasis = nondegeneratePairingDualBasisThm{family.Add(registry.ProofEntry{
	Name: "NondegeneratePairingDualBasis",
	Key:  "prop_b270d8a6e66d1ba8",
	Reading: "For a nonsymmetric pairing the duality is b(d(e),f)=δ(e,f), and the " +
		"expansion coefficients are b(x,e). Reversing either pairing would generally be false.",
	Build: family.Theorem(Statement{
		Binders: "∀K:field_on(A). ∀M:module_ops(A, B). ∀b:(B → B → A). ∀E:set(B).",
		Hypotheses: []string{
			"module_on(field_ring(K), M)",
			"bilinear_pairing(field_ring(K), M, b)",
			"pairing_nondegenerate(field_ring(K), M, b)",
			"finite(E)",
			"module_basis(field_ring(K), M, E)",
		},
		Conclusion: "∃d:(B → B). " +
			"    (∀e:B. e ∈ E ⇒ d(e) ∈ M.carrier) ∧ " +
			"    (∀e f:B. e ∈ E ∧ f ∈ E ⇒ b(d(e), f) = COND(e = f, K.one, K.zero)) ∧ " +
			"    module_basis(field_ring(K), M, image(d, E)) ∧ " +
			"    (∀x:B. x ∈ M.carrier ⇒ x = module_sum(M.add, M.zero, E, λe:B. M.smul(b(x, e), d(e)))) ∧ " +
			"    (∀c:(B → B). " +
			"        (∀e:B. e ∈ E ⇒ c(e) ∈ M.carrier) ∧ " +
			"        (∀e f:B. e ∈ E ∧ f ∈ E ⇒ b(c(e), f) = COND(e = f, K.one, K.zero)) ⇒ " +
			"        ∀e:B. e ∈ E ⇒ c(e) = d(e))",
	}, func(
		a *Argument,
		K field.FieldFact[on.K],
		M *Expr[ModuleOps[A, B]],
		b *Arrow2[B, B, A],
		E *Expr[Set[B]],
		data Fact,
	) {
		given := a.Conjuncts(
			data,
			"M is a module",
			"the pairing is bilinear",
			"the pairing is left-nondegenerate",
			"E is finite",
			"E is a basis")
		moduleM, bilinear, finiteE, basisE := given[0], given[1], given[3], given[4]
		R := a.TermAs[RingOps[A]]("field_ring(K)")
		inv := a.TermAs[Fun[A, A]]("K.inv")
		scalarsField := field.FieldRingSubfield.Read(K)
		dimension := a.Have(
			"the finite basis E gives M the finite dimension card(E)",
			"finite_dimensional(field_ring(K), M) ∧ module_dim(field_ring(K), M) = card(E)",
			By(finiteE, basisE, scalarsField, module_dimension.FiniteBasisDim.Read(moduleM).At(inv, E)))
		F, mapDef := a.LetAs[Fun2[B, B, A]]("F", "λx:B. λy:B. COND(y ∈ M.carrier, b(x, y), K.zero)")
		iso := a.Have(
			"the pairing identifies M with its dual",
			"module_isomorphism(field_ring(K), "+
				"    M, "+
				"    hom_module(field_ring(K), M, regular_module(field_ring(K))), "+
				"    F)",
			By(data, dimension, mapDef, NondegeneratePairingDualityIso.Read(K).At(M, b)))
		onMap := a.Conjuncts(
			a.Unfolded(iso, module_homomorphism.ModuleIsomorphismDef),
			"the pairing map is linear",
			"the pairing map is injective",
			"the pairing map is onto the dual")
		injective, onto := onMap[1], onMap[2]
		carrier := a.TermAs[Set[B]]("M.carrier")
		inE := a.Have(
			"a basis lies in M",
			"E ⊆ M.carrier",
			By(linear_independence.BasisInCarrier.Read(basisE)))
		basisIn := a.Unfolded(inE, set_basic.SubsetDef)
		coordDef := a.Let(
			"C",
			a.TermAs[Fun2[B, B, A]](
				"λe:B. λv:B. COND(v ∈ M.carrier, module_basis_coordinates(field_ring(K), M, E, v, e), K.zero)"))
		coordinates := a.Have(
			"each coordinate functional lies in the dual",
			"∀e:B. e ∈ E ⇒ C(e) ∈ hom_set(field_ring(K), M, regular_module(field_ring(K)))",
			Derive(func(q *Argument) {
				e := q.FixAs[B]("e")
				eIn := q.Assume()
				functional := q.TermAs[Fun[B, A]]("C(e)")
				coordinate := q.TermAs[Fun[B, A]]("λv:B. module_basis_coordinates(field_ring(K), M, E, v, e)")
				agree := q.Have(
					"on M the normalized coordinate is the coordinate",
					Statement{
						Binders: "∀v:B.",
						Hypotheses: []string{
							"v ∈ M.carrier",
						},
						Conclusion: "COND(v ∈ M.carrier, module_basis_coordinates(field_ring(K), M, E, v, e), K.zero) = " +
							"module_basis_coordinates(field_ring(K), M, E, v, e)",
					},
					q.ForEach(func(_ *Expr[B]) Action { return Basic() }))
				linear := q.Have(
					"so the normalized coordinate is linear",
					"module_homomorphism(field_ring(K), M, regular_module(field_ring(K)), C(e))",
					By(
						Normalized,
						finiteE,
						basisE,
						eIn,
						coordDef,
						agree,
						module_dimension.BasisCoordinateLinear.Read(moduleM).At(E, e),
						module_homomorphism.HomCongruence.At(
							R, M, q.TermAs[ModuleOps[A, A]]("regular_module(field_ring(K))"), coordinate, functional)))
				q.Show(
					"it is zero off M and therefore belongs to the dual",
					By(
						Normalized,
						linear,
						coordDef,
						hom_module.InHomSet.At(
							R, M, q.TermAs[ModuleOps[A, A]]("regular_module(field_ring(K))"), functional)))
			}))
		// Take d(e) to be the vector the pairing map carries to the coordinate functional C(e).
		dualMapDef := a.Let("d", a.TermAs[Fun[B, B]]("λe:B. inverse_on(M.carrier, F, C(e))"))
		d := a.TermAs[Fun[B, B]]("d")
		a.Take(d)
		pulled := a.Have(
			"the inverse pairing map pulls coordinates back to vectors",
			"∀e:B. e ∈ E ⇒ d(e) ∈ M.carrier ∧ F(d(e)) = C(e)",
			Derive(func(q *Argument) {
				e := q.FixAs[B]("e")
				eIn := q.Assume()
				functional := q.TermAs[Fun[B, A]]("C(e)")
				inImage := q.Have(
					"the coordinate functional is in the pairing image",
					"C(e) ∈ image(F, M.carrier)",
					By(Normalized, eIn, coordinates.At(e), onto))
				q.Show(
					"its chosen preimage lies in M and maps to the coordinate functional",
					By(
						Normalized,
						dualMapDef,
						inImage,
						functions.InverseOnIn.At(carrier, F, functional),
						functions.InverseOnRight.At(carrier, F, functional)))
			}))
		delta := a.Have(
			"the chosen vectors pair to the Kronecker delta on E",
			"∀e f:B. e ∈ E ∧ f ∈ E ⇒ b(d(e), f) = COND(e = f, K.one, K.zero)",
			Derive(func(q *Argument) {
				e := q.FixAs[B]("e")
				f := q.FixAs[B]("f")
				both := q.Assume()
				kronecker := q.Have(
					"the coordinates of f are its Kronecker delta",
					"module_basis_coordinates(field_ring(K), M, E, f) = (λx:B. COND(x = f, K.one, K.zero))",
					By(both, finiteE, basisE, module_dimension.BasisCoordinateDelta.Read(moduleM).At(E, f)))
				q.Have(
					"f belongs to M",
					"f ∈ M.carrier",
					BySets(both, inE))
				evaluation := q.Have(
					"evaluate the pulled coordinate at f",
					"F(d(e), f) = C(e, f)",
					By(Normalized, both, pulled.At(e)))
				read := q.Simplified(evaluation, Fwd(mapDef), Fwd(coordDef), Fwd(kronecker))
				q.Show(
					"the coordinate value is the required delta",
					By(read))
			}))

		T, regularDef := a.LetAs[ModuleOps[A, A]]("T", "regular_module(field_ring(K))")
		addT, zeroT := a.TermAs[Op[A]]("T.add"), a.TermAs[A]("T.zero")
		bilinearLaws := a.Conjuncts(
			a.Simplified(a.Unfolded(bilinear, BilinearPairingDef), Rev(regularDef)),
			"linearity in the second argument",
			"linearity in the first argument")
		columns, rows := bilinearLaws[0], bilinearLaws[1]
		separates := a.Have(
			"pairing values on E separate vectors of M",
			"∀x z:B. x ∈ M.carrier ∧ z ∈ M.carrier ∧ (∀e:B. e ∈ E ⇒ b(x, e) = b(z, e)) ⇒ x = z",
			Derive(func(q *Argument) {
				x := q.FixAs[B]("x")
				z := q.FixAs[B]("z")
				agree := q.Assume()
				equalMaps := q.Have(
					"the normalized functionals agree everywhere",
					"F(x) = F(z)",
					Funext(),
					Derive(func(r *Argument) {
						y := r.FixAs[B]("y")
						r.Cases(r.Term("y ∈ M.carrier"))
						r.When(
							"on M expand the evaluation point in E",
							func(p *Argument, yIn Fact) {
								ex := p.Have(
									"expand the functional b(x,-)",
									"b(x, y) = "+
										"module_sum(T.add, "+
										"    T.zero, "+
										"    E, "+
										"    λe:B. T.smul(module_basis_coordinates(field_ring(K), M, E, y, e), b(x, e)))",
									By(
										finiteE,
										basisE,
										columns.At(x),
										agree,
										yIn,
										module_dimension.HomBasisExpansion.At(R, M, T, E, p.TermAs[Fun[B, A]]("b(x)"), y)))
								ez := p.Have(
									"expand the functional b(z,-)",
									"b(z, y) = "+
										"module_sum(T.add, "+
										"    T.zero, "+
										"    E, "+
										"    λe:B. T.smul(module_basis_coordinates(field_ring(K), M, E, y, e), b(z, e)))",
									By(
										finiteE,
										basisE,
										columns.At(z),
										agree,
										yIn,
										module_dimension.HomBasisExpansion.At(R, M, T, E, p.TermAs[Fun[B, A]]("b(z)"), y)))
								sameSum := p.Have(
									"equal values on E give equal finite sums",
									"module_sum(T.add, "+
										"    T.zero, "+
										"    E, "+
										"    λe:B. T.smul(module_basis_coordinates(field_ring(K), M, E, y, e), b(x, e))) = "+
										"module_sum(T.add, "+
										"    T.zero, "+
										"    E, "+
										"    λe:B. T.smul(module_basis_coordinates(field_ring(K), M, E, y, e), b(z, e)))",
									By(
										agree,
										module.ModuleSumCongruence.At(
											addT,
											zeroT,
											E,
											p.TermAs[Fun[B, A]]("λe:B. T.smul(module_basis_coordinates(field_ring(K), M, E, y, e), b(x, e))"),
											p.TermAs[Fun[B, A]]("λe:B. T.smul(module_basis_coordinates(field_ring(K), M, E, y, e), b(z, e))"))))
								p.Do(Simp(Fwd(mapDef)))
								p.Show(
									"the expanded functionals agree",
									CalcEq(
										Leg(
											p.TermAs[A](
												"module_sum(T.add, "+
													"    T.zero, "+
													"    E, "+
													"    λe:B. T.smul(module_basis_coordinates(field_ring(K), M, E, y, e), b(x, e)))"),
											"expand the first functional",
											By(ex)),
										Leg(
											p.TermAs[A](
												"module_sum(T.add, "+
													"    T.zero, "+
													"    E, "+
													"    λe:B. T.smul(module_basis_coordinates(field_ring(K), M, E, y, e), b(z, e)))"),
											"replace equal basis values",
											By(sameSum)),
										FinalLeg(
											"recover the second functional",
											By(ez))))
							})
						r.Otherwise(
							"off M both normalized functionals vanish",
							Simp(Fwd(mapDef)),
							Basic())
					}))
				q.Show(
					"injectivity of the pairing map identifies the vectors",
					By(injective, agree, equalMaps, functions.InjectiveOnDef.At(carrier, F)))
			}))
		regularOps := a.Have(
			"regular-module values and scaling are scalar values and multiplication",
			"T.carrier = field_ring(K).carrier ∧ T.smul = field_ring(K).mul",
			Simp(
				Fwd(regularDef),
				Fwd(module_record.RegularModuleDef),
				Fwd(module_record.ModCarrierDef),
				Fwd(module_record.ModSmulDef)),
			Basic())
		values := a.Have(
			"pairings of vectors are scalars",
			"∀x y:B. x ∈ M.carrier ∧ y ∈ M.carrier ⇒ b(x, y) ∈ field_ring(K).carrier",
			Derive(func(q *Argument) {
				x := q.FixAs[B]("x")
				y := q.FixAs[B]("y")
				both := q.Assume()
				linear := q.Have(
					"fix the first pairing argument",
					"module_homomorphism(field_ring(K), M, T, b(x))",
					By(columns.At(x), both))
				q.Show(
					"the functional takes values in the scalar carrier",
					By(Normalized, both, regularOps, module_homomorphism.HomIn.Read(linear).AsFact().At(y)))
			}))
		coordinateValues := a.Have(
			"the pulled functional reads every coordinate",
			"∀e y:B. e ∈ E ∧ y ∈ M.carrier ⇒ b(d(e), y) = module_basis_coordinates(field_ring(K), M, E, y, e)",
			Derive(func(q *Argument) {
				e := q.FixAs[B]("e")
				q.FixAs[B]("y")
				both := q.Assume()
				atY := q.Have(
					"read the pulled coordinate at y",
					"F(d(e), y) = C(e, y)",
					By(Normalized, both, pulled.At(e)))
				read := q.Simplified(atY, Fwd(mapDef), Fwd(coordDef))
				q.Show(
					"on M normalization reads the coordinate",
					By(read, both))
			}))
		expansion := a.Have(
			"the dual vectors give the pairing expansion",
			"∀x:B. x ∈ M.carrier ⇒ x = module_sum(M.add, M.zero, E, λe:B. M.smul(b(x, e), d(e)))",
			Derive(func(q *Argument) {
				x := q.FixAs[B]("x")
				xIn := q.Assume()
				combination, combinationDef := q.LetAs[B](
					"combination", "module_sum(M.add, M.zero, E, λe:B. M.smul(b(x, e), d(e)))")
				coefficients := q.Have(
					"the coefficients are scalars and the dual vectors lie in M",
					"∀e:B. e ∈ E ⇒ b(x, e) ∈ field_ring(K).carrier ∧ d(e) ∈ M.carrier",
					Derive(func(r *Argument) {
						e := r.FixAs[B]("e")
						eIn := r.Assume()
						r.Show(
							"read the pairing value and the chosen preimage",
							By(xIn, eIn, basisIn.At(e), values.At(x, e), pulled.At(e)))
					}))
				terms := q.Have(
					"all terms of the expansion lie in M",
					"∀e:B. e ∈ E ⇒ M.smul(b(x, e), d(e)) ∈ M.carrier",
					Derive(func(r *Argument) {
						e := r.FixAs[B]("e")
						eIn := r.Assume()
						r.Show(
							"M is closed under the scalar multiple",
							By(
								eIn,
								coefficients.At(e),
								module.SmulIn.Read(moduleM).AsFact().At(b.Apply(x, e), r.TermAs[B]("d(e)"))))
					}))
				inM := q.Have(
					"the finite sum lies in M",
					"combination ∈ M.carrier",
					By(
						Normalized,
						finiteE,
						combinationDef,
						terms,
						module.ModuleSumIn.Read(moduleM).At(E, q.TermAs[Fun[B, B]]("λe:B. M.smul(b(x, e), d(e))"))))
				agrees := q.Have(
					"the sum and x have the same pairings on E",
					"∀f:B. f ∈ E ⇒ b(combination, f) = b(x, f)",
					Derive(func(r *Argument) {
						f := r.FixAs[B]("f")
						fIn := r.Assume()
						fInM := r.Have(
							"f belongs to M",
							"f ∈ M.carrier",
							BySets(fIn, inE))
						linear := r.Have(
							"fix f as the second pairing argument",
							"module_homomorphism(field_ring(K), M, T, λu:B. b(u, f))",
							By(fInM, rows.At(f)))
						mapped := r.Have(
							"move the finite sum through the pairing",
							"b(combination, f) = module_sum(T.add, T.zero, E, λe:B. b(M.smul(b(x, e), d(e)), f))",
							By(
								finiteE,
								combinationDef,
								terms,
								module_homomorphism.HomSum.Read(linear).At(E, r.TermAs[Fun[B, B]]("λe:B. M.smul(b(x, e), d(e))"))))
						onTerms := r.Have(
							"each pairing term is its coordinate term",
							Statement{
								Binders: "∀e:B.",
								Hypotheses: []string{
									"e ∈ E",
								},
								Conclusion: "b(M.smul(b(x, e), d(e)), f) = " +
									"T.smul(module_basis_coordinates(field_ring(K), M, E, f, e), b(x, e))",
							},
							Derive(func(p *Argument) {
								e := p.FixAs[B]("e")
								eIn := p.Assume()
								dualVector := p.TermAs[B]("d(e)")
								scaled := p.Have(
									"the pairing preserves this scalar multiple",
									"b(M.smul(b(x, e), d(e)), f) = T.smul(b(x, e), b(d(e), f))",
									By(
										eIn,
										coefficients.At(e),
										module_homomorphism.HomSmul.Read(linear).AsFact().At(b.Apply(x, e), dualVector)))
								coordinate := p.Have(
									"the pulled functional reads this coordinate",
									"b(d(e), f) = module_basis_coordinates(field_ring(K), M, E, f, e)",
									By(eIn, fInM, coordinateValues.At(e, f)))
								p.Do(Simp(Fwd(scaled), Fwd(regularOps), Rev(coordinate)))
								p.Show(
									"the scalar product commutes",
									ByArith(module.RingOn.Read(moduleM), eIn, fInM, coefficients.At(e), values.At(dualVector, f)))
							}))
						collected := r.Have(
							"collect the equal pairing terms",
							"module_sum(T.add, T.zero, E, λe:B. b(M.smul(b(x, e), d(e)), f)) = "+
								"module_sum(T.add, "+
								"    T.zero, "+
								"    E, "+
								"    λe:B. T.smul(module_basis_coordinates(field_ring(K), M, E, f, e), b(x, e)))",
							By(
								onTerms,
								module.ModuleSumCongruence.At(
									addT,
									zeroT,
									E,
									r.TermAs[Fun[B, A]]("λe:B. b(M.smul(b(x, e), d(e)), f)"),
									r.TermAs[Fun[B, A]]("λe:B. T.smul(module_basis_coordinates(field_ring(K), M, E, f, e), b(x, e))"))))
						atX := r.Have(
							"expand b(x,-) at f",
							"b(x, f) = "+
								"module_sum(T.add, "+
								"    T.zero, "+
								"    E, "+
								"    λe:B. T.smul(module_basis_coordinates(field_ring(K), M, E, f, e), b(x, e)))",
							By(
								finiteE,
								basisE,
								xIn,
								fInM,
								columns.At(x),
								module_dimension.HomBasisExpansion.At(R, M, T, E, r.TermAs[Fun[B, A]]("b(x)"), f)))
						r.Show(
							"the two evaluations agree",
							CalcEq(
								Leg(
									r.TermAs[A]("module_sum(T.add, T.zero, E, λe:B. b(M.smul(b(x, e), d(e)), f))"),
									"evaluate the sum term by term",
									By(mapped)),
								Leg(
									r.TermAs[A](
										"module_sum(T.add, "+
											"    T.zero, "+
											"    E, "+
											"    λe:B. T.smul(module_basis_coordinates(field_ring(K), M, E, f, e), b(x, e)))"),
									"collect its coordinate terms",
									By(collected)),
								FinalLeg(
									"this is the coordinate expansion of b(x,f)",
									By(atX))))
					}))
				q.Show(
					"separation on E identifies the sum with x",
					By(xIn, inM, agrees, separates.At(x, combination)))
			}))

		dualVectors, dualVectorsDef := a.LetAs[Set[B]]("dualVectors", "image(d, E)")
		inM := a.Have(
			"the dual vectors lie in M",
			"dualVectors ⊆ M.carrier",
			BySets(dualVectorsDef, pulled))
		dualSpan, spanDef := a.LetAs[Set[B]]("dualSpan", "module_span(field_ring(K), M, dualVectors)")
		subSpan := a.Have(
			"the span is a submodule of M",
			"submodule(field_ring(K), M, dualSpan)",
			By(Normalized, inM, spanDef, submodule.SpanSubmodule.Read(moduleM).At(dualVectors)))
		contains := a.Have(
			"the span contains every dual vector",
			"dualVectors ⊆ dualSpan",
			By(Normalized, spanDef, submodule.SubsetSpan.At(R, M, dualVectors)))
		reaches := a.Have(
			"every vector belongs to the dual-vector span",
			"∀x:B. x ∈ M.carrier ⇒ x ∈ dualSpan",
			Derive(func(q *Argument) {
				x := q.FixAs[B]("x")
				xIn := q.Assume()
				terms := q.Have(
					"the expansion terms lie in the span",
					"∀e:B. e ∈ E ⇒ M.smul(b(x, e), d(e)) ∈ dualSpan",
					Derive(func(r *Argument) {
						e := r.FixAs[B]("e")
						eIn := r.Assume()
						dualVector := r.TermAs[B]("d(e)")
						dualVectorInSpan := r.Have(
							"the dual vector lies in its span",
							"d(e) ∈ dualSpan",
							BySets(eIn, dualVectorsDef, contains))
						coefficient := r.Have(
							"the expansion coefficient is a scalar",
							"b(x, e) ∈ field_ring(K).carrier",
							By(xIn, eIn, basisIn.At(e), values.At(x, e)))
						r.Show(
							"the span is closed under scaling",
							By(
								dualVectorInSpan,
								coefficient,
								submodule.SubmoduleSmul.Read(subSpan).AsFact().At(b.Apply(x, e), dualVector)))
					}))
				sum := q.Have(
					"their finite sum lies in the span",
					"module_sum(M.add, M.zero, E, λe:B. M.smul(b(x, e), d(e))) ∈ dualSpan",
					By(
						subSpan,
						finiteE,
						terms,
						submodule.SubmoduleModuleSum.Read(moduleM).At(
							dualSpan, E, q.TermAs[Fun[B, B]]("λe:B. M.smul(b(x, e), d(e))"))))
				q.Show(
					"the expansion equals x",
					By(xIn, expansion.At(x), sum))
			}))
		spans := a.Have(
			"the dual vectors span all of M",
			"dualSpan = M.carrier",
			BySets(reaches, submodule.SubmoduleSubset.Read(subSpan)))
		oneToOne := a.Have(
			"distinct basis labels give distinct dual vectors",
			"∀e f:B. e ∈ E ∧ f ∈ E ∧ d(e) = d(f) ⇒ e = f",
			Derive(func(q *Argument) {
				e := q.FixAs[B]("e")
				f := q.FixAs[B]("f")
				equal := q.Assume()
				q.Show(
					"evaluate equal dual vectors at e",
					By(Normalized, equal, delta.At(e, e), delta.At(f, e), field.OneNotZeroOn.Read(K)))
			}))
		injectiveOnE := a.Have(
			"d is injective on E",
			"injective_on(E, d)",
			By(oneToOne, functions.InjectiveOnDef.At(E, d)))
		sized := a.Have(
			"there are as many dual vectors as the dimension of M",
			"has_size(dualVectors, module_dim(field_ring(K), M))",
			By(
				Normalized,
				finiteE,
				injectiveOnE,
				dualVectorsDef,
				dimension,
				cardinality.FiniteHasSize,
				cardinality.HasSizeImageInj.At(d, E, a.TermAs[Nat]("module_dim(field_ring(K), M)"))))
		dualBasis := a.Have(
			"a spanning set of dim M vectors is a basis",
			"module_basis(field_ring(K), M, dualVectors)",
			By(
				Normalized,
				scalarsField,
				spanDef,
				spans,
				sized,
				module_dimension.SpanningFullBasis.Read(moduleM).At(inv, dualVectors)))
		unique := a.Have(
			"the delta conditions determine the dual vectors on E",
			"∀c:(B → B). "+
				"    (∀e:B. e ∈ E ⇒ c(e) ∈ M.carrier) ∧ "+
				"    (∀e f:B. e ∈ E ∧ f ∈ E ⇒ b(c(e), f) = COND(e = f, K.one, K.zero)) ⇒ "+
				"    ∀e:B. e ∈ E ⇒ c(e) = d(e)",
			Derive(func(q *Argument) {
				q.FixAs[Fun[B, B]]("c")
				other := q.Conjuncts(
					q.Assume(),
					"the other vectors lie in M",
					"the other vectors have the delta pairings")
				e := q.FixAs[B]("e")
				eIn := q.Assume()
				both := q.Have(
					"both candidate vectors lie in M",
					"c(e) ∈ M.carrier ∧ d(e) ∈ M.carrier",
					By(eIn, other[0].At(e), pulled.At(e)))
				agree := q.Have(
					"their pairings agree on E",
					"∀f:B. f ∈ E ⇒ b(c(e), f) = b(d(e), f)",
					Derive(func(r *Argument) {
						f := r.FixAs[B]("f")
						fIn := r.Assume()
						r.Show(
							"both evaluations are the same delta",
							By(eIn, fIn, other[1].At(e, f), delta.At(e, f)))
					}))
				q.Show(
					"separation on E identifies the candidates",
					By(both, agree, separates.At(q.TermAs[B]("c(e)"), q.TermAs[B]("d(e)"))))
			}))
		a.Show(
			"the pulled coordinates give the dual basis, expansion and uniqueness",
			By(pulled, delta, dualBasis, dualVectorsDef, expansion, unique))
	}),
})}
