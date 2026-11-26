// trace.go — the finite-set basis trace and its coordinate interface.

package module_dimension

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ModuleBasisCoordinatesDef — The normalized coefficient function of a vector in a finite set basis.
var ModuleBasisCoordinatesDef = moduleBasisCoordinatesDefThm{family.Define(registry.DefEntry{
	Name:  "ModuleBasisCoordinatesDef",
	Key:   "prop_96f869d289f82ab4",
	Const: "module_basis_coordinates",
	Type:  "ring_ops(A) → module_ops(A, B) → set(B) → B → B → A",
	Reading: "Coordinates are fixed to R.zero off E. They are determined only at " +
		"a finite basis and a vector in M.carrier; no value off that domain is asserted.",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀E:set(B). ∀v:B. " +
			"    module_basis_coordinates(R, M, E, v) = " +
			"    εa:(B → A). " +
			"        (∀e:B. e ∈ E ⇒ a(e) ∈ R.carrier) ∧ " +
			"        (∀e:B. e ∉ E ⇒ a(e) = R.zero) ∧ " +
			"        module_sum(M.add, M.zero, E, λe:B. M.smul(a(e), e)) = v",
	},
})}

// ModuleBasisTraceDef — The sum of the diagonal coordinate functionals in a finite set basis.
var ModuleBasisTraceDef = moduleBasisTraceDefThm{family.Define(registry.DefEntry{
	Name:  "ModuleBasisTraceDef",
	Key:   "prop_46e4ae2a5d34b90c",
	Const: "module_basis_trace",
	Type:  "ring_ops(A) → module_ops(A, B) → set(B) → (B → B) → A",
	Deps:  []registry.EntryLike{ModuleBasisCoordinatesDef},
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀E:set(B). ∀f:(B → B). " +
			"    module_basis_trace(R, M, E, f) = " +
			"    module_sum(R.add, R.zero, E, λe:B. module_basis_coordinates(R, M, E, f(e), e))",
	},
})}

// ModuleTraceDef — The common finite-basis trace of an endomorphism.
var ModuleTraceDef = moduleTraceDefThm{family.Define(registry.DefEntry{
	Name:  "ModuleTraceDef",
	Key:   "prop_70d49ec1e4a06289",
	Const: "module_trace",
	Type:  "ring_ops(A) → module_ops(A, B) → (B → B) → A",
	Deps:  []registry.EntryLike{ModuleBasisTraceDef},
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀f:(B → B). " +
			"    module_trace(R, M, f) = " +
			"    εr:A. ∃E:set(B). finite(E) ∧ module_basis(R, M, E) ∧ r = module_basis_trace(R, M, E, f)",
	},
})}

// BasisCoordinatesSpec — the chosen coordinates of a vector of M lie in
// the scalar ring, vanish off the basis and expand the vector: v, lying
// in the span of E, is a combination over a finite part T of E, and its
// coefficients extended by R.zero to all of E are a coefficient
// function of the kind the definition chooses, so the choice is made.
var BasisCoordinatesSpec = basisCoordinatesSpecThm{family.Add(registry.ProofEntry{
	Name: "BasisCoordinatesSpec",
	Key:  "prop_bf7db44825c6428d",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀E:set(B). ∀v:B.",
		Hypotheses: []string{
			"finite(E)",
			"module_basis(R, M, E)",
			"v ∈ M.carrier",
		},
		Conclusion: "(∀e:B. e ∈ E ⇒ module_basis_coordinates(R, M, E, v, e) ∈ R.carrier) ∧ " +
			"(∀e:B. e ∉ E ⇒ module_basis_coordinates(R, M, E, v, e) = R.zero) ∧ " +
			"module_sum(M.add, M.zero, E, λe:B. module_basis_coordinates(R, M, E, v, e) • e) = v",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			E *Expr[Set[B]],
			v *Expr[B],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"E is finite",
				"E is a basis of M",
				"v lies in M")
			finiteE, basisE, vInM := given[0], given[1], given[2]
			onE := a.Conjuncts(
				a.Unfolded(basisE, linear_independence.ModuleBasisDef),
				"E is independent",
				"E spans M")
			independentE, spansE := onE[0], onE[1]

			eInM := a.Have(
				"an independent set lies in M, so E does",
				"E ⊆ M.carrier",
				By(linear_independence.IndependentInCarrier.Read(independentE)))
			vInSpan := a.Have(
				"v lies in M, which is the span of E",
				"v ∈ module_span(R, M, E)",
				By(Normalized, vInM, spansE))
			T, c, expansion := a.Obtain2As[Set[B], Fun[B, A]](
				"so v is a combination over a finite part T of E, with scalar coefficients c",
				"∃T:set(B). ∃c:(B → A). "+
					"    finite(T) ∧ "+
					"    T ⊆ E ∧ "+
					"    (∀x:B. x ∈ T ⇒ c(x) ∈ R.carrier) ∧ "+
					"    v = module_sum(M.add, M.zero, T, λx:B. c(x) • x)",
				By(eInM, vInSpan, linear_independence.SpanMembership.Read(moduleOn).At(E, v)))
			parts := a.Conjuncts(
				expansion,
				"T is finite",
				"T lies in E",
				"c is a scalar on T",
				"v is the combination over T")
			tInE, scalarsOnT, combination := parts[1], parts[2], parts[3]
			inE := a.Unfolded(tInE, set_basic.SubsetDef)

			scalars := a.Have(
				"extended by R.zero off T, c is a scalar at every point",
				"∀x:B. COND(x ∈ T, c(x), R.zero) ∈ R.carrier",
				a.ForEach(func(x *Expr[B]) Action {
					return By(scalarsOnT.At(x), comm_ring.ZeroIn.Read(module.RingOn.Read(moduleOn)))
				}))
			vanish := a.Have(
				"a point off E is off T, where the extension is R.zero",
				"∀e:B. e ∉ E ⇒ COND(e ∈ T, c(e), R.zero) = R.zero",
				a.ForEach(func(e *Expr[B]) Action { return By(inE.At(e)) }))
			expands := a.Have(
				"over E the extended coefficients sum to the combination over T, which is v",
				"module_sum(M.add, M.zero, E, λe:B. COND(e ∈ T, c(e), R.zero) • e) = v",
				By(
					finiteE,
					tInE,
					eInM,
					scalarsOnT,
					combination,
					linear_independence.CombinationExtendByZero.Read(moduleOn).At(T, E, c)))
			exists := a.Have(
				"so a coefficient function of the kind the coordinates choose exists",
				"∃b:(B → A). "+
					"    (∀e:B. e ∈ E ⇒ b(e) ∈ R.carrier) ∧ "+
					"    (∀e:B. e ∉ E ⇒ b(e) = R.zero) ∧ "+
					"    module_sum(M.add, M.zero, E, λe:B. b(e) • e) = v",
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Fun[B, A]]("λe:B. COND(e ∈ T, c(e), R.zero)"))
					b.Show(
						"the extension of c by R.zero is one",
						By(scalars, vanish, expands))
				}))
			a.Show(
				"the coordinates are the function the definition chooses, "+
					"and one exists, so they have its three properties",
				Simp(Fwd(ModuleBasisCoordinatesDef)),
				By(exists))
		}),
})}

// BasisCoordinatesUnique — a coefficient function that is scalar on
// the basis, R.zero off it and expands the vector is its coordinates:
// on E the coordinates and c are the coefficients of two expansions of
// v over E, which agree, E being independent; off E both are R.zero.
var BasisCoordinatesUnique = basisCoordinatesUniqueThm{family.Add(registry.ProofEntry{
	Name: "BasisCoordinatesUnique",
	Key:  "prop_f251fc88fc3bbf3a",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀E:set(B). ∀v:B. ∀c:(B → A).",
		Hypotheses: []string{
			"finite(E)",
			"module_basis(R, M, E)",
			"v ∈ M.carrier",
			"∀e:B. e ∈ E ⇒ c(e) ∈ R.carrier",
			"∀e:B. e ∉ E ⇒ c(e) = R.zero",
			"module_sum(M.add, M.zero, E, λe:B. c(e) • e) = v",
		},
		Conclusion: "module_basis_coordinates(R, M, E, v) = c",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			E *Expr[Set[B]],
			v *Expr[B],
			c *Arrow[B, A],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"E is finite",
				"E is a basis of M",
				"v lies in M",
				"c is a scalar on E",
				"c is R.zero off E",
				"c expands v over E")
			finiteE, basisE, vInM, cIn, cOff, cExpands :=
				given[0], given[1], given[2], given[3], given[4], given[5]
			onE := a.Conjuncts(
				a.Unfolded(basisE, linear_independence.ModuleBasisDef),
				"E is independent",
				"E spans M")
			independentE := onE[0]
			chosen := a.TermAs[Fun[B, A]]("module_basis_coordinates(R, M, E, v)")

			specified := a.Conjuncts(
				a.Have(
					"the coordinates of v are scalars on E, R.zero off E, and expand v",
					"(∀e:B. e ∈ E ⇒ module_basis_coordinates(R, M, E, v, e) ∈ R.carrier) ∧ "+
						"(∀e:B. e ∉ E ⇒ module_basis_coordinates(R, M, E, v, e) = R.zero) ∧ "+
						"module_sum(M.add, M.zero, E, λe:B. module_basis_coordinates(R, M, E, v, e) • e) = v",
					By(finiteE, basisE, BasisCoordinatesSpec.Read(moduleOn).At(E, a.MemberOf[on.M](v, vInM)))),
				"the coordinates are scalars on E",
				"they are R.zero off E",
				"they expand v over E")
			chosenIn, chosenOff, chosenExpands := specified[0], specified[1], specified[2]

			sameSum := a.Have(
				"the two expansions over E are both v",
				"module_sum(M.add, M.zero, E, λe:B. module_basis_coordinates(R, M, E, v, e) • e) = "+
					"module_sum(M.add, M.zero, E, λe:B. c(e) • e)",
				By(Normalized, chosenExpands, cExpands))
			scalars := a.Have(
				"both coefficient functions are scalars on E",
				"∀x:B. x ∈ E ⇒ module_basis_coordinates(R, M, E, v, x) ∈ R.carrier ∧ c(x) ∈ R.carrier",
				a.ForEach(func(x *Expr[B]) Action { return By(chosenIn.At(x), cIn.At(x)) }))
			agree := a.Have(
				"E is an independent finite part of itself, so the two expansions have the same coefficients on E",
				"∀z:B. z ∈ E ⇒ module_basis_coordinates(R, M, E, v, z) = c(z)",
				By(
					independentE,
					finiteE,
					scalars,
					sameSum,
					set_order.SubsetRefl.At(E),
					linear_independence.IndependentUniqueCoefficients.Read(moduleOn).AsFact().At(E, E, chosen, c)))

			// The two functions agree at every point.
			a.Do(Funext())
			e := a.FixAs[B]("e")
			a.Cases(a.Term("e ∈ E"))
			a.When(
				"on E the two expansions have the same coefficients",
				func(b *Argument, inE Fact) {
					b.Show(
						"the coefficient at e is c(e)",
						By(agree.At(e), inE))
				})
			a.Otherwise(
				"off E both coefficient functions are R.zero",
				func(b *Argument, outside Fact) {
					b.Show(
						"both coefficients at e are R.zero",
						By(Normalized, outside, chosenOff.At(e), cOff.At(e)))
				})
		}),
})}

// BasisCoordinatesRestrict — coordinates in a basis do not see a larger
// ring of scalars: when a finite set E is a basis of M over R and of a
// part S of M over a subring P of R, a vector of S has the same
// coordinates over R as over P. Its coordinates over P are scalars of P,
// so of R, on E, R.zero off E, and expand it, and its coordinates over R
// are the one such coefficient function (BasisCoordinatesUnique).
var BasisCoordinatesRestrict = basisCoordinatesRestrictThm{family.Add(registry.ProofEntry{
	Name: "BasisCoordinatesRestrict",
	Key:  "prop_f5a48f76c15be3ee",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀P:set(A). ∀S E:set(B). ∀v:B.",
		Hypotheses: []string{
			"P ⊆ R.carrier",
			"S ⊆ M.carrier",
			"module_on(restrict_ring(R, P), restrict_module(M, S))",
			"finite(E)",
			"module_basis(restrict_ring(R, P), restrict_module(M, S), E)",
			"module_basis(R, M, E)",
			"v ∈ S",
		},
		Conclusion: "module_basis_coordinates(R, M, E, v) = " +
			"module_basis_coordinates(restrict_ring(R, P), restrict_module(M, S), E, v)",
		Abbrev: Abbrev{
			{Name: "restrictedCoordinates", Text: "module_basis_coordinates(restrict_ring(R, P), " +
				"    restrict_module(M, S), " +
				"    E, " +
				"    v)"},
		},
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			P *Expr[Set[A]],
			S, E *Expr[Set[B]],
			v *Expr[B],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"P lies in R",
				"S lies in M",
				"S is a module over P",
				"E is finite",
				"E is a basis of S over P",
				"E is a basis of M over R",
				"v lies in S")
			pInR, sInM, overP, finiteE, basisP, basisR, vInS :=
				given[0], given[1], given[2], given[3], given[4], given[5], given[6]
			overSubring := a.Have(
				"over P the coordinates of v are scalars of P on E, R.zero off E, and expand v",
				"(∀e:B. e ∈ E ⇒ «restrictedCoordinates»(e) ∈ P) ∧ "+
					"(∀e:B. e ∉ E ⇒ «restrictedCoordinates»(e) = R.zero) ∧ "+
					"module_sum(M.add, M.zero, E, λe:B. «restrictedCoordinates»(e) • e) = v",
				By(finiteE, basisP, BasisCoordinatesSpec.Read(overP).At(E, proof.MemberOf(v, vInS))))
			vInM := a.MemberOf[on.M](v, a.Have(
				"v lies in M",
				"v ∈ M.carrier",
				By(vInS, sInM, set_basic.SubsetDef)))
			scalars := a.Have(
				"the coordinates over P are scalars of R on E",
				"∀e:B. e ∈ E ⇒ «restrictedCoordinates»(e) ∈ R.carrier",
				By(pInR, overSubring, set_basic.SubsetDef))
			a.Show(
				"so they are the coordinates over R, a coefficient function of that kind being unique",
				By(
					finiteE,
					basisR,
					scalars,
					overSubring,
					BasisCoordinatesUnique.Read(moduleOn).At(E, vInM,
						a.TermAs[Fun[B, A]]("module_basis_coordinates(restrict_ring(R, P), restrict_module(M, S), E, v)"))))
		}),
})}

// BasisCoordinatesAdd — the coordinates of a sum are the pointwise sum
// of the coordinates: the sums of the coordinates of u and of v are
// scalars on E, vanish off it and expand u + v, the two expansions
// adding termwise, so by uniqueness of the expansion they are the
// coordinates of u + v.
var BasisCoordinatesAdd = basisCoordinatesAddThm{family.Add(registry.ProofEntry{
	Name: "BasisCoordinatesAdd",
	Key:  "prop_c5cccf141308738f",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀E:set(B). ∀u v:B.",
		Hypotheses: []string{
			"finite(E)",
			"module_basis(R, M, E)",
			"u ∈ M.carrier",
			"v ∈ M.carrier",
		},
		Conclusion: "module_basis_coordinates(R, M, E, u + v) = " +
			"λe:B. module_basis_coordinates(R, M, E, u, e) + module_basis_coordinates(R, M, E, v, e)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			E *Expr[Set[B]],
			u, v *Expr[B],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"E is finite",
				"E is a basis of M",
				"u lies in M",
				"v lies in M")
			finiteE, basisE := given[0], given[1]
			uInM, vInM := a.MemberOf[on.M](u, given[2]), a.MemberOf[on.M](v, given[3])
			ring := module.RingOn.Read(moduleOn)

			ofU := a.Conjuncts(
				a.Have(
					"the coordinates of u are scalars on E, R.zero off E, and expand u",
					"(∀e:B. e ∈ E ⇒ module_basis_coordinates(R, M, E, u, e) ∈ R.carrier) ∧ "+
						"(∀e:B. e ∉ E ⇒ module_basis_coordinates(R, M, E, u, e) = R.zero) ∧ "+
						"module_sum(M.add, M.zero, E, λe:B. module_basis_coordinates(R, M, E, u, e) • e) = u",
					By(finiteE, basisE, BasisCoordinatesSpec.Read(moduleOn).At(E, uInM))),
				"the coordinates of u are scalars on E",
				"they are R.zero off E",
				"they expand u")
			uScalars, uOff, uExpands := ofU[0], ofU[1], ofU[2]
			ofV := a.Conjuncts(
				a.Have(
					"and those of v are scalars on E, R.zero off E, and expand v",
					"(∀e:B. e ∈ E ⇒ module_basis_coordinates(R, M, E, v, e) ∈ R.carrier) ∧ "+
						"(∀e:B. e ∉ E ⇒ module_basis_coordinates(R, M, E, v, e) = R.zero) ∧ "+
						"module_sum(M.add, M.zero, E, λe:B. module_basis_coordinates(R, M, E, v, e) • e) = v",
					By(finiteE, basisE, BasisCoordinatesSpec.Read(moduleOn).At(E, vInM))),
				"the coordinates of v are scalars on E",
				"they are R.zero off E",
				"they expand v")
			vScalars, vOff, vExpands := ofV[0], ofV[1], ofV[2]

			scalars := a.Have(
				"on E the summed coordinates are scalars",
				Statement{
					Binders: "∀x:B.",
					Hypotheses: []string{
						"x ∈ E",
					},
					Conclusion: "module_basis_coordinates(R, M, E, u, x) + module_basis_coordinates(R, M, E, v, x) ∈ " +
						"R.carrier",
				},
				By(uScalars, vScalars, comm_ring.AddIn.Read(ring)))
			vanish := a.Have(
				"off E they are R.zero + R.zero, which is R.zero",
				Statement{
					Binders: "∀x:B.",
					Hypotheses: []string{
						"x ∉ E",
					},
					Conclusion: "module_basis_coordinates(R, M, E, u, x) + module_basis_coordinates(R, M, E, v, x) = " +
						"R.zero",
				},
				a.ForEach(func(x *Expr[B]) Action {
					return By(
						Normalized,
						uOff.At(x),
						vOff.At(x),
						comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(ring)),
						comm_ring.ZeroIn.Read(ring))
				}))
			expands := a.Have(
				"and they expand u + v: the two expansions add termwise",
				"module_sum(M.add, "+
					"    M.zero, "+
					"    E, "+
					"    λx:B. "+
					"        (module_basis_coordinates(R, M, E, u, x) + module_basis_coordinates(R, M, E, v, x)) • "+
					"        x) = "+
					"u + v",
				By(
					finiteE,
					linear_independence.BasisInCarrier.Read(basisE),
					uScalars,
					vScalars,
					uExpands,
					vExpands,
					linear_independence.CombinationAdd.Read(moduleOn).At(
						E,
						a.TermAs[Fun[B, A]]("module_basis_coordinates(R, M, E, u)"),
						a.TermAs[Fun[B, A]]("module_basis_coordinates(R, M, E, v)"))))
			sum := group.MulIn.Read(module.AddGroupOn.Read(moduleOn)).At(uInM, vInM)
			a.Show(
				"so by uniqueness of the expansion they are the coordinates of u + v",
				By(
					finiteE,
					basisE,
					scalars,
					vanish,
					expands,
					BasisCoordinatesUnique.Read(moduleOn).At(E, sum,
						a.TermAs[Fun[B, A]](
							"λx:B. module_basis_coordinates(R, M, E, u, x) + module_basis_coordinates(R, M, E, v, x)"))))
		}),
})}

// BasisCoordinatesSmul — the coordinates of a multiple are the
// pointwise multiple of the coordinates: c times the coordinates of u
// are scalars on E, vanish off it and expand c • u, c scaling the
// expansion of u termwise, so by uniqueness of the expansion they are
// the coordinates of c • u.
var BasisCoordinatesSmul = basisCoordinatesSmulThm{family.Add(registry.ProofEntry{
	Name: "BasisCoordinatesSmul",
	Key:  "prop_701fdea9e7e9e677",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀E:set(B). ∀c:A. ∀u:B.",
		Hypotheses: []string{
			"finite(E)",
			"module_basis(R, M, E)",
			"c ∈ R.carrier",
			"u ∈ M.carrier",
		},
		Conclusion: "module_basis_coordinates(R, M, E, c • u) = " +
			"λe:B. c * module_basis_coordinates(R, M, E, u, e)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			E *Expr[Set[B]],
			c *Expr[A],
			u *Expr[B],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"E is finite",
				"E is a basis of M",
				"c is a scalar",
				"u lies in M")
			finiteE, basisE, cInR := given[0], given[1], given[2]
			scalar, uInM := a.MemberOf[on.R](c, cInR), a.MemberOf[on.M](u, given[3])
			ring := module.RingOn.Read(moduleOn)

			ofU := a.Conjuncts(
				a.Have(
					"the coordinates of u are scalars on E, R.zero off E, and expand u",
					"(∀e:B. e ∈ E ⇒ module_basis_coordinates(R, M, E, u, e) ∈ R.carrier) ∧ "+
						"(∀e:B. e ∉ E ⇒ module_basis_coordinates(R, M, E, u, e) = R.zero) ∧ "+
						"module_sum(M.add, M.zero, E, λe:B. module_basis_coordinates(R, M, E, u, e) • e) = u",
					By(finiteE, basisE, BasisCoordinatesSpec.Read(moduleOn).At(E, uInM))),
				"the coordinates of u are scalars on E",
				"they are R.zero off E",
				"they expand u")
			uScalars, uOff, uExpands := ofU[0], ofU[1], ofU[2]

			scalars := a.Have(
				"on E the scaled coordinates are scalars",
				"∀x:B. x ∈ E ⇒ c * module_basis_coordinates(R, M, E, u, x) ∈ R.carrier",
				By(cInR, uScalars, comm_ring.MulIn.Read(ring)))
			vanish := a.Have(
				"off E they are c * R.zero, which is R.zero",
				"∀x:B. x ∉ E ⇒ c * module_basis_coordinates(R, M, E, u, x) = R.zero",
				a.ForEach(func(x *Expr[B]) Action {
					return By(Normalized, uOff.At(x), cInR, comm_ring.MulRightZeroOn.Read(ring))
				}))
			expands := a.Have(
				"and they expand c • u: c scales the expansion of u termwise",
				"module_sum(M.add, M.zero, E, λx:B. (c * module_basis_coordinates(R, M, E, u, x)) • x) = c • u",
				By(
					finiteE,
					linear_independence.BasisInCarrier.Read(basisE),
					uScalars,
					uExpands,
					linear_independence.CombinationScale.Read(moduleOn).At(E,
						scalar, a.TermAs[Fun[B, A]]("module_basis_coordinates(R, M, E, u)"))))
			multiple := module.SmulIn.Read(moduleOn).At(scalar, uInM)
			a.Show(
				"so by uniqueness of the expansion they are the coordinates of c • u",
				By(
					finiteE,
					basisE,
					scalars,
					vanish,
					expands,
					BasisCoordinatesUnique.Read(moduleOn).At(E, multiple,
						a.TermAs[Fun[B, A]]("λx:B. c * module_basis_coordinates(R, M, E, u, x)"))))
		}),
})}

// BasisCoordinateLinear — each coordinate is a linear functional on
// the module: by uniqueness of the expansion the coordinates of a sum
// and of a multiple are the sum and the multiple of the coordinates,
// and read at e that makes the coordinate at e a homomorphism into R.
var BasisCoordinateLinear = basisCoordinateLinearThm{family.Add(registry.ProofEntry{
	Name: "BasisCoordinateLinear",
	Key:  "prop_33e0383ae4d65b3b",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀E:set(B). ∀e:B.",
		Hypotheses: []string{
			"finite(E)",
			"module_basis(R, M, E)",
			"e ∈ E",
		},
		Conclusion: "module_homomorphism(R, " +
			"    M, " +
			"    regular_module(R), " +
			"    λv:B. module_basis_coordinates(R, M, E, v, e))",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			E *Expr[Set[B]],
			e *Expr[B],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"E is finite",
				"E is a basis of M",
				"e lies in E")
			finiteE, basisE, eInE := given[0], given[1], given[2]
			R := a.TermAs[RingOps[A]]("R")
			ring := module.RingOn.Read(moduleOn)
			sums := a.Have(
				"the coordinate at e of a sum is the sum of the coordinates at e",
				Statement{
					Binders: "∀u v:B.",
					Hypotheses: []string{
						"u ∈ M.carrier",
						"v ∈ M.carrier",
					},
					Conclusion: "module_basis_coordinates(R, M, E, u + v, e) = " +
						"module_basis_coordinates(R, M, E, u, e) + module_basis_coordinates(R, M, E, v, e)",
				},
				Derive(func(b *Argument) {
					u, v := b.FixAs[B]("u"), b.FixAs[B]("v")
					members := b.Conjuncts(
						b.Assume(),
						"u lies in M",
						"v lies in M")
					uInM, vInM := b.MemberOf[on.M](u, members[0]), b.MemberOf[on.M](v, members[1])
					added := b.Have(
						"the coordinates of u + v are the pointwise sum of those of u and v",
						"module_basis_coordinates(R, M, E, u + v) = "+
							"λx:B. module_basis_coordinates(R, M, E, u, x) + module_basis_coordinates(R, M, E, v, x)",
						By(finiteE, basisE, BasisCoordinatesAdd.Read(moduleOn).At(E, uInM, vInM)))
					b.Show(
						"and at e the coordinate of u + v is the sum of those of u and v",
						added.Rw(),
						Basic())
				}))
			multiples := a.Have(
				"the coordinate at e of a multiple is the multiple of the coordinate at e",
				Statement{
					Binders: "∀c:A. ∀u:B.",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"u ∈ M.carrier",
					},
					Conclusion: "module_basis_coordinates(R, M, E, c • u, e) = " +
						"c * module_basis_coordinates(R, M, E, u, e)",
				},
				Derive(func(b *Argument) {
					c, u := b.FixAs[A]("c"), b.FixAs[B]("u")
					members := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"u lies in M")
					scalar, uInM := b.MemberOf[on.R](c, members[0]), b.MemberOf[on.M](u, members[1])
					scaled := b.Have(
						"the coordinates of c • u are c times those of u",
						"module_basis_coordinates(R, M, E, c • u) = λx:B. c * module_basis_coordinates(R, M, E, u, x)",
						By(finiteE, basisE, BasisCoordinatesSmul.Read(moduleOn).At(E, scalar, uInM)))
					b.Show(
						"and at e the coordinate of c • u is c times that of u",
						scaled.Rw(),
						Basic())
				}))
			into := a.Have(
				"the coordinate at e of a vector of M is a scalar",
				"∀v:B. v ∈ M.carrier ⇒ module_basis_coordinates(R, M, E, v, e) ∈ R.carrier",
				Derive(func(b *Argument) {
					v := b.FixAs[B]("v")
					vInM := b.MemberOf[on.M](v, b.Assume())
					b.Show(
						"the coordinates of v are scalars on E, which holds e",
						By(finiteE, basisE, eInE, BasisCoordinatesSpec.Read(moduleOn).At(E, vInM)))
				}))
			a.Show(
				"so the coordinate at e is a homomorphism from M to R, a module over itself",
				By(
					module_homomorphism.ModuleHomomorphismDef,
					moduleOn,
					ring,
					module.RegularModuleOn.At(R),
					into,
					sums,
					multiples))
		}),
})}

// HomBasisExpansion — a linear map is the coordinate combination of its
// values on a finite basis: v is the combination of the basis with its
// coordinates as coefficients, and h carries that combination to the
// combination of the basis values with the same coefficients.
var HomBasisExpansion = homBasisExpansionThm{family.Add(registry.ProofEntry{
	Name: "HomBasisExpansion",
	Key:  "prop_e67f74bed91a1e45",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀E:set(B). " +
			"∀h:(B → C). " +
			"∀v:B.",
		Hypotheses: []string{
			"finite(E)",
			"module_basis(R, M, E)",
			"module_homomorphism(R, M, N, h)",
			"v ∈ M.carrier",
		},
		Conclusion: "h(v) = " +
			"module_sum(N.add, N.zero, E, λe:B. module_basis_coordinates(R, M, E, v, e) • h(e))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			E *Expr[Set[B]],
			h *Arrow[B, C],
			v *Expr[B],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"E is finite",
				"E is a basis of M",
				"h is a homomorphism of M into N",
				"v lies in M")
			finiteE, basisE, hom, vInM := given[0], given[1], given[2], proof.MemberOf(v, given[3])
			coordinates := a.Conjuncts(
				a.Have(
					"the coordinates of v are scalars on E, R.zero off E, and expand v",
					"(∀e:B. e ∈ E ⇒ module_basis_coordinates(R, M, E, v, e) ∈ R.carrier) ∧ "+
						"(∀e:B. e ∉ E ⇒ module_basis_coordinates(R, M, E, v, e) = R.zero) ∧ "+
						"module_sum(M.add, M.zero, E, λe:B. module_basis_coordinates(R, M, E, v, e) • e) = v",
					By(
						finiteE,
						basisE,
						BasisCoordinatesSpec.Read(module_homomorphism.HomSource.Read(hom)).At(E, vInM))),
				"the coordinates are scalars on E",
				"they are R.zero off E",
				"they expand v")
			mapped := a.Have(
				"h carries the coordinate combination to the combination of the basis values",
				"h(module_sum(M.add, M.zero, E, λe:B. module_basis_coordinates(R, M, E, v, e) • e)) = "+
					"module_sum(N.add, N.zero, E, λe:B. module_basis_coordinates(R, M, E, v, e) • h(e))",
				By(
					finiteE,
					a.Unfolded(linear_independence.BasisInCarrier.Read(basisE), set_basic.SubsetDef),
					coordinates[0],
					module_homomorphism.HomCombination.Read(hom).At(E,
						a.TermAs[Fun[B, A]]("module_basis_coordinates(R, M, E, v)"),
						a.TermAs[Fun[B, B]]("λe:B. e"))))
			a.Show(
				"v is its coordinate combination, so h(v) is the "+
					"combination of the basis values with the coordinates of v",
				By(coordinates[2], mapped))
		}),
})}

// IndexedBasisExpansion — a vector of M is the sum, over the indices of an
// indexed basis, of its coordinates times the basis vectors: the basis set
// expands it (BasisCoordinatesSpec), and the sum over that set is the sum
// over the indices, e being one-to-one on them.
var IndexedBasisExpansion = indexedBasisExpansionThm{family.Add(registry.ProofEntry{
	Name: "IndexedBasisExpansion",
	Key:  "prop_8da6764b64fe3260",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀e:(num → B). ∀v:B.",
		Hypotheses: []string{"module_on(R, M)", "indexed_module_basis(R, M, n, e)", "v ∈ M.carrier"},
		Conclusion: "module_sum(M.add, " +
			"    M.zero, " +
			"    «I», " +
			"    λi:num. M.smul(module_basis_coordinates(R, M, «basis», v, e(i)), e(i))) = " +
			"v",
		Abbrev: Abbrev{{Name: "I", Text: "{i:num | i < n}"}, {Name: "basis", Text: "image(e, «I»)"}},
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		M *Expr[ModuleOps[A, B]],
		n *Expr[Nat],
		e *Arrow[Nat, B],
		v *Expr[B],
		assumptions Fact,
	) {
		parts := a.Conjuncts(
			assumptions,
			"the module laws",
			"the indexed basis",
			"v lies in the module")
		image := a.Have(
			"the image has its indexed set description",
			"«basis» = {e(i):B | i:num | i < n}",
			BySets())
		data := a.Have(
			"the indexed basis has a finite injective image",
			"finite(«I») ∧ "+
				"injective_on(«I», e) ∧ "+
				"finite(«basis») ∧ "+
				"module_basis(R, M, «basis») ∧ "+
				"«basis» ⊆ M.carrier",
			image.Rw(),
			By(
				parts[1],
				num_segment.FiniteBelowStrict.At(n),
				linear_independence.IndexedBasisImage.At(R, M, n, e),
				linear_independence.BasisInCarrier.At(R, M, a.TermAs[Set[B]]("{e(i):B | i:num | i < n}"))))
		expansion := a.Have(
			"the basis set expands v",
			"module_sum(M.add, "+
				"    M.zero, "+
				"    «basis», "+
				"    λx:B. M.smul(module_basis_coordinates(R, M, «basis», v, x), x)) = "+
				"v",
			By(parts[0], parts[2], data, BasisCoordinatesSpec.At(R, M, a.TermAs[Set[B]]("«basis»"), v)))
		members := a.Have(
			"the indexed expansion summands lie in the module",
			"∀i:num. i < n ⇒ M.smul(module_basis_coordinates(R, M, «basis», v, e(i)), e(i)) ∈ M.carrier",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				inRange := b.Assume()
				b.Show(
					"each coefficient is a scalar on a basis vector",
					BySets(
						inRange,
						data,
						parts[2],
						BasisCoordinatesSpec.At(R, M, b.TermAs[Set[B]]("«basis»"), v),
						At(
							module.SmulIn.Read(parts[0]),
							b.TermAs[A]("module_basis_coordinates(R, M, «basis», v, e(i))"),
							e.Apply(i))))
			}))
		a.Show(
			"reindex the basis expansion by its injective enumeration",
			BySets(
				members,
				expansion,
				data,
				At(module.ModuleSumImage.Read(parts[0]), a.TermAs[Set[Nat]]("«I»"), e,
					a.TermAs[Fun[B, B]]("λx:B. M.smul(module_basis_coordinates(R, M, «basis», v, x), x)"))))
	}),
})}

// IndexedFunctionalExpansion — a linear functional is the sum, over an
// indexed basis, of its values weighted by the coordinates: h(v) is the
// coordinate combination of h's values on the finite basis the vectors
// e(k) form (HomBasisExpansion), its scalar factors commute, and the sum
// over that set is the sum over the indices, e being one-to-one on them.
var IndexedFunctionalExpansion = indexedFunctionalExpansionThm{family.Add(registry.ProofEntry{
	Name: "IndexedFunctionalExpansion",
	Key:  "prop_869d17e4b5c840e1",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀e:(num → B). ∀v:B. ∀h:(B → A).",
		Hypotheses: []string{
			"module_on(R, M)",
			"indexed_module_basis(R, M, n, e)",
			"v ∈ M.carrier",
			"module_homomorphism(R, M, regular_module(R), h)",
		},
		Conclusion: "h(v) = " +
			"module_sum(R.add, " +
			"    R.zero, " +
			"    {k:num | k < n}, " +
			"    λk:num. h(e(k)) * module_basis_coordinates(R, M, {e(i) | i:num | i < n}, v, e(k)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			n *Expr[Nat],
			e *Vec[B, DimN],
			v *Expr[B],
			h *Arrow[B, A],
			given Fact,
		) {
			p := a.Conjuncts(
				given,
				"M is a module",
				"e is an indexed basis",
				"v lies in M",
				"h is a linear functional")
			moduleOn, indexed, vInM, functional := p[0], p[1], p[2], p[3]
			E := a.TermAs[Set[B]]("{e(i):B | i:num | i < n}")
			indices := a.TermAs[Set[Nat]]("{i:num | i < n}")
			data := a.Have(
				"the vectors of e form a finite basis, indexed one-to-one, the image of the indices",
				"finite({e(i):B | i:num | i < n}) ∧ "+
					"module_basis(R, M, {e(i):B | i:num | i < n}) ∧ "+
					"injective_on({i:num | i < n}, e) ∧ "+
					"{e(i):B | i:num | i < n} = image(e, {i:num | i < n})",
				BySets(indexed, linear_independence.IndexedBasisImage.At(R, M, n, e)))
			ring := module.RingOn.Read(moduleOn)
			scalars := a.Have(
				"each scalar summand lies in R and its factors commute",
				Statement{
					Binders: "∀x:B.",
					Hypotheses: []string{
						"x ∈ {e(i):B | i:num | i < n}",
					},
					Conclusion: "h(x) * module_basis_coordinates(R, M, {e(i):B | i:num | i < n}, v, x) = " +
						"module_basis_coordinates(R, M, {e(i):B | i:num | i < n}, v, x) * h(x) ∧ " +
						"h(x) * module_basis_coordinates(R, M, {e(i):B | i:num | i < n}, v, x) ∈ R.carrier",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					inE := b.Assume()
					coefficient := b.TermAs[A]("module_basis_coordinates(R, M, {e(i):B | i:num | i < n}, v, x)")
					b.Show(
						"both factors are scalars",
						By(
							moduleOn,
							vInM,
							inE,
							data,
							linear_independence.BasisInCarrier.At(R, M, E),
							set_basic.SubsetDef.At(E, b.TermAs[Set[B]]("M.carrier")),
							module_homomorphism.HomIn.Read(functional).AsFact().At(x),
							BasisCoordinatesSpec.At(R, M, E, v),
							comm_ring.MulIn.Read(ring).AsFact().At(h.Apply(x), coefficient),
							comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(h.Apply(x), coefficient)))
				}))
			expansion := a.Have(
				"h(v) is the coordinate combination of the values of h on the basis",
				"h(v) = "+
					"module_sum(R.add, "+
					"    R.zero, "+
					"    {e(i):B | i:num | i < n}, "+
					"    λx:B. module_basis_coordinates(R, M, {e(i):B | i:num | i < n}, v, x) * h(x))",
				By(
					data,
					vInM,
					functional,
					HomBasisExpansion.At(R, M, a.TermAs[ModuleOps[A, A]]("regular_module(R)"), E, h, v)))
			forward := a.TermAs[Fun[B, A]](
				"λx:B. h(x) * module_basis_coordinates(R, M, {e(i):B | i:num | i < n}, v, x)")
			reverse := a.TermAs[Fun[B, A]](
				"λx:B. module_basis_coordinates(R, M, {e(i):B | i:num | i < n}, v, x) * h(x)")
			overImage := a.Have(
				"commute the factors in the expansion",
				"h(v) = "+
					"module_sum(R.add, "+
					"    R.zero, "+
					"    {e(i):B | i:num | i < n}, "+
					"    λx:B. h(x) * module_basis_coordinates(R, M, {e(i):B | i:num | i < n}, v, x))",
				By(
					scalars,
					expansion,
					module.ModuleSumCongruence.At(
						a.TermAs[Op[A]]("R.add"), a.TermAs[A]("R.zero"), E, forward, reverse)))
			indexedScalars := a.Have(
				"the reindexed summands are scalars",
				Statement{
					Binders: "∀k:num.",
					Hypotheses: []string{
						"k < n",
					},
					Conclusion: "h(e(k)) * module_basis_coordinates(R, M, {e(i):B | i:num | i < n}, v, e(k)) ∈ " +
						"R.carrier",
				},
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					below := b.Assume()
					b.Show(
						"the k-th basis vector belongs to the image",
						By(scalars.At(b.TermAs[B]("e(k)")), below, data, set_image.FunInImage.At(e, indices, k)))
				}))
			a.Show(
				"reindex the scalar sum along e",
				By(
					indexedScalars,
					overImage,
					data,
					num_segment.FiniteBelowStrict.At(n),
					module.ModuleSumImage.Read(module.RegularModuleOn.Read(ring)).At(indices, e, forward)))
		}),
})}

// IndexedImageCoordinates — the coordinates of f(v) in a finite basis E
// are the coordinates of the images f(e(k)) of an indexed basis, weighted
// by the coordinates of v: the coordinate at d is a linear functional
// (BasisCoordinateLinear), so is its composite
// with the linear map f, and that composite expands along the indexed
// basis (IndexedFunctionalExpansion).
var IndexedImageCoordinates = indexedImageCoordinatesThm{family.Add(registry.ProofEntry{
	Name: "IndexedImageCoordinates",
	Key:  "prop_2ac0a772283bca8d",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀E:set(B). " +
			"∀n:num. " +
			"∀e:(num → B). " +
			"∀f:(B → B). " +
			"∀v d:B.",
		Hypotheses: []string{
			"module_on(R, M)",
			"finite(E)",
			"module_basis(R, M, E)",
			"indexed_module_basis(R, M, n, e)",
			"module_homomorphism(R, M, M, f)",
			"v ∈ M.carrier",
			"d ∈ E",
		},
		Conclusion: "module_basis_coordinates(R, M, E, f(v), d) = " +
			"module_sum(R.add, " +
			"    R.zero, " +
			"    {k:num | k < n}, " +
			"    λk:num. " +
			"        module_basis_coordinates(R, M, E, f(e(k)), d) * " +
			"        module_basis_coordinates(R, M, {e(i) | i:num | i < n}, v, e(k)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			E *Expr[Set[B]],
			n *Expr[Nat],
			e *Vec[B, DimN],
			f *Arrow[B, B],
			v, d *Expr[B],
			given Fact,
		) {
			regular := a.TermAs[ModuleOps[A, A]]("regular_module(R)")
			coordinate := a.TermAs[Fun[B, A]]("λu:B. module_basis_coordinates(R, M, E, u, d)")
			composite := a.TermAs[Fun[B, A]]("λu:B. module_basis_coordinates(R, M, E, f(u), d)")
			linear := a.Have(
				"the coordinate after f is a linear functional",
				"module_homomorphism(R, M, regular_module(R), λu:B. module_basis_coordinates(R, M, E, f(u), d))",
				By(
					given,
					BasisCoordinateLinear.At(R, M, E, d),
					module_homomorphism.HomCompose.At(R, M, M, regular, f, coordinate),
					functions.ComposeApply.At(coordinate, f)))
			a.Show(
				"apply the functional to the indexed expansion of v",
				By(given, linear, IndexedFunctionalExpansion.At(R, M, n, e, v, composite)))
		}),
})}

// BasisCoordinateDelta — a basis vector has its Kronecker coordinate
// function: the coefficients R.one at d and R.zero elsewhere are
// scalars vanishing off E, and their combination over E is d, every
// term but d's being M.zero; so they are d's coordinates.
var BasisCoordinateDelta = basisCoordinateDeltaThm{family.Add(registry.ProofEntry{
	Name: "BasisCoordinateDelta",
	Key:  "prop_245655848445ac12",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀E:set(B). ∀d:B.",
		Hypotheses: []string{
			"finite(E)",
			"module_basis(R, M, E)",
			"d ∈ E",
		},
		Conclusion: "module_basis_coordinates(R, M, E, d) = λx:B. COND(x = d, R.one, R.zero)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			E *Expr[Set[B]],
			d *Expr[B],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"E is finite",
				"E is a basis of M",
				"d lies in E")
			finiteE, basisE, dInE := given[0], given[1], given[2]
			ring := module.RingOn.Read(moduleOn)
			eInM := a.Have(
				"a basis lies in M",
				"E ⊆ M.carrier",
				By(linear_independence.BasisInCarrier.Read(basisE)))
			eachInM := a.Unfolded(eInM, set_basic.SubsetDef)
			dInM := a.MemberOf[on.M](d, a.Have(
				"d lies in M",
				"d ∈ M.carrier",
				By(eachInM.At(d), dInE)))

			delta := a.TermAs[Fun[B, A]]("λx:B. COND(x = d, R.one, R.zero)")
			summand := a.TermAs[Fun[B, B]]("λx:B. COND(x = d, R.one, R.zero) • x")
			scalar := a.Have(
				"the delta coefficient is a scalar, R.one or R.zero",
				"∀x:B. COND(x = d, R.one, R.zero) ∈ R.carrier",
				By(comm_ring.OneIn.Read(ring), comm_ring.ZeroIn.Read(ring)))
			offE := a.Have(
				"off E it is R.zero, d lying in E",
				"∀x:B. x ∉ E ⇒ COND(x = d, R.one, R.zero) = R.zero",
				By(dInE))
			terms := a.Have(
				"each term over E lies in M",
				"∀x:B. x ∈ E ⇒ COND(x = d, R.one, R.zero) • x ∈ M.carrier",
				By(scalar, eachInM, module.SmulIn.Read(moduleOn)))
			vanish := a.Have(
				"off d the term is R.zero • x, which is M.zero",
				"∀x:B. x ∈ E ∧ x ≠ d ⇒ COND(x = d, R.one, R.zero) • x = M.zero",
				a.ForEach(func(x *Expr[B]) Action {
					return By(eachInM.At(x), module.ZeroSmul.Read(moduleOn).AsFact().At(x))
				}))
			expands := a.Have(
				"the delta combination over E is d",
				"module_sum(M.add, M.zero, E, λx:B. COND(x = d, R.one, R.zero) • x) = d",
				CalcEq(
					Leg(
						a.TermAs[B]("R.one • d"),
						"every term but d's vanishes, so the sum is the term at d",
						By(finiteE, dInE, terms, vanish, module.ModuleSumSingle.Read(moduleOn).At(E, d, summand))),
					FinalLeg(
						"R.one fixes d",
						By(module.SmulOne.Read(moduleOn).At(dInM))),
				))
			a.Show(
				"so the delta coefficients are the coordinates of d",
				By(
					finiteE,
					basisE,
					scalar,
					offE,
					expands,
					BasisCoordinatesUnique.Read(moduleOn).At(E, dInM, delta)))
		}),
})}

// BasisTraceInCarrier — the diagonal coordinate sum belongs to the scalar
// ring: f carries basis vectors into M, their coordinates are scalars,
// and the finite sum lies in R, viewed as a module over itself.
var BasisTraceInCarrier = basisTraceInCarrierThm{family.Add(registry.ProofEntry{
	Name: "BasisTraceInCarrier",
	Key:  "prop_4795c021545695a0",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀E:set(B). ∀f:(B → B).",
		Hypotheses: []string{
			"finite(E)",
			"module_basis(R, M, E)",
			"module_homomorphism(R, M, M, f)",
		},
		Conclusion: "module_basis_trace(R, M, E, f) ∈ R.carrier",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			E *Expr[Set[B]],
			f *Arrow[B, B],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"E is finite",
				"E is a basis of M",
				"f is an endomorphism of M")
			finiteE, basisE, hom := given[0], given[1], given[2]
			eInM := a.Have(
				"a basis lies in M",
				"E ⊆ M.carrier",
				By(linear_independence.BasisInCarrier.Read(basisE)))
			eachInM := a.Unfolded(eInM, set_basic.SubsetDef)
			ring := module.RingOn.Read(moduleOn)
			regular := module.RegularModuleOn.Read(ring)

			diagonal := a.Have(
				"each diagonal coordinate is a scalar",
				"∀e:B. e ∈ E ⇒ module_basis_coordinates(R, M, E, f(e), e) ∈ R.carrier",
				Derive(func(b *Argument) {
					e := b.FixAs[B]("e")
					eInE := b.Assume()
					vector := proof.MemberOf(e, b.Have(
						"e lies in M",
						"e ∈ M.carrier",
						By(eachInM.At(e), eInE)))
					image := b.MemberOf[on.M](f.Apply(e), b.Have(
						"f carries e into M",
						"f(e) ∈ M.carrier",
						By(module_homomorphism.HomIn.Read(hom).At(vector))))
					b.Show(
						"the coordinates of f(e) are scalars on E, which holds e",
						By(finiteE, basisE, eInE, BasisCoordinatesSpec.Read(moduleOn).At(E, image)))
				}))
			total := a.Have(
				"the finite diagonal sum is a scalar",
				"module_sum(R.add, R.zero, E, λe:B. module_basis_coordinates(R, M, E, f(e), e)) ∈ R.carrier",
				By(
					finiteE,
					diagonal,
					module.ModuleSumIn.Read(regular).At(E,
						a.TermAs[Fun[B, A]]("λe:B. module_basis_coordinates(R, M, E, f(e), e)"))))
			a.Show(
				"the basis trace is that diagonal sum",
				Simp(Fwd(ModuleBasisTraceDef)),
				By(total))
		}),
})}

// BasisTraceIndependent — two finite bases give the same trace: expand
// the diagonal coordinates in the other basis, interchange the finite
// scalar sums, and recover the other diagonal by its basis expansion.
var BasisTraceIndependent = basisTraceIndependentThm{family.Add(registry.ProofEntry{
	Name: "BasisTraceIndependent",
	Key:  "prop_e98e84ee0ce5b21d",
	Build: family.Sections(module.ModuleOn.Statement(Statement{
		Binders: "∀E F:set(B). ∀f:(B → B).",
		Hypotheses: []string{
			"finite(E)",
			"module_basis(R, M, E)",
			"finite(F)",
			"module_basis(R, M, F)",
			"module_homomorphism(R, M, M, f)",
		},
		Conclusion: "module_basis_trace(R, M, E, f) = module_basis_trace(R, M, F, f)",
	}),
		func(ctx *Script, headline string) *GoalStackNode {
			mappedCoordinates := ctx.Lemma(module.ModuleOn.Statement(Statement{
				Binders: "∀E F:set(B). ∀f:(B → B). ∀v j:B.",
				Hypotheses: []string{
					"finite(E)",
					"module_basis(R, M, E)",
					"finite(F)",
					"module_basis(R, M, F)",
					"module_homomorphism(R, M, M, f)",
					"v ∈ M.carrier",
					"j ∈ F",
				},
				Conclusion: "module_basis_coordinates(R, M, F, f(v), j) = " +
					"module_sum(R.add, " +
					"    R.zero, " +
					"    E, " +
					"    λe:B. module_basis_coordinates(R, M, E, v, e) * module_basis_coordinates(R, M, F, f(e), j))",
			}),
				func(
					a *Argument,
					R *Expr[RingOps[A]],
					M *Expr[ModuleOps[A, B]],
					moduleOn module.ModuleFact[on.R, on.M],
					E, F *Expr[Set[B]],
					f *Arrow[B, B],
					v, j *Expr[B],
					hypotheses Fact,
				) {
					given := a.Conjuncts(
						hypotheses,
						"E is finite",
						"E is a basis of M",
						"F is finite",
						"F is a basis of M",
						"f is an endomorphism",
						"v lies in M",
						"j lies in F")
					coordinate := a.TermAs[Fun[B, A]]("λu:B. module_basis_coordinates(R, M, F, u, j)")
					regular := a.TermAs[ModuleOps[A, A]]("regular_module(R)")
					linear := a.Have(
						"the F-coordinate at j is a linear functional",
						"module_homomorphism(R, M, regular_module(R), λu:B. module_basis_coordinates(R, M, F, u, j))",
						By(given[2], given[3], given[6], BasisCoordinateLinear.Read(moduleOn).At(F, j)))
					composite := a.Have(
						"the F-coordinate after f is a linear functional",
						"module_homomorphism(R, M, regular_module(R), λu:B. module_basis_coordinates(R, M, F, f(u), j))",
						By(
							given[4],
							linear,
							module_homomorphism.HomCompose.At(R, M, M, regular, f, coordinate),
							functions.ComposeApply.At(coordinate, f)))
					a.Show(
						"apply that functional to the E-expansion of v",
						By(
							given[0],
							given[1],
							composite,
							given[5],
							HomBasisExpansion.At(R, M, regular, E,
								a.TermAs[Fun[B, A]]("λu:B. module_basis_coordinates(R, M, F, f(u), j)"), v)))
				})

			traceDoubleSum := ctx.Lemma(module.ModuleOn.Statement(Statement{
				Binders: "∀E F:set(B). ∀f:(B → B).",
				Hypotheses: []string{
					"finite(E)",
					"module_basis(R, M, E)",
					"finite(F)",
					"module_basis(R, M, F)",
					"module_homomorphism(R, M, M, f)",
				},
				Conclusion: "module_basis_trace(R, M, F, f) = " +
					"module_sum(R.add, " +
					"    R.zero, " +
					"    F, " +
					"    λj:B. " +
					"        module_sum(R.add, " +
					"            R.zero, " +
					"            E, " +
					"            λe:B. " +
					"                module_basis_coordinates(R, M, E, j, e) * " +
					"                module_basis_coordinates(R, M, F, f(e), j)))",
			}),
				func(
					a *Argument,
					R *Expr[RingOps[A]],
					M *Expr[ModuleOps[A, B]],
					moduleOn module.ModuleFact[on.R, on.M],
					E, F *Expr[Set[B]],
					f *Arrow[B, B],
					hypotheses Fact,
				) {
					given := a.Conjuncts(
						hypotheses,
						"E is finite",
						"E is a basis of M",
						"F is finite",
						"F is a basis of M",
						"f is an endomorphism")
					fInM := a.Have(
						"the basis F lies in M",
						"F ⊆ M.carrier",
						By(linear_independence.BasisInCarrier.Read(given[3])))
					eachInM := a.Unfolded(fInM, set_basic.SubsetDef)
					diagonal := a.Have(
						"expand each F-diagonal coordinate along E",
						Statement{
							Binders: "∀j:B.",
							Hypotheses: []string{
								"j ∈ F",
							},
							Conclusion: "module_basis_coordinates(R, M, F, f(j), j) = " +
								"module_sum(R.add, " +
								"    R.zero, " +
								"    E, " +
								"    λe:B. module_basis_coordinates(R, M, E, j, e) * module_basis_coordinates(R, M, F, f(e), j))",
						},
						Derive(func(b *Argument) {
							j := b.FixAs[B]("j")
							jInF := b.Assume()
							b.Show(
								"read the coordinate expansion at j",
								By(
									given[0],
									given[1],
									given[2],
									given[3],
									given[4],
									eachInM.At(j),
									jInF,
									Read(mappedCoordinates, moduleOn).At(E, F, f, j, j)))
						}))
					a.Show(
						"the trace is the sum of those expanded diagonal coordinates",
						Simp(Fwd(ModuleBasisTraceDef)),
						By(diagonal, module.ModuleSumCongruence))
				})

			contractExpansion := ctx.Lemma(module.ModuleOn.Statement(Statement{
				Binders: "∀E F:set(B). ∀v e:B.",
				Hypotheses: []string{
					"finite(E)",
					"module_basis(R, M, E)",
					"finite(F)",
					"module_basis(R, M, F)",
					"v ∈ M.carrier",
					"e ∈ E",
				},
				Conclusion: "module_sum(R.add, " +
					"    R.zero, " +
					"    F, " +
					"    λj:B. module_basis_coordinates(R, M, E, j, e) * module_basis_coordinates(R, M, F, v, j)) = " +
					"module_basis_coordinates(R, M, E, v, e)",
			}),
				func(
					a *Argument,
					R *Expr[RingOps[A]],
					M *Expr[ModuleOps[A, B]],
					moduleOn module.ModuleFact[on.R, on.M],
					E, F *Expr[Set[B]],
					v, e *Expr[B],
					hypotheses Fact,
				) {
					given := a.Conjuncts(
						hypotheses,
						"E is finite",
						"E is a basis of M",
						"F is finite",
						"F is a basis of M",
						"v lies in M",
						"e lies in E")
					fInM := a.Have(
						"the basis F lies in M",
						"F ⊆ M.carrier",
						By(linear_independence.BasisInCarrier.Read(given[3])))
					eachInM := a.Unfolded(fInM, set_basic.SubsetDef)
					coordinate := a.TermAs[Fun[B, A]]("λu:B. module_basis_coordinates(R, M, E, u, e)")
					linear := a.Have(
						"the E-coordinate at e is a linear functional",
						"module_homomorphism(R, M, regular_module(R), λu:B. module_basis_coordinates(R, M, E, u, e))",
						By(given[0], given[1], given[5], BasisCoordinateLinear.Read(moduleOn).At(E, e)))
					eScalars := a.Have(
						"the E-coordinate of every F-vector is a scalar",
						"∀j:B. j ∈ F ⇒ module_basis_coordinates(R, M, E, j, e) ∈ R.carrier",
						By(eachInM, module_homomorphism.HomIn.Read(linear)))
					fScalars := a.Have(
						"the F-coordinates of v are scalars",
						"∀j:B. j ∈ F ⇒ module_basis_coordinates(R, M, F, v, j) ∈ R.carrier",
						By(given[2], given[3], BasisCoordinatesSpec.Read(moduleOn).At(F, a.MemberOf[on.M](v, given[4]))))
					commute := a.Have(
						"the two scalar factors commute at each F-vector",
						Statement{
							Binders: "∀j:B.",
							Hypotheses: []string{
								"j ∈ F",
							},
							Conclusion: "module_basis_coordinates(R, M, E, j, e) * module_basis_coordinates(R, M, F, v, j) = " +
								"module_basis_coordinates(R, M, F, v, j) * module_basis_coordinates(R, M, E, j, e)",
						},
						a.ForEach(func(j *Expr[B]) Action {
							return By(
								eScalars.At(j),
								fScalars.At(j),
								comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(module.RingOn.Read(moduleOn))))
						}))
					expanded := a.Have(
						"apply the E-coordinate functional to the F-expansion of v",
						"module_basis_coordinates(R, M, E, v, e) = "+
							"module_sum(R.add, "+
							"    R.zero, "+
							"    F, "+
							"    λj:B. module_basis_coordinates(R, M, F, v, j) * module_basis_coordinates(R, M, E, j, e))",
						By(
							given[2],
							given[3],
							linear,
							given[4],
							HomBasisExpansion.At(R, M, a.TermAs[ModuleOps[A, A]]("regular_module(R)"), F, coordinate, v)))
					a.Show(
						"the inner sum recovers the E-coordinate of v",
						CalcEq(
							Leg(
								a.TermAs[A](
									"module_sum(R.add, "+
										"    R.zero, "+
										"    F, "+
										"    λj:B. module_basis_coordinates(R, M, F, v, j) * module_basis_coordinates(R, M, E, j, e))"),
								"commute the scalar factors in the sum",
								By(commute, module.ModuleSumCongruence)),
							FinalLeg(
								"the sum is the coordinate of v",
								By(expanded)),
						))
				})

			return ctx.Theorem(headline,
				func(
					a *Argument,
					R *Expr[RingOps[A]],
					M *Expr[ModuleOps[A, B]],
					moduleOn module.ModuleFact[on.R, on.M],
					E, F *Expr[Set[B]],
					f *Arrow[B, B],
					hypotheses Fact,
				) {
					given := a.Conjuncts(
						hypotheses,
						"E is finite",
						"E is a basis of M",
						"F is finite",
						"F is a basis of M",
						"f is an endomorphism")
					finiteE, basisE, finiteF, basisF, hom := given[0], given[1], given[2], given[3], given[4]
					eInM := a.Have(
						"the basis E lies in M",
						"E ⊆ M.carrier",
						By(linear_independence.BasisInCarrier.Read(basisE)))
					eachE := a.Unfolded(eInM, set_basic.SubsetDef)
					fInM := a.Have(
						"the basis F lies in M",
						"F ⊆ M.carrier",
						By(linear_independence.BasisInCarrier.Read(basisF)))
					eachF := a.Unfolded(fInM, set_basic.SubsetDef)
					ring := module.RingOn.Read(moduleOn)
					regular := module.RegularModuleOn.Read(ring)
					images := a.Have(
						"f carries each E-vector into M",
						"∀e:B. e ∈ E ⇒ f(e) ∈ M.carrier",
						By(eachE, module_homomorphism.HomIn.Read(hom)))
					products := a.Have(
						"each summand of the double sum is a scalar",
						Statement{
							Binders: "∀j e:B.",
							Hypotheses: []string{
								"j ∈ F",
								"e ∈ E",
							},
							Conclusion: "module_basis_coordinates(R, M, E, j, e) * " +
								"module_basis_coordinates(R, M, F, f(e), j) ∈ " +
								"R.carrier",
						},
						Derive(func(b *Argument) {
							j, e := b.FixAs[B]("j"), b.FixAs[B]("e")
							members := b.Conjuncts(
								b.Assume(),
								"j lies in F",
								"e lies in E")
							jInM := b.MemberOf[on.M](j, b.Have(
								"j lies in M",
								"j ∈ M.carrier",
								By(eachF.At(j), members[0])))
							image := b.MemberOf[on.M](f.Apply(e), b.Have(
								"f(e) lies in M",
								"f(e) ∈ M.carrier",
								By(images.At(e), members[1])))
							left := b.MemberOf[on.R](b.TermAs[A]("module_basis_coordinates(R, M, E, j, e)"),
								b.Have(
									"the E-coordinate of j is a scalar",
									"module_basis_coordinates(R, M, E, j, e) ∈ R.carrier",
									By(finiteE, basisE, members[1], BasisCoordinatesSpec.Read(moduleOn).At(E, jInM))))
							right := b.MemberOf[on.R](b.TermAs[A]("module_basis_coordinates(R, M, F, f(e), j)"),
								b.Have(
									"the F-coordinate of f(e) is a scalar",
									"module_basis_coordinates(R, M, F, f(e), j) ∈ R.carrier",
									By(finiteF, basisF, members[0], BasisCoordinatesSpec.Read(moduleOn).At(F, image))))
							b.Show(
								"the product of those scalars is a scalar",
								By(comm_ring.MulIn.Read(ring).At(left, right)))
						}))
					contracted := a.Have(
						"each inner sum recovers its E-diagonal coordinate",
						Statement{
							Binders: "∀e:B.",
							Hypotheses: []string{
								"e ∈ E",
							},
							Conclusion: "module_sum(R.add, " +
								"    R.zero, " +
								"    F, " +
								"    λj:B. " +
								"        module_basis_coordinates(R, M, E, j, e) * module_basis_coordinates(R, M, F, f(e), j)) = " +
								"module_basis_coordinates(R, M, E, f(e), e)",
						},
						Derive(func(b *Argument) {
							e := b.FixAs[B]("e")
							eInE := b.Assume()
							image := b.MemberOf[on.M](f.Apply(e), b.Have(
								"f(e) lies in M",
								"f(e) ∈ M.carrier",
								By(images.At(e), eInE)))
							b.Show(
								"apply the coordinate contraction to f(e)",
								By(
									finiteE,
									basisE,
									finiteF,
									basisF,
									image,
									eInE,
									Read(contractExpansion, moduleOn).At(E, F, image, e)))
						}))
					a.Show(
						"the two bases give the same trace",
						CalcEq(
							Leg(
								a.TermAs[A](
									"module_sum(R.add, "+
										"    R.zero, "+
										"    E, "+
										"    λe:B. "+
										"        module_sum(R.add, "+
										"            R.zero, "+
										"            F, "+
										"            λj:B. "+
										"                module_basis_coordinates(R, M, E, j, e) * "+
										"                module_basis_coordinates(R, M, F, f(e), j)))"),
								"expand each E-diagonal coordinate as its inner sum over F",
								Simp(Fwd(ModuleBasisTraceDef)),
								By(contracted, module.ModuleSumCongruence)),
							Leg(
								a.TermAs[A](
									"module_sum(R.add, "+
										"    R.zero, "+
										"    F, "+
										"    λj:B. "+
										"        module_sum(R.add, "+
										"            R.zero, "+
										"            E, "+
										"            λe:B. "+
										"                module_basis_coordinates(R, M, E, j, e) * "+
										"                module_basis_coordinates(R, M, F, f(e), j)))"),
								"interchange the two finite scalar sums",
								By(
									finiteF,
									finiteE,
									products,
									module.ModuleSumSwap.Read(regular).At(F, E,
										a.TermAs[Fun2[B, B, A]](
											"λj:B. λe:B. "+
												"    module_basis_coordinates(R, M, E, j, e) * module_basis_coordinates(R, M, F, f(e), j)")))),
							FinalLeg(
								"the double sum is the F-diagonal expanded in E",
								By(finiteE, basisE, finiteF, basisF, hom, Read(traceDoubleSum, moduleOn).At(E, F, f))),
						))
				})
		}),
})}

// TraceFromBasis — any finite basis computes the trace: its trace value
// witnesses the defining choice, and basis independence identifies the
// trace in the chosen finite basis with the trace in E.
var TraceFromBasis = traceFromBasisThm{family.Add(registry.ProofEntry{
	Name: "TraceFromBasis",
	Key:  "prop_24a6673e9a2f5e1a",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀E:set(B). ∀f:(B → B).",
		Hypotheses: []string{
			"finite(E)",
			"module_basis(R, M, E)",
			"module_homomorphism(R, M, M, f)",
		},
		Conclusion: "module_trace(R, M, f) = module_basis_trace(R, M, E, f)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			E *Expr[Set[B]],
			f *Arrow[B, B],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"E is finite",
				"E is a basis of M",
				"f is an endomorphism")
			finiteE, basisE, hom := given[0], given[1], given[2]
			possible := a.Have(
				"E and its trace value witness the defining choice",
				"∃r:A. ∃F:set(B). finite(F) ∧ module_basis(R, M, F) ∧ r = module_basis_trace(R, M, F, f)",
				Derive(func(b *Argument) {
					b.Take(b.TermAs[A]("module_basis_trace(R, M, E, f)"))
					b.Take(E)
					b.Show(
						"E supplies a finite basis and that trace value",
						By(finiteE, basisE))
				}))
			specified := a.Have(
				"the chosen trace is the trace in a finite basis",
				"∃F:set(B). "+
					"    finite(F) ∧ module_basis(R, M, F) ∧ module_trace(R, M, f) = module_basis_trace(R, M, F, f)",
				Simp(Fwd(ModuleTraceDef)),
				By(possible))
			F, chosen := a.UnpackAs[Set[B]](specified, "F")
			selection := a.Conjuncts(
				chosen,
				"F is finite",
				"F is a basis of M",
				"the chosen trace is the trace in F")
			same := a.Have(
				"the two finite bases give the same trace",
				"module_basis_trace(R, M, F, f) = module_basis_trace(R, M, E, f)",
				By(
					selection[0],
					selection[1],
					finiteE,
					basisE,
					hom,
					BasisTraceIndependent.Read(moduleOn).At(F, E, f)))
			a.Show(
				"E computes the chosen trace",
				CalcEq(
					Leg(
						a.TermAs[A]("module_basis_trace(R, M, F, f)"),
						"the chosen finite basis F computes the trace",
						By(selection[2])),
					FinalLeg(
						"basis independence replaces F by E",
						By(same)),
				))
		}),
})}

// TraceCongruence — two maps that agree on the module have the same
// trace: a finite basis lies in M, so the two maps have the same
// diagonal coordinates on it and the same basis trace; the trace is the
// choice of a basis trace value, so the two traces choose from one
// predicate.
var TraceCongruence = traceCongruenceThm{family.Add(registry.ProofEntry{
	Name: "TraceCongruence",
	Key:  "prop_b7f24e3cf1169245",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀f g:(B → B).",
		Hypotheses: []string{
			"∀v:B. v ∈ M.carrier ⇒ f(v) = g(v)",
		},
		Conclusion: "module_trace(R, M, f) = module_trace(R, M, g)",
	},
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], f, g *Arrow[B, B], agree Fact) {
			sameBasisTrace := a.Have(
				"every finite basis gives the two maps the same basis trace",
				Statement{
					Binders: "∀E:set(B).",
					Hypotheses: []string{
						"finite(E)",
						"module_basis(R, M, E)",
					},
					Conclusion: "module_basis_trace(R, M, E, f) = module_basis_trace(R, M, E, g)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[B]]("E")
					onE := b.Conjuncts(
						b.Assume(),
						"E is finite",
						"E is a basis of M")
					within := b.Have(
						"the basis E lies in M",
						"E ⊆ M.carrier",
						By(linear_independence.BasisInCarrier.Read(onE[1])))
					diagonal := b.Have(
						"on E the two maps have the same diagonal coordinates",
						Statement{
							Binders: "∀e:B.",
							Hypotheses: []string{
								"e ∈ E",
							},
							Conclusion: "module_basis_coordinates(R, M, E, f(e), e) = " +
								"module_basis_coordinates(R, M, E, g(e), e)",
						},
						By(Normalized, b.Unfolded(within, set_basic.SubsetDef), agree))
					b.Show(
						"so the same diagonal sum",
						Simp(Fwd(ModuleBasisTraceDef)),
						By(diagonal, module.ModuleSumCongruence))
				}))
			samePredicate := a.Have(
				"so the two maps leave the same trace values acceptable",
				"(λr:A. ∃E:set(B). finite(E) ∧ module_basis(R, M, E) ∧ r = module_basis_trace(R, M, E, f)) = "+
					"λr:A. ∃E:set(B). finite(E) ∧ module_basis(R, M, E) ∧ r = module_basis_trace(R, M, E, g)",
				Funext(),
				By(sameBasisTrace))
			a.Show(
				"the trace chooses from that one predicate",
				Simp(Fwd(ModuleTraceDef)),
				By(samePredicate))
		}),
})}

// TraceAdd — the trace of the pointwise sum of two endomorphisms is the
// sum of their traces: a finite basis E of M computes all three traces,
// the diagonal coordinate of f + g at each vector of E is the sum of
// those of f and g, and the finite scalar sum over E distributes over
// the addition.
var TraceAdd = traceAddThm{family.Add(registry.ProofEntry{
	Name: "TraceAdd",
	Key:  "prop_1376c740b4462495",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀f g:(B → B).",
		Hypotheses: []string{
			"finite_dimensional(R, M)",
			"module_homomorphism(R, M, M, f)",
			"module_homomorphism(R, M, M, g)",
		},
		Conclusion: "module_trace(R, M, λv:B. f(v) + g(v)) = module_trace(R, M, f) + module_trace(R, M, g)",
	},
		func(a *Argument, moduleOn module.ModuleFact[on.R, on.M], f, g *Arrow[B, B], hypotheses Fact) {
			given := a.Conjuncts(
				hypotheses,
				"M is finite-dimensional",
				"f is an endomorphism",
				"g is an endomorphism")
			finiteM, homF, homG := given[0], given[1], given[2]
			E, finiteBasis := a.UnpackAs[Set[B]](a.Unfolded(finiteM, FiniteDimensionalDef), "E")
			onE := a.Conjuncts(
				finiteBasis,
				"E is finite",
				"E is a basis of M")
			finiteE, basisE := onE[0], onE[1]
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			within := a.Have(
				"the basis E lies in M",
				"E ⊆ M.carrier",
				By(linear_independence.BasisInCarrier.Read(basisE)))
			eachInM := a.Unfolded(within, set_basic.SubsetDef)
			images := a.Have(
				"f and g carry the basis vectors into M",
				"∀e:B. e ∈ E ⇒ f(e) ∈ M.carrier ∧ g(e) ∈ M.carrier",
				a.ForEach(func(e *Expr[B]) Action {
					return By(
						eachInM.At(e),
						module_homomorphism.HomIn.Read(homF).AsFact().At(e),
						module_homomorphism.HomIn.Read(homG).AsFact().At(e))
				}))
			diagonal := a.Have(
				"both diagonal coefficient functions take scalar values on E",
				Statement{
					Binders: "∀e:B.",
					Hypotheses: []string{
						"e ∈ E",
					},
					Conclusion: "module_basis_coordinates(R, M, E, f(e), e) ∈ R.carrier ∧ " +
						"module_basis_coordinates(R, M, E, g(e), e) ∈ R.carrier",
				},
				Derive(func(b *Argument) {
					e := b.FixAs[B]("e")
					eInE := b.Assume()
					inM := b.Conjuncts(
						b.Have(
							"f and g carry e into M",
							"f(e) ∈ M.carrier ∧ g(e) ∈ M.carrier",
							By(images.At(e), eInE)),
						"f(e) lies in M",
						"g(e) lies in M")
					imageF, imageG := b.MemberOf[on.M](f.Apply(e), inM[0]), b.MemberOf[on.M](g.Apply(e), inM[1])
					b.Show(
						"the coordinates of f(e) and of g(e) are scalars on E, which holds e",
						By(
							finiteE,
							basisE,
							eInE,
							BasisCoordinatesSpec.Read(moduleOn).At(E, imageF),
							BasisCoordinatesSpec.Read(moduleOn).At(E, imageG)))
				}))
			added := a.Have(
				"the diagonal coefficient of the sum is the sum of the diagonal coefficients",
				Statement{
					Binders: "∀e:B.",
					Hypotheses: []string{
						"e ∈ E",
					},
					Conclusion: "module_basis_coordinates(R, M, E, f(e) + g(e), e) = " +
						"module_basis_coordinates(R, M, E, f(e), e) + module_basis_coordinates(R, M, E, g(e), e)",
				},
				Derive(func(b *Argument) {
					e := b.FixAs[B]("e")
					eInE := b.Assume()
					coordinates := b.Have(
						"the coordinate function of the sum is the pointwise sum",
						"module_basis_coordinates(R, M, E, f(e) + g(e)) = "+
							"λx:B. module_basis_coordinates(R, M, E, f(e), x) + module_basis_coordinates(R, M, E, g(e), x)",
						By(
							finiteE,
							basisE,
							eInE,
							images.At(e),
							BasisCoordinatesAdd.Read(moduleOn).AsFact().At(E, f.Apply(e), g.Apply(e))))
					b.Show(
						"evaluate that coordinate function at e",
						coordinates.Rw(),
						Basic())
				}))
			regular := module.RegularModuleOn.Read(module.RingOn.Read(moduleOn))
			basisTrace := a.Have(
				"in E the trace of f + g is the sum of the traces of f and g",
				"module_basis_trace(R, M, E, λv:B. f(v) + g(v)) = "+
					"module_basis_trace(R, M, E, f) + module_basis_trace(R, M, E, g)",
				Simp(Fwd(ModuleBasisTraceDef)),
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    E, "+
								"    λe:B. "+
								"        module_basis_coordinates(R, M, E, f(e), e) + module_basis_coordinates(R, M, E, g(e), e))"),
						"replace each diagonal coefficient by its sum",
						By(added, module.ModuleSumCongruence)),
					FinalLeg(
						"the finite scalar sum distributes over addition",
						By(
							finiteE,
							diagonal,
							module.ModuleSumAdd.Read(regular).At(
								E,
								a.TermAs[Fun[B, A]]("λe:B. module_basis_coordinates(R, M, E, f(e), e)"),
								a.TermAs[Fun[B, A]]("λe:B. module_basis_coordinates(R, M, E, g(e), e)")))),
				))
			sumHom := a.Have(
				"the pointwise sum f + g is an endomorphism",
				"module_homomorphism(R, M, M, λv:B. f(v) + g(v))",
				By(homF, homG, module_homomorphism.HomPointwiseSum.At(R, M, M, f, g)))
			traceF := a.Have(
				"E computes the trace of f",
				"module_trace(R, M, f) = module_basis_trace(R, M, E, f)",
				By(finiteE, basisE, homF, TraceFromBasis.Read(moduleOn).At(E, f)))
			traceG := a.Have(
				"E computes the trace of g",
				"module_trace(R, M, g) = module_basis_trace(R, M, E, g)",
				By(finiteE, basisE, homG, TraceFromBasis.Read(moduleOn).At(E, g)))
			traceSum := a.Have(
				"E computes the trace of f + g",
				"module_trace(R, M, λv:B. f(v) + g(v)) = module_basis_trace(R, M, E, λv:B. f(v) + g(v))",
				By(
					finiteE,
					basisE,
					sumHom,
					TraceFromBasis.Read(moduleOn).At(E, a.TermAs[Fun[B, B]]("λv:B. f(v) + g(v)"))))
			a.Show(
				"so the trace of f + g is the sum of the traces",
				CalcEq(
					Leg(
						a.TermAs[A]("module_basis_trace(R, M, E, λv:B. f(v) + g(v))"),
						"compute the trace in E",
						By(traceSum)),
					FinalLeg(
						"distribute the diagonal sum and recover the two traces",
						Simp(Fwd(basisTrace), Rev(traceF), Rev(traceG)),
						Basic()),
				))
		}),
})}

// TraceScale — the trace of a scalar multiple of an endomorphism is the
// scalar times its trace: a finite basis E of M computes both traces,
// the diagonal coordinate of c • f at each vector of E is c times that
// of f, and c factors out of the finite scalar sum over E.
var TraceScale = traceScaleThm{family.Add(registry.ProofEntry{
	Name: "TraceScale",
	Key:  "prop_badb0f018a5daa8e",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀c:A. ∀f:(B → B).",
		Hypotheses: []string{
			"finite_dimensional(R, M)",
			"c ∈ R.carrier",
			"module_homomorphism(R, M, M, f)",
		},
		Conclusion: "module_trace(R, M, λv:B. c • f(v)) = c * module_trace(R, M, f)",
	},
		func(
			a *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			c *Expr[A],
			f *Arrow[B, B],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"M is finite-dimensional",
				"c is a scalar",
				"f is an endomorphism")
			finiteM, homF := given[0], given[2]
			scalar := a.MemberOf[on.R](c, given[1])
			E, finiteBasis := a.UnpackAs[Set[B]](a.Unfolded(finiteM, FiniteDimensionalDef), "E")
			onE := a.Conjuncts(
				finiteBasis,
				"E is finite",
				"E is a basis of M")
			finiteE, basisE := onE[0], onE[1]
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			within := a.Have(
				"the basis E lies in M",
				"E ⊆ M.carrier",
				By(linear_independence.BasisInCarrier.Read(basisE)))
			eachInM := a.Unfolded(within, set_basic.SubsetDef)
			images := a.Have(
				"f carries the basis vectors into M",
				"∀e:B. e ∈ E ⇒ f(e) ∈ M.carrier",
				a.ForEach(func(e *Expr[B]) Action {
					return By(eachInM.At(e), module_homomorphism.HomIn.Read(homF).AsFact().At(e))
				}))
			diagonal := a.Have(
				"the diagonal coefficient function takes scalar values on E",
				"∀e:B. e ∈ E ⇒ module_basis_coordinates(R, M, E, f(e), e) ∈ R.carrier",
				Derive(func(b *Argument) {
					e := b.FixAs[B]("e")
					eInE := b.Assume()
					image := b.MemberOf[on.M](f.Apply(e), b.Have(
						"f carries e into M",
						"f(e) ∈ M.carrier",
						By(images.At(e), eInE)))
					b.Show(
						"the coordinates of f(e) are scalars on E, which holds e",
						By(finiteE, basisE, eInE, BasisCoordinatesSpec.Read(moduleOn).At(E, image)))
				}))
			multiplied := a.Have(
				"the diagonal coefficient of the multiple is the multiple of the diagonal coefficient",
				Statement{
					Binders: "∀e:B.",
					Hypotheses: []string{
						"e ∈ E",
					},
					Conclusion: "module_basis_coordinates(R, M, E, c • f(e), e) = " +
						"c * module_basis_coordinates(R, M, E, f(e), e)",
				},
				Derive(func(b *Argument) {
					e := b.FixAs[B]("e")
					eInE := b.Assume()
					coordinates := b.Have(
						"the coordinate function of the multiple is the scalar multiple",
						"module_basis_coordinates(R, M, E, c • f(e)) = "+
							"λx:B. c * module_basis_coordinates(R, M, E, f(e), x)",
						By(
							finiteE,
							basisE,
							scalar,
							eInE,
							images.At(e),
							BasisCoordinatesSmul.Read(moduleOn).AsFact().At(E, scalar, f.Apply(e))))
					b.Show(
						"evaluate that coordinate function at e",
						coordinates.Rw(),
						Basic())
				}))
			regular := module.RegularModuleOn.Read(module.RingOn.Read(moduleOn))
			basisTrace := a.Have(
				"in E the trace of c • f is c times the trace of f",
				"module_basis_trace(R, M, E, λv:B. c • f(v)) = c * module_basis_trace(R, M, E, f)",
				Simp(Fwd(ModuleBasisTraceDef)),
				CalcEq(
					Leg(
						a.TermAs[A]("module_sum(R.add, R.zero, E, λe:B. c * module_basis_coordinates(R, M, E, f(e), e))"),
						"replace each diagonal coefficient by its multiple",
						By(multiplied, module.ModuleSumCongruence)),
					FinalLeg(
						"the finite scalar sum commutes with scaling",
						By(
							finiteE,
							scalar,
							diagonal,
							module.ModuleSumSmul.Read(regular).At(E, scalar,
								a.TermAs[Fun[B, A]]("λe:B. module_basis_coordinates(R, M, E, f(e), e)")))),
				))
			multipleHom := a.Have(
				"the multiple c • f is an endomorphism",
				"module_homomorphism(R, M, M, λv:B. c • f(v))",
				By(homF, scalar, module_homomorphism.HomScalarMultiple.At(R, M, M, f, c)))
			traceF := a.Have(
				"E computes the trace of f",
				"module_trace(R, M, f) = module_basis_trace(R, M, E, f)",
				By(finiteE, basisE, homF, TraceFromBasis.Read(moduleOn).At(E, f)))
			traceMultiple := a.Have(
				"E computes the trace of c • f",
				"module_trace(R, M, λv:B. c • f(v)) = module_basis_trace(R, M, E, λv:B. c • f(v))",
				By(
					finiteE,
					basisE,
					multipleHom,
					TraceFromBasis.Read(moduleOn).At(E, a.TermAs[Fun[B, B]]("λv:B. c • f(v)"))))
			a.Show(
				"so the trace of c • f is c times the trace of f",
				CalcEq(
					Leg(
						a.TermAs[A]("module_basis_trace(R, M, E, λv:B. c • f(v))"),
						"compute the trace in E",
						By(traceMultiple)),
					FinalLeg(
						"scale the diagonal sum and recover the trace of f",
						Simp(Fwd(basisTrace), Rev(traceF)),
						Basic()),
				))
		}),
})}

// IdempotentTraceIsRank — The trace of an idempotent is the field multiple of one given by its image dimension.
var IdempotentTraceIsRank = idempotentTraceIsRankThm{family.Add(registry.ProofEntry{
	Name: "IdempotentTraceIsRank",
	Key:  "prop_caddd6ee21accdeb",
	Deps: []registry.EntryLike{
		module_homomorphism.IdempotentSplits,
		TraceFromBasis,
		BasisCoordinateDelta,
		SubmoduleDim,
		linear_independence.BasisExists,
		DimBasis,
	},
	Build: family.Card(module.ModuleOn.Statement(Statement{
		Binders: "∀invR:(A → A). ∀f:(B → B).",
		Hypotheses: []string{
			"ring_subfield(R, invR, R.carrier)",
			"finite_dimensional(R, M)",
			"module_homomorphism(R, M, M, f)",
			"∀v:B. v ∈ M.carrier ⇒ f(f(v)) = f(v)",
		},
		Conclusion: "module_trace(R, M, f) = " +
			"monoid_pow(R.add, R.zero, R.one, module_dim(R, restrict_module(M, image(f, M.carrier))))",
	}),
		"Choose bases of image and kernel and concatenate their disjoint "+
			"nonzero basis sets using IdempotentSplits. In that basis the diagonal "+
			"coordinates of f are one on the image and zero on the kernel."),
})}
