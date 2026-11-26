// poles.go — the spaces L(n) of functions with poles of order at most n at a
// regular rational point P: the powers of the inverse of P as lattice pairs, the
// nested k-subspaces their sections form, their dimensions, and the orders at P
// of what lies in them.

package regular_point

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/valuation_order"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/filtered_space"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_twist"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// PolePairDegree — the pair of functions with poles of order at most n at a
// regular point P is invertible of degree n: it begins at the structure pair,
// of degree zero, and each next power is the twist of the one before at P, which
// keeps invertibility and raises the degree by one.
var PolePairDegree = polePairDegreeThm{family.Add(registry.ProofEntry{
	Name: "PolePairDegree",
	Key:  "prop_3c72adea3c2ea865",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀n:num.",
		Hypotheses: []string{
			"«rpCurve»",
			"«rpPoint»(P)",
		},
		Conclusion: "invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, «rpPolePair»(n)) ∧ " +
			"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «rpPolePair»(n)) = n",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			n *Expr[Nat],
			curve, point Fact,
		) {
			chart := GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t))
			a.Induct(n)
			a.Base(
				"the zeroth power is the structure pair, invertible of degree zero",
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				By(chart, curve_degree.DegreeStructure.Read(L).At(k, A0, A1, A01)))
			a.Step(
				"the next power is the twist of this one at P",
				func(b *Argument, ih Fact) {
					power := b.TermAs[_LatticePair]("«rpPolePair»(n)")
					b.Do(Simp(Fwd(comm_monoid.MonoidPowDef), Rev(lattice_pair_twist.LatticePairTwistDef)))
					b.Show(
						"a twist at P keeps invertibility and raises the degree by one",
						ByArith(
							ih,
							curve,
							point,
							chart,
							lattice_pair_twist.BiaffineRegularPointDef,
							lattice_pair_twist.TwistInvertible.Read(L).At(A0, A1, A01, t, power, P),
							curve_degree.DegreeTwist.Read(L).At(k, A0, A1, A01, t, power, P)))
				})
		}),
})}

// PoleSpaceSubmodule — each pole space is a k-submodule of the function field:
// it is H⁰ of the pole pair, and k lies in both charts.
var PoleSpaceSubmodule = poleSpaceSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "PoleSpaceSubmodule",
	Key:  "prop_7990e4e2ca877868",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀n:num.",
		Hypotheses: []string{
			"«rpCurve»",
			"«rpPoint»(P)",
		},
		Conclusion: "submodule(«rpScalars», regular_module(field_ring(L)), «rpPoles»(n).carrier)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			n *Expr[Nat],
			curve, point Fact,
		) {
			line := a.Simplified(
				GroupPremises(curve, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)),
				Fwd(module_record.RestrictRingTwice))
			invertible := a.Have(
				"the n-th pole pair is invertible",
				"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, «rpPolePair»(n))",
				By(curve, point, PolePairDegree.Read(L).At(k, A0, A1, A01, t, P, n)))
			lattice := a.Have(
				"so it is a lattice pair over the overlap",
				"lattice_pair(restrict_ring(field_ring(L), A₀₁), "+
					"    A₀, "+
					"    A₁, "+
					"    regular_module(field_ring(L)), "+
					"    «rpPolePair»(n))",
				By(a.Unfolded(invertible, invertible_lattice_pair.InvertibleLatticePairDef)))
			constants := a.Have(
				"k lies in both charts",
				"k ⊆ A₀ ∧ k ⊆ A₁",
				BySets(line))
			record := a.Have(
				"the pole space is H⁰ of the pole pair",
				"«rpPoles»(n) = "+
					"restrict_module(regular_module(field_ring(L)), fst(«rpPolePair»(n)) ∩ snd(«rpPolePair»(n)))",
				Simp(Fwd(SinglePointPoleSpaceDef), Fwd(lattice_pair.LatticePairH0Def)),
				Refl())
			overlap := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), A₀₁)")
			functions := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			pair := a.TermAs[_LatticePair]("«rpPolePair»(n)")
			meet := a.Simplified(
				GroupPremises(lattice, constants, lattice_pair.H0Submodule.At(overlap, A0, A1, k, functions, pair)),
				Fwd(module_record.RestrictRingTwice))
			a.Show(
				"H⁰ of a lattice pair is a submodule over the scalars both charts hold",
				record.Rw(),
				By(line, lattice, constants, meet))
		}),
})}

// PoleSpaceModule — a pole space is a module over the constants: it is the
// function field restricted to its carrier, a submodule over k.
var PoleSpaceModule = poleSpaceModuleThm{family.Add(registry.ProofEntry{
	Name: "PoleSpaceModule",
	Key:  "prop_c4dd03997deca58c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀n:num.",
		Hypotheses: []string{
			"«rpCurve»",
			"«rpPoint»(P)",
		},
		Conclusion: "module_on(«rpScalars», «rpPoles»(n))",
		Abbrev: Abbrev{
			{Name: "sections", Text: "fst(«rpPolePair»(n)) ∩ snd(«rpPolePair»(n))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			n *Expr[Nat],
			curve, point Fact,
		) {
			restriction := a.Have(
				"the pole space is the function field restricted to its carrier",
				"restrict_module(regular_module(field_ring(L)), «sections») = «rpPoles»(n)",
				Simp(Fwd(SinglePointPoleSpaceDef), Fwd(lattice_pair.LatticePairH0Def)),
				Refl())
			a.Show(
				"that carrier is a submodule of the function field over k",
				By(
					restriction,
					curve,
					point,
					a.Simplified(
						GroupPremises(curve, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)),
						Fwd(module_record.RestrictRingTwice)),
					PoleSpaceSubmodule.Read(L).At(k, A0, A1, A01, t, P, n),
					submodule.SubmoduleModuleOn.At(
						a.TermAs[RingOps[A]]("«rpScalars»"),
						a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"),
						a.TermAs[Set[A]]("«sections»"))))
		}),
})}

// PoleSpacesNested — the pole spaces increase with the order of the pole: a pair
// lies inside its twist at P, which is the next power, so a pole space lies in the
// next, and then in each later one by induction on the gap.
var PoleSpacesNested = poleSpacesNestedThm{family.Add(registry.ProofEntry{
	Name: "PoleSpacesNested",
	Key:  "prop_26395b1870b1fbe1",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀m n:num.",
		Hypotheses: []string{
			"«rpCurve»",
			"«rpPoint»(P)",
			"m ≤ n",
		},
		Conclusion: "«rpPoles»(m).carrier ⊆ «rpPoles»(n).carrier",
		Abbrev: Abbrev{
			{Name: "sections", Text: "λn:num. fst(«rpPolePair»(n)) ∩ snd(«rpPolePair»(n))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			m, n *Expr[Nat],
			curve, point, ordered Fact,
		) {
			chart := GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t))
			step := a.Have(
				"each pole space lies in the next",
				"∀j:num. «sections»(j) ⊆ «sections»(suc(j))",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					power := b.TermAs[_LatticePair]("«rpPolePair»(j)")
					inTwist := b.Have(
						"each chart of a pair lies in that chart of its twist at P",
						"fst(«rpPolePair»(j)) ⊆ fst(lattice_pair_twist(field_ring(L), A₀, A₁, «rpPolePair»(j), P)) ∧ "+
							"snd(«rpPolePair»(j)) ⊆ snd(lattice_pair_twist(field_ring(L), A₀, A₁, «rpPolePair»(j), P))",
						By(
							curve,
							point,
							chart,
							PolePairDegree.Read(L).At(k, A0, A1, A01, t, P, j),
							lattice_pair_twist.TwistQuotientDim.Read(L).At(k, A0, A1, A01, t, power, P)))
					b.Show(
						"that twist is the next power, so the sections at j are sections at suc(j)",
						Simp(Fwd(comm_monoid.MonoidPowDef), Rev(lattice_pair_twist.LatticePairTwistDef)),
						BySets(inTwist))
				}))
			offsets := a.Have(
				"so each pole space lies in all the later ones",
				"∀d:num. «sections»(m) ⊆ «sections»(m + d)",
				Derive(func(b *Argument) {
					d := b.FixAs[Nat]("d")
					b.Induct(d)
					b.Base(
						"at no offset the two are one",
						Simp(Fwd(nat_arith.AddZero)),
						By(set_order.SubsetRefl))
					b.Step(
						"one offset more is one step more",
						func(c *Argument, ih Fact) {
							c.Do(Simp(Fwd(nat_arith.AddSuc)))
							c.Show(
								"the step extends the inclusion",
								BySets(ih, step.At(c.TermAs[Nat]("m + d"))))
						})
				}))
			difference := a.Have(
				"m ≤ n writes n as m plus their difference",
				"m + (n - m) = n",
				ByArith(ordered))
			a.Show(
				"so the n-th pole space holds the m-th",
				Simp(Fwd(SinglePointPoleSpaceDef), Fwd(lattice_pair.LatticePairH0Def)),
				By(a.Simplified(offsets.At(a.TermAs[Nat]("n - m")), Fwd(difference))))
		}),
})}

// SinglePointPoleFiltration — the spaces of functions on the curve with poles of
// order at most n at a regular point P filter them over the constants: no pole
// allowed leaves the constants, products add the budgets, each step adds at most
// one dimension to a space of finite dimension, and the n-th has dimension at least
// n + 1 - g. The n-th space is the sections of the n-th power of the inverse of P:
// the upper bounds count from H⁰(O) = k along the residue line of the point, the
// lower bound is Euler's Riemann–Roch with the dimension of H¹ dropped, the products
// are taken chart by chart, and each space lies in the next.
var SinglePointPoleFiltration = singlePointPoleFiltrationThm{family.Add(registry.ProofEntry{
	Name: "SinglePointPoleFiltration",
	Key:  "prop_572ba787c17af160",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«rpCurve»",
			"«rpPoint»(P)",
		},
		Conclusion: "«rpPoles»(0).carrier = k ∧ " +
			"(∀a b:num. set_mul(«rpPoles»(a).carrier, «rpPoles»(b).carrier) ⊆ «rpPoles»(a + b).carrier) ∧ " +
			"(∀n:num. " +
			"    finite_dimensional(«rpScalars», «rpPoles»(n)) ∧ " +
			"    «rpPoleDim»(n) ≤ n + 1 ∧ " +
			"    int_of_num(n) + int_of_num(1) - int_of_num(«rpGenus») ≤ int_of_num(«rpPoleDim»(n))) ∧ " +
			"(∀n:num. 0 < n ⇒ «rpPoleDim»(n - 1) ≤ «rpPoleDim»(n) ∧ «rpPoleDim»(n) ≤ «rpPoleDim»(n - 1) + 1)",
		Abbrev: Abbrev{
			{Name: "sections", Text: "λn:num. fst(«rpPolePair»(n)) ∩ snd(«rpPolePair»(n))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			curve, point Fact,
		) {
			inverse := a.TermAs[Fun[A, A]]("L.inv")
			scalarRing := a.TermAs[module_record.RingOps[A]]("«rpScalars»")
			functions := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			chart := GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t))
			constants := a.Have(
				"the functions regular on both charts are the constants",
				"A₀ ∩ A₁ = k",
				By(GroupPremises(curve, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t))))
			spaces := a.Have(
				"each pole space is H⁰ of its pair, the functions in both of its charts",
				"∀n:num. «rpPoles»(n) = restrict_module(regular_module(field_ring(L)), «sections»(n))",
				Simp(Fwd(SinglePointPoleSpaceDef), Fwd(lattice_pair.LatticePairH0Def)),
				Basic())

			// The constants, and the products of sections.
			noPoles := a.Have(
				"a function with no poles allowed lies in A₀ ∩ A₁",
				"«rpPoles»(0).carrier = k",
				Simp(Fwd(spaces), Fwd(comm_monoid.MonoidPowDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(Normalized, constants))
			monoid := a.Have(
				"the invertible pairs are a commutative monoid with identity the structure pair",
				"comm_monoid_on( "+
					"    {X:prod(set(A), set(A)) | invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, X)}, "+
					"    lattice_pair_mul(field_ring(L), A₀, A₁), "+
					"    (A₀, A₁))",
				By(chart, invertible_lattice_pair.InvertiblePairsCommMonoid.Read(L).At(A0, A1, A01, t)))
			exponents := a.Have(
				"exponents add in that monoid, the inverse of P being one of its members",
				"∀m n:num. "+
					"    «rpPolePair»(m + n) = "+
					"    lattice_pair_mul(field_ring(L), A₀, A₁, «rpPolePair»(m), «rpPolePair»(n))",
				By(
					chart,
					point,
					lattice_pair_twist.BiaffineRegularPointDef,
					invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, P),
					comm_monoid.PowAddOn.Read(monoid)))
			products := a.Have(
				"a product of sections of two powers is a section of their product",
				"∀m n:num. ∀x y:A. x ∈ «sections»(m) ∧ y ∈ «sections»(n) ⇒ x * y ∈ «sections»(m + n)",
				Derive(func(b *Argument) {
					b.Fix("m")
					b.Fix("n")
					x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
					given := b.Assume()
					charts := b.Have(
						"the charts at m + n are the products of the charts at m and at n",
						"fst(«rpPolePair»(m + n)) = "+
							"fractional_mul(field_ring(L), A₀, fst(«rpPolePair»(m)), fst(«rpPolePair»(n))) ∧ "+
							"snd(«rpPolePair»(m + n)) = "+
							"fractional_mul(field_ring(L), A₁, snd(«rpPolePair»(m)), snd(«rpPolePair»(n)))",
						Simp(
							Fwd(exponents),
							Fwd(invertible_lattice_pair.LatticePairMulDef),
							Fwd(pairs.Fst),
							Fwd(pairs.Snd)),
						Basic())
					b.Show(
						"each chart of a product holds the products of the charts",
						BySets(
							given,
							charts,
							fractional_ideal.FractionalMulHolds.Read(L).At(
								A0,
								b.TermAs[Set[A]]("fst(«rpPolePair»(m))"),
								b.TermAs[Set[A]]("fst(«rpPolePair»(n))"),
								x,
								y),
							fractional_ideal.FractionalMulHolds.Read(L).At(
								A1,
								b.TermAs[Set[A]]("snd(«rpPolePair»(m))"),
								b.TermAs[Set[A]]("snd(«rpPolePair»(n))"),
								x,
								y)))
				}))
			budgets := a.Have(
				"so products add pole budgets",
				"∀a b:num. set_mul(«rpPoles»(a).carrier, «rpPoles»(b).carrier) ⊆ «rpPoles»(a + b).carrier",
				Derive(func(b *Argument) {
					m, n := b.FixAs[Nat]("m"), b.FixAs[Nat]("n")
					b.Do(Simp(Fwd(quotient_group.SetMulDef)))
					b.Show(
						"a member of the product set is a product of members",
						BySets(products.At(m, n)))
				}))

			// Finiteness and the lower bound.
			sized := a.Have(
				"each pole space is finite-dimensional, of dimension at least n + 1 - g",
				"∀n:num. "+
					"    finite_dimensional(«rpScalars», «rpPoles»(n)) ∧ "+
					"    n + &1 - int_of_num(«rpGenus») ≤ int_of_num(«rpPoleDim»(n))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					power := b.TermAs[_LatticePair]("«rpPolePair»(n)")
					finite := b.Simplified(
						algebraic_curve.InvertibleFinite.Read(L).At(k, A0, A1, A01, t, power),
						Fwd(module_record.RestrictRingTwice),
						Fwd(lattice_pair.LatticePairFiniteDef))
					euler := b.Simplified(
						GroupPremises(curve, curve_degree.RiemannRochEuler.Read(L).At(k, A0, A1, A01, t, power)),
						Fwd(module_record.RestrictRingTwice),
						Fwd(lattice_pair.LatticePairEulerDef),
						Fwd(lattice_pair.LatticePairH0DimDef))
					b.Do(Simp(Fwd(SinglePointPoleSpaceDef)))
					b.Show(
						"χ = dim H⁰ - dim H¹ is the degree n plus 1 - g, and dim H¹ is a natural number",
						ByArith(curve, point, PolePairDegree.Read(L).At(k, A0, A1, A01, t, P, n), finite, euler))
				}))

			// The upper bounds, from the order at P.
			growth := a.Have(
				"the residue line at P bounds each step by one",
				"∀n:num. «rpPoleDim»(suc(n)) ≤ «rpPoleDim»(n) + 1",
				Simp(Fwd(nat_arith.Add1)),
				By(a.Simplified(
					GroupPremises(curve, point, RegularPointOrderAndFiltration.Read(L).At(k, A0, A1, A01, t, P)))))
			one := a.Have(
				"the constants are a line over themselves",
				"«rpPoleDim»(0) = 1",
				Simp(Fwd(SinglePointPoleSpaceDef), Fwd(comm_monoid.MonoidPowDef)),
				By(
					curve,
					a.Simplified(
						GroupPremises(curve, algebraic_curve.StructureH0.Read(L).At(k, A0, A1, A01, t)),
						Fwd(module_record.RestrictRingTwice),
						Fwd(lattice_pair.LatticePairH0DimDef))))
			bounded := a.Have(
				"so the n-th space has dimension at most n + 1",
				"∀n:num. «rpPoleDim»(n) ≤ n + 1",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Induct(n)
					b.Base(
						"the constants have dimension one",
						ByArith(one))
					b.Step(
						"each next space adds at most one dimension",
						func(c *Argument, ih Fact) {
							c.Show(
								"n + 2 bounds the next dimension",
								ByArith(growth.At(n), ih))
						})
				}))

			// The spaces grow.
			scalars := a.Have(
				"k is a subfield of L, a field of scalars",
				"ring_subfield(«rpScalars», L.inv, k)",
				By(chart, field.SubfieldRingSubfield.Read(L).At(k, k)))
			subspaces := a.Have(
				"the sections of each power are a k-subspace of L",
				"∀n:num. submodule(«rpScalars», regular_module(field_ring(L)), «sections»(n))",
				a.ForEach(func(n *Expr[Nat]) Action {
					return By(curve, point, PoleSpaceSubmodule.Read(L).At(k, A0, A1, A01, t, P, n))
				}))
			monotone := a.Have(
				"each space is a subspace of the next, so its dimension is no larger",
				"∀n:num. «rpPoleDim»(n) ≤ «rpPoleDim»(suc(n))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					next := b.TermAs[Nat]("suc(n)")
					smaller := b.TermAs[Set[A]]("«sections»(n)")
					larger := b.TermAs[Set[A]]("«sections»(suc(n))")
					nested := b.Have(
						"the sections at n are sections at suc(n)",
						"«sections»(n) ⊆ «sections»(suc(n))",
						ByArith(curve, point, PoleSpacesNested.Read(L).At(k, A0, A1, A01, t, P, n, next)))
					nextSpace := b.Have(
						"the next space is a vector space over k",
						"module_on(«rpScalars», restrict_module(regular_module(field_ring(L)), «sections»(suc(n))))",
						By(spaces.At(next), curve, point, PoleSpaceModule.Read(L).At(k, A0, A1, A01, t, P, next)))
					inside := b.Have(
						"and this space is a subspace of it",
						"submodule(«rpScalars», "+
							"    restrict_module(regular_module(field_ring(L)), «sections»(suc(n))), "+
							"    «sections»(n))",
						By(subspaces.At(n), nested, submodule.SubmoduleRestrict.At(scalarRing, functions, larger, smaller)))
					b.Do(Simp(Fwd(spaces)))
					b.Show(
						"a subspace of a finite-dimensional space has no larger dimension",
						By(
							nextSpace,
							scalars,
							sized.At(next),
							spaces.At(next),
							inside,
							b.Simplified(
								module_dimension.SubmoduleDim.Read(nextSpace).At(inverse, smaller),
								Fwd(module_record.RestrictModuleTwice))))
				}))
			steps := a.Have(
				"at a positive index the two step bounds read one index down",
				"∀n:num. 0 < n ⇒ «rpPoleDim»(n - 1) ≤ «rpPoleDim»(n) ∧ «rpPoleDim»(n) ≤ «rpPoleDim»(n - 1) + 1",
				Derive(func(b *Argument) {
					b.Fix("n")
					positive := b.Assume()
					before := b.TermAs[Nat]("n - 1")
					index := b.Have(
						"n is the successor of n - 1",
						"suc(n - 1) = n",
						ByArith(positive))
					b.Show(
						"from n - 1 to n the dimension grows, by at most one",
						By(index, monotone.At(before), growth.At(before)))
				}))
			a.Show(
				"the constants, the products of budgets, the size of each space and its growth",
				By(noPoles, budgets, sized, bounded, steps))
		}),
})}

// PoleOrderBounds — a nonzero function with poles of order at most n at P has
// order between -n and 0 there. The lower bound is the point's own; a function
// of nonnegative order lies in the zeroth pole space, the constants, and a
// nonzero constant has order zero, since it and its inverse have nonnegative
// orders adding up to the order of one.
var PoleOrderBounds = poleOrderBoundsThm{family.Add(registry.ProofEntry{
	Name: "PoleOrderBounds",
	Key:  "prop_ef60d5d289686ef0",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀n:num. ∀f:A.",
		Hypotheses: []string{
			"«rpCurve»",
			"«rpPoint»(P)",
			"f ∈ «rpPoles»(n).carrier",
			"f ≠ L.zero",
		},
		Conclusion: "-n ≤ «rpOrder»(f) ∧ «rpOrder»(f) ≤ 0",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			n *Expr[Nat],
			f *Expr[A],
			curve, point, inPoles, nonzero Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("L")
			one := a.TermAs[A]("L.one")
			zero := a.TermAs[Nat]("0")
			constants := a.Conjuncts(
				a.Have(
					"k is a subfield of L, lying in it",
					"subfield(L, k) ∧ k ⊆ L.carrier",
					By(
						GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
						field.SubfieldSubset.At(ops, k))),
				"k is a subfield of L",
				"k lies in L")
			subfieldK, constantsInL := constants[0], constants[1]
			order := a.Conjuncts(
				a.Have(
					"the order at P is a valuation, bounded below on the pole spaces, which it tells apart",
					"valuation_order(field_ring(L), «rpOrder») ∧ "+
						"(∀g:A. ∀m:num. g ∈ «rpPoles»(m).carrier ∧ g ≠ L.zero ⇒ -m ≤ «rpOrder»(g)) ∧ "+
						"(∀g:A. ∀m l:num. "+
						"    g ∈ «rpPoles»(m).carrier ∧ l ≤ m ⇒ "+
						"    (g ∈ «rpPoles»(l).carrier ⇔ g = L.zero ∨ -l ≤ «rpOrder»(g)))",
					Simp(Fwd(SinglePointPoleSpaceDef), Fwd(lattice_pair.LatticePairH0Def)),
					By(a.Simplified(
						GroupPremises(curve, point, RegularPointOrderAndFiltration.Read(L).At(k, A0, A1, A01, t, P))))),
				"the order at P is a valuation",
				"each pole space bounds the order below",
				"the order tells the pole spaces apart")
			valuation, below, criterion := order[0], order[1], order[2]
			products := a.Unfolded(valuation, valuation_order.ValuationOrderDef)
			constantPoles := a.Have(
				"the zeroth pole space is k",
				"«rpPoles»(0).carrier = k",
				By(curve, point, SinglePointPoleFiltration.Read(L).At(k, A0, A1, A01, t, P)))
			square := a.Have(
				"one is its own square",
				"L.one * L.one = L.one",
				ByArith(L))
			oneOrder := a.Have(
				"so one has order zero",
				"«rpOrder»(L.one) = 0",
				ByArith(
					square,
					comm_ring.OneIn.Read(field.RingOn.Read(L)),
					field.OneNotZeroOn.Read(L),
					products.At(one, one)))
			constantOrder := a.Have(
				"a nonzero constant has order zero: it and its inverse "+
					"have nonnegative orders adding up to that of one",
				"∀c:A. c ∈ k ∧ c ≠ L.zero ⇒ «rpOrder»(c) = 0",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					parts := b.Conjuncts(
						b.Assume(),
						"c is a constant",
						"c is nonzero")
					isConstant, isNonzero := parts[0], parts[1]
					inL := b.Have(
						"c lies in L",
						"c ∈ L.carrier",
						BySets(isConstant, constantsInL))
					cm := b.MemberOf[on.L](c, inL)
					inverse := b.TermAs[A]("L.inv(c)")
					inverted := b.Have(
						"its inverse is a nonzero constant inverting it",
						"L.inv(c) ∈ k ∧ L.inv(c) ≠ L.zero ∧ c * L.inv(c) = L.one",
						By(
							isConstant,
							isNonzero,
							subfieldK,
							field.SubfieldInv.At(ops, k, c),
							field.InvEqZeroOn.Read(L).At(cm),
							field.MulRightInverseOn.Read(L).At(cm)))
					inverseInL := b.Have(
						"so does its inverse",
						"L.inv(c) ∈ L.carrier",
						BySets(inverted, constantsInL))
					inZeroth := b.Have(
						"c and its inverse lie in the zeroth pole space",
						"c ∈ «rpPoles»(0).carrier ∧ L.inv(c) ∈ «rpPoles»(0).carrier",
						By(Normalized, constantPoles, isConstant, inverted))
					nonnegative := b.Have(
						"so c and its inverse have nonnegative order",
						"-0 ≤ «rpOrder»(c) ∧ -0 ≤ «rpOrder»(L.inv(c))",
						By(below.At(c, zero), below.At(inverse, zero), inZeroth, isNonzero, inverted))
					b.Show(
						"their orders add up to that of one, which is zero",
						ByArith(products.At(c, inverse), inL, inverseInL, isNonzero, inverted, nonnegative, oneOrder))
				}))
			lower := a.Have(
				"the order of f is at least -n",
				"-n ≤ «rpOrder»(f)",
				By(below.At(f, n), inPoles, nonzero))
			a.Cases(a.TermAs[Bool]("-0 ≤ «rpOrder»(f)"))
			a.When(
				"a function of nonnegative order is a constant, of order zero",
				func(b *Argument, nonnegative Fact) {
					reads := b.Have(
						"zero is at most n, and f meets the criterion at zero",
						"0 ≤ n ∧ (f = L.zero ∨ -0 ≤ «rpOrder»(f))",
						ByArith(nonnegative))
					zeroth := b.Have(
						"so f lies in the zeroth pole space",
						"f ∈ «rpPoles»(0).carrier",
						By(reads, inPoles, criterion.At(f, n, zero)))
					constant := b.Have(
						"which is k",
						"f ∈ k",
						By(Normalized, constantPoles, zeroth))
					b.Show(
						"its order is zero",
						ByArith(lower, constantOrder.At(f), constant, nonzero))
				})
			a.Otherwise(
				"a function of negative order satisfies the bound as it stands",
				func(b *Argument, negative Fact) {
					b.Show(
						"its order lies between -n and 0",
						ByArith(lower, negative))
				})
		}),
})}

// PoleOrderAdaptedBasis — the pole space of order a has a finite k-basis of
// distinct orders, all between -a and 0: the filtration {0} ⊆ L(0) ⊆ … ⊆ L(a)
// by pole spaces grows by at most one dimension at a step, so it has a basis
// adapted to it, and a basis vector entering at L(j) has order exactly -j, lying
// in L(j) and outside L(j - 1).
var PoleOrderAdaptedBasis = poleOrderAdaptedBasisThm{family.Add(registry.ProofEntry{
	Name: "PoleOrderAdaptedBasis",
	Key:  "prop_8c9c292d86f3da53",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀a:num.",
		Hypotheses: []string{
			"«rpCurve»",
			"«rpPoint»(P)",
		},
		Conclusion: "∃E:set(A). " +
			"    finite(E) ∧ " +
			"    module_basis(«rpScalars», «rpPoles»(a), E) ∧ " +
			"    injective_on(E, «rpOrder») ∧ " +
			"    (∀x:A. x ∈ E ⇒ -a ≤ «rpOrder»(x) ∧ «rpOrder»(x) ≤ 0)",
		Abbrev: Abbrev{
			{Name: "functions", Text: "regular_module(field_ring(L))"},
			{Name: "poleSet", Text: "λi:num. fst(«rpPolePair»(i)) ∩ snd(«rpPolePair»(i))"},
			{Name: "poleModule", Text: "restrict_module(«functions», «poleSet»(a))"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			a *Expr[Nat],
			curve, point Fact,
		) {
			scalars := arg.TermAs[RingOps[A]]("«rpScalars»")
			regularFunctions := arg.TermAs[module_record.ModuleOps[A, A]]("«functions»")
			poleModule := arg.TermAs[module_record.ModuleOps[A, A]]("«poleModule»")
			top := arg.TermAs[Set[A]]("«poleSet»(a)")
			steps := arg.TermAs[Nat]("a + 1")
			inverse := arg.TermAs[Fun[A, A]]("L.inv")
			zero := arg.TermAs[Nat]("0")
			constants := arg.Conjuncts(
				arg.Have(
					"k is a subfield of L, and a field",
					"subfield(L, k) ∧ field_on(restrict_field(L, k))",
					By(GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)))),
				"k is a subfield of L",
				"k is a field")
			subfieldK, scalarField := constants[0], constants[1]
			filtration := arg.Conjuncts(
				GroupPremises(curve, point, SinglePointPoleFiltration.Read(L).At(k, A0, A1, A01, t, P)),
				"the zeroth pole space is k",
				"pole orders add under products",
				"the pole spaces are finite dimensional, of dimension at most one more than the order",
				"each pole space adds at most one dimension to the one before")
			sizes, growth := filtration[2], filtration[3]
			pieces := arg.Have(
				"each pole space is a k-submodule of the function field",
				"∀i:num. submodule(«rpScalars», «functions», «poleSet»(i))",
				arg.ForEach(func(i *Expr[Nat]) Action {
					return By(curve, point, PoleSpaceSubmodule.Read(L).At(k, A0, A1, A01, t, P, i))
				}))
			functionModule := arg.Have(
				"the function field is a module over k",
				"module_on(«rpScalars», «functions»)",
				By(arg.Simplified(
					GroupPremises(curve, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)),
					Fwd(module_record.RestrictRingTwice))))
			dimensions := arg.Have(
				"a pole space is the function field restricted to its carrier",
				"∀i:num. module_dim(«rpScalars», restrict_module(«functions», «poleSet»(i))) = «rpPoleDim»(i)",
				Simp(Fwd(SinglePointPoleSpaceDef), Fwd(lattice_pair.LatticePairH0Def)),
				Basic())
			record := arg.Have(
				"in particular the a-th",
				"«poleModule» = «rpPoles»(a)",
				Simp(Fwd(SinglePointPoleSpaceDef), Fwd(lattice_pair.LatticePairH0Def)),
				Refl())
			nested := arg.Have(
				"the pole spaces increase",
				"∀i j:num. i ≤ j ⇒ «poleSet»(i) ⊆ «poleSet»(j)",
				Derive(func(b *Argument) {
					i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
					b.Show(
						"the i-th pole space lies in the j-th",
						By(b.Assume(), curve, point, PoleSpacesNested.Read(L).At(k, A0, A1, A01, t, P, i, j)))
				}))
			F, FDef := arg.LetAs[Fun[Nat, Set[A]]]("F", "λi:num. COND(i = 0, {L.zero}, «poleSet»(i - 1))")
			start := arg.Have(
				"the filtration starts at zero",
				"F(0) = {L.zero}",
				Simp(Fwd(FDef)),
				Basic())
			later := arg.Have(
				"and then runs through the pole spaces",
				"∀i:num. 0 < i ⇒ F(i) = «poleSet»(i - 1)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					positive := b.Assume()
					nonzero := b.Have(
						"i is not zero",
						"i ≠ 0",
						ByArith(positive))
					b.Show(
						"past the first step F reads the pole space",
						Simp(Fwd(FDef)),
						By(nonzero))
				}))
			shifted := arg.Have(
				"so its step after i is the i-th pole space",
				"∀i:num. F(i + 1) = «poleSet»(i)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					following := b.TermAs[Nat]("i + 1")
					positive := b.Have(
						"i + 1 is positive",
						"0 < i + 1",
						ByArith())
					b.Show(
						"the predecessor of i + 1 is i",
						By(positive, later.At(following), nat_monus.AddSubCancel))
				}))
			moduleOnPoles := arg.Have(
				"the a-th pole space is a module over k",
				"module_on(«rpScalars», «poleModule»)",
				record.Rw(),
				By(curve, point, PoleSpaceModule.Read(L).At(k, A0, A1, A01, t, P, a)))
			finitePoles := arg.Have(
				"of finite dimension",
				"finite_dimensional(«rpScalars», «poleModule»)",
				record.Rw(),
				By(sizes.At(a)))
			submodules := arg.Have(
				"each step of the filtration is a submodule of the a-th pole space",
				"∀i:num. i ≤ a + 1 ⇒ submodule(«rpScalars», «poleModule», F(i))",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					below := b.Assume()
					b.Cases(b.TermAs[Bool]("i = 0"))
					b.When(
						"the first step is the zero submodule",
						func(c *Argument, isZero Fact) {
							c.Show(
								"zero is a submodule",
								isZero.Rw(),
								start.Rw(),
								By(moduleOnPoles, submodule.ZeroSubmodule.At(scalars, poleModule)))
						})
					b.Otherwise(
						"a later step is a pole space below the a-th",
						func(c *Argument, nonzero Fact) {
							previous := c.TermAs[Nat]("i - 1")
							inside := c.TermAs[Set[A]]("«poleSet»(i - 1)")
							order := c.Have(
								"i is positive and i - 1 ≤ a",
								"0 < i ∧ i - 1 ≤ a",
								ByArith(below, nonzero))
							inTop := c.Have(
								"so the pole space lies in the a-th",
								"«poleSet»(i - 1) ⊆ «poleSet»(a)",
								By(nested.At(previous, a), order))
							c.Show(
								"a submodule lying in a set is a submodule of the restriction to it",
								GroupPremises(order, later.At(i)).Rw(),
								By(
									pieces.At(previous),
									inTop,
									submodule.SubmoduleRestrict.At(scalars, regularFunctions, top, inside)))
						})
				}))
			fieldScalars := arg.Have(
				"k is a field of scalars",
				"ring_subfield(«rpScalars», L.inv, k)",
				By(subfieldK, field.SubfieldRingSubfield.Read(L).At(k, k)))
			growthSteps := arg.Have(
				"the filtration increases, by at most one dimension at each step",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"i < a + 1",
					},
					Conclusion: "F(i) ⊆ F(i + 1) ∧ " +
						"module_dim(«rpScalars», restrict_module(«functions», F(i + 1))) ≤ " +
						"module_dim(«rpScalars», restrict_module(«functions», F(i))) + 1",
				},
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Assume()
					b.Do(shifted.At(i).Rw())
					b.Cases(b.TermAs[Bool]("i = 0"))
					b.When(
						"zero lies in the constants, whose dimension is at most one",
						func(c *Argument, isZero Fact) {
							first := c.TermAs[Set[A]]("«poleSet»(0)")
							zeroIn := c.Have(
								"zero lies in the zeroth pole space, a submodule",
								"L.zero ∈ «poleSet»(0)",
								By(pieces.At(zero), submodule.SubmoduleZero.At(scalars, regularFunctions, first)))
							inFirst := c.Have(
								"so the zero submodule lies in it",
								"{L.zero} ⊆ «poleSet»(0)",
								BySets(zeroIn))
							c.Show(
								"the zero submodule has dimension zero",
								isZero.Rw(),
								start.Rw(),
								ByArith(
									inFirst,
									sizes.At(zero),
									dimensions.At(zero),
									fieldScalars,
									functionModule,
									module_dimension.ZeroSubmoduleDim.At(scalars, inverse, regularFunctions)))
						})
					b.Otherwise(
						"a later step is the growth of the pole spaces",
						func(c *Argument, nonzero Fact) {
							previous := c.TermAs[Nat]("i - 1")
							order := c.Have(
								"i - 1 ≤ i and i is positive",
								"i - 1 ≤ i ∧ 0 < i",
								ByArith(nonzero))
							c.Show(
								"each pole space lies in the next and adds at most one dimension",
								GroupPremises(order, later.At(i)).Rw(),
								ByArith(order, nested.At(previous, i), growth.At(i), dimensions.At(i), dimensions.At(previous)))
						})
				}))
			base := arg.Simplified(
				filtered_space.FilteredSpaceAdaptedBasis.Read(scalarField).At(poleModule, F, steps),
				Rev(field.RestrictFieldRing),
				Fwd(module_record.RestrictModuleTwice))
			E, _, adapted := arg.Obtain2As[Set[A], Fun[A, Nat]](
				"the filtration has an adapted basis",
				"∃E:set(A). ∃layer:(A → num). "+
					"    finite(E) ∧ "+
					"    module_basis(«rpScalars», «poleModule», E) ∧ "+
					"    injective_on(E, layer) ∧ "+
					"    (∀e:A. e ∈ E ⇒ 0 < layer(e) ∧ layer(e) ≤ a + 1 ∧ e ∈ F(layer(e)) ∧ e ∉ F(layer(e) - 1)) ∧ "+
					"    (∀i:num. "+
					"        i ≤ a + 1 ⇒ module_span(«rpScalars», «poleModule», {e:A | e ∈ E ∧ layer(e) ≤ i}) = F(i))",
				By(base, moduleOnPoles, finitePoles, start, shifted.At(a), submodules, growthSteps),
				Named("E", "layer"))
			basis := arg.Conjuncts(
				adapted,
				"E is finite",
				"E is a basis of the a-th pole space",
				"its layers are distinct",
				"each vector enters at its layer",
				"the vectors up to a layer span that step")
			finiteE, isBasis, distinctLayers, entries := basis[0], basis[1], basis[2], basis[3]
			criterion := arg.Have(
				"the order tells the pole spaces apart",
				"∀g:A. ∀m l:num. g ∈ «poleSet»(m) ∧ l ≤ m ⇒ (g ∈ «poleSet»(l) ⇔ g = L.zero ∨ -l ≤ «rpOrder»(g))",
				By(arg.Simplified(
					GroupPremises(curve, point, RegularPointOrderAndFiltration.Read(L).At(k, A0, A1, A01, t, P)))))
			orders := arg.Have(
				"a basis vector entering at the step after j has order -j",
				"∀e:A. e ∈ E ⇒ «rpOrder»(e) = -int_of_num(layer(e) - 1) ∧ layer(e) - 1 ≤ a",
				Derive(func(b *Argument) {
					e := b.FixAs[A]("e")
					eInE := b.Assume()
					entry := b.Conjuncts(
						GroupPremises(eInE, entries.At(e)),
						"its layer is positive",
						"and at most a + 1",
						"e lies in the step of its layer",
						"and outside the step before")
					positive, bounded, inside, outside := entry[0], entry[1], entry[2], entry[3]
					j := b.TermAs[Nat]("layer(e) - 1")
					l := b.TermAs[Nat]("layer(e)")
					inPole := b.Have(
						"e lies in the pole space of order j",
						"e ∈ «poleSet»(layer(e) - 1)",
						By(inside, positive, later.At(l)))
					before := b.TermAs[Set[A]]("F(layer(e) - 1)")
					inRange := b.Have(
						"the step before is one of the filtration",
						"layer(e) - 1 ≤ a + 1",
						ByArith(bounded))
					nonzero := b.Have(
						"e is nonzero, as zero lies in every step of the filtration",
						"e ≠ L.zero",
						By(outside, inRange, submodules.At(j), submodule.SubmoduleZero.At(scalars, poleModule, before)))
					bounds := b.Have(
						"so e has order between -j and 0",
						"-(layer(e) - 1) ≤ «rpOrder»(e) ∧ «rpOrder»(e) ≤ 0",
						By(curve, point, inPole, nonzero, PoleOrderBounds.Read(L).At(k, A0, A1, A01, t, P, j, e)))
					b.Cases(b.TermAs[Bool]("layer(e) - 1 = 0"))
					b.When(
						"e enters at the constants, of order zero",
						func(c *Argument, atZero Fact) {
							c.Show(
								"between -0 and 0, the order is zero",
								ByArith(bounds, atZero, bounded))
						})
					b.Otherwise(
						"e enters at a pole of order j, outside the pole space of order j - 1",
						func(c *Argument, away Fact) {
							positiveOrder := c.Have(
								"j is positive and j - 1 ≤ j",
								"0 < layer(e) - 1 ∧ layer(e) - 1 - 1 ≤ layer(e) - 1",
								ByArith(away))
							previous := c.TermAs[Nat]("layer(e) - 1 - 1")
							notBelow := c.Have(
								"so e does not reach the order of the pole space before",
								"¬(-(layer(e) - 1 - 1) ≤ «rpOrder»(e))",
								Derive(func(d *Argument) {
									reaches := d.SupposeNot()
									d.Show(
										"the criterion would put e in the pole space before",
										By(reaches, outside, inPole, positiveOrder, later.At(j), criterion.At(e, j, previous)))
								}))
							successor := c.Have(
								"j is one more than j - 1",
								"(layer(e) - 1 - 1) + 1 = layer(e) - 1",
								ByArith(positiveOrder))
							c.Show(
								"so its order is exactly -j",
								ByArith(bounds, notBelow, bounded, successor))
						})
				}))
			layersApart := arg.Unfolded(distinctLayers, functions.InjectiveOnDef)
			distinct := arg.Have(
				"orders of basis vectors are distinct, as their layers are",
				"injective_on(E, «rpOrder»)",
				Unfold(functions.InjectiveOnDef),
				Derive(func(b *Argument) {
					u, v := b.FixAs[A]("x"), b.FixAs[A]("y")
					parts := b.Conjuncts(
						b.Assume(),
						"x lies in E",
						"y lies in E",
						"x and y have one order")
					casts := b.Have(
						"their orders agree, so the steps they enter after do, as integers",
						"int_of_num(layer(x) - 1) = int_of_num(layer(y) - 1)",
						ByArith(parts[0], parts[1], parts[2], orders.At(u), orders.At(v)))
					before := b.Have(
						"so as numbers",
						"layer(x) - 1 = layer(y) - 1",
						By(casts, int_embed.OfNumEq))
					same := b.Have(
						"and so do their layers, which are positive",
						"layer(x) = layer(y)",
						ByArith(parts[0], parts[1], entries.At(u), entries.At(v), before))
					b.Show(
						"and layers tell basis vectors apart",
						By(parts[0], parts[1], same, layersApart.At(u, v)))
				}))
			within := arg.Have(
				"so the orders of E lie between -a and 0",
				"∀x:A. x ∈ E ⇒ -a ≤ «rpOrder»(x) ∧ «rpOrder»(x) ≤ 0",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					member := b.Assume()
					b.Show(
						"the order is -j for some j ≤ a",
						ByArith(member, orders.At(x)))
				}))
			arg.Take(E)
			arg.Show(
				"E is the basis, its orders are distinct and between -a and 0",
				By(finiteE, arg.Simplified(isBasis, Fwd(record)), distinct, within))
		}),
})}

// PoleProductBudget — poles of order at most m times poles of order at most l are
// poles of order at most m + l, the product of the two spaces lying in the third.
var PoleProductBudget = poleProductBudgetThm{family.Add(registry.ProofEntry{
	Name: "PoleProductBudget",
	Key:  "prop_5b641838a137a1c1",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀m l:num. ∀u v:A.",
		Hypotheses: []string{
			"«rpCurve»",
			"«rpPoint»(P)",
			"u ∈ «rpPoles»(m).carrier",
			"v ∈ «rpPoles»(l).carrier",
		},
		Conclusion: "u * v ∈ «rpPoles»(m + l).carrier",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			m, l *Expr[Nat],
			u, v *Expr[A],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"the charts are a curve over the line",
				"P is a regular point",
				"u has poles of order at most m",
				"v has poles of order at most l")
			curve, point, inFirst, inSecond := given[0], given[1], given[2], given[3]
			budget := a.Have(
				"the product of the two spaces lies in the third",
				"set_mul(«rpPoles»(m).carrier, «rpPoles»(l).carrier) ⊆ «rpPoles»(m + l).carrier",
				By(curve, point, SinglePointPoleFiltration.Read(L).At(k, A0, A1, A01, t, P)))
			product := a.Have(
				"u * v is a product of a member of any set holding u and any set holding v",
				"∀X Y:set(A). u ∈ X ∧ v ∈ Y ⇒ u * v ∈ set_mul(X, Y)",
				By(quotient_group.InSetMul))
			inProduct := a.Have(
				"so it lies in the product of the two spaces",
				"u * v ∈ set_mul(«rpPoles»(m).carrier, «rpPoles»(l).carrier)",
				By(product, inFirst, inSecond))
			a.Show(
				"which lies in the third",
				By(inProduct, budget, set_basic.SubsetDef))
		}),
})}

// PolePowerBudget — the n-th power of a function with poles of order at most b has
// poles of order at most n * b: the empty power is the constant one, and one more
// factor adds b to the budget.
var PolePowerBudget = polePowerBudgetThm{family.Add(registry.ProofEntry{
	Name: "PolePowerBudget",
	Key:  "prop_33b3f852bca8c14d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀b n:num. ∀x:A.",
		Hypotheses: []string{
			"«rpCurve»",
			"«rpPoint»(P)",
			"x ∈ «rpPoles»(b).carrier",
		},
		Conclusion: "monoid_pow(L.mul, L.one, x, n) ∈ «rpPoles»(n * b).carrier",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			b, n *Expr[Nat],
			x *Expr[A],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"the charts are a curve over the line",
				"P is a regular point",
				"x has poles of order at most b")
			curve, point, member := given[0], given[1], given[2]
			a.Induct(n)
			a.Base(
				"the empty power is one, a constant",
				func(c *Argument) {
					constants := c.Have(
						"the zeroth pole space is k",
						"«rpPoles»(0).carrier = k",
						By(curve, point, SinglePointPoleFiltration.Read(L).At(k, A0, A1, A01, t, P)))
					oneIn := c.Have(
						"which holds one",
						"L.one ∈ «rpPoles»(0).carrier",
						By(
							Normalized,
							constants,
							c.Have(
								"k holds one",
								"L.one ∈ k",
								By(
									GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
									field.SubfieldOne.At(c.TermAs[FieldOps[A]]("L"), k)))))
					power := c.Have(
						"the empty power is one",
						"monoid_pow(L.mul, L.one, x, 0) = L.one",
						By(comm_monoid.MonoidPowDef))
					budget := c.Have(
						"and no copies of b are none",
						"0 * b = 0",
						ByArith())
					c.Show(
						"so the power lies in the zeroth pole space",
						power.Rw(),
						budget.Rw(),
						By(oneIn))
				})
			a.Step(
				"one more factor adds b to the budget",
				func(c *Argument, ih Fact) {
					budget := c.Have(
						"one more copy of b",
						"suc(n) * b = b + n * b",
						ByArith())
					power := c.Have(
						"one more factor of x",
						"monoid_pow(L.mul, L.one, x, suc(n)) = x * monoid_pow(L.mul, L.one, x, n)",
						By(comm_monoid.MonoidPowDef))
					c.Show(
						"x times the n-th power lies in the sum of their budgets",
						power.Rw(),
						budget.Rw(),
						By(
							curve,
							point,
							member,
							ih,
							At(
								PoleProductBudget.Read(L),
								k,
								A0,
								A1,
								A01,
								t,
								P,
								b,
								c.TermAs[Nat]("n * b"),
								x,
								c.TermAs[A]("monoid_pow(L.mul, L.one, x, n)"))))
				})
		}),
})}

// PoleBasisInField — a basis of a pole space lies in L, misses zero, and a
// combination of it with coefficients in k vanishes only when every coefficient
// does. The pole space is L's regular module restricted to the two charts of an
// invertible pair, so its operations are L's, and those charts lie in L; a basis
// holding zero would have a vanishing combination with coefficient one.
var PoleBasisInField = poleBasisInFieldThm{family.Add(registry.ProofEntry{
	Name: "PoleBasisInField",
	Key:  "prop_7a77ab56e90ebd70",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k A₀ A₁ A₀₁:set(A). " +
			"∀t:A. " +
			"∀P:prod(set(A), set(A)). " +
			"∀n:num. " +
			"∀B:set(A).",
		Hypotheses: []string{
			"«rpCurve»",
			"«rpPoint»(P)",
			"module_basis(«rpScalars», «rpPoles»(n), B)",
		},
		Conclusion: "B ⊆ L.carrier ∧ " +
			"L.zero ∉ B ∧ " +
			"(∀c:(A → A). " +
			"    finite(B) ∧ " +
			"    (∀y:A. y ∈ B ⇒ c(y) ∈ k) ∧ " +
			"    module_sum(L.add, L.zero, B, λy:A. c(y) * y) = L.zero ⇒ " +
			"    ∀y:A. y ∈ B ⇒ c(y) = L.zero)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			n *Expr[Nat],
			B *Expr[Set[A]],
			curve, point, basis Fact,
		) {
			ring := field.RingOn.Read(L)
			polePair := a.TermAs[_LatticePair]("«rpPolePair»(n)")
			invertible := a.Have(
				"the n-th pole pair is invertible",
				"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, «rpPolePair»(n))",
				By(curve, point, PolePairDegree.Read(L).At(k, A0, A1, A01, t, P, n)))
			charts := a.Have(
				"its charts lie in L",
				"fst(«rpPolePair»(n)) ⊆ L.carrier ∧ snd(«rpPolePair»(n)) ⊆ L.carrier",
				By(invertible, invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, polePair)))
			restricted := a.Simplified(basis, Fwd(SinglePointPoleSpaceDef), Fwd(lattice_pair.LatticePairH0Def))
			independent := a.Conjuncts(
				a.Unfolded(restricted, linear_independence.ModuleBasisDef),
				"the basis is independent",
				"the basis spans")[0]
			law := a.Conjuncts(
				a.Unfolded(independent, linear_independence.ModuleIndependentDef),
				"the basis lies in both charts",
				"a combination of a finite part of the basis vanishes only with its coefficients")
			oneIn := a.Have(
				"k holds one",
				"L.one ∈ k",
				By(
					curve,
					algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t),
					field.SubfieldOne.At(a.TermAs[FieldOps[A]]("L"), k)))
			zero := a.TermAs[A]("L.zero")
			single := a.TermAs[Set[A]]("{L.zero}")
			combination := a.Have(
				"the combination of the single point zero with coefficient one is zero",
				"module_sum(L.add, L.zero, {L.zero}, λx:A. L.one * x) = L.zero",
				By(
					module.ModuleSumSingleMonoid.Read(comm_ring.AddMonoidOn.Read(ring)).At(
						single, zero, a.TermAs[Fun[A, A]]("λx:A. L.one * x")),
					comm_ring.MulRightZeroOn.Read(ring),
					comm_ring.ZeroIn.Read(ring),
					comm_ring.OneIn.Read(ring),
					comm_ring.MulIn.Read(ring),
					set_order.SubsetRefl))
			noZero := a.Have(
				"zero is no point of the basis, its coefficient one being nonzero",
				"L.zero ∉ B",
				Derive(func(b *Argument) {
					member := b.SupposeNot()
					b.Show(
						"the vanishing combination at zero would make one zero",
						BySets(
							law[1].At(single, b.TermAs[Fun[A, A]]("λx:A. L.one"), zero),
							combination,
							oneIn,
							member,
							field.OneNotZeroOn.Read(L),
							finite_set.FiniteSing))
				}))
			inL := a.Have(
				"the basis lies in L, through the charts",
				"B ⊆ L.carrier",
				BySets(charts, law[0]))
			a.Show(
				"the law for the whole basis is the law for its finite part B",
				By(inL, noZero, law[1], set_order.SubsetRefl))
		}),
})}

// PolesHoldOne — one has poles of no order at P, so it lies in every pole space: it
// lies in both charts of the structure pair, the zeroth power, and the pole spaces
// increase.
var PolesHoldOne = polesHoldOneThm{family.Add(registry.ProofEntry{
	Name: "PolesHoldOne",
	Key:  "prop_dc1ccd36cd322074",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀n:num.",
		Hypotheses: []string{
			"«rpCurve»",
			"«rpPoint»(P)",
		},
		Conclusion: "L.one ∈ «rpPoles»(n).carrier",
		Abbrev: Abbrev{
			{Name: "sections", Text: "λn:num. fst(«rpPolePair»(n)) ∩ snd(«rpPolePair»(n))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			n *Expr[Nat],
			curve, point Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			charts := a.Have(
				"the charts are subrings of L",
				"subring(field_ring(L), A₀) ∧ subring(field_ring(L), A₁)",
				By(
					GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
					invertible_lattice_pair.ChartRingsInField.Read(L).At(A0, A1, A01, t)))
			zeroth := a.Have(
				"the zeroth power is the structure pair, holding one",
				"L.one ∈ «sections»(0)",
				Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				BySets(charts, comm_ring.SubringOne.At(ring, A0), comm_ring.SubringOne.At(ring, A1)))
			nested := a.Have(
				"the pole spaces increase, so the zeroth lies in the n-th",
				"«sections»(0) ⊆ «sections»(n)",
				ByArith(curve, point, PoleSpacesNested.Read(L).At(k, A0, A1, A01, t, P, a.TermAs[Nat]("0"), n)))
			a.Show(
				"so one lies in the n-th",
				Simp(Fwd(SinglePointPoleSpaceDef), Fwd(lattice_pair.LatticePairH0Def)),
				BySets(zeroth, nested))
		}),
})}
