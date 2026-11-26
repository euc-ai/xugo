// residue_points.go — points of a finite residue field in an algebraically
// closed host. A subalgebra S of M over a finite field k, and a maximal ideal m
// of S with S/m of dimension d over k: S/m has q^d elements, exactly d points
// of S in M have kernel m, and each has image the subfield of M with q^d
// elements. The argument embeds a finite extension into a closed field, reads
// off the image of a point, and lets the automorphisms of that subfield act on
// the points. A point in a subfield is a point in M with values there, so the
// points with kernel m in the subfield of q^n elements are none unless d
// divides n, and then d.

package residue_points

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// PointsInSubfield — a point of S in a subfield l is a point of S in M with
// values in l: the two maps differ only in the target they are read into.
var PointsInSubfield = pointsInSubfieldThm{family.Add(registry.ProofEntry{
	Name: "PointsInSubfield",
	Key:  "prop_979460040a3c2f33",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀k S l:set(A). ∀φ:(A → A).",
		Hypotheses: []string{"subfield(M, l)"},
		Conclusion: "(φ ∈ «pointsInL» ⇔ φ ∈ «pointsInM» ∧ image(φ, S) ⊆ l)",
		Abbrev: Abbrev{
			{Name: "source", Text: "restrict_ring(field_ring(M), S)"},
			{Name: "targetRing", Text: "restrict_ring(field_ring(M), l)"},
			{Name: "pointsInL", Text: "algebra_points(«source», «targetRing», k, λx:A. x)"},
			{Name: "pointsInM", Text: "algebra_points(«source», field_ring(M), k, λx:A. x)"},
		},
	},
		func(a *Argument, M field.FieldFact[on.M], k, S, l *Expr[Set[A]], φ *Arrow[A, A], subL Fact) {
			record := a.TermAs[FieldOps[A]]("M")
			ambient := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			source := a.TermAs[module_record.RingOps[A]]("«source»")
			target := a.TermAs[module_record.RingOps[A]]("«targetRing»")
			identity := a.TermAs[Fun[A, A]]("λx:A. x")
			a.Iff()
			a.Forward(
				"a point in l is a ring map into M with values in l",
				func(b *Argument, point Fact) {
					clauses := b.Conjuncts(
						b.Have(
							"φ is a ring map into l that fixes k and vanishes off S",
							"ring_homomorphism(«source», «targetRing», φ) ∧ "+
								"(∀x:A. x ∈ k ⇒ φ(x) = x) ∧ "+
								"(∀x:A. x ∉ S ⇒ φ(x) = M.zero)",
							By(point, algebra_points.AlgebraPointsMember.At(source, target, k, identity, φ))),
						"φ is a ring map into l",
						"it fixes k",
						"it vanishes off S")
					ringMap := clauses[0]
					values := b.Have(
						"its values lie in l",
						"image(φ, S) ⊆ l",
						By(ringMap, set_image.ImageSubsetIff, ring_homomorphism.MapIn.Read(ringMap)))
					intoM := b.Have(
						"and it is a ring map into M",
						"ring_homomorphism(«source», field_ring(M), φ)",
						By(
							ringMap,
							subL,
							field.RingOn.Read(M),
							ring_homomorphism.RingHomExtendTarget.At(source, ambient, φ, l),
							field.SubfieldSubset.At(record, l)))
					b.Show(
						"so it is a point in M",
						By(
							clauses[1],
							clauses[2],
							values,
							intoM,
							algebra_points.AlgebraPointsMember.At(source, ambient, k, identity, φ)))
				})
			a.Backward(
				"a point in M with values in l is a ring map into l",
				func(b *Argument, point Fact) {
					clauses := b.Have(
						"φ is a ring map into M that fixes k and vanishes off S",
						"ring_homomorphism(«source», field_ring(M), φ) ∧ "+
							"(∀x:A. x ∈ k ⇒ φ(x) = x) ∧ "+
							"(∀x:A. x ∉ S ⇒ φ(x) = M.zero)",
						By(point, algebra_points.AlgebraPointsMember.At(source, ambient, k, identity, φ)))
					intoL := b.Have(
						"its values lying in the subring l, it is a ring map into l",
						"ring_homomorphism(«source», «targetRing», φ)",
						By(
							point,
							subL,
							clauses,
							ring_homomorphism.RingHomCorestrict.At(source, ambient, φ, l),
							field.SubfieldSubring.Read(M),
							set_image.ImageSubsetIff))
					b.Show(
						"so it is a point in l",
						By(clauses, intoL, algebra_points.AlgebraPointsMember.At(source, target, k, identity, φ)))
				})
		}),
})}

// ConstantPointsWithKernel — the points of S in the subfield with q^n elements
// with kernel m, a maximal ideal of residue degree d over k: there are none
// unless d divides n, and then there are d. The points of S in M with kernel m
// number d and each has image the subfield with q^d elements, which lies in the
// subfield with q^n elements exactly when d divides n.
var ConstantPointsWithKernel = constantPointsWithKernelThm{family.Add(registry.ProofEntry{
	Name: "ConstantPointsWithKernel",
	Key:  "prop_cb0d07c6e451c38",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k S m:set(A). ∀n:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"finite(k)",
			"subring(field_ring(M), S)",
			"k ⊆ S",
			"maximal_ideal(«source», m)",
			"finite_dimensional(«scalars», «residues»)",
			"0 < n",
		},
		Conclusion: "(∀φ:A → A. φ ∈ «fibre» ⇒ «degree» ∣ n) ∧ («degree» ∣ n ⇒ has_size(«fibre», «degree»))",
		Abbrev: Abbrev{
			{Name: "source", Text: "restrict_ring(field_ring(M), S)"},
			{Name: "scalars", Text: "restrict_ring(field_ring(M), k)"},
			{Name: "residues", Text: "quotient_module(restrict_module(regular_module(field_ring(M)), S), m)"},
			{Name: "degree", Text: "module_dim(«scalars», «residues»)"},
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), n)"},
			{Name: "smaller", Text: "finite_constants(field_ring(M), card(k), «degree»)"},
			{Name: "points", Text: "algebra_points(«source», " +
				"    restrict_ring(field_ring(M), «constants»), " +
				"    k, " +
				"    λx:A. x)"},
			{Name: "pointsInM", Text: "algebra_points(«source», field_ring(M), k, λx:A. x)"},
			{Name: "fibre", Text: "{φ:A → A | φ ∈ «points» ∧ ring_kernel(M.zero, S, φ) = m}"},
			{Name: "fibreInM", Text: "{φ:A → A | φ ∈ «pointsInM» ∧ ring_kernel(M.zero, S, φ) = m}"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, S, m *Expr[Set[A]],
			n *Expr[Nat],
			closed, subK, finiteK, subS, kInS, maximal, finiteDimension, positive Fact,
		) {
			constants := a.TermAs[Set[A]]("«constants»")
			degree := a.TermAs[Nat]("«degree»")
			constantsField := a.Have(
				"the constants are a subfield of M",
				"subfield(M, «constants») ∧ k ⊆ «constants»",
				By(closed, subK, finiteK, positive, finite_field.FiniteConstantsSubfield.Read(M).At(k, n)))
			inM := a.Conjuncts(
				a.Have(
					"in M there are d points with kernel m, each with image the subfield with q^d points",
					"has_size(«fibreInM», «degree») ∧ "+
						"(∀φ:(A → A). φ ∈ «pointsInM» ∧ ring_kernel(M.zero, S, φ) = m ⇒ image(φ, S) = «smaller»)",
					By(
						M,
						closed,
						subK,
						finiteK,
						subS,
						kInS,
						maximal,
						finiteDimension,
						ResiduePoints.Read(M).At(k, S, m))),
				"there are d points in M",
				"each has image the subfield with q^d points")
			positiveDegree := a.Have(
				"d is positive",
				"0 < «degree»",
				By(M, subK, finiteK, subS, kInS, maximal, finiteDimension, ResidueSize.Read(M).At(k, S, m)))
			bridge := a.Have(
				"a point in the constants is a point in M with values there",
				"∀φ:(A → A). φ ∈ «points» ⇔ φ ∈ «pointsInM» ∧ image(φ, S) ⊆ «constants»",
				a.ForEach(func(φ *Expr[Fun[A, A]]) Action {
					return By(constantsField, PointsInSubfield.Read(M).At(k, S, constants, φ))
				}))
			contained := finite_field.FiniteConstantsContained.Read(M).At(k, degree, n)
			necessary := a.Have(
				"a point with kernel m puts the subfield with q^d points inside the constants, so d divides n",
				"∀φ:A → A. φ ∈ «fibre» ⇒ «degree» ∣ n",
				Derive(func(b *Argument) {
					φ := b.FixAs[Fun[A, A]]("φ")
					inFibre := b.Assume()
					inside := b.Have(
						"its image is that subfield, and its values lie in the constants",
						"«smaller» ⊆ «constants»",
						By(bridge.At(φ), inFibre, inM[1]))
					b.Show(
						"the subfields lie in each other exactly when d divides n",
						By(M, closed, subK, finiteK, positiveDegree, positive, inside, contained))
				}))
			sufficient := a.Have(
				"when d divides n all d points of M land in the constants",
				"«degree» ∣ n ⇒ has_size(«fibre», «degree»)",
				Derive(func(b *Argument) {
					divides := b.Assume()
					inside := b.Have(
						"the subfield with q^d points lies in the constants",
						"«smaller» ⊆ «constants»",
						By(M, closed, subK, finiteK, positiveDegree, positive, divides, contained))
					landing := b.Have(
						"so a point of M with kernel m has its values in the constants",
						"∀φ:(A → A). φ ∈ «pointsInM» ∧ ring_kernel(M.zero, S, φ) = m ⇒ image(φ, S) ⊆ «constants»",
						Derive(func(c *Argument) {
							φ := c.FixAs[Fun[A, A]]("φ")
							point := c.Assume()
							c.Show(
								"its image is the subfield with q^d points",
								By(inM[1].At(φ), point, inside))
						}))
					agree := b.Have(
						"a point lies in one fibre exactly when it lies in the other",
						"∀φ:(A → A). "+
							"    (φ ∈ «points» ∧ ring_kernel(M.zero, S, φ) = m) ⇔ "+
							"    (φ ∈ «pointsInM» ∧ ring_kernel(M.zero, S, φ) = m)",
						b.ForEach(func(φ *Expr[Fun[A, A]]) Action {
							return By(bridge.At(φ), landing.At(φ))
						}))
					same := b.Have(
						"so the fibres in the constants and in M are one set",
						"«fibre» = «fibreInM»",
						BySets(agree))
					b.Show(
						"and that set has d points",
						By(same, inM[0]))
				}))
			a.Show(
				"both clauses stand",
				By(necessary, sufficient))
		}),
})}

// ResidueModuleOn — over a subfield k of M inside a subring S, the quotient of
// S by an ideal is a k-module: S is M's ring restricted, and the regular
// module of that ring is M's regular module restricted to S.
var ResidueModuleOn = residueModuleOnThm{family.Add(registry.ProofEntry{
	Name: "ResidueModuleOn",
	Key:  "prop_f12f704fb92f1d90",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k S I:set(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subring(field_ring(M), S)",
			"k ⊆ S",
			"ring_ideal(«source», I)",
		},
		Conclusion: "module_on(restrict_ring(field_ring(M), k), " +
			"    quotient_module(restrict_module(regular_module(field_ring(M)), S), I))",
		Abbrev: Abbrev{
			{Name: "source", Text: "restrict_ring(field_ring(M), S)"},
		},
	}, func(a *Argument, M field.FieldFact[on.M], k, S, I *Expr[Set[A]], subK, subS, kInS, ideal Fact) {
		ambient := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		source := a.TermAs[module_record.RingOps[A]]("«source»")
		inv := a.TermAs[Fun[A, A]]("M.inv")
		rings := a.Have(
			"S is a commutative ring holding the field k",
			"comm_ring_on(«source») ∧ ring_subfield(«source», M.inv, k) ∧ k ⊆ «source».carrier",
			By(
				subK,
				subS,
				kInS,
				comm_ring.SubringRingOn.Read(field.RingOn.Read(M)).At(S),
				field.SubfieldRingSubfield.Read(M).At(k, S)))
		regular := a.Have(
			"M's regular module restricted to S is the regular module of S",
			"restrict_module(regular_module(field_ring(M)), S) = regular_module(«source»)",
			By(module_record.RegularModuleRestrict.At(ambient, S)))
		quotient := a.Have(
			"S modulo I is a module over k",
			"module_on(restrict_ring(«source», k), quotient_module(regular_module(«source»), I))",
			By(rings, ideal, module_dimension.IdealQuotientModuleOn.At(source, k, inv, I)))
		a.Show(
			"restricting S to k is restricting M to k",
			regular.Rw(),
			By(Normalized, quotient, module_record.RestrictRingTwice.At(ambient, S, k)))
	}),
})}

// PointKernelMaximal — a point of S in a finite subfield has maximal kernel
// with finite residues over k: the image is a finite domain, so the kernel is a
// prime of finite index, hence maximal, and S modulo it has finitely many
// elements.
var PointKernelMaximal = pointKernelMaximalThm{family.Add(registry.ProofEntry{
	Name: "PointKernelMaximal",
	Key:  "prop_9dfc92684cdca6e5",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k S l:set(A). ∀φ:(A → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, l)",
			"finite(l)",
			"subring(field_ring(M), S)",
			"k ⊆ S",
			"φ ∈ algebra_points(«source», restrict_ring(field_ring(M), l), k, λx:A. x)",
		},
		Conclusion: "maximal_ideal(«source», ring_kernel(M.zero, S, φ)) ∧ " +
			"finite_dimensional(restrict_ring(field_ring(M), k), «residues»)",
		Abbrev: Abbrev{
			{Name: "source", Text: "restrict_ring(field_ring(M), S)"},
			{Name: "residues", Text: "quotient_module(restrict_module(regular_module(field_ring(M)), S), " +
				"    ring_kernel(M.zero, S, φ))"},
			{Name: "quotient", Text: "ideal_quotient_ring(«source», ring_kernel(M.zero, S, φ))"},
			{Name: "classes", Text: "left_cosets(M.add, S, ring_kernel(M.zero, S, φ))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, S, l *Expr[Set[A]],
		φ *Arrow[A, A],
		subK, subL, finiteL, subS, kInS, point Fact,
	) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		ambient := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		source := a.TermAs[module_record.RingOps[A]]("«source»")
		target := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), l)")
		residuesRing := a.TermAs[module_record.RingOps[Set[A]]]("«quotient»")
		classes := a.TermAs[Set[Set[A]]]("«classes»")
		kernel := a.TermAs[Set[A]]("ring_kernel(M.zero, S, φ)")
		induced := a.TermAs[Fun[Set[A], A]]("induced_map(φ)")
		intoL := a.Have(
			"φ is a ring map into l",
			"ring_homomorphism(«source», restrict_ring(field_ring(M), l), φ)",
			By(
				point,
				algebra_points.AlgebraPointsMember.At(source, target, k, a.TermAs[Fun[A, A]]("λx:A. x"), φ)))
		intoM := a.Have(
			"and so into M",
			"ring_homomorphism(«source», field_ring(M), φ)",
			By(
				intoL,
				subL,
				field.RingOn.Read(M),
				ring_homomorphism.RingHomExtendTarget.At(source, ambient, φ, l),
				field.SubfieldSubset.At(fieldM, l)))
		quotient := a.Have(
			"S modulo the kernel is the image of φ",
			"ring_isomorphism(«quotient», restrict_ring(field_ring(M), image(φ, S)), induced_map(φ))",
			By(intoM, quotient_ring.KernelQuotientImage.At(source, ambient, φ)))
		bijection := a.Have(
			"so the classes are in bijection with the image",
			"injective_on(«classes», induced_map(φ)) ∧ image(induced_map(φ), «classes») = image(φ, S)",
			By(
				quotient,
				ring_homomorphism.RingIsomorphismDef.At(
					residuesRing,
					a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), image(φ, S))"),
					induced)))
		finiteImage := a.Have(
			"the image lies in the finite l",
			"finite(image(φ, S))",
			By(
				finiteL,
				intoL,
				finite_set.FiniteSubset,
				set_image.ImageSubsetIff,
				ring_homomorphism.MapIn.Read(intoL)))
		finiteClasses := a.Have(
			"so there are finitely many classes",
			"finite(«classes»)",
			By(bijection, finiteImage, finite_set.FiniteImageInjEq.At(induced, classes)))
		ideal := a.Have(
			"the kernel is an ideal",
			"ring_ideal(«source», ring_kernel(M.zero, S, φ))",
			By(ring_homomorphism.KernelIdeal.Read(intoM)))
		kernelPoints := a.Have(
			"the kernel is what φ sends to zero in S",
			"∀x:A. x ∈ ring_kernel(M.zero, S, φ) ⇔ x ∈ S ∧ φ(x) = M.zero",
			BySets(ring_homomorphism.RingKernelDef))
		proper := a.Have(
			"φ keeps one, so one is outside the kernel",
			"M.one ∉ ring_kernel(M.zero, S, φ)",
			By(M, kernelPoints, ring_homomorphism.MapOne.Read(intoM), field.OneNotZeroOn.Read(M)))
		products := a.Have(
			"a product falls in the kernel only through a factor, the values lying in a field",
			Statement{
				Binders:    "∀x y:A.",
				Hypotheses: []string{"x ∈ S", "y ∈ S", "M.mul(x, y) ∈ ring_kernel(M.zero, S, φ)"},
				Conclusion: "x ∈ ring_kernel(M.zero, S, φ) ∨ y ∈ ring_kernel(M.zero, S, φ)",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				members := b.Assume()
				values := b.Have(
					"φ(x) and φ(y) are elements of M with product zero",
					"φ(x) ∈ M.carrier ∧ φ(y) ∈ M.carrier ∧ M.mul(φ(x), φ(y)) = M.zero",
					By(
						kernelPoints,
						members,
						ring_homomorphism.MapMul.Read(intoM),
						ring_homomorphism.MapIn.Read(intoM)))
				b.Show(
					"a field has no zero divisors",
					By(M, kernelPoints, members, values, field.MulEqZeroOn.At(fieldM, φ.Apply(x), φ.Apply(y))))
			}))
		prime := a.Have(
			"the kernel is prime",
			"prime_ideal(«source», ring_kernel(M.zero, S, φ))",
			By(ideal, proper, products, ring_ideal.PrimeIdealDef.At(source, kernel)))
		maximal := a.Have(
			"a prime of finite index is maximal",
			"maximal_ideal(«source», ring_kernel(M.zero, S, φ))",
			By(
				prime,
				finiteClasses,
				ring_homomorphism.Source.Read(intoM),
				quotient_ring.FiniteIndexPrimeMaximal.At(source, kernel)))
		module := a.Have(
			"the residues are a module over k",
			"module_on(restrict_ring(field_ring(M), k), «residues»)",
			By(M, subK, subS, kInS, ideal, ResidueModuleOn.At(fieldM, k, S, kernel)))
		a.Show(
			"a finite module over a field is finite-dimensional",
			By(
				maximal,
				subK,
				module,
				finiteClasses,
				module_dimension.FiniteCarrierFiniteDimensional.At(
					a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), k)"),
					a.TermAs[module_record.ModuleOps[A, Set[A]]]("«residues»"),
					a.TermAs[Fun[A, A]]("M.inv")),
				field.SubfieldRingSubfield.Read(M).At(k, k)))
	}),
})}

// PointResidueField — a ring map φ from S into M, with S over a finite subfield
// k and S modulo the kernel finite-dimensional over k, has maximal kernel and a
// subfield of q^d elements as image, q = card(k) and d that dimension: the
// classes modulo the kernel are a k-space of dimension d, so q^d of them; the
// kernel is prime, the values lying in a field, and of finite index, hence
// maximal; and φ carries the field S modulo its kernel one-to-one onto its
// image.
var PointResidueField = pointResidueFieldThm{family.Add(registry.ProofEntry{
	Name: "PointResidueField",
	Key:  "prop_cdf7be2510e692b3",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k S:set(A). ∀φ:(A → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
			"subring(field_ring(M), S)",
			"k ⊆ S",
			"ring_homomorphism(«source», field_ring(M), φ)",
			"finite_dimensional(«scalars», «residues»)",
		},
		Conclusion: "maximal_ideal(«source», ring_kernel(M.zero, S, φ)) ∧ " +
			"subfield(M, image(φ, S)) ∧ " +
			"has_size(image(φ, S), card(k) ^ module_dim(«scalars», «residues»))",
		Abbrev: Abbrev{
			{Name: "source", Text: "restrict_ring(field_ring(M), S)"},
			{Name: "scalars", Text: "restrict_ring(field_ring(M), k)"},
			{Name: "residues", Text: "quotient_module(restrict_module(regular_module(field_ring(M)), S), " +
				"    ring_kernel(M.zero, S, φ))"},
			{Name: "quotient", Text: "ideal_quotient_ring(«source», ring_kernel(M.zero, S, φ))"},
			{Name: "residueField", Text: "ideal_quotient_field(«source», ring_kernel(M.zero, S, φ))"},
			{Name: "classes", Text: "left_cosets(M.add, S, ring_kernel(M.zero, S, φ))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, S *Expr[Set[A]],
		φ *Arrow[A, A],
		subK, finiteK, subS, kInS, point, finiteDimension Fact,
	) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		fieldK := a.TermAs[FieldOps[A]]("restrict_field(M, k)")
		ambient := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		source := a.TermAs[module_record.RingOps[A]]("«source»")
		quotient := a.TermAs[module_record.RingOps[Set[A]]]("«quotient»")
		residue := a.TermAs[FieldOps[Set[A]]]("«residueField»")
		onto := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), image(φ, S))")
		values := a.TermAs[Set[A]]("image(φ, S)")
		kernel := a.TermAs[Set[A]]("ring_kernel(M.zero, S, φ)")
		classes := a.TermAs[Set[Set[A]]]("«classes»")
		induced := a.TermAs[Fun[Set[A], A]]("induced_map(φ)")
		residues := a.TermAs[module_record.ModuleOps[A, Set[A]]]("«residues»")
		size := a.TermAs[Nat]("card(k) ^ module_dim(«scalars», «residues»)")
		ideal := a.Have(
			"the kernel is an ideal of S",
			"ring_ideal(«source», ring_kernel(M.zero, S, φ))",
			By(ring_homomorphism.KernelIdeal.Read(point)))
		module := a.Have(
			"the classes are a k-space",
			"module_on(«scalars», «residues»)",
			By(M, subK, subS, kInS, ideal, ResidueModuleOn.At(fieldM, k, S, kernel)))
		kField := a.Have(
			"k is a field under the operations of M",
			"field_on(restrict_field(M, k))",
			By(M, subK, field.SubfieldFieldOn.At(fieldM, k)))
		sized := a.Have(
			"a k-space of dimension d has q^d elements",
			"has_size(«classes», card(k) ^ module_dim(«scalars», «residues»))",
			By(
				kField,
				finiteK,
				module,
				finiteDimension,
				field.RestrictFieldRing.At(fieldM, k),
				finite_field.FiniteDimensionalSpaceSize.At(fieldK, residues),
				finite_field.FiniteFieldDef,
				finite_field.FieldSizeDef))
		kernelPoints := a.Have(
			"the kernel is what φ sends to zero in S",
			"∀x:A. x ∈ ring_kernel(M.zero, S, φ) ⇔ x ∈ S ∧ φ(x) = M.zero",
			BySets(ring_homomorphism.RingKernelDef))
		products := a.Have(
			"a product falls in the kernel only through a factor, the values lying in a field",
			Statement{
				Binders:    "∀x y:A.",
				Hypotheses: []string{"x ∈ S", "y ∈ S", "x * y ∈ ring_kernel(M.zero, S, φ)"},
				Conclusion: "x ∈ ring_kernel(M.zero, S, φ) ∨ y ∈ ring_kernel(M.zero, S, φ)",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				members := b.Assume()
				b.Show(
					"a field has no zero divisors",
					By(
						M,
						kernelPoints,
						members,
						ring_homomorphism.MapMul.Read(point),
						ring_homomorphism.MapIn.Read(point),
						field.MulEqZeroOn.At(fieldM, φ.Apply(x), φ.Apply(y))))
			}))
		maximal := a.Have(
			"a prime of finite index is maximal",
			"maximal_ideal(«source», ring_kernel(M.zero, S, φ))",
			By(
				ideal,
				products,
				a.Have(
					"φ keeps one, so one is outside the kernel",
					"M.one ∉ ring_kernel(M.zero, S, φ)",
					By(M, kernelPoints, ring_homomorphism.MapOne.Read(point), field.OneNotZeroOn.Read(M))),
				a.Have(
					"the classes are finitely many",
					"finite(«classes»)",
					By(sized, cardinality.HasSizeDef)),
				ring_ideal.PrimeIdealDef.At(source, kernel),
				ring_homomorphism.Source.Read(point),
				quotient_ring.FiniteIndexPrimeMaximal.At(source, kernel)))
		isomorphic := a.Have(
			"S modulo the kernel is the image of φ",
			"subring(field_ring(M), image(φ, S)) ∧ "+
				"ring_isomorphism(«quotient», restrict_ring(field_ring(M), image(φ, S)), induced_map(φ))",
			By(point, quotient_ring.KernelQuotientImage.At(source, ambient, φ)))
		bijection := a.Have(
			"the induced map is a ring bijection of the classes with the image",
			"injective_on(«classes», induced_map(φ)) ∧ "+
				"image(induced_map(φ), «classes») = image(φ, S) ∧ "+
				"ring_homomorphism(«quotient», restrict_ring(field_ring(M), image(φ, S)), induced_map(φ))",
			By(isomorphic, ring_homomorphism.RingIsomorphismDef.At(quotient, onto, induced)))
		residueField := a.Have(
			"S modulo the kernel is a field, and the induced map a map of fields into M",
			"field_on(«residueField») ∧ "+
				"ring_homomorphism(field_ring(«residueField»), field_ring(M), induced_map(φ))",
			By(
				maximal,
				ring_homomorphism.Source.Read(point),
				a.Have(
					"the induced map lands in M",
					"ring_homomorphism(«quotient», field_ring(M), induced_map(φ))",
					By(
						M,
						bijection,
						isomorphic,
						ring_homomorphism.RingHomExtendTarget.At(quotient, ambient, induced, values),
						field.RingOn.Read(M),
						comm_ring.SubringDef.At(ambient, values))),
				quotient_ring.QuotientFieldOn.At(source, kernel),
				quotient_ring.IdealQuotientFieldRing.At(source, kernel)))
		a.Show(
			"the kernel is maximal, and φ carries the q^d classes onto a subfield",
			By(
				maximal,
				bijection,
				sized,
				a.Have(
					"the image of a field under a map of fields is a subfield",
					"subfield(M, image(φ, S))",
					By(M, residueField, bijection, ring_homomorphism.ImageSubfield.At(residue, fieldM, induced))),
				cardinality.HasSizeImageInj.At(induced, classes, size)))
	}),
})}

// ResidueSize — S modulo a maximal ideal m, of dimension d over the finite
// field k, has q^d classes, and d is positive: the classes are a finite
// vector space over k, and they form a field, with at least two elements.
var ResidueSize = residueSizeThm{family.Add(registry.ProofEntry{
	Name: "ResidueSize",
	Key:  "prop_7fa0df307c2c91fb",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k S m:set(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
			"subring(field_ring(M), S)",
			"k ⊆ S",
			"maximal_ideal(«source», m)",
			"finite_dimensional(«scalars», «residues»)",
		},
		Conclusion: "0 < module_dim(«scalars», «residues») ∧ " +
			"has_size(left_cosets(M.add, S, m), card(k) ^ module_dim(«scalars», «residues»))",
		Abbrev: Abbrev{
			{Name: "source", Text: "restrict_ring(field_ring(M), S)"},
			{Name: "scalars", Text: "restrict_ring(field_ring(M), k)"},
			{Name: "residues", Text: "quotient_module(restrict_module(regular_module(field_ring(M)), S), m)"},
			{Name: "residueField", Text: "ideal_quotient_field(«source», m)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, S, m *Expr[Set[A]],
		subK, finiteK, subS, kInS, maximal, finiteDimension Fact,
	) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		fieldK := a.TermAs[FieldOps[A]]("restrict_field(M, k)")
		source := a.TermAs[module_record.RingOps[A]]("«source»")
		residues := a.TermAs[module_record.ModuleOps[A, Set[A]]]("«residues»")
		residueField := a.TermAs[FieldOps[Set[A]]]("«residueField»")
		ideal := a.Have(
			"m is an ideal of S",
			"ring_ideal(«source», m)",
			By(maximal, ring_ideal.MaximalIdealIdeal.At(source, m)))
		module := a.Have(
			"the classes are a k-module",
			"module_on(«scalars», «residues»)",
			By(M, subK, subS, kInS, ideal, ResidueModuleOn.At(fieldM, k, S, m)))
		kField := a.Have(
			"k is a field under the operations of M",
			"field_on(restrict_field(M, k))",
			By(M, subK, field.SubfieldFieldOn.At(fieldM, k)))
		size := a.Have(
			"a space of dimension d over k has q^d elements",
			"has_size(left_cosets(M.add, S, m), card(k) ^ module_dim(«scalars», «residues»))",
			By(
				kField,
				finiteK,
				module,
				finiteDimension,
				field.RestrictFieldRing.At(fieldM, k),
				finite_field.FiniteDimensionalSpaceSize.At(fieldK, residues),
				finite_field.FiniteFieldDef,
				finite_field.FieldSizeDef))
		counted := a.Have(
			"so the classes are finitely many, q^d of them",
			"finite(left_cosets(M.add, S, m)) ∧ "+
				"card(left_cosets(M.add, S, m)) = card(k) ^ module_dim(«scalars», «residues»)",
			By(size, cardinality.HasSizeDef))
		residuesField := a.Have(
			"the classes form a field",
			"field_on(«residueField»)",
			By(
				subS,
				comm_ring.SubringRingOn.Read(field.RingOn.Read(M)).At(S),
				maximal,
				quotient_ring.QuotientFieldOn.At(source, m)))
		two := a.Have(
			"a finite field has at least two elements",
			"2 ≤ card(left_cosets(M.add, S, m))",
			By(
				residuesField,
				counted,
				field.CarrierSubfield.At(residueField),
				finite_field.FiniteSubfieldAtLeastTwo.At(
					residueField, a.TermAs[Set[Set[A]]]("«residueField».carrier"))))
		positive := a.Have(
			"so d is not zero",
			"0 < module_dim(«scalars», «residues»)",
			Derive(func(b *Argument) {
				notPositive := b.SupposeNot()
				zero := b.Have(
					"the dimension would be zero",
					"module_dim(«scalars», «residues») = 0",
					ByArith(notPositive))
				b.Show(
					"q^0 is one, which is less than two",
					ByArith(zero, counted, two, nat_arith.NatPow))
			}))
		a.Show(
			"d is positive and the classes number q^d",
			By(positive, size))
	}),
})}

// PointTwist — an automorphism of the image of a point carries the point to a
// point with the same kernel: the composite is a ring map, it fixes k, and an
// injection fixing zero vanishes exactly where its argument does.
var PointTwist = pointTwistThm{family.Add(registry.ProofEntry{
	Name: "PointTwist",
	Key:  "prop_8600790e5393f8db",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k S E:set(A). ∀φ:(A → A). ∀p:permutation(A).",
		Hypotheses: []string{
			"subfield(M, E)",
			"φ ∈ «points»",
			"image(φ, S) = E",
			"p ∈ field_automorphisms(M, k, E)",
		},
		Conclusion: "(λx:A. permutation_map(p, φ(x))) ∈ «points» ∧ " +
			"ring_kernel(M.zero, S, λx:A. permutation_map(p, φ(x))) = ring_kernel(M.zero, S, φ)",
		Abbrev: Abbrev{
			{Name: "source", Text: "restrict_ring(field_ring(M), S)"},
			{Name: "points", Text: "algebra_points(«source», field_ring(M), k, λx:A. x)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, S, E *Expr[Set[A]],
		φ *Arrow[A, A],
		p *Expr[symmetric_group.Permutation[A]],
		subE, point, imageE, automorphism Fact,
	) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		fieldE := a.TermAs[FieldOps[A]]("restrict_field(M, E)")
		ambient := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		ringE := a.TermAs[module_record.RingOps[A]]("field_ring(restrict_field(M, E))")
		source := a.TermAs[module_record.RingOps[A]]("«source»")
		identity := a.TermAs[Fun[A, A]]("λx:A. x")
		permutation := a.TermAs[Fun[A, A]]("permutation_map(p)")
		twisted := a.TermAs[Fun[A, A]]("λx:A. permutation_map(p, φ(x))")
		data := a.Have(
			"φ is a ring map fixing k and vanishing off S",
			"ring_homomorphism(«source», field_ring(M), φ) ∧ "+
				"(∀c:A. c ∈ k ⇒ φ(c) = c) ∧ "+
				"(∀x:A. x ∉ S ⇒ φ(x) = M.zero)",
			By(point, algebra_points.AlgebraPointsMember.At(source, ambient, k, identity, φ)))
		eField := a.Have(
			"E is a field and p a ring map of it",
			"field_on(restrict_field(M, E)) ∧ "+
				"ring_homomorphism(field_ring(restrict_field(M, E)), "+
				"    field_ring(restrict_field(M, E)), "+
				"    permutation_map(p))",
			By(
				M,
				subE,
				automorphism,
				field.SubfieldFieldOn.At(fieldM, E),
				field_automorphism.AutomorphismRingHomomorphism.At(fieldM, k, E, p)))
		injective := a.Have(
			"p is injective on E and fixes zero",
			"injective_on(E, permutation_map(p)) ∧ permutation_map(p, M.zero) = M.zero",
			By(
				M,
				subE,
				automorphism,
				eField,
				ring_homomorphism.FieldHomomorphismInjective.At(fieldE, fieldE, permutation),
				field_automorphism.AutomorphismFixesUnits.At(fieldM, k, E, p)))
		into := a.Have(
			"φ maps S into E",
			"∀x:A. x ∈ S ⇒ φ(x) ∈ E",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inS := b.Assume()
				b.Show(
					"φ(x) is a value of φ",
					By(Normalized, inS, imageE, set_image.FunInImage.At(φ, S, x)))
			}))
		corestricted := a.Have(
			"so φ is a ring map into E",
			"ring_homomorphism(«source», field_ring(restrict_field(M, E)), φ)",
			By(
				M,
				subE,
				data,
				into,
				ring_homomorphism.RingHomCorestrict.At(source, ambient, φ, E),
				field.SubfieldSubring.At(fieldM, E),
				field.RestrictFieldRing.At(fieldM, E)))
		composite := a.Have(
			"the composite is a ring map into E",
			"ring_homomorphism(«source», field_ring(restrict_field(M, E)), λx:A. permutation_map(p, φ(x)))",
			By(corestricted, eField, ring_homomorphism.RingHomCompose.At(source, ringE, ringE, φ, permutation)))
		intoM := a.Have(
			"and so into M",
			"ring_homomorphism(«source», field_ring(M), λx:A. permutation_map(p, φ(x)))",
			By(
				M,
				subE,
				composite,
				field.RingOn.At(fieldM),
				ring_homomorphism.RingHomExtendTarget.At(source, ambient, twisted, E),
				field.RestrictFieldRing.At(fieldM, E),
				field.SubfieldSubset.At(fieldM, E)))
		fixesK := a.Have(
			"p fixes k",
			"∀c:A. c ∈ k ⇒ permutation_map(p, c) = c",
			BySets(automorphism, field_automorphism.FieldAutomorphismsDef.At(fieldM, k, E)))
		member := a.Have(
			"the composite is a point",
			"(λx:A. permutation_map(p, φ(x))) ∈ «points»",
			By(
				Normalized,
				fixesK,
				intoM,
				data,
				injective,
				algebra_points.AlgebraPointsMember.At(source, ambient, k, identity, twisted)))
		zeros := a.Have(
			"p sends a value to zero exactly when the value is zero",
			"∀x:A. x ∈ S ⇒ (permutation_map(p, φ(x)) = M.zero ⇔ φ(x) = M.zero)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				inS := b.Assume()
				values := b.Have(
					"φ(x) and zero lie in E",
					"φ(x) ∈ E ∧ M.zero ∈ E",
					By(M, into, inS, subE, field.SubfieldZero.At(fieldM, E)))
				b.Iff()
				b.Forward(
					"p is injective on E",
					func(c *Argument, vanishes Fact) {
						c.Show(
							"φ(x) and zero have one value under p",
							By(injective, values, vanishes, functions.InjectiveOnDef.At(E, permutation)))
					})
				b.Backward(
					"p fixes zero",
					func(c *Argument, vanishes Fact) {
						c.Show(
							"the value is zero",
							By(Normalized, vanishes, injective))
					})
			}))
		kernel := a.Have(
			"so the kernels agree",
			"ring_kernel(M.zero, S, λx:A. permutation_map(p, φ(x))) = ring_kernel(M.zero, S, φ)",
			Simp(Fwd(ring_homomorphism.RingKernelDef)),
			BySets(zeros))
		a.Show(
			"the composite is a point with the kernel of φ",
			By(member, kernel))
	}),
})}

// ResiduePointExists — a maximal ideal m of finite residue dimension over the
// finite field k is the kernel of a point of S in the closed field M: S/m is a
// finite field holding a copy of k; the inverse of k → S/m extends along S/m
// into M; and the composite with the projection, cut off outside S, is a point
// that kills exactly m.
var ResiduePointExists = residuePointExistsThm{family.Add(registry.ProofEntry{
	Name: "ResiduePointExists",
	Key:  "prop_efd89e58a0d051f0",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k S m:set(A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"finite(k)",
			"subring(field_ring(M), S)",
			"k ⊆ S",
			"maximal_ideal(«source», m)",
			"finite_dimensional(«scalars», «residues»)",
		},
		Conclusion: "∃φ:(A → A). φ ∈ «points» ∧ ring_kernel(M.zero, S, φ) = m",
		Abbrev: Abbrev{
			{Name: "source", Text: "restrict_ring(field_ring(M), S)"},
			{Name: "scalars", Text: "restrict_ring(field_ring(M), k)"},
			{Name: "residues", Text: "quotient_module(restrict_module(regular_module(field_ring(M)), S), m)"},
			{Name: "degree", Text: "module_dim(«scalars», «residues»)"},
			{Name: "points", Text: "algebra_points(«source», field_ring(M), k, λx:A. x)"},
			{Name: "quotient", Text: "ideal_quotient_ring(«source», m)"},
			{Name: "residueField", Text: "ideal_quotient_field(«source», m)"},
			{Name: "projection", Text: "ideal_quotient_projection(«source», m)"},
			{Name: "base", Text: "image(«projection», k)"},
			{Name: "baseRing", Text: "restrict_ring(field_ring(«residueField»), «base»)"},
			{Name: "adjoined", Text: "field_adjoin(«residueField», «base», «residueField».carrier)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, S, m *Expr[Set[A]],
		closed, subK, finiteK, subS, kInS, maximal, finiteDimension Fact,
	) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		fieldK := a.TermAs[FieldOps[A]]("restrict_field(M, k)")
		ambient := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		source := a.TermAs[module_record.RingOps[A]]("«source»")
		ringK := a.TermAs[module_record.RingOps[A]]("field_ring(restrict_field(M, k))")
		quotient := a.TermAs[module_record.RingOps[Set[A]]]("«quotient»")
		residue := a.TermAs[FieldOps[Set[A]]]("«residueField»")
		ringResidue := a.TermAs[module_record.RingOps[Set[A]]]("field_ring(«residueField»)")
		baseRing := a.TermAs[module_record.RingOps[Set[A]]]("«baseRing»")
		projection := a.TermAs[Fun[A, Set[A]]]("«projection»")
		base := a.TermAs[Set[Set[A]]]("«base»")
		carrier := a.TermAs[Set[Set[A]]]("«residueField».carrier")
		adjoined := a.TermAs[Set[Set[A]]]("«adjoined»")
		inverse := a.TermAs[Fun[Set[A], A]]("inverse_on(k, «projection»)")
		sourceRing := a.Have(
			"S is a commutative ring",
			"comm_ring_on(«source»)",
			By(subS, comm_ring.SubringRingOn.Read(field.RingOn.Read(M)).At(S)))
		ideal := a.Have(
			"m is an ideal of S",
			"ring_ideal(«source», m)",
			By(maximal, ring_ideal.MaximalIdealIdeal.At(source, m)))
		kField := a.Have(
			"k is a field under the operations of M",
			"field_on(restrict_field(M, k))",
			By(M, subK, field.SubfieldFieldOn.At(fieldM, k)))
		residueField := a.Have(
			"S/m is a field",
			"field_on(«residueField»)",
			By(sourceRing, maximal, quotient_ring.QuotientFieldOn.At(source, m)))
		projects := a.Have(
			"the projection is a ring map",
			"ring_homomorphism(«source», «quotient», «projection»)",
			By(sourceRing, ideal, quotient_ring.ProjectionHomomorphism.At(source, m)))
		kInSource := a.Have(
			"k is a subring of S",
			"subring(«source», k)",
			By(
				Normalized,
				M,
				subK,
				kInS,
				sourceRing,
				comm_ring.SubringRingOn.At(source, k),
				module_record.RestrictRingTwice.At(ambient, S, k),
				comm_ring.SubringRingOn.At(ambient, k),
				field.SubfieldSubring.At(fieldM, k),
				field.RingOn.At(fieldM)))
		onK := a.Have(
			"the projection restricts to a map of fields from k to S/m",
			"ring_homomorphism(field_ring(restrict_field(M, k)), field_ring(«residueField»), «projection»)",
			Derive(func(b *Argument) {
				restricted := b.Have(
					"the projection restricts to k",
					"ring_homomorphism(restrict_ring(«source», k), «quotient», «projection»)",
					By(
						projects,
						kInSource,
						ring_homomorphism.RingHomRestrictSource.At(source, quotient, projection, k)))
				b.Show(
					"read in the field records",
					By(
						Normalized,
						restricted,
						module_record.RestrictRingTwice.At(ambient, S, k),
						field.RestrictFieldRing.At(fieldM, k),
						quotient_ring.IdealQuotientFieldRing.At(source, m)))
			}))
		copyOfK := a.Have(
			"so the classes of k are a subfield, and k injects",
			"subfield(«residueField», «base») ∧ injective_on(k, «projection»)",
			By(
				kField,
				residueField,
				onK,
				ring_homomorphism.ImageSubfield.At(fieldK, residue, projection),
				ring_homomorphism.FieldHomomorphismInjective.At(fieldK, residue, projection)))
		baseRings := a.Have(
			"the rings of k and of its copy are commutative",
			"subring(field_ring(«residueField»), «base») ∧ "+
				"comm_ring_on(«baseRing») ∧ "+
				"comm_ring_on(field_ring(restrict_field(M, k)))",
			By(
				residueField,
				kField,
				copyOfK,
				field.SubfieldSubring.At(residue, base),
				comm_ring.SubringRingOn.At(ringResidue, base),
				field.RingOn.At(residue),
				field.RingOn.At(fieldK)))
		toCopy := a.Have(
			"the projection maps k onto its copy",
			"ring_isomorphism(field_ring(restrict_field(M, k)), «baseRing», «projection»)",
			Derive(func(b *Argument) {
				corestricted := b.Have(
					"the projection takes k into its copy",
					"ring_homomorphism(field_ring(restrict_field(M, k)), «baseRing», «projection»)",
					By(
						onK,
						baseRings,
						ring_homomorphism.RingHomCorestrict.At(ringK, ringResidue, projection, base),
						At(set_image.FunInImage, projection, k)))
				b.Show(
					"it is injective, with image the copy",
					By(corestricted, copyOfK, ring_homomorphism.RingIsomorphismDef.At(ringK, baseRing, projection)))
			}))
		baseMap := a.Have(
			"so the copy of k maps back into M",
			"ring_homomorphism(«baseRing», field_ring(M), inverse_on(k, «projection»))",
			Derive(func(b *Argument) {
				back := b.Have(
					"the inverse is an isomorphism back to k",
					"ring_isomorphism(«baseRing», field_ring(restrict_field(M, k)), inverse_on(k, «projection»))",
					By(toCopy, ring_homomorphism.IsomorphismInverse.At(ringK, baseRing, projection)))
				intoK := b.Have(
					"so it is a ring map into k",
					"ring_homomorphism(«baseRing», restrict_ring(field_ring(M), k), inverse_on(k, «projection»))",
					By(
						back,
						ring_homomorphism.RingIsomorphismDef.At(baseRing, ringK, inverse),
						field.RestrictFieldRing.At(fieldM, k)))
				b.Show(
					"and k lies in M",
					By(
						M,
						subK,
						intoK,
						ring_homomorphism.RingHomExtendTarget.At(baseRing, ambient, inverse, k),
						field.RingOn.At(fieldM),
						field.SubfieldSubset.At(fieldM, k)))
			}))
		finiteResidue := a.Have(
			"S/m has finitely many elements",
			"finite(«residueField».carrier)",
			Derive(func(b *Argument) {
				size := b.Have(
					"it has q^d of them",
					"0 < «degree» ∧ has_size(left_cosets(M.add, S, m), card(k) ^ «degree»)",
					By(M, subK, finiteK, subS, kInS, maximal, finiteDimension, ResidueSize.At(fieldM, k, S, m)))
				b.Show(
					"a set of a given size is finite",
					By(size, cardinality.HasSizeDef))
			}))
		whole := a.Have(
			"S/m is a subfield of itself, holding the copy of k",
			"subfield(«residueField», «residueField».carrier) ∧ «base» ⊆ «residueField».carrier",
			By(
				residueField,
				copyOfK,
				field.CarrierSubfield.At(residue),
				field.SubfieldSubset.At(residue, base)))
		finiteOver := a.Have(
			"so S/m is finite over the copy of k",
			"finite_extension(«residueField», «base», «residueField».carrier)",
			By(
				residueField,
				copyOfK,
				finiteResidue,
				whole,
				finite_field.FiniteSubfieldSize.At(residue, base, carrier)))
		algebraic := a.Have(
			"and every class is algebraic over the copy",
			"∀x:set(A). x ∈ «residueField».carrier ⇒ algebraic_over(«residueField», «base», x)",
			Derive(func(b *Argument) {
				x := b.FixAs[Set[A]]("x")
				member := b.Assume()
				b.Show(
					"an element of a finite extension is algebraic",
					By(
						residueField,
						copyOfK,
						whole,
						finiteOver,
						member,
						algebraic_element.FiniteExtensionAlgebraic.At(residue, base, carrier, x)))
			}))
		generated := a.Have(
			"S/m is generated by all its classes",
			"«adjoined» = «residueField».carrier",
			Derive(func(b *Argument) {
				bounds := b.Have(
					"the adjunction is a subfield holding every class",
					"subfield(«residueField», «adjoined») ∧ «base» ⊆ «adjoined» ∧ «residueField».carrier ⊆ «adjoined»",
					By(
						residueField,
						whole,
						algebraic_element.AdjoinSubfield.At(residue, base, carrier),
						set_order.SubsetRefl))
				b.Show(
					"and a subfield lies in the carrier",
					By(
						bounds,
						field.SubfieldSubset.At(residue, adjoined),
						set_order.SubsetAntisym.At(adjoined, carrier)))
			}))
		g, extension := a.ObtainAs[Fun[Set[A], A]](
			"the map back from the copy of k extends to all of S/m",
			"∃g:(set(A) → A). "+
				"    ring_homomorphism(field_ring(«residueField»), field_ring(M), g) ∧ "+
				"    (∀x:set(A). x ∈ «base» ⇒ g(x) = inverse_on(k, «projection», x))",
			Derive(func(b *Argument) {
				h, extended := b.ObtainAs[Fun[Set[A], A]](
					"adjoin the classes one at a time",
					"∃h:(set(A) → A). "+
						"    ring_homomorphism(restrict_ring(field_ring(«residueField»), «adjoined»), "+
						"        field_ring(M), "+
						"        h) ∧ "+
						"    (∀x:set(A). x ∈ «base» ⇒ h(x) = inverse_on(k, «projection», x))",
					By(
						M,
						closed,
						residueField,
						copyOfK,
						finiteResidue,
						algebraic,
						baseMap,
						algebraic_closure.FiniteAdjoinEmbedding.At(residue, fieldM, base, carrier, inverse),
						set_order.SubsetRefl))
				everything := b.Have(
					"the adjunction is the whole ring of S/m",
					"restrict_ring(field_ring(«residueField»), «adjoined») = field_ring(«residueField»)",
					generated.Rw(),
					By(module_record.RestrictRingCarrier.At(ringResidue)))
				b.Take(h)
				b.Show(
					"h is the extension",
					By(everything, extended))
			}))
		onQuotient := a.Have(
			"g is a ring map on S/m",
			"ring_homomorphism(«quotient», field_ring(M), g)",
			By(extension, quotient_ring.IdealQuotientFieldRing.At(source, m)))
		composite := a.Have(
			"g after the projection is a ring map",
			"ring_homomorphism(«source», field_ring(M), λx:A. g(«projection»(x)))",
			By(
				projects,
				onQuotient,
				ring_homomorphism.RingHomCompose.At(source, quotient, ambient, projection, g)))
		fixesK := a.Have(
			"it fixes k, g inverting the projection there",
			"∀c:A. c ∈ k ⇒ g(«projection»(c)) = c",
			Derive(func(b *Argument) {
				c := b.FixAs[A]("c")
				inK := b.Assume()
				b.Show(
					"the class of c lies in the copy of k",
					By(
						inK,
						extension,
						copyOfK,
						set_image.FunInImage.At(projection, k, c),
						functions.InverseOnLeft.At(k, projection, c)))
			}))
		kills := a.Have(
			"it kills exactly m in S",
			"∀x:A. x ∈ S ⇒ (g(«projection»(x)) = M.zero ⇔ x ∈ m)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inS := b.Assume()
				class := b.TermAs[Set[A]]("«projection»(x)")
				member := b.Have(
					"the class of x and m are classes, and g sends m to zero",
					"«projection»(x) ∈ left_cosets(M.add, S, m) ∧ m ∈ left_cosets(M.add, S, m) ∧ g(m) = M.zero",
					By(
						inS,
						projects,
						onQuotient,
						ring_homomorphism.MapIn.Read(projects),
						ring_homomorphism.MapZero.Read(projects),
						ring_homomorphism.MapZero.Read(onQuotient),
						comm_ring.ZeroIn.Read(ring_homomorphism.Source.Read(onQuotient))))
				zeroClass := b.Have(
					"the class of x is m exactly when x lies in m",
					"(«projection»(x) = m ⇔ x ∈ m)",
					By(
						Normalized,
						sourceRing,
						ideal,
						inS,
						quotient_ring.CosetEqIdealIff.At(source, m, x),
						quotient_ring.IdealQuotientProjectionDef.At(source, m, x)))
				injective := b.Have(
					"g is injective on the classes",
					"injective_on(left_cosets(M.add, S, m), g)",
					By(M, residueField, extension, ring_homomorphism.FieldHomomorphismInjective.At(residue, fieldM, g)))
				opened := b.Unfolded(injective, functions.InjectiveOnDef)
				b.Iff()
				b.Forward(
					"a class g sends to zero is the class m",
					func(c *Argument, vanishes Fact) {
						classIsM := c.Have(
							"g is injective on the classes",
							"«projection»(x) = m",
							By(opened.At(class, m), member, vanishes))
						c.Show(
							"so x lies in m",
							By(zeroClass, classIsM))
					})
				b.Backward(
					"an element of m has class m, which g sends to zero",
					func(c *Argument, inM Fact) {
						classIsM := c.Have(
							"its class is m",
							"«projection»(x) = m",
							By(zeroClass, inM))
						c.Show(
							"and g sends m to zero",
							By(Normalized, classIsM, member))
					})
			}))
		ψ, ψDef := a.LetAs[Fun[A, A]]("ψ", "λx:A. COND(x ∈ S, g(«projection»(x)), M.zero)")
		values := a.Have(
			"ψ is g after the projection on S, and zero off S",
			"∀x:A. (x ∈ S ⇒ ψ(x) = g(«projection»(x))) ∧ (x ∉ S ⇒ ψ(x) = M.zero)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				b.Show(
					"the definition of ψ",
					By(Normalized, ψDef))
			}))
		pointMap := a.Have(
			"ψ is a ring map",
			"ring_homomorphism(«source», field_ring(M), ψ)",
			By(
				composite,
				values,
				ring_homomorphism.RingHomCongruence.At(
					source, ambient, a.TermAs[Fun[A, A]]("λx:A. g(«projection»(x))"), ψ)))
		fixes := a.Have(
			"ψ fixes k",
			"∀c:A. c ∈ k ⇒ ψ(c) = c",
			BySets(kInS, values, fixesK))
		member := a.Have(
			"ψ is a point",
			"ψ ∈ «points»",
			By(
				pointMap,
				values,
				fixes,
				algebra_points.AlgebraPointsMember.At(source, ambient, k, a.TermAs[Fun[A, A]]("λx:A. x"), ψ)))
		inS := a.Have(
			"m lies in S",
			"m ⊆ S",
			By(Normalized, ideal, ring_ideal.IdealSubset))
		kernel := a.Have(
			"the kernel of ψ is m",
			"ring_kernel(M.zero, S, ψ) = m",
			BySets(values, kills, inS, ring_homomorphism.RingKernelDef))
		a.Take(ψ)
		a.Show(
			"ψ is the point",
			By(member, kernel))
	}),
})}

// ResiduePointImage — a point with kernel m has image the subfield of M with
// q^d elements: S/m makes the image a subfield of q^d elements, each fixed by the
// q^d-th power, and the fixed points number the same.
var ResiduePointImage = residuePointImageThm{family.Add(registry.ProofEntry{
	Name: "ResiduePointImage",
	Key:  "prop_34247d1fc9eca861",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k S m:set(A). ∀φ:(A → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"finite(k)",
			"subring(field_ring(M), S)",
			"k ⊆ S",
			"maximal_ideal(«source», m)",
			"finite_dimensional(«scalars», «residues»)",
			"φ ∈ «points»",
			"ring_kernel(M.zero, S, φ) = m",
		},
		Conclusion: "image(φ, S) = finite_constants(field_ring(M), card(k), «degree»)",
		Abbrev: Abbrev{
			{Name: "source", Text: "restrict_ring(field_ring(M), S)"},
			{Name: "scalars", Text: "restrict_ring(field_ring(M), k)"},
			{Name: "residues", Text: "quotient_module(restrict_module(regular_module(field_ring(M)), S), m)"},
			{Name: "degree", Text: "module_dim(«scalars», «residues»)"},
			{Name: "points", Text: "algebra_points(«source», field_ring(M), k, λx:A. x)"},
			{Name: "quotient", Text: "ideal_quotient_ring(«source», m)"},
			{Name: "residueField", Text: "ideal_quotient_field(«source», m)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, S, m *Expr[Set[A]],
		φ *Arrow[A, A],
		closed, subK, finiteK, subS, kInS, maximal, finiteDimension, point, kernel Fact,
	) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		ambient := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		source := a.TermAs[module_record.RingOps[A]]("«source»")
		quotient := a.TermAs[module_record.RingOps[Set[A]]]("«quotient»")
		residue := a.TermAs[FieldOps[Set[A]]]("«residueField»")
		onto := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), image(φ, S))")
		values := a.TermAs[Set[A]]("image(φ, S)")
		classes := a.TermAs[Set[Set[A]]]("left_cosets(M.add, S, m)")
		induced := a.TermAs[Fun[Set[A], A]]("induced_map(φ)")
		degree := a.TermAs[Nat]("«degree»")
		size := a.TermAs[Nat]("card(k) ^ «degree»")
		hom := a.Have(
			"φ is a ring map",
			"ring_homomorphism(«source», field_ring(M), φ)",
			By(
				point,
				algebra_points.AlgebraPointsMember.At(source, ambient, k, a.TermAs[Fun[A, A]]("λx:A. x"), φ)))
		isomorphic := a.Have(
			"S/m is the image of φ",
			"subring(field_ring(M), image(φ, S)) ∧ "+
				"ring_isomorphism(«quotient», restrict_ring(field_ring(M), image(φ, S)), induced_map(φ))",
			By(Normalized, kernel, hom, quotient_ring.KernelQuotientImage.At(source, ambient, φ)))
		bijection := a.Have(
			"the induced map is a ring bijection of the classes with the image",
			"injective_on(left_cosets(M.add, S, m), induced_map(φ)) ∧ "+
				"image(induced_map(φ), left_cosets(M.add, S, m)) = image(φ, S) ∧ "+
				"ring_homomorphism(«quotient», restrict_ring(field_ring(M), image(φ, S)), induced_map(φ))",
			By(isomorphic, ring_homomorphism.RingIsomorphismDef.At(quotient, onto, induced)))
		intoM := a.Have(
			"so it is a ring map into M",
			"ring_homomorphism(«quotient», field_ring(M), induced_map(φ))",
			By(
				M,
				bijection,
				isomorphic,
				ring_homomorphism.RingHomExtendTarget.At(quotient, ambient, induced, values),
				field.RingOn.At(fieldM),
				comm_ring.SubringDef.At(ambient, values)))
		residueField := a.Have(
			"S/m is a field, and the induced map a map of fields",
			"field_on(«residueField») ∧ "+
				"ring_homomorphism(field_ring(«residueField»), field_ring(M), induced_map(φ))",
			By(
				Normalized,
				subS,
				comm_ring.SubringRingOn.Read(field.RingOn.Read(M)).At(S),
				maximal,
				intoM,
				quotient_ring.QuotientFieldOn.At(source, m),
				quotient_ring.IdealQuotientFieldRing.At(source, m)))
		inducedImage := a.Have(
			"so its image is a subfield",
			"subfield(M, image(induced_map(φ), left_cosets(M.add, S, m)))",
			By(M, residueField, ring_homomorphism.ImageSubfield.At(residue, fieldM, induced)))
		subfieldImage := a.Have(
			"and that image is the image of φ",
			"subfield(M, image(φ, S))",
			By(inducedImage, bijection))
		sized := a.Have(
			"S/m has q^d classes, d positive",
			"0 < «degree» ∧ has_size(left_cosets(M.add, S, m), card(k) ^ «degree»)",
			By(
				M,
				subK,
				finiteK,
				subS,
				kInS,
				maximal,
				finiteDimension,
				ResidueSize.At(a.TermAs[FieldOps[A]]("M"), k, S, m)))
		sizedImage := a.Have(
			"so the image of φ has q^d elements",
			"has_size(image(φ, S), card(k) ^ «degree»)",
			By(bijection, sized, cardinality.HasSizeImageInj.At(induced, classes, size)))
		constants := a.Have(
			"as has the subfield of the q^d-th power's fixed points",
			"subfield(M, finite_constants(field_ring(M), card(k), «degree»)) ∧ "+
				"has_size(finite_constants(field_ring(M), card(k), «degree»), card(k) ^ «degree»)",
			By(M, closed, subK, finiteK, sized, finite_field.FiniteConstantsSubfield.At(fieldM, k, degree)))
		imageField := a.Have(
			"the image is a field under the operations of M",
			"field_on(restrict_field(M, image(φ, S)))",
			By(M, subfieldImage, field.SubfieldFieldOn.At(fieldM, values)))
		inside := a.Have(
			"every element of the image is fixed by the q^d-th power",
			"image(φ, S) ⊆ finite_constants(field_ring(M), card(k), «degree»)",
			Derive(func(b *Argument) {
				b.Do(Simp(Fwd(finite_field.FiniteConstantsDef), Fwd(set_basic.SubsetDef)))
				x := b.FixAs[A]("x")
				member := b.Assume()
				fixed := b.Have(
					"a finite field is fixed by the power of its size",
					"monoid_pow(M.mul, M.one, x, card(image(φ, S))) = x",
					By(
						imageField,
						member,
						sizedImage,
						finite_field.FiniteFieldFixedByFrobenius.At(
							a.TermAs[FieldOps[A]]("restrict_field(M, image(φ, S))"), x),
						cardinality.HasSizeDef.At(values, size)))
				inM := b.Have(
					"the element lies in M",
					"x ∈ M.carrier",
					BySets(subfieldImage, member, field.SubfieldSubset.At(fieldM, values)))
				power := b.Have(
					"and that power is the q^d-th",
					"monoid_pow(M.mul, M.one, x, card(k) ^ «degree») = x",
					By(fixed, sizedImage, cardinality.CardOfSized.At(values, size)))
				b.Show(
					"so it is a fixed point in M",
					BySets(inM, power))
			}))
		a.Show(
			"a subset of the same finite size is the whole",
			By(
				sizedImage,
				constants,
				inside,
				cardinality.CardSubsetEq.At(
					values, a.TermAs[Set[A]]("finite_constants(field_ring(M), card(k), «degree»)")),
				cardinality.HasSizeDef))
	}),
})}

// PointFactorsThroughAutomorphism — two points with one kernel and one image E
// differ by an automorphism of E over k: both identify S modulo the kernel with
// E, so the second after the inverse of the first is a ring map of E into M; it
// fixes k and keeps E, hence is an automorphism.
var PointFactorsThroughAutomorphism = pointFactorsThroughAutomorphismThm{family.Add(registry.ProofEntry{
	Name: "PointFactorsThroughAutomorphism",
	Key:  "prop_f68f2b5de4e21db4",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k S E:set(A). ∀φ ψ:(A → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, E)",
			"k ⊆ E",
			"finite_extension(M, k, E)",
			"k ⊆ S",
			"φ ∈ «points»",
			"ψ ∈ «points»",
			"image(φ, S) = E",
			"image(ψ, S) = E",
			"ring_kernel(M.zero, S, ψ) = ring_kernel(M.zero, S, φ)",
		},
		Conclusion: "∃p:permutation(A). " +
			"    p ∈ field_automorphisms(M, k, E) ∧ ψ = (λx:A. permutation_map(p, φ(x)))",
		Abbrev: Abbrev{
			{Name: "source", Text: "restrict_ring(field_ring(M), S)"},
			{Name: "points", Text: "algebra_points(«source», field_ring(M), k, λx:A. x)"},
			{Name: "quotient", Text: "ideal_quotient_ring(«source», ring_kernel(M.zero, S, φ))"},
			{Name: "projection", Text: "ideal_quotient_projection(«source», ring_kernel(M.zero, S, φ))"},
			{Name: "classes", Text: "left_cosets(M.add, S, ring_kernel(M.zero, S, φ))"},
			{Name: "target", Text: "restrict_ring(field_ring(M), E)"},
			{Name: "inverse", Text: "inverse_on(«classes», induced_map(φ))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, S, E *Expr[Set[A]],
		φ, ψ *Arrow[A, A],
		subK, subE, kInE, finiteOver, kInS, pointφ, pointψ, imageφ, imageψ, kernels Fact,
	) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		ambient := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		source := a.TermAs[module_record.RingOps[A]]("«source»")
		quotient := a.TermAs[module_record.RingOps[Set[A]]]("«quotient»")
		target := a.TermAs[module_record.RingOps[A]]("«target»")
		classes := a.TermAs[Set[Set[A]]]("«classes»")
		kernel := a.TermAs[Set[A]]("ring_kernel(M.zero, S, φ)")
		inducedφ := a.TermAs[Fun[Set[A], A]]("induced_map(φ)")
		inducedψ := a.TermAs[Fun[Set[A], A]]("induced_map(ψ)")
		inverse := a.TermAs[Fun[A, Set[A]]]("«inverse»")
		identity := a.TermAs[Fun[A, A]]("λx:A. x")
		dataφ := a.Have(
			"φ is a ring map fixing k and vanishing off S",
			"ring_homomorphism(«source», field_ring(M), φ) ∧ "+
				"(∀c:A. c ∈ k ⇒ φ(c) = c) ∧ "+
				"(∀x:A. x ∉ S ⇒ φ(x) = M.zero)",
			By(pointφ, algebra_points.AlgebraPointsMember.At(source, ambient, k, identity, φ)))
		dataψ := a.Have(
			"and so is ψ",
			"ring_homomorphism(«source», field_ring(M), ψ) ∧ "+
				"(∀c:A. c ∈ k ⇒ ψ(c) = c) ∧ "+
				"(∀x:A. x ∉ S ⇒ ψ(x) = M.zero)",
			By(pointψ, algebra_points.AlgebraPointsMember.At(source, ambient, k, identity, ψ)))
		isoφ := a.Have(
			"φ identifies S modulo the kernel with E",
			"ring_isomorphism(«quotient», «target», induced_map(φ)) ∧ "+
				"(∀r:A. r ∈ S ⇒ induced_map(φ, «projection»(r)) = φ(r))",
			By(imageφ, dataφ, quotient_ring.KernelQuotientImage.At(source, ambient, φ)))
		isoψ := a.Have(
			"and ψ, of the same kernel, does too",
			"ring_isomorphism(«quotient», «target», induced_map(ψ)) ∧ "+
				"(∀r:A. r ∈ S ⇒ induced_map(ψ, «projection»(r)) = ψ(r))",
			By(Normalized, imageψ, kernels, dataψ, quotient_ring.KernelQuotientImage.At(source, ambient, ψ)))
		parts := a.Have(
			"φ is injective on the classes, ψ a ring map of them",
			"injective_on(«classes», induced_map(φ)) ∧ ring_homomorphism(«quotient», «target», induced_map(ψ))",
			By(
				isoφ,
				isoψ,
				ring_homomorphism.RingIsomorphismDef.At(quotient, target, inducedφ),
				ring_homomorphism.RingIsomorphismDef.At(quotient, target, inducedψ)))
		rings := a.Have(
			"the rings in play are commutative, and E lies in M",
			"comm_ring_on(«quotient») ∧ comm_ring_on(«target») ∧ comm_ring_on(field_ring(M)) ∧ E ⊆ M.carrier",
			By(
				M,
				subE,
				parts,
				ring_homomorphism.Source,
				ring_homomorphism.Target,
				field.RingOn.At(fieldM),
				field.SubfieldSubset.At(fieldM, E)))
		backward := a.Have(
			"the inverse of the isomorphism of φ is a ring map",
			"ring_homomorphism(«target», «quotient», «inverse»)",
			By(
				isoφ,
				ring_homomorphism.IsomorphismInverse.At(quotient, target, inducedφ),
				ring_homomorphism.RingIsomorphismDef.At(target, quotient, inverse)))
		forward := a.Have(
			"and that of ψ a ring map into M",
			"ring_homomorphism(«quotient», field_ring(M), induced_map(ψ))",
			By(parts, rings, ring_homomorphism.RingHomExtendTarget.At(quotient, ambient, inducedψ, E)))
		compare := a.Have(
			"so the comparison of φ and ψ is a ring map of E into M",
			"ring_homomorphism(«target», field_ring(M), λy:A. induced_map(ψ, «inverse»(y)))",
			By(
				backward,
				forward,
				ring_homomorphism.RingHomCompose.At(target, quotient, ambient, inverse, inducedψ)))
		θ, θDef := a.LetAs[Fun[A, A]]("θ", "λy:A. induced_map(ψ, «inverse»(y))")
		sourceData := a.Have(
			"S is a commutative ring with the ideal the kernel",
			"comm_ring_on(«source») ∧ ring_ideal(«source», ring_kernel(M.zero, S, φ))",
			By(Normalized, dataφ, ring_homomorphism.Source, ring_homomorphism.KernelIdeal))
		projects := a.Have(
			"the projection is a ring map",
			"ring_homomorphism(«source», «quotient», «projection»)",
			By(sourceData, quotient_ring.ProjectionHomomorphism.At(source, kernel)))
		formula := a.Have(
			"θ carries φ to ψ",
			"∀x:A. x ∈ S ⇒ θ(φ(x)) = ψ(x)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				inS := b.Assume()
				class := b.TermAs[Set[A]]("«projection»(x)")
				member := b.Have(
					"the class of x is a class",
					"«projection»(x) ∈ «classes»",
					By(inS, projects, ring_homomorphism.MapIn.Read(projects)))
				inverted := b.Have(
					"the inverse takes φ(x) back to the class of x",
					"«inverse»(φ(x)) = «projection»(x)",
					By(isoφ, inS, parts, member, functions.InverseOnLeft.At(classes, inducedφ, class)))
				b.Show(
					"and ψ sends the class of x to ψ(x)",
					By(Normalized, θDef, isoψ, inS, inverted))
			}))
		fixes := a.Have(
			"θ fixes k",
			"∀c:A. c ∈ k ⇒ θ(c) = c",
			Derive(func(b *Argument) {
				b.FixAs[A]("c")
				inK := b.Assume()
				values := b.Have(
					"c lies in S and both points fix it",
					"c ∈ S ∧ φ(c) = c ∧ ψ(c) = c",
					BySets(kInS, inK, dataφ, dataψ))
				b.Show(
					"θ carries φ(c) to ψ(c)",
					By(Normalized, formula, values))
			}))
		stable := a.Have(
			"θ carries the values of φ to values of ψ",
			"∀y:A. y ∈ image(φ, S) ⇒ θ(y) ∈ image(ψ, S)",
			Derive(func(b *Argument) {
				b.Do(Simp(Fwd(set_image.ForallInImage)))
				x := b.FixAs[A]("x")
				inS := b.Assume()
				b.Show(
					"θ(φ(x)) is ψ(x)",
					By(Normalized, formula, inS, set_image.FunInImage.At(ψ, S, x)))
			}))
		keepsE := a.Have(
			"so θ keeps E",
			"∀y:A. y ∈ E ⇒ θ(y) ∈ E",
			By(Normalized, stable, imageφ, imageψ))
		inside := a.Have(
			"its image lies in E",
			"image(θ, E) ⊆ E",
			BySets(keepsE))
		onto := a.Have(
			"a map of a finite extension into itself is onto",
			"image(θ, E) = E",
			By(
				M,
				subK,
				subE,
				kInE,
				finiteOver,
				compare,
				fixes,
				inside,
				field_extension.FiniteEmbeddingOnto.At(fieldM, k, E, θ)))
		q, automorphism := a.ObtainAs[symmetric_group.Permutation[A]](
			"so θ is an automorphism q of E over k",
			"∃q:permutation(A). "+
				"    q ∈ field_automorphisms(M, k, E) ∧ (∀x:A. x ∈ E ⇒ permutation_map(q, x) = θ(x))",
			By(M, subE, compare, fixes, onto, field_automorphism.EmbeddingPermutation.At(fieldM, k, E, θ)))
		zero := a.Have(
			"q fixes zero",
			"permutation_map(q, M.zero) = M.zero",
			By(M, subE, automorphism, field_automorphism.AutomorphismFixesUnits.At(fieldM, k, E, q)))
		agrees := a.Have(
			"ψ is q after φ",
			"ψ = (λx:A. permutation_map(q, φ(x)))",
			Derive(func(b *Argument) {
				b.Do(Funext())
				x := b.FixAs[A]("x")
				b.Cases(b.TermAs[Bool]("x ∈ S"))
				b.When(
					"on S, q acts on the value φ(x) of E as θ does",
					func(c *Argument, inS Fact) {
						value := c.Have(
							"φ(x) lies in E",
							"φ(x) ∈ image(φ, S) ∧ φ(x) ∈ E",
							By(Normalized, inS, imageφ, set_image.FunInImage.At(φ, S, x)))
						c.Show(
							"θ(φ(x)) is ψ(x)",
							By(Normalized, formula, automorphism, inS, value))
					})
				b.Otherwise(
					"off S, both sides vanish",
					func(c *Argument, outside Fact) {
						c.Show(
							"φ(x) and ψ(x) are zero, and q fixes zero",
							By(Normalized, dataφ, dataψ, outside, zero))
					})
			}))
		a.Take(q)
		a.Show(
			"q is the automorphism",
			By(automorphism, agrees))
	}),
})}

// ResiduePoints — the points of a finite residue field in a closed field: for a
// maximal ideal m of S with S/m of dimension d over the finite field k, exactly
// d points of S in M have kernel m, and each has image the subfield of M with
// q^d elements. A point exists, its image is that subfield E, and the
// automorphisms of E over k, d in number, act simply and transitively on the
// points with kernel m.
var ResiduePoints = residuePointsThm{family.Add(registry.ProofEntry{
	Name: "ResiduePoints",
	Key:  "prop_6e53889f1cc5d899",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k S m:set(A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"finite(k)",
			"subring(field_ring(M), S)",
			"k ⊆ S",
			"maximal_ideal(«source», m)",
			"finite_dimensional(«scalars», «residues»)",
		},
		Conclusion: "has_size({φ:A → A | φ ∈ «points» ∧ ring_kernel(M.zero, S, φ) = m}, «degree») ∧ " +
			"(∀φ:A → A. " +
			"    φ ∈ «points» ∧ ring_kernel(M.zero, S, φ) = m ⇒ " +
			"    image(φ, S) = finite_constants(field_ring(M), card(k), «degree»))",
		Abbrev: Abbrev{
			{Name: "source", Text: "restrict_ring(field_ring(M), S)"},
			{Name: "scalars", Text: "restrict_ring(field_ring(M), k)"},
			{Name: "residues", Text: "quotient_module(restrict_module(regular_module(field_ring(M)), S), m)"},
			{Name: "degree", Text: "module_dim(«scalars», «residues»)"},
			{Name: "points", Text: "algebra_points(«source», field_ring(M), k, λx:A. x)"},
			{Name: "fibre", Text: "{φ:A → A | φ ∈ «points» ∧ ring_kernel(M.zero, S, φ) = m}"},
			{Name: "twist", Text: "λp:permutation(A). λx:A. permutation_map(p, ω(x))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, S, m *Expr[Set[A]],
		closed, subK, finiteK, subS, kInS, maximal, finiteDimension Fact,
	) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		degree := a.TermAs[Nat]("«degree»")
		positiveDegree := a.Have(
			"d is positive",
			"0 < «degree»",
			By(M, subK, finiteK, subS, kInS, maximal, finiteDimension, ResidueSize.At(fieldM, k, S, m)))
		imageOfPoints := a.Have(
			"every point with kernel m has image the subfield with q^d elements",
			Statement{
				Binders: "∀φ:(A → A).",
				Hypotheses: []string{
					"φ ∈ «points»",
					"ring_kernel(M.zero, S, φ) = m",
				},
				Conclusion: "image(φ, S) = finite_constants(field_ring(M), card(k), «degree»)",
			},
			Derive(func(b *Argument) {
				φ := b.FixAs[Fun[A, A]]("φ")
				point := b.Assume()
				b.Show(
					"S/m is that subfield",
					By(
						M,
						closed,
						subK,
						finiteK,
						subS,
						kInS,
						maximal,
						finiteDimension,
						point,
						ResiduePointImage.At(fieldM, k, S, m, φ)))
			}))
		ω, basePoint := a.ObtainAs[Fun[A, A]](
			"a point ω with kernel m exists",
			"∃ω:A → A. ω ∈ «points» ∧ ring_kernel(M.zero, S, ω) = m",
			By(
				M,
				closed,
				subK,
				finiteK,
				subS,
				kInS,
				maximal,
				finiteDimension,
				ResiduePointExists.At(fieldM, k, S, m)))
		E, EDef := a.LetAs[Set[A]]("E", "finite_constants(field_ring(M), card(k), «degree»)")
		G, GDef := a.LetAs[Set[symmetric_group.Permutation[A]]]("G", "field_automorphisms(M, k, E)")
		baseImage := a.Have(
			"its image is E",
			"image(ω, S) = E",
			By(imageOfPoints.At(ω), basePoint))
		automorphisms := a.Have(
			"E has degree d over k and d automorphisms",
			"finite_extension(M, k, E) ∧ extension_degree(M, k, E) = «degree» ∧ has_size(G, «degree»)",
			By(
				EDef,
				GDef,
				M,
				closed,
				subK,
				finiteK,
				positiveDegree,
				finite_field.FiniteConstantsAutomorphisms.At(fieldM, k, degree)))
		constants := a.Have(
			"E is a subfield holding k",
			"subfield(M, E) ∧ k ⊆ E",
			By(
				EDef,
				M,
				closed,
				subK,
				finiteK,
				positiveDegree,
				finite_field.FiniteConstantsSubfield.At(fieldM, k, degree)))
		twists := a.Have(
			"an automorphism carries ω to a point of kernel m",
			Statement{
				Binders:    "∀p:permutation(A).",
				Hypotheses: []string{"p ∈ G"},
				Conclusion: "(λx:A. permutation_map(p, ω(x))) ∈ «points» ∧ " +
					"ring_kernel(M.zero, S, λx:A. permutation_map(p, ω(x))) = m",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[symmetric_group.Permutation[A]]("p")
				member := b.Assume()
				twisted := b.Have(
					"the twisted point has the kernel of ω",
					"(λx:A. permutation_map(p, ω(x))) ∈ «points» ∧ "+
						"ring_kernel(M.zero, S, λx:A. permutation_map(p, ω(x))) = ring_kernel(M.zero, S, ω)",
					By(GDef, M, constants, basePoint, baseImage, member, PointTwist.At(fieldM, k, S, E, ω, p)))
				b.Show(
					"which is m",
					By(twisted, basePoint))
			}))
		factors := a.Have(
			"and every point of kernel m comes from ω so",
			Statement{
				Binders:    "∀ψ:A → A.",
				Hypotheses: []string{"ψ ∈ «points»", "ring_kernel(M.zero, S, ψ) = m"},
				Conclusion: "∃p:permutation(A). p ∈ G ∧ ψ = (λx:A. permutation_map(p, ω(x)))",
			},
			Derive(func(b *Argument) {
				ψ := b.FixAs[Fun[A, A]]("ψ")
				point := b.Assume()
				b.Show(
					"two points of one kernel and one image differ by an automorphism",
					By(
						GDef,
						M,
						subK,
						constants,
						automorphisms,
						kInS,
						basePoint,
						point,
						baseImage,
						imageOfPoints.At(ψ),
						PointFactorsThroughAutomorphism.At(fieldM, k, S, E, ω, ψ)))
			}))
		separates := a.Have(
			"distinct automorphisms carry ω to distinct points",
			Statement{
				Binders: "∀p q:permutation(A).",
				Hypotheses: []string{
					"p ∈ G",
					"q ∈ G",
					"(λx:A. permutation_map(p, ω(x))) = (λx:A. permutation_map(q, ω(x)))",
				},
				Conclusion: "p = q",
			},
			Derive(func(b *Argument) {
				b.FixAs[symmetric_group.Permutation[A]]("p")
				b.FixAs[symmetric_group.Permutation[A]]("q")
				same := b.Assume()
				onS := b.Have(
					"p and q agree at the values of ω",
					"∀x:A. x ∈ S ⇒ permutation_map(p, ω(x)) = permutation_map(q, ω(x))",
					Derive(func(c *Argument) {
						c.FixAs[A]("x")
						c.Assume()
						c.Show(
							"the two functions are equal",
							By(Normalized, same))
					}))
				onImage := b.Have(
					"so on the image of ω",
					"∀y:A. y ∈ image(ω, S) ⇒ permutation_map(p, y) = permutation_map(q, y)",
					Simp(Fwd(set_image.ForallInImage)),
					By(onS))
				offE := b.Have(
					"and off E both are the identity",
					"∀y:A. y ∉ E ⇒ permutation_map(p, y) = y ∧ permutation_map(q, y) = y",
					Derive(func(c *Argument) {
						c.FixAs[A]("y")
						outside := c.Assume()
						symmetric := c.Have(
							"automorphisms of E move only elements of E",
							"p ∈ symmetric_group(E) ∧ q ∈ symmetric_group(E)",
							BySets(same, GDef, field_automorphism.FieldAutomorphismsDef.At(fieldM, k, E)))
						c.Show(
							"y lies off E",
							By(symmetric, outside, symmetric_group.InSymmetricGroup))
					}))
				b.Do(Simp(Fwd(symmetric_group.PermutationEq)))
				b.FixAs[A]("x")
				b.Cases(b.TermAs[Bool]("x ∈ E"))
				b.When(
					"on E, the image of ω",
					func(c *Argument, inE Fact) {
						c.Show(
							"p and q agree on the image of ω",
							By(Normalized, onImage, baseImage, inE))
					})
				b.Otherwise(
					"off E, both fix the element",
					func(c *Argument, outside Fact) {
						c.Show(
							"both are the identity there",
							By(Normalized, offE, outside))
					})
			}))
		twist := a.TermAs[Fun[symmetric_group.Permutation[A], Fun[A, A]]]("«twist»")
		fibre := a.TermAs[Set[Fun[A, A]]]("«fibre»")
		orbit := a.TermAs[Set[Fun[A, A]]]("image(«twist», G)")
		injective := a.Have(
			"the action on ω is injective",
			"injective_on(G, «twist»)",
			By(separates, functions.InjectiveOnDef.At(G, twist)))
		sizedOrbit := a.Have(
			"so the orbit of ω has d points",
			"has_size(image(«twist», G), «degree»)",
			By(injective, automorphisms, cardinality.HasSizeImageInj.At(twist, G, degree)))
		within := a.Have(
			"the orbit lies among the points of kernel m",
			"image(«twist», G) ⊆ «fibre»",
			Simp(Fwd(set_image.ImageSubsetIff)),
			BySets(twists))
		covers := a.Have(
			"and it is all of them",
			"«fibre» ⊆ image(«twist», G)",
			Derive(func(b *Argument) {
				b.Do(Simp(Fwd(set_basic.SubsetDef)))
				ψ := b.FixAs[Fun[A, A]]("ψ")
				member := b.Assume()
				point := b.Have(
					"ψ is a point of kernel m",
					"ψ ∈ «points» ∧ ring_kernel(M.zero, S, ψ) = m",
					BySets(member))
				comes := b.Have(
					"so ψ comes from ω",
					"∃p:permutation(A). p ∈ G ∧ ψ = (λx:A. permutation_map(p, ω(x)))",
					By(point, factors.At(ψ)))
				b.Show(
					"that is, ψ lies in the orbit",
					By(comes, set_basic.InImage.At(twist, G, ψ)))
			}))
		orbitIsFibre := a.Have(
			"the points of kernel m are the orbit of ω",
			"«fibre» = image(«twist», G)",
			By(within, covers, set_order.SubsetAntisym.At(fibre, orbit)))
		a.Show(
			"there are d of them, each with image E",
			By(imageOfPoints, orbitIsFibre, sizedOrbit))
	}),
})}
