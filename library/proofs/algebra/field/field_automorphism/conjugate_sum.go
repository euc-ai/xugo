// conjugate_sum.go — the sum of the conjugates under a finite group of
// automorphisms of C fixing K. Each automorphism is K-linear; the sum of the
// conjugates is fixed by every automorphism, it is not the zero map
// (Dedekind), and it carries an element integral over a principal ideal
// domain inside K to one.

package field_automorphism

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// AutomorphismLinear — an automorphism of C fixing K is K-linear: it keeps sums
// and products on C, and multiplying by a scalar of K multiplies the image by
// that same scalar.
var AutomorphismLinear = automorphismLinearThm{family.Add(registry.ProofEntry{
	Name: "AutomorphismLinear",
	Key:  "prop_6bacca50050d295a",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "restrict_ring(field_ring(M), K)"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(M)), C)"},
		},
		Binders: "∀M:field_on(A). ∀K C:set(A). ∀g:permutation(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"subfield(M, C)",
			"K ⊆ C",
			"g ∈ field_automorphisms(M, K, C)",
		},
		Conclusion: "module_homomorphism(«scalars», «vectors», «vectors», permutation_map(g))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, C *Expr[Set[A]],
			g *Expr[symmetric_group.Permutation[A]],
			subK, subC, KInC, inG Fact,
		) {
			scalars := a.TermAs[module_record.RingOps[A]]("«scalars»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»")
			gMap := a.TermAs[Fun[A, A]]("permutation_map(g)")
			laws := a.Conjuncts(
				a.Have(
					"g permutes C, keeps its sums and products, and fixes K",
					"g ∈ symmetric_group(C) ∧ "+
						"(∀u v:A. "+
						"    u ∈ C ∧ v ∈ C ⇒ "+
						"    permutation_map(g, u + v) = permutation_map(g, u) + permutation_map(g, v)) ∧ "+
						"(∀u v:A. "+
						"    u ∈ C ∧ v ∈ C ⇒ "+
						"    permutation_map(g, u * v) = permutation_map(g, u) * permutation_map(g, v)) ∧ "+
						"(∀u:A. u ∈ K ⇒ permutation_map(g, u) = u)",
					BySets(a.Unfolded(inG, FieldAutomorphismsDef))),
				"g permutes C",
				"g keeps sums",
				"g keeps products",
				"g fixes K")
			permutes, sums, products, fixes := laws[0], laws[1], laws[2], laws[3]
			into := a.Have(
				"g maps C into C",
				"∀u:A. u ∈ C ⇒ permutation_map(g, u) ∈ C",
				By(permutes, symmetric_group.SymmetricGroupMapsInto))
			scaled := a.Have(
				"g takes a scalar of K out of a product",
				"∀c u:A. c ∈ K ∧ u ∈ C ⇒ permutation_map(g, c * u) = c * permutation_map(g, u)",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					u := b.FixAs[A]("u")
					members := b.Assume()
					inC := b.Have(
						"c lies in C",
						"c ∈ C",
						BySets(members, KInC))
					b.Show(
						"g keeps the product and fixes c",
						By(Normalized, members, inC, fixes.At(c), products.At(c, u)))
				}))
			a.Show(
				"g meets the conditions of a linear map",
				By(
					field_extension.ExtensionModuleOn.Read(M).At(K, C),
					subK,
					subC,
					KInC,
					into,
					sums,
					scaled,
					module_homomorphism.ModuleHomomorphismDef.At(scalars, vectors, vectors, gMap)))
		}),
})}

// GaloisTraceFixed — the sum of the conjugates of b is fixed by every
// automorphism h: h carries the sum to the sum of the h(g(b)), and multiplying
// by h is a one-to-one self-map of the finite group, so onto it.
var GaloisTraceFixed = galoisTraceFixedThm{family.Add(registry.ProofEntry{
	Name: "GaloisTraceFixed",
	Key:  "prop_bb0c83672c4c0a2f",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "trace", Text: "λb:A. " +
				"    module_sum(M.add, " +
				"        M.zero, " +
				"        field_automorphisms(M, K, C), " +
				"        λg:permutation(A). permutation_map(g, b))"},
			{Name: "scalars", Text: "restrict_ring(field_ring(M), K)"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(M)), C)"},
		},
		Binders: "∀M:field_on(A). ∀K C:set(A). ∀h:permutation(A). ∀b:A.",
		Hypotheses: []string{
			"subfield(M, K)",
			"subfield(M, C)",
			"K ⊆ C",
			"finite(field_automorphisms(M, K, C))",
			"h ∈ field_automorphisms(M, K, C)",
			"b ∈ C",
		},
		Conclusion: "permutation_map(h, «trace»(b)) = «trace»(b)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, C *Expr[Set[A]],
			h *Expr[symmetric_group.Permutation[A]],
			b *Expr[A],
			subK, subC, KInC, finiteG, hIn, bIn Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			scalars := a.TermAs[module_record.RingOps[A]]("«scalars»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»")
			permutations := a.TermAs[group.GroupOps[symmetric_group.Permutation[A]]]("permutation_group")
			G := a.TermAs[Set[symmetric_group.Permutation[A]]]("field_automorphisms(M, K, C)")
			hMap := a.TermAs[Fun[A, A]]("permutation_map(h)")
			evaluate := a.TermAs[Fun[symmetric_group.Permutation[A], A]](
				"λg:permutation(A). permutation_map(g, b)")
			translate := a.TermAs[Fun[symmetric_group.Permutation[A], symmetric_group.Permutation[A]]](
				"λg:permutation(A). permutation_compose(h, g)")
			moduleC := a.Have(
				"C is a module over K",
				"module_on(«scalars», «vectors»)",
				By(M, subK, subC, KInC, field_extension.ExtensionModuleOn.Read(M).At(K, C)))
			conjugates := a.Have(
				"each conjugate of b lies in C",
				"∀g:permutation(A). g ∈ field_automorphisms(M, K, C) ⇒ permutation_map(g, b) ∈ C",
				Derive(func(c *Argument) {
					g := c.FixAs[symmetric_group.Permutation[A]]("g")
					gIn := c.Assume()
					linear := c.Have(
						"g is linear over K",
						"module_homomorphism(«scalars», «vectors», «vectors», permutation_map(g))",
						By(M, subK, subC, KInC, gIn, AutomorphismLinear.At(m, K, C, g)))
					c.Show(
						"g maps C into itself",
						By(bIn, module_homomorphism.HomIn.Read(linear)))
				}))
			linearH := a.Have(
				"h is linear over K",
				"module_homomorphism(«scalars», «vectors», «vectors», permutation_map(h))",
				By(M, subK, subC, KInC, hIn, AutomorphismLinear.At(m, K, C, h)))
			mapped := a.Have(
				"h carries the sum of the conjugates to the sum of their images",
				"permutation_map(h, «trace»(b)) = "+
					"module_sum(M.add, "+
					"    M.zero, "+
					"    field_automorphisms(M, K, C), "+
					"    λg:permutation(A). permutation_map(h, permutation_map(g, b)))",
				By(
					finiteG,
					conjugates,
					linearH,
					module_homomorphism.HomSum.At(scalars, vectors, vectors, hMap, G, evaluate)))
			injective := a.Have(
				"multiplying by h is one-to-one",
				"injective_on(field_automorphisms(M, K, C), λg:permutation(A). permutation_compose(h, g))",
				By(
					functions.InjectiveOnDef.At(G, translate),
					group.LeftCancel.Read(symmetric_group.SymmetricGroup)))
			subgroup := a.Conjuncts(
				AutomorphismsSubgroup.Read(M).At(K, C),
				"the automorphisms are a subgroup",
				"inside the symmetric group of C")[0]
			products := a.Have(
				"multiplying by h keeps the group",
				Statement{
					Binders:    "∀g:permutation(A).",
					Hypotheses: []string{"g ∈ field_automorphisms(M, K, C)"},
					Conclusion: "permutation_compose(h, g) ∈ field_automorphisms(M, K, C)",
				},
				Derive(func(c *Argument) {
					g := c.FixAs[symmetric_group.Permutation[A]]("g")
					gIn := c.Assume()
					c.Show(
						"a subgroup is closed under products",
						By(hIn, gIn, subgroup, group.SubgroupMul.At(permutations, G, h, g)))
				}))
			inGroup := a.Have(
				"the image lies in the group",
				"image(λg:permutation(A). permutation_compose(h, g), field_automorphisms(M, K, C)) ⊆ "+
					"field_automorphisms(M, K, C)",
				By(products, set_image.ImageSubsetIff.At(translate, G, G)))
			onto := a.Have(
				"so it permutes the finite group",
				"image(λg:permutation(A). permutation_compose(h, g), field_automorphisms(M, K, C)) = "+
					"field_automorphisms(M, K, C)",
				By(
					finiteG,
					injective,
					inGroup,
					cardinality.CardImageInj.At(translate, G),
					cardinality.CardSubsetEq.At(
						a.TermAs[Set[symmetric_group.Permutation[A]]](
							"image(λg:permutation(A). permutation_compose(h, g), field_automorphisms(M, K, C))"),
						G)))
			compose := a.Have(
				"the composite moves b by g and then by h",
				"∀g:permutation(A). "+
					"    permutation_map(h, permutation_map(g, b)) = permutation_map(permutation_compose(h, g), b)",
				a.ForEach(func(g *Expr[symmetric_group.Permutation[A]]) Action {
					return By(symmetric_group.MapCompose.At(h, g, b))
				}))
			translated := a.Have(
				"the conjugates by the translated group lie in C",
				Statement{
					Binders:    "∀g:permutation(A).",
					Hypotheses: []string{"g ∈ field_automorphisms(M, K, C)"},
					Conclusion: "permutation_map(permutation_compose(h, g), b) ∈ C",
				},
				Derive(func(c *Argument) {
					g := c.FixAs[symmetric_group.Permutation[A]]("g")
					gIn := c.Assume()
					c.Show(
						"the translate of g lies in the group",
						By(
							gIn,
							products.At(g),
							conjugates.At(c.TermAs[symmetric_group.Permutation[A]]("permutation_compose(h, g)"))))
				}))
			reindexed := a.Have(
				"reindexing by the translation",
				"module_sum(M.add, "+
					"    M.zero, "+
					"    image(λg:permutation(A). permutation_compose(h, g), field_automorphisms(M, K, C)), "+
					"    λg:permutation(A). permutation_map(g, b)) = "+
					"module_sum(M.add, "+
					"    M.zero, "+
					"    field_automorphisms(M, K, C), "+
					"    λg:permutation(A). permutation_map(permutation_compose(h, g), b))",
				By(
					finiteG,
					injective,
					translated,
					module.ModuleSumImage.Read(moduleC).AsFact().At(G, translate, evaluate)))
			a.Do(reindexed.Simp(Fwd(onto)))
			a.Show(
				"the sum of the h(g(b)) is the sum over the translated group, which is the group",
				mapped.Rw(),
				Simp(Fwd(compose)),
				By(reindexed))
		}),
})}

// GaloisTraceNonzero — the sum of the automorphisms is not the zero map: they
// are independent (Dedekind), and the identity lies among them with coefficient
// one.
var GaloisTraceNonzero = galoisTraceNonzeroThm{family.Add(registry.ProofEntry{
	Name: "GaloisTraceNonzero",
	Key:  "prop_834274bb83aa7a10",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "trace", Text: "λb:A. " +
				"    module_sum(M.add, " +
				"        M.zero, " +
				"        field_automorphisms(M, K, C), " +
				"        λg:permutation(A). permutation_map(g, b))"},
		},
		Binders: "∀M:field_on(A). ∀K C:set(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"subfield(M, C)",
			"K ⊆ C",
			"finite(field_automorphisms(M, K, C))",
		},
		Conclusion: "∃b:A. b ∈ C ∧ «trace»(b) ≠ M.zero",
	},
		func(a *Argument, M field.FieldFact[on.M], K, C *Expr[Set[A]], subK, subC, KInC, finiteG Fact) {
			m := a.TermAs[FieldOps[A]]("M")
			permutations := a.TermAs[group.GroupOps[symmetric_group.Permutation[A]]]("permutation_group")
			G := a.TermAs[Set[symmetric_group.Permutation[A]]]("field_automorphisms(M, K, C)")
			add := a.TermAs[Op[A]]("M.add")
			zero := a.TermAs[A]("M.zero")
			unit := a.TermAs[Fun[symmetric_group.Permutation[A], A]]("λq:permutation(A). M.one")
			identity := a.TermAs[symmetric_group.Permutation[A]]("permutation_identity")
			vanishes := a.SupposeNot()
			everywhere := a.Have(
				"then the sum of the conjugates vanishes on C",
				"∀b:A. b ∈ C ⇒ «trace»(b) = M.zero",
				By(Normalized, vanishes))
			coefficient := a.Have(
				"so does the combination of the automorphisms with coefficient one",
				Statement{
					Binders:    "∀b:A.",
					Hypotheses: []string{"b ∈ C"},
					Conclusion: "module_sum(M.add, " +
						"    M.zero, " +
						"    field_automorphisms(M, K, C), " +
						"    λr:permutation(A). (λq:permutation(A). M.one)(r) * permutation_map(r, b)) = " +
						"M.zero",
				},
				Derive(func(c *Argument) {
					c.FixAs[A]("b")
					bIn := c.Assume()
					unitTimes := c.TermAs[Fun[symmetric_group.Permutation[A], A]](
						"λr:permutation(A). (λq:permutation(A). M.one)(r) * permutation_map(r, b)")
					evaluate := c.TermAs[Fun[symmetric_group.Permutation[A], A]](
						"λg:permutation(A). permutation_map(g, b)")
					each := c.Have(
						"one fixes each conjugate of b",
						Statement{
							Binders:    "∀r:permutation(A).",
							Hypotheses: []string{"r ∈ field_automorphisms(M, K, C)"},
							Conclusion: "M.one * permutation_map(r, b) = permutation_map(r, b)",
						},
						Derive(func(d *Argument) {
							r := d.FixAs[symmetric_group.Permutation[A]]("r")
							rIn := d.Assume()
							linear := d.Have(
								"r is linear over K",
								"module_homomorphism(restrict_ring(field_ring(M), K), "+
									"    restrict_module(regular_module(field_ring(M)), C), "+
									"    restrict_module(regular_module(field_ring(M)), C), "+
									"    permutation_map(r))",
								By(M, subK, subC, KInC, rIn, AutomorphismLinear.At(m, K, C, r)))
							inC := d.Have(
								"the conjugate lies in C",
								"permutation_map(r, b) ∈ C",
								By(bIn, module_homomorphism.HomIn.Read(linear)))
							inField := d.Have(
								"so it lies in M",
								"permutation_map(r, b) ∈ M.carrier",
								BySets(inC, subC, field.SubfieldSubset.At(m, C)))
							d.Show(
								"one is the identity of M",
								ByArith(M, inField))
						}))
					c.Show(
						"the combination is the sum of the conjugates",
						By(each, bIn, everywhere, module.ModuleSumCongruence.At(add, zero, G, unitTimes, evaluate)))
				}))
			subgroup := a.Conjuncts(
				AutomorphismsSubgroup.Read(M).At(K, C),
				"the automorphisms are a subgroup",
				"inside the symmetric group of C")[0]
			identityIn := a.Have(
				"the identity is an automorphism",
				"permutation_identity ∈ field_automorphisms(M, K, C)",
				By(subgroup, group.SubgroupOne.At(permutations, G)))
			antitone := a.Have(
				"each automorphism fixing K is one fixing nothing",
				"field_automorphisms(M, K, C) ⊆ field_automorphisms(M, ∅, C)",
				By(AutomorphismsAntitone.Read(M).At(a.TermAs[Set[A]]("∅"), K, C), set_order.EmptySubset))
			a.Show(
				"the coefficient one of the identity would vanish",
				By(
					M,
					subC,
					finiteG,
					antitone,
					coefficient,
					identityIn,
					comm_ring.OneIn.Read(field.RingOn.Read(M)),
					field.OneNotZeroOn.Read(M),
					Dedekind.Read(M).At(C, G, unit, identity)))
		}),
})}

// GaloisTraceIntegral — the sum of the conjugates of an integral element is
// integral: a monic relation over S ⊆ K has its coefficients fixed by the
// group, so each conjugate is a root of the same relation, and a finite sum of
// integral elements is integral.
var GaloisTraceIntegral = galoisTraceIntegralThm{family.Add(registry.ProofEntry{
	Name: "GaloisTraceIntegral",
	Key:  "prop_36dd2a3d4b0ebb3b",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "trace", Text: "λb:A. " +
				"    module_sum(M.add, " +
				"        M.zero, " +
				"        field_automorphisms(M, K, C), " +
				"        λg:permutation(A). permutation_map(g, b))"},
			{Name: "ring", Text: "restrict_ring(field_ring(M), S)"},
			{Name: "scalars", Text: "restrict_ring(field_ring(M), K)"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(M)), C)"},
		},
		Binders: "∀M:field_on(A). ∀K C S:set(A). ∀b:A.",
		Hypotheses: []string{
			"subfield(M, K)",
			"subfield(M, C)",
			"K ⊆ C",
			"finite(field_automorphisms(M, K, C))",
			"subring(field_ring(M), S)",
			"S ⊆ K",
			"b ∈ C",
			"integral_over(«ring», b)",
		},
		Conclusion: "integral_over(«ring», «trace»(b))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, C, S *Expr[Set[A]],
			b *Expr[A],
			subK, subC, KInC, finiteG, subS, SInK, bIn, integral Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			G := a.TermAs[Set[symmetric_group.Permutation[A]]]("field_automorphisms(M, K, C)")
			zero := a.TermAs[A]("M.zero")
			evaluate := a.TermAs[Fun[symmetric_group.Permutation[A], A]](
				"λg:permutation(A). permutation_map(g, b)")
			p, relation := a.UnpackAs[Fun[Nat, A]](a.Unfolded(integral, integral_element.IntegralOverDef), "p")
			parts := a.Conjuncts(
				relation,
				"p is over S",
				"p is monic",
				"of positive degree",
				"b is a root of p")
			overK := a.Have(
				"p is over K",
				"polynomial_over(K, p)",
				By(SInK, parts[0], polynomial.PolynomialOverMono.At(zero, S, K, p)))
			conjugates := a.Have(
				"each conjugate of b is a root of p, so integral over S",
				Statement{
					Binders:    "∀g:permutation(A).",
					Hypotheses: []string{"g ∈ field_automorphisms(M, K, C)"},
					Conclusion: "permutation_map(g, b) ∈ M.carrier ∧ integral_over(«ring», permutation_map(g, b))",
				},
				Derive(func(c *Argument) {
					g := c.FixAs[symmetric_group.Permutation[A]]("g")
					gIn := c.Assume()
					root := c.Have(
						"g fixes K, so it sends the root b of p to a root of p",
						"polynomial_eval(p, permutation_map(g, b)) = M.zero",
						By(M, subC, KInC, gIn, overK, bIn, parts[3], AutomorphismPermutesRoots.At(m, K, C, p, g, b)))
					linear := c.Have(
						"g is linear over K",
						"module_homomorphism(«scalars», «vectors», «vectors», permutation_map(g))",
						By(M, subK, subC, KInC, gIn, AutomorphismLinear.At(m, K, C, g)))
					inField := c.Have(
						"the conjugate lies in M",
						"permutation_map(g, b) ∈ M.carrier",
						BySets(bIn, module_homomorphism.HomIn.Read(linear), subC, field.SubfieldSubset.At(m, C)))
					integralConjugate := c.Have(
						"the same monic relation holds at the conjugate",
						"integral_over(«ring», permutation_map(g, b))",
						Simp(Fwd(integral_element.IntegralOverDef)),
						Witness(p),
						By(parts[0], parts[1], parts[2], root))
					c.Show(
						"it lies in M and is integral",
						By(inField, integralConjugate))
				}))
			a.Show(
				"a finite sum of integral elements is integral",
				By(M, subS, finiteG, conjugates, integral_element.IntegralModuleSum.At(m, S, G, evaluate)))
		}),
})}
