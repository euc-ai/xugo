package class_number

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ideal_norm"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/integral_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/number_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ring_of_integers"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// integerBoxCardinality counts bounded integer coefficients on the finite
// basis image. A pinned map is a coefficient map on the basis image E,
// extended by zero off E; there are (H+1)^n pinned maps with values between
// zero and H. Independence makes the sum encoding injective; reindexing
// identifies its image with the coordinate box.
var integerBoxCardinality = integerBoxCardinalityThm{family.Add(registry.ProofEntry{
	Name: "integerBoxCardinality",
	Key:  "prop_cfbbd9ad6ce8651a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀n H:num. ∀e:(num → A).",
		Hypotheses: []string{
			"number_field(L)",
			"integral_basis(field_ring(L), n, e)",
		},
		Conclusion: "has_size(integer_coordinate_box(field_ring(L), n, e, H), (H + 1) ^ n)",
	}, func(a *Argument, L field.FieldFact[on.L], n, H *Expr[Nat], e *Arrow[Nat, A], given Fact) {
		fieldL := a.TermAs[field.FieldOps[A]]("L")
		R := a.TermAs[RingOps[A]]("field_ring(L)")
		integerScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), integer_image(field_ring(L)))")
		integerModuleTerm := a.TermAs[module_record.ModuleOps[A, A]](
			"restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L)))")
		zeroInt := a.TermAs[Int]("0")
		one := a.TermAs[Nat]("1")
		s, sDef := a.LetAs[Set[Nat]]("s", "{i:num | i < n}")
		E, basisDef := a.LetAs[Set[A]]("E", "{e(i):A | i:num | i < n}")
		t, intervalDef := a.LetAs[Set[Int]]("t", "{z:int | 0 ≤ z ∧ z ≤ H}")
		F, mapsDef := a.LetAs[Set[Fun[A, Int]]](
			"F", "{h:A → int | (∀x:A. x ∈ E ⇒ h(x) ∈ t) ∧ (∀x:A. x ∉ E ⇒ h(x) = 0)}")
		f, encodeDef := a.LetAs[Fun[Fun[A, Int], A]](
			"f", "λh:(A → int). module_sum(L.add, L.zero, E, λx:A. L.mul(integer_map(field_ring(L), h(x)), x))")
		charZero := a.Have(
			"the number field has characteristic zero",
			"characteristic_zero(field_ring(L))",
			By(given, number_field.NumberFieldDef.At(fieldL)))
		intervalCount := a.Have(
			"the inclusive integer interval has H plus one points",
			"finite(t) ∧ int_of_num(card(t)) = H + 1",
			Derive(func(b *Argument) {
				rawCount := b.Have(
					"the interval size formula applies to its endpoints",
					"finite(t) ∧ int_of_num(card(t)) = int_max(&H - 0 + 1, 0)",
					By(intervalDef, int_embed.IntIntervalSize.At(zeroInt, b.TermAs[Int]("H"))))
				b.Show(
					"the nonnegative upper endpoint simplifies the size",
					ByArith(rawCount, int_embed.OfNumAdd.At(H, one)))
			}))
		intervalSize := a.Have(
			"the interval has the required finite size",
			"has_size(t, H + 1)",
			By(
				intervalCount,
				int_embed.OfNumEq.At(a.TermAs[Nat]("card(t)"), a.TermAs[Nat]("H+1")),
				cardinality.HasSizeDef.Inst[Int]().At(t, a.TermAs[Nat]("H+1"))))
		integerModule := a.Conjuncts(
			GroupPremises(L, given, ring_of_integers.RingOfIntegersIntegerModule.At(fieldL)),
			"the integer ring is closed under integer scalars",
			"the integer ring is an integer module")[1]
		indexed := a.Have(
			"the integral basis is an indexed basis of the integer module",
			"indexed_module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L))), "+
				"    n, "+
				"    e)",
			By(given, ring_of_integers.IntegralBasisDef.At(R, n, e)))
		basisInfo := a.Have(
			"the basis image has n points and distinct indexed vectors",
			"finite(E) ∧ "+
				"card(E) = n ∧ "+
				"module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L))), "+
				"    E) ∧ "+
				"injective_on(s, e)",
			By(
				basisDef,
				sDef,
				indexed,
				linear_independence.IndexedBasisImage.At(integerScalars, integerModuleTerm, n, e)))
		independent := a.Have(
			"the basis image is independent and lies in the integer ring",
			"module_independent(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), ring_of_integers(field_ring(L))), "+
				"    E) ∧ "+
				"E ⊆ ring_of_integers(field_ring(L))",
			BySets(
				basisInfo,
				linear_independence.ModuleBasisDef.At(integerScalars, integerModuleTerm, E),
				linear_independence.BasisInCarrier.At(integerScalars, integerModuleTerm, E)))
		scalarIn := a.Have(
			"every integer coefficient is an integer scalar",
			"∀z:int. "+
				"    integer_map(field_ring(L), z) ∈ "+
				"    restrict_ring(field_ring(L), integer_image(field_ring(L))).carrier",
			Simp(Fwd(module_record.RestrictRingDef), Fwd(module_record.RingCarrierDef)),
			BySets(characteristic_zero.IntegerImageDef.At(R)))
		basisSize := a.Have(
			"the basis image has size n",
			"has_size(E, n)",
			By(basisInfo, cardinality.HasSizeDef.Inst[A]().At(E, n)))
		mapsSize := a.Have(
			"pinned maps choose one of H plus one coefficients at each basis vector",
			"has_size(F, (H + 1) ^ n)",
			By(
				mapsDef,
				basisSize,
				intervalSize,
				cardinality.HasSizeFunspace.At(E, t, n, a.TermAs[Nat]("H+1"), zeroInt)))
		integerInjective := a.Have(
			"the integer map is injective",
			"injective_on(𝕌, integer_map(field_ring(L)))",
			By(field.RingOn.Read(L), charZero, characteristic_zero.IntegerMapInjective.At(R)))
		encodingInjective := a.Have(
			"independence distinguishes the pinned coefficient maps",
			"injective_on(F, f)",
			Simp(Fwd(functions.InjectiveOnDef)),
			Derive(func(b *Argument) {
				b.FixAs[Fun[A, Int]]("p")
				b.FixAs[Fun[A, Int]]("q")
				equalImages := b.Assume()
				coefficients := b.Have(
					"equal encoded sums have equal scalar coefficients on the basis",
					"∀z:A. z ∈ E ⇒ integer_map(field_ring(L), p(z)) = integer_map(field_ring(L), q(z))",
					Derive(func(c *Argument) {
						inScalars := c.Have(
							"both coefficient functions take scalar values on E",
							Statement{
								Binders: "∀z:A.",
								Hypotheses: []string{
									"z ∈ E",
								},
								Conclusion: "integer_map(field_ring(L), p(z)) ∈ " +
									"restrict_ring(field_ring(L), integer_image(field_ring(L))).carrier ∧ " +
									"integer_map(field_ring(L), q(z)) ∈ " +
									"restrict_ring(field_ring(L), integer_image(field_ring(L))).carrier",
							},
							By(scalarIn))
						equalSums := c.Have(
							"the encoding equality is equality of the two basis sums",
							"module_sum(L.add, L.zero, E, λz:A. L.mul(integer_map(field_ring(L), p(z)), z)) = "+
								"module_sum(L.add, L.zero, E, λz:A. L.mul(integer_map(field_ring(L), q(z)), z))",
							By(Normalized, encodeDef, equalImages))
						c.Show(
							"coefficient uniqueness applies on the common finite support",
							By(
								independent,
								basisInfo,
								inScalars,
								equalSums,
								set_order.SubsetRefl,
								linear_independence.IndependentUniqueCoefficients.Read(integerModule).AsFact().At(
									E,
									E,
									c.TermAs[Fun[A, A]]("λz:A. integer_map(field_ring(L), p(z))"),
									c.TermAs[Fun[A, A]]("λz:A. integer_map(field_ring(L), q(z))"))))
					}))
				agree := b.Have(
					"integer-map injectivity gives equality of the original coefficients",
					"∀z:A. z ∈ E ⇒ p(z) = q(z)",
					BySets(
						coefficients,
						integerInjective,
						functions.InjectiveOnDef.At(
							b.TermAs[Set[Int]]("𝕌"), b.TermAs[Fun[Int, A]]("integer_map(field_ring(L))"))))
				b.Show(
					"the maps agree on E and both are zero outside E",
					Funext(),
					BySets(agree, mapsDef, equalImages))
			}))
		imageBasis := a.Have(
			"the basis image is the image of the strict index segment",
			"E = image(e, s)",
			BySets(basisDef, sDef))
		finiteIndices := a.Have(
			"the index segment is finite",
			"finite(s)",
			By(sDef, num_segment.FiniteBelowStrict.At(n)))
		weightedIn := a.Have(
			"each weighted basis vector belongs to the integer module",
			Statement{
				Binders: "∀h:(A → int). ∀i:num.",
				Hypotheses: []string{
					"i ∈ s",
				},
				Conclusion: "L.mul(integer_map(field_ring(L), h(e(i))), e(i)) ∈ ring_of_integers(field_ring(L))",
			},
			BySets(Normalized, module.SmulIn.Read(integerModule), scalarIn, imageBasis, independent))
		reindexed := a.Have(
			"the encoding sum reindexes along the distinct basis vectors",
			"∀h:(A → int). "+
				"    f(h) = module_sum(L.add, L.zero, s, λi:num. L.mul(integer_map(field_ring(L), h(e(i))), e(i)))",
			Derive(func(b *Argument) {
				b.FixAs[Fun[A, Int]]("h")
				b.Show(
					"the finite image sum equals the indexed sum",
					By(
						encodeDef,
						imageBasis,
						basisInfo,
						finiteIndices,
						weightedIn,
						module.ModuleSumImage.Read(integerModule).At(
							s, e, b.TermAs[Fun[A, A]]("λz:A. L.mul(integer_map(field_ring(L), h(z)), z)"))))
			}))
		imageBox := a.Have(
			"the encoded pinned maps give exactly the integer coordinate box",
			"image(f, F) = integer_coordinate_box(field_ring(L), n, e, H)",
			Simp(Fwd(set_basic.Extension)),
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				b.Iff()
				b.Forward(
					"an encoded map supplies the indexed box coefficients",
					func(c *Argument, inImage Fact) {
						_, encoded := c.ObtainAs[Fun[A, Int]](
							"take a pinned map encoding this element",
							"∃h:(A → int). h ∈ F ∧ x = f(h)",
							BySets(inImage),
							Named("h"))
						bounded := c.Have(
							"the map values at indexed basis vectors lie in the coefficient interval",
							"∀i:num. i < n ⇒ 0 ≤ h(e(i)) ∧ h(e(i)) ≤ H",
							BySets(Normalized, mapsDef, intervalDef, basisDef, encoded))
						c.Show(
							"these coefficients witness membership in the coordinate box",
							BySets(Normalized, bounded, reindexed, encoded, sDef, integerCoordinateBoxDef.At(R, n, H, e)))
					})
				b.Backward(
					"pinning a box witness on the basis gives an encoding preimage",
					func(c *Argument, inBox Fact) {
						_, coordinates := c.ObtainAs[Fun[Nat, Int]](
							"take the bounded indexed coefficients",
							"∃u:(num → int). "+
								"    (∀i:num. i < n ⇒ 0 ≤ u(i) ∧ u(i) ≤ H) ∧ "+
								"    x = module_sum(L.add, L.zero, s, λi:num. L.mul(integer_map(field_ring(L), u(i)), e(i)))",
							BySets(Normalized, inBox, sDef, integerCoordinateBoxDef.At(R, n, H, e)),
							Named("u"))
						pinnedDef := c.Let("pinned", c.TermAs[Fun[A, Int]]("λv:A. COND(v ∈ E, u(inverse_on(s, e, v)), 0)"))
						inverseIn := c.Have(
							"the inverse index of a basis vector lies in the index segment",
							"∀v:A. v ∈ E ⇒ inverse_on(s, e, v) ∈ s",
							By(
								Normalized,
								imageBasis,
								functions.InverseOnIn.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[A]()).At(s, e)))
						inMaps := c.Have(
							"the pinned map has bounded values on E and zero values elsewhere",
							"pinned ∈ F",
							BySets(Normalized, pinnedDef, mapsDef, intervalDef, sDef, inverseIn, coordinates))
						recovered := c.Have(
							"the inverse index recovers every original indexed coefficient",
							"∀i:num. i ∈ s ⇒ pinned(e(i)) = u(i)",
							BySets(
								Normalized,
								pinnedDef,
								imageBasis,
								basisInfo,
								functions.InverseOnLeft.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[A]()).At(s, e)))
						encoded := c.Have(
							"the pinned map encodes the original box element",
							"f(pinned) = x",
							By(
								Normalized,
								reindexed,
								recovered,
								coordinates,
								module.ModuleSumCongruence.At(
									c.TermAs[Fun[A, Fun[A, A]]]("L.add"),
									c.TermAs[A]("L.zero"),
									s,
									c.TermAs[Fun[Nat, A]]("λi:num. L.mul(integer_map(field_ring(L), pinned(e(i))), e(i))"),
									c.TermAs[Fun[Nat, A]]("λi:num. L.mul(integer_map(field_ring(L), u(i)), e(i))"))))
						c.Show(
							"the pinned map witnesses the image membership",
							BySets(inMaps, encoded))
					})
			}))
		a.Show(
			"injectivity transports the finite map count to the coordinate box",
			By(
				Normalized,
				imageBox,
				encodingInjective,
				mapsSize,
				cardinality.HasSizeImageInj.At(f, F, a.TermAs[Nat]("(H + 1) ^ n"))))
	}),
})}

// integerRootFloorBounds places a positive radicand between consecutive nth
// powers: take the greatest natural whose nth power is at most the radicand.
var integerRootFloorBounds = integerRootFloorBoundsThm{family.Add(registry.ProofEntry{
	Name: "integerRootFloorBounds",
	Key:  "prop_d0ee78e93e388dd9",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"0 < m",
			"0 < n",
		},
		Conclusion: "integer_root_floor(m, n) ^ n ≤ m ∧ m < (integer_root_floor(m, n) + 1) ^ n",
	}, func(a *Argument, m, n *Expr[Nat], positive Fact) {
		one := a.TermAs[Nat]("1")
		bounded := a.Have(
			"admissible roots do not exceed the radicand",
			"∀r:num. r ^ n ≤ m ⇒ r ≤ m",
			Derive(func(b *Argument) {
				r := b.FixAs[Nat]()
				b.Show(
					"a positive power is at least its base",
					ByArith(positive, nat_order.LessEqSelfPow.At(r, n)))
			}))
		nonempty := a.Have(
			"one is an admissible root",
			"∃r:num. r ^ n ≤ m",
			Witness(one),
			ByArith(positive, nat_arith.OnePow.At(n)))
		boundedAbove := a.Have(
			"the admissible roots are bounded above",
			"∃M:num. ∀r:num. r ^ n ≤ m ⇒ r ≤ M",
			Witness(m),
			By(bounded))
		h, maximum := a.ObtainAs[Nat](
			"take the greatest admissible root",
			"∃h:num. h ^ n ≤ m ∧ (∀x:num. x ^ n ≤ m ⇒ x ≤ h)",
			By(boundedAbove, nonempty, nat_order.MaximumExists.At(a.TermAs[Set[Nat]]("λx:num. x ^ n ≤ m"))),
			Named("h"))
		parts := a.Conjuncts(
			maximum,
			"the root is admissible",
			"every admissible root is at most h")
		upper := a.Have(
			"the successor is not admissible",
			"m < (h + 1) ^ n",
			ByArith(parts[1].At(a.TermAs[Nat]("h + 1"))))
		enclosed := a.Have(
			"adjacent powers enclose the radicand",
			"∃k:num. k ^ n ≤ m ∧ m < (k + 1) ^ n",
			Witness(h),
			By(upper, parts[0]))
		a.Show(
			"the defining choice has the adjacent-power bounds",
			Simp(Fwd(integerRootFloorDef)),
			BySets(HilbertDenoted, enclosed))
	}),
})}

// smallCoordinateIdealElement takes two box vectors in the same ideal coset:
// the box of coordinates between zero and the floor root r of N(I) has
// (r+1)^n > N(I) points, more than the N(I) cosets of I, so two distinct box
// vectors share a coset. Their nonzero difference lies in the ideal, and its
// coordinates are differences of integers between zero and r.
var smallCoordinateIdealElement = smallCoordinateIdealElementThm{family.Add(registry.ProofEntry{
	Name: "smallCoordinateIdealElement",
	Key:  "prop_ddd46fe964ad5644",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀n:num. ∀e:(num → A). ∀I:set(A).",
		Hypotheses: []string{
			"number_field(L)",
			"integral_basis(field_ring(L), n, e)",
			"ring_ideal(«R», I)",
			"I ≠ {L.zero}",
		},
		Conclusion: "∃a:A. " +
			"    a ∈ I ∧ " +
			"    a ≠ L.zero ∧ " +
			"    (∀i:num. " +
			"        i < n ⇒ " +
			"        int_abs(integer_value(field_ring(L), " +
			"                module_basis_coordinates( " +
			"                    restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
			"                    restrict_module(regular_module(field_ring(L)), «O»), " +
			"                    {e(j) | j:num | j < n}, " +
			"                    a, " +
			"                    e(i)))) ≤ " +
			"        int_of_num(integer_root_floor(number_ideal_norm(field_ring(L), I), n)))",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		n *Expr[Nat],
		e *Arrow[Nat, A],
		I *Expr[Set[A]],
		given Fact,
	) {
		fieldL := a.TermAs[field.FieldOps[A]]("L")
		fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
		integerRing := a.TermAs[RingOps[A]]("«R»")
		integerScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), integer_image(field_ring(L)))")
		integerModuleTerm := a.TermAs[module_record.ModuleOps[A, A]](
			"restrict_module(regular_module(field_ring(L)), «O»)")
		additiveGroupTerm := a.TermAs[group.GroupOps[A]]("additive_group(«R»)")
		s, sDef := a.LetAs[Set[Nat]]("s", "{i:num | i < n}")
		E, basisDef := a.LetAs[Set[A]]("E", "{e(i):A | i:num | i < n}")
		m, normDef := a.LetAs[Nat]("m", "number_ideal_norm(field_ring(L), I)")
		r, rootDef := a.LetAs[Nat]("r", "integer_root_floor(m, n)")
		B, boxDef := a.LetAs[Set[A]]("B", "integer_coordinate_box(field_ring(L), n, e, r)")
		Q, quotientDef := a.LetAs[Set[Set[A]]]("Q", "left_cosets(L.add, «O», I)")
		q, cosetDef := a.LetAs[Fun[A, Set[A]]]("q", "λv:A. left_coset(L.add, v, I)")
		scalars := a.Conjuncts(
			GroupPremises(L, given, number_field.NumberFieldScalars.At(fieldL)),
			"L has characteristic zero",
			"its rational image is a subfield",
			"the integer image lies in the rational image",
			"the integer image is a commutative ring",
			"and a principal ideal domain",
			"L is a module over the integer image",
			"and over the rational image")
		charZero, scalarRing := scalars[0], scalars[3]
		structure := a.Have(
			"the integer ring is a subring containing the integer scalars",
			"«O» ⊆ L.carrier ∧ comm_ring_on(«R») ∧ integer_image(field_ring(L)) ⊆ «O»",
			By(
				given,
				integral_closure.IntegralClosureSubring.Read(L),
				comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(a.TermAs[Set[A]]("«O»"))))
		integersInL := a.Have(
			"so the integer scalars lie in the field",
			"integer_image(field_ring(L)) ⊆ L.carrier",
			BySets(structure))
		moduleOn := a.Conjuncts(
			GroupPremises(L, given, ring_of_integers.RingOfIntegersIntegerModule.At(fieldL)),
			"the integer ring is closed under integer scalars",
			"the integer ring is an integer module")[1]
		indexed := a.Have(
			"the integral basis is an indexed integer-module basis",
			"indexed_module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), «O»), "+
				"    n, "+
				"    e)",
			By(given, ring_of_integers.IntegralBasisDef.At(fieldRing, n, e)))
		basisInfo := a.Have(
			"the basis image is finite and its indexed vectors are distinct",
			"finite(E) ∧ "+
				"card(E) = n ∧ "+
				"module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), «O»), "+
				"    E) ∧ "+
				"injective_on(s, e)",
			By(
				basisDef,
				sDef,
				indexed,
				linear_independence.IndexedBasisImage.At(integerScalars, integerModuleTerm, n, e)))
		basisIn := a.Have(
			"the basis vectors lie in the integer ring",
			"E ⊆ «O»",
			BySets(basisInfo, linear_independence.BasisInCarrier.At(integerScalars, integerModuleTerm, E)))
		oneNonzero := a.Have(
			"the integer ring contains the nonzero field unit",
			"L.one ∈ «O» ∧ L.one ≠ L.zero",
			By(structure, comm_ring.OneIn.Inst[A]().At(integerRing), field.OneNotZeroOn.Read(L)))
		positiveRank := a.Have(
			"a module containing the nonzero unit has positive basis length",
			"0 < n",
			Derive(func(b *Argument) {
				nonpositive := b.SupposeNot()
				zeroRank := b.Have(
					"a natural number that is not positive is zero",
					"n = 0",
					ByArith(nonpositive))
				empty := b.Have(
					"a zero-length basis has empty image",
					"E = ∅",
					BySets(basisDef, zeroRank, nat_order.LessThanZeroClause))
				expansion := b.Have(
					"the unit has its basis expansion",
					"module_sum(L.add, "+
						"    L.zero, "+
						"    E, "+
						"    λy:A. "+
						"        L.mul(module_basis_coordinates( "+
						"                restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"                restrict_module(regular_module(field_ring(L)), «O»), "+
						"                E, "+
						"                L.one, "+
						"                y), "+
						"            y)) = "+
						"L.one",
					By(
						basisInfo,
						oneNonzero,
						module_dimension.BasisCoordinatesSpec.Read(moduleOn).AsFact().At(E, b.TermAs[A]("L.one"))))
				b.Show(
					"the empty expansion would make the unit zero",
					By(
						Normalized,
						empty,
						expansion,
						oneNonzero,
						module.ModuleSumEmpty.At(
							b.TermAs[Op[A]]("L.add"),
							b.TermAs[A]("L.zero"),
							b.TermAs[Fun[A, A]](
								"λy:A. "+
									"    L.mul(module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
									"            restrict_module(regular_module(field_ring(L)), «O»), "+
									"            E, "+
									"            L.one, "+
									"            y), "+
									"        y)"))))
			}))
		quotientCount := a.Have(
			"the nonzero ideal has a finite quotient of positive norm",
			"0 < m ∧ finite(Q) ∧ card(Q) = m",
			By(
				Normalized,
				normDef,
				quotientDef,
				given,
				ideal_norm.IdealNormPositive.Read(L).At(I),
				ring_of_integers.NonzeroIdealFiniteIndex.Read(L).At(I),
				ideal_norm.IdealNormDef.At(fieldRing, I)))
		larger := a.Have(
			"the floor-root box has more points than the ideal norm",
			"m < (r + 1) ^ n",
			By(Normalized, positiveRank, quotientCount, rootDef, integerRootFloorBounds.At(m, n)))
		boxCount := a.Have(
			"the finite box has the expected product cardinality",
			"finite(B) ∧ card(B) = (r + 1) ^ n",
			By(
				Normalized,
				boxDef,
				given,
				integerBoxCardinality.Read(L).At(n, r, e),
				cardinality.HasSizeDef.Inst[A]().At(B, a.TermAs[Nat]("(r + 1) ^ n"))))
		finiteIndices := a.Have(
			"the strict index segment is finite",
			"finite(s)",
			By(sDef, num_segment.FiniteBelowStrict.At(n)))
		scalarIn := a.Have(
			"every integer coefficient lies in the integer scalar image",
			"∀z:int. "+
				"    integer_map(field_ring(L), z) ∈ "+
				"    restrict_ring(field_ring(L), integer_image(field_ring(L))).carrier",
			Simp(Fwd(module_record.RestrictRingDef), Fwd(module_record.RingCarrierDef)),
			BySets(characteristic_zero.IntegerImageDef.At(fieldRing)))
		imageBasis := a.Have(
			"the basis image is the image of the index segment",
			"E = image(e, s)",
			BySets(basisDef, sDef))
		weightedIn := a.Have(
			"integer multiples of indexed basis vectors lie in the integer ring",
			"∀c:(num → int). ∀i:num. i ∈ s ⇒ L.mul(integer_map(field_ring(L), c(i)), e(i)) ∈ «O»",
			BySets(Normalized, scalarIn, imageBasis, basisIn, module.SmulIn.Read(moduleOn)))
		boxIn := a.Have(
			"every box vector lies in the integer ring",
			"B ⊆ «O»",
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				inBox := b.Assume()
				_, coordinates := b.ObtainAs[Fun[Nat, Int]](
					"take the indexed coefficients of the box vector",
					"∃c:(num → int). "+
						"    (∀i:num. i < n ⇒ 0 ≤ c(i) ∧ c(i) ≤ r) ∧ "+
						"    x = module_sum(L.add, L.zero, s, λi:num. L.mul(integer_map(field_ring(L), c(i)), e(i)))",
					BySets(Normalized, boxDef, sDef, inBox, integerCoordinateBoxDef.At(fieldRing, n, r, e)),
					Named("c"))
				b.Show(
					"a finite sum of integer-module vectors lies in the integer module",
					By(
						Normalized,
						finiteIndices,
						weightedIn,
						coordinates,
						module.ModuleSumIn.Read(moduleOn).At(
							s, b.TermAs[Fun[Nat, A]]("λi:num. L.mul(integer_map(field_ring(L), c(i)), e(i))"))))
			}))
		additiveGroup := a.Have(
			"the integer ring is an additive group",
			"group_on(additive_group(«R»))",
			By(
				structure,
				comm_ring.AddGroupOn.Inst[A]().At(integerRing),
				abelian_group.GroupOn.Inst[A]().At(additiveGroupTerm)))
		idealIn := a.Have(
			"the ideal lies in the integer ring",
			"I ⊆ «O»",
			BySets(given, ring_ideal.IdealSubset.At(integerRing, I)))
		cosetsIn := a.Have(
			"the coset map sends the box into the ideal quotient",
			"image(q, B) ⊆ Q",
			BySets(
				Normalized,
				cosetDef,
				quotientDef,
				boxIn,
				idealIn,
				quotient_group.LeftCosetInLeftCosets.Read(additiveGroup).AsFact().At(I)))
		collision := a.Have(
			"the coset map cannot be injective on the larger box",
			"¬injective_on(B, q)",
			Derive(func(b *Argument) {
				injective := b.SupposeNot()
				imageCount := b.Have(
					"an injective coset map would preserve the box cardinality",
					"card(image(q, B)) = card(B)",
					By(injective, boxCount, cardinality.CardImageInj.At(q, B)))
				atMost := b.Have(
					"the image has at most as many points as the quotient",
					"card(image(q, B)) ≤ card(Q)",
					By(quotientCount, cosetsIn, cardinality.CardSubset.At(b.TermAs[Set[Set[A]]]("image(q, B)"), Q)))
				b.Show(
					"the cardinal inequalities contradict the strict box bound",
					ByArith(imageCount, atMost, larger, boxCount, quotientCount))
			}))
		u, v, collided := a.Obtain2As[A, A](
			"take distinct box vectors with equal ideal cosets",
			"∃u v:A. u ∈ B ∧ v ∈ B ∧ q(u) = q(v) ∧ u ≠ v",
			By(collision, functions.InjectiveOnDef.At(B, q)),
			Named("u", "v"))
		idealSubgroup := a.Have(
			"the ideal is an additive subgroup of the integer ring",
			"subgroup(additive_group(«R»), I)",
			By(
				Normalized,
				given,
				idealIn,
				structure,
				group.SubgroupDef.At(additiveGroupTerm, I),
				ring_ideal.IdealZero.At(integerRing, I),
				ring_ideal.IdealAdd.Inst[A]().At(integerRing, I),
				ring_ideal.IdealNeg.Inst[A]().At(integerRing, I)))
		vectorsIn := a.Have(
			"both collision vectors lie in the integer ring",
			"u ∈ «O» ∧ v ∈ «O»",
			BySets(collided, boxIn))
		delta, differenceDef := a.LetAs[A]("delta", "L.add(L.neg(u), v)")
		differenceIn := a.Have(
			"equal cosets put the difference in the ideal",
			"delta ∈ I",
			By(
				Normalized,
				differenceDef,
				cosetDef,
				collided,
				vectorsIn,
				idealSubgroup,
				group.LeftCosetEqOn.Read(additiveGroup).AsFact().At(u, v, I)))
		nonzero := a.Have(
			"distinct collision vectors give a nonzero difference",
			"delta ≠ L.zero",
			By(
				Normalized,
				differenceDef,
				collided,
				vectorsIn,
				group.InvMulEqOneOn.Read(additiveGroup).AsFact().At(u, v)))
		differenceCarrier := a.Have(
			"the difference and the negated first vector lie in the integer ring",
			"delta ∈ «O» ∧ L.neg(u) ∈ «O»",
			BySets(differenceIn, idealIn, vectorsIn, structure, comm_ring.NegIn.Inst[A]().At(integerRing, u)))
		boxCoordinates := a.Have(
			"box witnesses are the actual bounded integer basis coefficients",
			Statement{
				Binders: "∀x:A.",
				Hypotheses: []string{
					"x ∈ B",
				},
				Conclusion: "∃w:(num → int). " +
					"    (∀i:num. i < n ⇒ 0 ≤ w(i) ∧ w(i) ≤ r) ∧ " +
					"    (∀i:num. " +
					"        i < n ⇒ " +
					"        module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
					"            restrict_module(regular_module(field_ring(L)), «O»), " +
					"            E, " +
					"            x, " +
					"            e(i)) = " +
					"        integer_map(field_ring(L), w(i)))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inBox := b.Assume()
				w, supplied := b.ObtainAs[Fun[Nat, Int]](
					"take the supplied bounded indexed coefficients",
					"∃w:(num → int). "+
						"    (∀i:num. i < n ⇒ 0 ≤ w(i) ∧ w(i) ≤ r) ∧ "+
						"    x = module_sum(L.add, L.zero, s, λi:num. L.mul(integer_map(field_ring(L), w(i)), e(i)))",
					BySets(Normalized, boxDef, sDef, inBox, integerCoordinateBoxDef.At(fieldRing, n, r, e)),
					Named("w"))
				coeff, coeffDef := b.LetAs[Fun[A, A]](
					"coeff", "λz:A. COND(z ∈ E, integer_map(field_ring(L), w(inverse_on(s, e, z))), L.zero)")
				scalarGuards := b.Have(
					"the pinned coefficients are scalars on E and zero off E",
					"(∀z:A. z ∈ E ⇒ coeff(z) ∈ restrict_ring(field_ring(L), integer_image(field_ring(L))).carrier) ∧ "+
						"(∀z:A. z ∉ E ⇒ coeff(z) = restrict_ring(field_ring(L), integer_image(field_ring(L))).zero)",
					Derive(func(c *Argument) {
						zero := c.Have(
							"the restricted scalar ring has the field zero",
							"restrict_ring(field_ring(L), integer_image(field_ring(L))).zero = L.zero",
							Simp(Fwd(module_record.RestrictRingDef), Fwd(module_record.RingZeroDef), Fwd(field.FieldRingDef)),
							Refl())
						c.Show(
							"the conditional chooses a scalar on E and the common zero outside E",
							BySets(Normalized, coeffDef, scalarIn, zero))
					}))
				recovered := b.Have(
					"injectivity of the indexing recovers the original coefficients",
					"∀i:num. i ∈ s ⇒ coeff(e(i)) = integer_map(field_ring(L), w(i))",
					BySets(
						Normalized,
						coeffDef,
						imageBasis,
						basisInfo,
						functions.InverseOnLeft.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[A]()).At(s, e)))
				weighted := b.Have(
					"the recovered weighted coefficients lie in the integer ring",
					"∀i:num. i ∈ s ⇒ L.mul(coeff(e(i)), e(i)) ∈ «O»",
					By(Normalized, weightedIn, recovered))
				expansion := b.Have(
					"the pinned basis sum is the supplied indexed sum",
					"module_sum(L.add, L.zero, E, λz:A. L.mul(coeff(z), z)) = x",
					By(
						Normalized,
						imageBasis,
						finiteIndices,
						basisInfo,
						recovered,
						weighted,
						supplied,
						module.ModuleSumImage.Read(moduleOn).At(s, e, b.TermAs[Fun[A, A]]("λz:A. L.mul(coeff(z), z)")),
						module.ModuleSumCongruence.At(
							b.TermAs[Op[A]]("L.add"),
							b.TermAs[A]("L.zero"),
							s,
							b.TermAs[Fun[Nat, A]]("λi:num. L.mul(coeff(e(i)), e(i))"),
							b.TermAs[Fun[Nat, A]]("λi:num. L.mul(integer_map(field_ring(L), w(i)), e(i))"))))
				xIn := b.Have(
					"the box vector belongs to the integer module",
					"x ∈ «O»",
					BySets(inBox, boxIn))
				unique := b.Have(
					"coordinate uniqueness identifies the pinned coefficient map",
					"module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    restrict_module(regular_module(field_ring(L)), «O»), "+
						"    E, "+
						"    x) = "+
						"coeff",
					By(
						basisInfo,
						xIn,
						scalarGuards,
						expansion,
						module_dimension.BasisCoordinatesUnique.Read(moduleOn).AsFact().At(E, x, coeff)))
				b.Take(w)
				b.Show(
					"the supplied indexed integers are the chosen basis coefficients",
					BySets(Normalized, supplied, unique, recovered, sDef))
			}))
		_, firstCoordinates := a.UnpackAs[Fun[Nat, Int]](GroupPremises(collided, boxCoordinates.At(u)), "p")
		_, secondCoordinates := a.UnpackAs[Fun[Nat, Int]](
			GroupPremises(collided, boxCoordinates.At(v)), "k")
		added := a.Have(
			"coordinates add for the negated first vector and the second vector",
			"module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), «O»), "+
				"    E, "+
				"    delta) = "+
				"λz:A. "+
				"    L.add(module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"            restrict_module(regular_module(field_ring(L)), «O»), "+
				"            E, "+
				"            L.neg(u), "+
				"            z), "+
				"        module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"            restrict_module(regular_module(field_ring(L)), «O»), "+
				"            E, "+
				"            v, "+
				"            z))",
			By(
				differenceDef,
				basisInfo,
				differenceCarrier,
				vectorsIn,
				module_dimension.BasisCoordinatesAdd.Read(moduleOn).AsFact().At(E, a.TermAs[A]("L.neg(u)"), v)))
		minusOneIn := a.Have(
			"minus one is an integer scalar",
			"L.neg(L.one) ∈ restrict_ring(field_ring(L), integer_image(field_ring(L))).carrier",
			By(
				scalarRing,
				comm_ring.OneIn.Inst[A]().At(integerScalars),
				comm_ring.NegIn.Inst[A]().At(
					integerScalars, a.TermAs[A]("restrict_ring(field_ring(L), integer_image(field_ring(L))).one"))))
		negated := a.Have(
			"coordinates of the negated vector are minus one times its coordinates",
			"module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), «O»), "+
				"    E, "+
				"    L.neg(u)) = "+
				"λz:A. "+
				"    L.mul(L.neg(L.one), "+
				"        module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"            restrict_module(regular_module(field_ring(L)), «O»), "+
				"            E, "+
				"            u, "+
				"            z))",
			By(
				basisInfo,
				vectorsIn,
				minusOneIn,
				module_dimension.BasisCoordinatesSmul.Read(moduleOn).AsFact().At(E, a.TermAs[A]("L.neg(L.one)"), u),
				module.NegOneSmul.Read(moduleOn).AsFact().At(u)))
		differenceCoordinates := a.Have(
			"the difference coordinates are images of differences of bounded integers",
			Statement{
				Binders: "∀i:num.",
				Hypotheses: []string{
					"i < n",
				},
				Conclusion: "module_basis_coordinates( " +
					"    restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
					"    restrict_module(regular_module(field_ring(L)), «O»), " +
					"    E, " +
					"    delta, " +
					"    e(i)) = " +
					"integer_map(field_ring(L), -p(i) + k(i))",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				index := b.Assume()
				coefficientIn := b.Have(
					"the first coordinate is a field element",
					"module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"    restrict_module(regular_module(field_ring(L)), «O»), "+
						"    E, "+
						"    u, "+
						"    e(i)) ∈ "+
						"L.carrier",
					BySets(Normalized, firstCoordinates, index, scalarIn, integersInL))
				embedding := b.Have(
					"the integer map preserves the required sum and negative",
					"integer_map(field_ring(L), -p(i) + k(i)) = "+
						"L.add(integer_map(field_ring(L), -p(i)), integer_map(field_ring(L), k(i))) ∧ "+
						"integer_map(field_ring(L), -p(i)) = L.neg(integer_map(field_ring(L), p(i)))",
					By(field.RingOn.Read(L), characteristic_zero.IntegerMapHom.Inst[A]().At(fieldRing)))
				b.Show(
					"additivity and the minus-one identities give the integer difference",
					By(
						Normalized,
						added,
						negated,
						firstCoordinates,
						secondCoordinates,
						index,
						embedding,
						coefficientIn,
						field.RingOn.Read(L),
						comm_ring.NegOneMulOn.Inst[A]().At(
							fieldRing,
							b.TermAs[A](
								"module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
									"    restrict_module(regular_module(field_ring(L)), «O»), "+
									"    E, "+
									"    u, "+
									"    e(i))"))))
			}))
		bounded := a.Have(
			"the difference of two box coefficients has absolute value at most the floor root",
			Statement{
				Binders: "∀i:num.",
				Hypotheses: []string{
					"i < n",
				},
				Conclusion: "int_abs(integer_value(field_ring(L), " +
					"        module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
					"            restrict_module(regular_module(field_ring(L)), «O»), " +
					"            E, " +
					"            delta, " +
					"            e(i)))) ≤ " +
					"r",
			},
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				index := b.Assume()
				value := b.Have(
					"the chosen integer coordinate is the difference of the supplied integers",
					"integer_value(field_ring(L), "+
						"    module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"        restrict_module(regular_module(field_ring(L)), «O»), "+
						"        E, "+
						"        delta, "+
						"        e(i))) = "+
						"-p(i) + k(i)",
					By(
						differenceCoordinates.At(i),
						index,
						charZero,
						characteristic_zero.IntegerValueLeftInverse.Read(field.RingOn.Read(L)).At(
							b.TermAs[Int]("-p(i) + k(i)"))))
				intervals := b.Have(
					"both supplied integers lie between zero and the floor root",
					"0 ≤ p(i) ∧ p(i) ≤ r ∧ 0 ≤ k(i) ∧ k(i) ≤ r",
					By(firstCoordinates, secondCoordinates, index))
				b.Show(
					"the integer interval bounds control the absolute difference",
					ByArith(intervals, value))
			}))
		a.Take(delta)
		a.Show(
			"the nonzero ideal difference has all the required small coordinates",
			By(differenceIn, nonzero, bounded, rootDef, normDef))
	}),
})}

// smallNormIdealElement — a nonzero integral ideal contains a nonzero element
// of field norm bounded by its ideal norm times the class-number bound:
// choose small integral coordinates and compare the floor-root power to the norm.
var smallNormIdealElement = smallNormIdealElementThm{family.Add(registry.ProofEntry{
	Name: "smallNormIdealElement",
	Key:  "prop_ef52a5b47d7ece34",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀n:num. ∀e:(num → A). ∀I:set(A).",
		Hypotheses: []string{
			"number_field(L)",
			"integral_basis(field_ring(L), n, e)",
			"ring_ideal(«R», I)",
			"I ≠ {L.zero}",
		},
		Conclusion: "∃a:A. " +
			"    a ∈ I ∧ " +
			"    a ≠ L.zero ∧ " +
			"    real_abs(rational_value(L, field_norm(field_ring(L), rational_image(L), a))) ≤ " +
			"    real_of_num(class_number_bound(field_ring(L), n, e) * number_ideal_norm(field_ring(L), I))",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		n *Expr[Nat],
		e *Arrow[Nat, A],
		I *Expr[Set[A]],
		given Fact,
	) {
		fieldL := a.TermAs[field.FieldOps[A]]("L")
		fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
		integerScalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), integer_image(field_ring(L)))")
		integerRing := a.TermAs[RingOps[A]]("«R»")
		integerModule := a.TermAs[module_record.ModuleOps[A, A]](
			"restrict_module(regular_module(field_ring(L)), «O»)")
		E := a.TermAs[Set[A]]("{e(i):A | i:num | i < n}")
		x, small := a.UnpackAs[A](
			GroupPremises(given, smallCoordinateIdealElement.Read(L).At(n, e, I)), "x")
		xIntegral := a.Have(
			"the ideal lies in the integer ring",
			"x ∈ «O»",
			BySets(small, given, ring_ideal.IdealSubset.At(integerRing, I)))
		positiveNorm := a.Have(
			"a nonzero integral ideal has positive norm",
			"0 < number_ideal_norm(field_ring(L), I)",
			By(given, ideal_norm.IdealNormPositive.Read(L).At(I)))
		structure := a.Have(
			"the integer ring is a subring containing the integer scalars",
			"«O» ⊆ L.carrier ∧ comm_ring_on(«R») ∧ integer_image(field_ring(L)) ⊆ «O»",
			By(
				given,
				integral_closure.IntegralClosureSubring.Read(L),
				comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(a.TermAs[Set[A]]("«O»"))))
		moduleOn := a.Conjuncts(
			GroupPremises(L, given, ring_of_integers.RingOfIntegersIntegerModule.At(fieldL)),
			"the integer ring is closed under integer scalars",
			"the integer ring is an integer module")[1]
		basis := a.Have(
			"the indexed integral basis gives a finite module basis",
			"finite({e(i):A | i:num | i < n}) ∧ "+
				"module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
				"    restrict_module(regular_module(field_ring(L)), «O»), "+
				"    {e(i):A | i:num | i < n})",
			By(
				given,
				ring_of_integers.IntegralBasisDef.At(fieldRing, n, e),
				linear_independence.IndexedBasisImage.At(integerScalars, integerModule, n, e)))
		oneNonzero := a.Have(
			"the integer ring contains the nonzero field unit",
			"L.one ∈ «O» ∧ L.one ≠ L.zero",
			By(structure, comm_ring.OneIn.Inst[A]().At(integerRing), field.OneNotZeroOn.Read(L)))
		positiveRank := a.Have(
			"a module containing the nonzero unit has positive basis length",
			"0 < n",
			Derive(func(b *Argument) {
				nonpositive := b.SupposeNot()
				zeroRank := b.Have(
					"a natural number that is not positive is zero",
					"n = 0",
					ByArith(nonpositive))
				empty := b.Have(
					"a zero-length basis has empty image",
					"{e(i):A | i:num | i < n} = ∅",
					BySets(zeroRank, nat_order.LessThanZeroClause))
				expansion := b.Have(
					"the unit has its basis expansion",
					"module_sum(L.add, "+
						"    L.zero, "+
						"    {e(i):A | i:num | i < n}, "+
						"    λy:A. "+
						"        L.mul(module_basis_coordinates( "+
						"                restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
						"                restrict_module(regular_module(field_ring(L)), «O»), "+
						"                {e(i):A | i:num | i < n}, "+
						"                L.one, "+
						"                y), "+
						"            y)) = "+
						"L.one",
					By(
						basis,
						oneNonzero,
						module_dimension.BasisCoordinatesSpec.Read(moduleOn).AsFact().At(E, b.TermAs[A]("L.one"))))
				b.Show(
					"the empty expansion would make the unit zero",
					By(
						Normalized,
						empty,
						expansion,
						oneNonzero,
						module.ModuleSumEmpty.At(b.TermAs[Op[A]]("L.add"), b.TermAs[A]("L.zero"),
							b.TermAs[Fun[A, A]](
								"λy:A. "+
									"    L.mul(module_basis_coordinates(restrict_ring(field_ring(L), integer_image(field_ring(L))), "+
									"            restrict_module(regular_module(field_ring(L)), «O»), "+
									"            {e(i):A | i:num | i < n}, "+
									"            L.one, "+
									"            y), "+
									"        y)"))))
			}))
		m := a.TermAs[Nat]("number_ideal_norm(field_ring(L), I)")
		h := a.TermAs[Nat]("integer_root_floor(number_ideal_norm(field_ring(L), I), n)")
		C := a.TermAs[Nat]("class_number_bound(field_ring(L), n, e)")
		rootPower := a.TermAs[Nat]("integer_root_floor(number_ideal_norm(field_ring(L), I), n) ^ n")
		rootBound := a.Have(
			"the floor root raised to the basis length is at most the ideal norm",
			"integer_root_floor(number_ideal_norm(field_ring(L), I), n) ^ n ≤ "+
				"number_ideal_norm(field_ring(L), I)",
			By(positiveNorm, positiveRank, integerRootFloorBounds.At(m, n)))
		coordinateBound := a.Have(
			"the coordinate bounds control the field norm",
			"real_abs(rational_value(L, field_norm(field_ring(L), rational_image(L), x))) ≤ "+
				"real_of_num(class_number_bound(field_ring(L), n, e) * "+
				"    integer_root_floor(number_ideal_norm(field_ring(L), I), n) ^ n)",
			By(xIntegral, small, given, fieldNormCoordinateBound.Read(L).At(n, h, e, x)))
		scaledBound := a.Have(
			"multiply both sides of the floor-root bound by the class-number bound",
			"class_number_bound(field_ring(L), n, e) * "+
				"integer_root_floor(number_ideal_norm(field_ring(L), I), n) ^ n ≤ "+
				"class_number_bound(field_ring(L), n, e) * number_ideal_norm(field_ring(L), I)",
			By(rootBound, nat_order.LessEqMulMono.At(C, rootPower, m)))
		a.Show(
			"the same nonzero element satisfies the required norm bound",
			Witness(x),
			ByArith(
				small,
				coordinateBound,
				scaledBound,
				real_construction.OfNumLessEq.At(
					a.TermAs[Nat](
						"class_number_bound(field_ring(L), n, e) * "+
							"integer_root_floor(number_ideal_norm(field_ring(L), I), n) ^ n"),
					a.TermAs[Nat]("class_number_bound(field_ring(L), n, e) * number_ideal_norm(field_ring(L), I)"))))
	}),
})}
