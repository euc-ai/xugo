// ring_transport.go — a ring carried along a map onto the image of its
// carrier: each operation reads its arguments back through the chosen
// preimage, operates in the source and pushes the result forward, the
// zero and the one are pushed forward, and the six operations and the
// image are packed as one ring record. Along a map injective on the
// carrier the transported operations make the image of every subring a
// ring and the map an isomorphism onto it. A field is carried the same
// way, its inverse and division transported beside the ring operations:
// along a map injective on its carrier the transported record is a
// field, and the map a ring homomorphism from the field to it.

package ring_transport

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// TransportBinaryOpDef — `transport_binary_op(ι, c, op)`: the operation
// op on c read on the image of c under ι — both arguments pulled back to
// c by the chosen preimage, combined in the source, the result pushed
// forward.
var TransportBinaryOpDef = transportBinaryOpDefThm{family.Define(registry.DefEntry{
	Name:  "TransportBinaryOpDef",
	Key:   "prop_dc5c7bf26f1f28fb",
	Const: "transport_binary_op",
	Type:  "(A → B) → set(A) → (A → A → A) → B → B → B",
	Equations: []string{
		"∀ι:(A → B). ∀c:set(A). ∀op:(A → A → A). ∀u v:B. " +
			"    transport_binary_op(ι, c, op, u, v) = ι(op(inverse_on(c, ι, u), inverse_on(c, ι, v)))",
	},
	Reading: "At a point off the image of c the chosen preimage is an unspecified " +
		"value of A, so the operation there is whatever op makes of it; only arguments on " +
		"the image are ever read. On the image, with ι injective on c, the preimage of ι(x) " +
		"is x itself (functions.InverseOnLeft), so ι(x) combined with ι(y) is ι(op(x, y)).",
})}

// transportUnaryOpDef — `transport_unary_op(ι, c, op)`: the map op on c
// read on the image of c under ι — the argument pulled back to c by the
// chosen preimage, mapped in the source, the result pushed forward.
var transportUnaryOpDef = transportUnaryOpDefThm{family.Define(registry.DefEntry{
	Name:  "transportUnaryOpDef",
	Key:   "prop_5bc6e517eb5690be",
	Const: "transport_unary_op",
	Type:  "(A → B) → set(A) → (A → A) → B → B",
	Equations: []string{
		"∀ι:(A → B). ∀c:set(A). ∀op:(A → A). ∀u:B. " +
			"    transport_unary_op(ι, c, op, u) = ι(op(inverse_on(c, ι, u)))",
	},
})}

// TransportRingDef — `transport_ring(ι, R)`: the ring R carried along ι
// as one record — the sum, the negation, the product and the difference
// transported on R's carrier, the zero and the one pushed forward, and
// the carrier `image(ι, R.carrier)`.
var TransportRingDef = transportRingDefThm{family.Define(registry.DefEntry{
	Name:  "TransportRingDef",
	Key:   "prop_e54fc4234e62a460",
	Const: "transport_ring",
	Type:  "(A → B) → ring_ops(A) → ring_ops(B)",
	Equations: []string{
		"∀ι:(A → B). ∀R:ring_ops(A). " +
			"    transport_ring(ι, R) = " +
			"    mk_ring(transport_binary_op(ι, R.carrier, R.add), " +
			"        ι(R.zero), " +
			"        transport_unary_op(ι, R.carrier, R.neg), " +
			"        transport_binary_op(ι, R.carrier, R.mul), " +
			"        ι(R.one), " +
			"        transport_binary_op(ι, R.carrier, R.sub), " +
			"        image(ι, R.carrier))",
	},
	Reading: "The record is a ring only when ι is injective on R's carrier: two points of " +
		"the carrier with one image would make the transported operations choose between them. " +
		"Injectivity off the carrier is never read, since every preimage is chosen in the carrier.",
	Deps: []registry.EntryLike{TransportBinaryOpDef, transportUnaryOpDef},
})}

// TransportBinaryOpAtImage — at the values of two points of c, the
// operation transported on c reads its arguments back as those points
// themselves, so it is ι of the operation at them: the preimage chosen
// in c of ι(x) is x, ι being injective on c (functions.InverseOnLeft).
// TransportBinaryOpDef's reading made a theorem.
var TransportBinaryOpAtImage = transportBinaryOpAtImageThm{family.Add(registry.ProofEntry{
	Name: "TransportBinaryOpAtImage",
	Key:  "prop_405543db47274927",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(A → B). ∀c:set(A). ∀op:(A → A → A). ∀x y:A.",
		Hypotheses: []string{
			"injective_on(c, ι)",
			"x ∈ c",
			"y ∈ c",
		},
		Conclusion: "transport_binary_op(ι, c, op, ι(x), ι(y)) = ι(op(x, y))",
	},
		func(a *Argument, ι *Arrow[A, B], c *Expr[Set[A]], op *Arrow2[A, A, A], x, y *Expr[A], _ Fact) {
			a.Show(
				"the preimages of ι(x) and ι(y) chosen in c are x and y, ι being injective there",
				Simp(Fwd(TransportBinaryOpDef), Fwd(functions.InverseOnLeft)),
				Basic())
		}),
})}

// TransportUnaryOpAtImage — at the value of a point of c, the map
// transported on c reads its argument back as that point itself, so it
// is ι of the map at it: the preimage chosen in c of ι(x) is x, ι being
// injective on c (functions.InverseOnLeft).
var TransportUnaryOpAtImage = transportUnaryOpAtImageThm{family.Add(registry.ProofEntry{
	Name: "TransportUnaryOpAtImage",
	Key:  "prop_9f61de4e9ce81c5b",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(A → B). ∀c:set(A). ∀op:(A → A). ∀x:A.",
		Hypotheses: []string{
			"injective_on(c, ι)",
			"x ∈ c",
		},
		Conclusion: "transport_unary_op(ι, c, op, ι(x)) = ι(op(x))",
	},
		func(a *Argument, ι *Arrow[A, B], c *Expr[Set[A]], op *Arrow[A, A], x *Expr[A], _ Fact) {
			a.Show(
				"the preimage of ι(x) chosen in c is x, ι being injective there",
				Simp(Fwd(transportUnaryOpDef), Fwd(functions.InverseOnLeft)),
				Basic())
		}),
})}

// ---------------------------------------------------------------------------
// The transported ring
// ---------------------------------------------------------------------------

// TransportCommRingOn — along a map injective on R's carrier, the
// transported operations make the image of every subring of R a
// commutative ring; at the whole carrier, the transported record is a
// commutative ring. On the image of c each transported operation reads
// its arguments back as their own preimages, since the preimage is chosen
// in R.carrier, where ι is injective (TransportBinaryOpAtImage and
// TransportUnaryOpAtImage at R.carrier); so ι keeps the sum, the
// negation, the product and the difference, the zero and the one are
// pushed forward by definition, and the image of a commutative ring along
// a map that keeps the six operations is one
// (ring_homomorphism.ImageCommRingOn).
var TransportCommRingOn = transportCommRingOnThm{family.Add(registry.ProofEntry{
	Name: "TransportCommRingOn",
	Key:  "prop_29d898a6540d37ae",
	Reading: "The subring c is read under R's operations, and its image under the transported ones, " +
		"whose preimages are chosen in the whole carrier: injectivity on R.carrier, not on c alone, is " +
		"load-bearing, since a second point of the carrier with the image of a point of c could be the " +
		"one chosen. At c = R.carrier the image is transport_ring(ι, R).carrier; a smaller c is the " +
		"shape of the free algebra on a set of variables inside the one on every variable.",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(A → B). ∀R:ring_ops(A). ∀c:set(A).",
		Hypotheses: []string{
			"injective_on(R.carrier, ι)",
			"c ⊆ R.carrier",
			"comm_ring_on(restrict_ring(R, c))",
		},
		Conclusion: "comm_ring_on(restrict_ring(transport_ring(ι, R), image(ι, c)))",
	},
		func(
			a *Argument,
			ι *Arrow[A, B],
			R *Expr[RingOps[A]],
			c *Expr[Set[A]],
			injective, inCarrier, ring Fact,
		) {
			// The sum, the product and the difference at once: the law
			// holds for every operation on A.
			binary := a.Have(
				"a transported operation of ι(x) and ι(y) is ι of the operation of x and y",
				Statement{
					Binders:    "∀op:(A → A → A). ∀x y:A.",
					Hypotheses: []string{"x ∈ c", "y ∈ c"},
					Conclusion: "ι(op(x, y)) = transport_binary_op(ι, R.carrier, op, ι(x), ι(y))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Op[A]]("op")
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					points := b.Assume()
					inR := b.Have(
						"x and y lie in R.carrier, which holds c",
						"x ∈ R.carrier ∧ y ∈ R.carrier",
						BySets(inCarrier, points))
					b.Show(
						"the preimages of ι(x) and ι(y) chosen in R.carrier are x and y, ι being injective there",
						By(TransportBinaryOpAtImage, injective, inR))
				}))
			negation := a.Have(
				"the transported negation of ι(x) is ι(-x)",
				"∀x:A. x ∈ c ⇒ ι(R.neg(x)) = transport_unary_op(ι, R.carrier, R.neg, ι(x))",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					point := b.Assume()
					inR := b.Have(
						"x lies in R.carrier, which holds c",
						"x ∈ R.carrier",
						BySets(inCarrier, point))
					b.Show(
						"the preimage of ι(x) chosen in R.carrier is x, ι being injective there",
						By(TransportUnaryOpAtImage, injective, inR))
				}))
			transported := a.TermAs[RingOps[B]]("restrict_ring(transport_ring(ι, R), image(ι, c))")
			a.Show(
				"the zero and the one are pushed forward by definition, so ι "+
					"keeps all six operations of the ring on c, and its image is one",
				By(ring_homomorphism.ImageCommRingOn.Read(ring).At(transported, ι), binary, negation))
		}),
})}

// TransportRingIsomorphism — along a map injective on R's carrier, the
// map is a ring isomorphism from every subring of R onto its image
// under the transported operations. The source is a ring by hypothesis
// and the target by TransportCommRingOn; ι sends c into and onto its
// image, the target's carrier by restriction; the transported sum and
// product of ι(x) and ι(y)
// read their arguments back as x and y, which lie in R.carrier ⊇ c
// (TransportBinaryOpAtImage); the transported one is ι(R.one) by
// definition; and ι is injective on c, a part of R.carrier.
var TransportRingIsomorphism = transportRingIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "TransportRingIsomorphism",
	Key:  "prop_2cde80afeb20fa06",
	Reading: "injective_on(c, ι) follows from injectivity on the whole carrier and c ⊆ R.carrier, " +
		"and the image clause is the restriction's carrier; the whole-carrier hypothesis is " +
		"load-bearing, because the transported operations pick their preimages in R.carrier, not in c.",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(A → B). ∀R:ring_ops(A). ∀c:set(A).",
		Hypotheses: []string{
			"injective_on(R.carrier, ι)",
			"c ⊆ R.carrier",
			"comm_ring_on(restrict_ring(R, c))",
		},
		Conclusion: "ring_isomorphism(restrict_ring(R, c), " +
			"    restrict_ring(transport_ring(ι, R), image(ι, c)), " +
			"    ι)",
	},
		func(
			a *Argument,
			ι *Arrow[A, B],
			R *Expr[RingOps[A]],
			c *Expr[Set[A]],
			injective, inCarrier, ring Fact,
		) {
			a.Show(
				"ι is one-to-one from c onto the transported carrier and "+
					"keeps the sum and the product; the transported one is ι(R.one)",
				Unfold(ring_homomorphism.RingIsomorphismDef),
				Unfold(ring_homomorphism.RingHomomorphism),
				SplitConjAll(
					Case(
						"c is a commutative ring under R's operations by hypothesis",
						By(ring)),
					Case(
						"the image of c is a commutative ring under the transported operations",
						By(injective, inCarrier, ring, TransportCommRingOn.At(ι, R, c))),
					Case(
						"each point of c maps into its image",
						By(set_image.FunInImage)),
					Case(
						"the transported sum reads ι(x) and ι(y) back as x and y, points of c and so of R.carrier",
						By(injective, inCarrier, set_basic.SubsetDef, TransportBinaryOpAtImage)),
					Case(
						"the transported product reads ι(x) and ι(y) back as x and y, points of c and so of R.carrier",
						By(injective, inCarrier, set_basic.SubsetDef, TransportBinaryOpAtImage)),
					Case(
						"ι is one-to-one on R.carrier, so on its part c",
						By(injective, inCarrier, functions.InjectiveOnSubset))))
		}),
})}

// ---------------------------------------------------------------------------
// The transported field
// ---------------------------------------------------------------------------

// TransportFieldDef — `transport_field(ι, F)`: the field record F carried
// along ι — the ring operations as in transport_ring, the inverse and the
// division transported on F's carrier the same way, and the carrier
// `image(ι, F.carrier)`.
var TransportFieldDef = transportFieldDefThm{family.Define(registry.DefEntry{
	Name:  "TransportFieldDef",
	Key:   "prop_798e1fb4fd0b8c55",
	Const: "transport_field",
	Type:  "(A → B) → field_ops(A) → field_ops(B)",
	Equations: []string{
		"∀ι:(A → B). ∀F:field_ops(A). " +
			"    transport_field(ι, F) = " +
			"    mk_field(transport_binary_op(ι, F.carrier, F.add), " +
			"        ι(F.zero), " +
			"        transport_unary_op(ι, F.carrier, F.neg), " +
			"        transport_binary_op(ι, F.carrier, F.mul), " +
			"        ι(F.one), " +
			"        transport_binary_op(ι, F.carrier, F.sub), " +
			"        transport_unary_op(ι, F.carrier, F.inv), " +
			"        transport_binary_op(ι, F.carrier, F.div), " +
			"        image(ι, F.carrier))",
	},
	Reading: "Its ring projection field_ring(transport_field(ι, F)) is transport_ring(ι, " +
		"field_ring(F)), field by field, so every ring law above reads the transported field.",
	Deps: []registry.EntryLike{TransportBinaryOpDef, transportUnaryOpDef},
})}

// TransportFieldOn — along a map injective on F's carrier, the
// transported record of a field is a field: its ring is the transported
// ring, and its inverse and division laws are the images of F's laws.
var TransportFieldOn = transportFieldOnThm{family.Add(registry.ProofEntry{
	Name: "TransportFieldOn",
	Key:  "prop_ae3fcbd59e3689a4",
	Reading: "The closure and inverse axioms hold on the image because the " +
		"preimage of ι(x) is x; the axiom inv(zero) = zero is read at ι(F.zero), " +
		"whose preimage is F.zero, so it holds although nothing is said off the image.",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(A → B). ∀F:field_on(A).",
		Hypotheses: []string{
			"injective_on(F.carrier, ι)",
		},
		Conclusion: "field_on(transport_field(ι, F))",
	},
		func(a *Argument, ι *Arrow[A, B], F field.FieldFact[on.F], injective Fact) {
			carrier := a.TermAs[Set[A]]("F.carrier")
			source := a.TermAs[FieldOps[A]]("F")
			ringRecord := a.TermAs[RingOps[A]]("field_ring(F)")
			ring := field.RingOn.Read(F)
			inverse := a.TermAs[Fun[A, A]]("F.inv")
			product := a.TermAs[Op[A]]("F.mul")
			division := a.TermAs[Op[A]]("F.div")
			a.Show(
				"the ring and the inverse axioms hold on the image carrier",
				Simp(Fwd(field.FieldOn)),
				SplitConjAll(
					Case(
						"the ring projection is the transported commutative ring",
						Derive(func(b *Argument) {
							imageRing := b.Have(
								"the full carrier transports to a commutative ring on its image",
								"comm_ring_on(restrict_ring(transport_ring(ι, field_ring(F)), image(ι, F.carrier)))",
								By(
									ring,
									injective,
									TransportCommRingOn.At(ι, ringRecord, carrier),
									module_record.RestrictRingCarrier.At(ringRecord),
									field.FieldRingDef.At(source),
									set_order.SubsetRefl.At(carrier)))
							simplified := b.Simplified(
								imageRing,
								Fwd(field.FieldRingDef),
								Fwd(TransportRingDef),
								Fwd(module_record.RestrictRingDef))
							b.Show(
								"the transported field has exactly these ring operations and carrier",
								Simp(Fwd(field.FieldRingDef), Fwd(TransportFieldDef)),
								By(simplified))
						})),
					Case(
						"the image carrier is closed under inverse",
						Simp(Fwd(set_image.ForallInImage)),
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							xF := b.MemberOf[on.F](x, b.Assume())
							invX := field.InvIn.Read(F).At(xF)
							b.Show(
								"the inverse of ι(x) is the image of the source inverse",
								By(
									Normalized,
									injective,
									xF,
									invX,
									TransportUnaryOpAtImage.At(ι, carrier, inverse, x),
									set_image.FunInImage.At(ι, carrier, invX)))
						})),
					Case(
						"injectivity keeps the images of one and zero distinct",
						By(
							field.OneNotZeroOn.Read(F),
							comm_ring.OneIn.Read(ring),
							comm_ring.ZeroIn.Read(ring),
							injective,
							functions.InjectiveOnDef.At(carrier, ι))),
					Case(
						"a nonzero image point has a left inverse",
						Simp(Fwd(set_image.ForallInImage)),
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							xF := b.MemberOf[on.F](x, b.Assume())
							nonzero := b.Assume()
							invX := field.InvIn.Read(F).At(xF)
							b.Show(
								"the source inverse equation transfers to ι(x)",
								By(
									Normalized,
									nonzero,
									injective,
									xF,
									invX,
									field.MulLeftInverseOn.Read(F).At(xF),
									TransportUnaryOpAtImage.At(ι, carrier, inverse, x),
									TransportBinaryOpAtImage.At(ι, carrier, product, invX, x)))
						})),
					Case(
						"the inverse of the transported zero is zero",
						By(
							comm_ring.ZeroIn.Read(ring),
							field.InvZeroOn.Read(F),
							injective,
							TransportUnaryOpAtImage.At(ι, carrier, inverse, a.TermAs[A]("F.zero")))),
					Case(
						"division is multiplication by the transported inverse",
						Simp(Fwd(set_image.ForallInImagePair)),
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							y := b.FixAs[A]("y")
							points := b.Conjuncts(
								b.Assume(),
								"x lies in F",
								"y lies in F")
							xF, yF := b.MemberOf[on.F](x, points[0]), b.MemberOf[on.F](y, points[1])
							invY := field.InvIn.Read(F).At(yF)
							b.Show(
								"the source division equation transfers to ι(x) and ι(y)",
								By(
									Normalized,
									injective,
									xF,
									yF,
									invY,
									field.DivMulInvOn.Read(F).At(xF, yF),
									TransportUnaryOpAtImage.At(ι, carrier, inverse, y),
									TransportBinaryOpAtImage.At(ι, carrier, division, x, y),
									TransportBinaryOpAtImage.At(ι, carrier, product, x, invY)))
						}))))
		}),
})}

// TransportFieldHomomorphism — along a map injective on a field's
// carrier, the map is a ring homomorphism from the field to its
// transported field. Both are the rings of fields, the transported record
// a field by TransportFieldOn; ι sends the carrier into its image, the
// transported carrier; the transported sum and product of ι(x) and ι(y)
// read their arguments back as x and y, ι being injective on the carrier
// (TransportBinaryOpAtImage); and the transported one is ι(F.one) by
// definition.
var TransportFieldHomomorphism = transportFieldHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "TransportFieldHomomorphism",
	Key:  "prop_ab90e47987f269e",
	Build: family.Theorem(Statement{
		Binders: "∀ι:(A → B). ∀F:field_on(A).",
		Hypotheses: []string{
			"injective_on(F.carrier, ι)",
		},
		Conclusion: "ring_homomorphism(field_ring(F), field_ring(transport_field(ι, F)), ι)",
	},
		func(a *Argument, ι *Arrow[A, B], F field.FieldFact[on.F], injective Fact) {
			carrier := a.TermAs[Set[A]]("F.carrier")
			transported := a.Have(
				"the transported record is a field",
				"field_on(transport_field(ι, F))",
				By(F, injective, TransportFieldOn.At(ι, a.TermAs[FieldOps[A]]("F"))))
			a.Show(
				"ι keeps the carrier, the sum and the product; the transported one is ι(F.one) by definition",
				Unfold(ring_homomorphism.RingHomomorphism),
				SplitConjAll(
					Case(
						"the source is a commutative ring",
						By(field.RingOn.Read(F))),
					Case(
						"the transported field supplies the target ring",
						By(field.RingOn.Read(transported))),
					Case(
						"each source point maps into the image carrier",
						By(set_image.FunInImage)),
					Case(
						"the transported sum reads ι(x) and ι(y) back as x and y",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							y := b.FixAs[A]("y")
							points := b.Assume()
							b.Show(
								"x and y lie in the carrier, where ι is injective",
								By(injective, points, TransportBinaryOpAtImage.At(ι, carrier, b.TermAs[Op[A]]("F.add"), x, y)))
						})),
					Case(
						"the transported product reads ι(x) and ι(y) back as x and y",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							y := b.FixAs[A]("y")
							points := b.Assume()
							b.Show(
								"x and y lie in the carrier, where ι is injective",
								By(injective, points, TransportBinaryOpAtImage.At(ι, carrier, b.TermAs[Op[A]]("F.mul"), x, y)))
						}))))
		}),
})}
