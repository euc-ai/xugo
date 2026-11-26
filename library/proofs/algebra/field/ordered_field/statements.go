package ordered_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_transport"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// OrderedFieldOn — A field with a strict linear order compatible with addition and positive multiplication.
var OrderedFieldOn = orderedFieldOnThm{family.DefineStructure(registry.DefEntry{
	Name: "OrderedFieldOn", Const: "ordered_field_on", Type: "field_ops(A) → (A → A → bool) → bool",
	Key: "prop_138f0d8eef57e675",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). " +
			"    ordered_field_on(F, lt) ⇔ " +
			"    field_on(F) ∧ " +
			"    (∀x:A. x ∈ F.carrier ⇒ ¬lt(x, x)) ∧ " +
			"    (∀x y z:A. " +
			"        x ∈ F.carrier ∧ y ∈ F.carrier ∧ z ∈ F.carrier ∧ lt(x, y) ∧ lt(y, z) ⇒ lt(x, z)) ∧ " +
			"    (∀x y:A. x ∈ F.carrier ∧ y ∈ F.carrier ⇒ lt(x, y) ∨ x = y ∨ lt(y, x)) ∧ " +
			"    (∀x y z:A. " +
			"        x ∈ F.carrier ∧ y ∈ F.carrier ∧ z ∈ F.carrier ∧ lt(x, y) ⇒ " +
			"        lt(F.add(x, z), F.add(y, z))) ∧ " +
			"    (∀x y:A. " +
			"        x ∈ F.carrier ∧ y ∈ F.carrier ∧ lt(F.zero, x) ∧ lt(F.zero, y) ⇒ lt(F.zero, F.mul(x, y)))",
	},
})}

// OrderedLeDef — The weak order associated to a strict order.
var OrderedLeDef = orderedLeDefThm{family.Define(registry.DefEntry{
	Name: "OrderedLeDef", Const: "ordered_le", Type: "(A → A → bool) → A → A → bool",
	Key:       "prop_9f7c5639161b6335",
	Equations: []string{"∀lt:(A → A → bool). ∀x y:A. ordered_le(lt, x, y) ⇔ x = y ∨ lt(x, y)"},
})}

// OrderedEmbeddingDef — An embedding preserves ring operations and preserves and reflects strict order.
var OrderedEmbeddingDef = orderedEmbeddingDefThm{family.Define(registry.DefEntry{
	Name:  "OrderedEmbeddingDef",
	Const: "ordered_field_embedding",
	Type:  "field_ops(A) → (A → A → bool) → field_ops(B) → (B → B → bool) → (A → B) → bool",
	Key:   "prop_2839c411db8ed17e",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀G:field_ops(B). ∀ls:(B → B → bool). ∀i:(A → B). " +
			"    ordered_field_embedding(F, lt, G, ls, i) ⇔ " +
			"    ordered_field_on(F, lt) ∧ " +
			"    ordered_field_on(G, ls) ∧ " +
			"    ring_homomorphism(field_ring(F), field_ring(G), i) ∧ " +
			"    injective_on(F.carrier, i) ∧ " +
			"    (∀x y:A. x ∈ F.carrier ∧ y ∈ F.carrier ⇒ (lt(x, y) ⇔ ls(i(x), i(y))))",
	},
	Deps: []registry.EntryLike{OrderedFieldOn},
})}

// TransportOrderDef — Order on an image is read through the chosen preimage in the source carrier.
var TransportOrderDef = transportOrderDefThm{family.Define(registry.DefEntry{
	Name:  "TransportOrderDef",
	Const: "transport_order",
	Type:  "(A → B) → set(A) → (A → A → bool) → B → B → bool",
	Key:   "prop_dfc3665d65434232",
	Equations: []string{
		"∀i:(A → B). ∀C:set(A). ∀lt:(A → A → bool). ∀x y:B. " +
			"    transport_order(i, C, lt, x, y) ⇔ lt(inverse_on(C, i, x), inverse_on(C, i, y))",
	},
})}

// OrderedSignDef — The three-valued sign of a field element.
var OrderedSignDef = orderedSignDefThm{family.Define(registry.DefEntry{
	Name: "OrderedSignDef", Const: "ordered_sign", Type: "field_ops(A) → (A → A → bool) → A → int",
	Key: "prop_f8e17d41ccf9db3c",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀x:A. " +
			"    ordered_sign(F, lt, x) = " +
			"    COND(lt(x, F.zero), -int_of_num(1), COND(x = F.zero, int_of_num(0), 1))",
	},
})}

// FieldOn — An ordered field is a field.
var FieldOn = fieldOnThm{family.Add(registry.ProofEntry{
	Name:  "FieldOn",
	Key:   "prop_2af472caa389686c",
	Build: OrderedFieldOn.Axiom("field_on(F)"),
})}

// Irreflexive — No point of the carrier lies below itself.
var Irreflexive = irreflexiveThm{family.Add(registry.ProofEntry{
	Name: "Irreflexive",
	Key:  "prop_8a9d5b1bdde9c1e3",
	Build: OrderedFieldOn.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
		},
		Conclusion: "¬lt(x, x)",
	}),
})}

// Transitive — The order is transitive on the carrier.
var Transitive = transitiveThm{family.Add(registry.ProofEntry{
	Name: "Transitive",
	Key:  "prop_a58fb68a29b8daae",
	Build: OrderedFieldOn.Axiom(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
			"z ∈ F.carrier",
			"lt(x, y)",
			"lt(y, z)",
		},
		Conclusion: "lt(x, z)",
	}),
})}

// Trichotomy — Two points of the carrier are comparable.
var Trichotomy = trichotomyThm{family.Add(registry.ProofEntry{
	Name: "Trichotomy",
	Key:  "prop_3a545aba7847e7bb",
	Build: OrderedFieldOn.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
		},
		Conclusion: "lt(x, y) ∨ x = y ∨ lt(y, x)",
	}),
})}

// AddPreservesOrder — Adding a point of the carrier preserves the order.
var AddPreservesOrder = addPreservesOrderThm{family.Add(registry.ProofEntry{
	Name: "AddPreservesOrder",
	Key:  "prop_589b92c01b040566",
	Build: OrderedFieldOn.Axiom(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
			"z ∈ F.carrier",
			"lt(x, y)",
		},
		Conclusion: "lt(x + z, y + z)",
	}),
})}

// MulPositive — A product of positive points is positive.
var MulPositive = mulPositiveThm{family.Add(registry.ProofEntry{
	Name: "MulPositive",
	Key:  "prop_c2ef703a0077f83a",
	Build: OrderedFieldOn.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
			"lt(F.zero, x)",
			"lt(F.zero, y)",
		},
		Conclusion: "lt(F.zero, x * y)",
	}),
})}

// OnePositive — One is strictly positive: since 1 ≠ 0, comparability
// leaves 0 < 1 or 1 < 0, and from 1 < 0 adding −1 gives 0 < −1, so that
// 1 = (−1)(−1) is a product of positives after all.
var OnePositive = onePositiveThm{family.Add(registry.ProofEntry{
	Name: "OnePositive",
	Key:  "prop_b7b59de618c34f4",
	Build: OrderedFieldOn.Law("lt(F.zero, F.one)", func(a *Argument, ordered OrderedFieldFact[on.F]) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		zero := a.MemberOf[on.F](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		one := a.MemberOf[on.F](a.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
		minusOne := comm_ring.NegIn.Read(ring).At(one)
		arithmetic := a.Have(
			"1 + (−1) = 0, 0 + (−1) = −1, and (−1)(−1) = 1·1 = 1 by the rule of signs",
			"F.one + -F.one = F.zero ∧ F.zero + -F.one = -F.one ∧ -F.one * -F.one = F.one",
			ByArith(ring, comm_ring.MulNegNegOn.Read(ring).At(one, one)))
		negative := a.Assuming(
			a.TermAs[Bool]("lt(F.one, F.zero)"),
			"if 1 is not below 0, then 0 < 1",
			Given(func(b *Argument, notNegative Fact) {
				b.Show(
					"0 and 1 are comparable, and 1 ≠ 0",
					By(
						Trichotomy.Read(ordered).At(zero, one),
						notNegative,
						field.OneNotZeroOn.Read(FieldOn.Read(ordered))))
			}))
		minusOnePositive := a.Have(
			"adding −1 to 1 < 0 gives 0 < −1",
			"lt(F.zero, -F.one)",
			By(AddPreservesOrder.Read(ordered).At(one, zero, minusOne), negative, arithmetic))
		a.Show(
			"so 1 = (−1)(−1) is a product of positives",
			By(MulPositive.Read(ordered).At(minusOne, minusOne), minusOnePositive, arithmetic))
	}),
})}

// AddOrderIff — Translation preserves and reflects strict order: adding z
// preserves it by the axiom, and adding −z to x + z < y + z gives back x < y.
var AddOrderIff = addOrderIffThm{family.Add(registry.ProofEntry{
	Name: "AddOrderIff",
	Key:  "prop_7d5085c75bc6569d",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
			"z ∈ F.carrier",
		},
		Conclusion: "lt(x + z, y + z) ⇔ lt(x, y)",
	}, func(a *Argument, ordered OrderedFieldFact[on.F], x, y, z *Member[A, on.F]) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		cancel := a.Have(
			"adding −z undoes adding z",
			"(x + z) + -z = x ∧ (y + z) + -z = y",
			ByArith(ring, x, y, z))
		a.Iff()
		a.Forward(
			"adding −z to x + z < y + z gives back x < y",
			func(b *Argument, sums Fact) {
				b.Show(
					"x + z < y + z translated by −z",
					By(
						Normalized,
						AddPreservesOrder.Read(ordered).At(
							comm_ring.AddIn.Read(ring).At(x, z),
							comm_ring.AddIn.Read(ring).At(y, z),
							comm_ring.NegIn.Read(ring).At(z)),
						sums,
						cancel))
			})
		a.Backward(
			"adding z preserves the order",
			func(b *Argument, less Fact) {
				b.Show(
					"x < y translated by z",
					By(AddPreservesOrder.Read(ordered).At(x, y, z), less))
			})
	}),
})}

// WeakOrderTranslation — In an ordered field, adding a carrier value keeps and reflects the weak
// order: it keeps and reflects the strict order, and it is one-to-one.
var WeakOrderTranslation = weakOrderTranslationThm{family.Add(registry.ProofEntry{
	Name: "WeakOrderTranslation",
	Key:  "prop_248c3ce7794cf72f",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
			"z ∈ F.carrier",
		},
		Conclusion: "ordered_le(lt, x + z, y + z) ⇔ ordered_le(lt, x, y)",
	}, func(a *Argument, ordered OrderedFieldFact[on.F], x, y, z *Member[A, on.F]) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		a.Show(
			"the weak order is equality or the strict order, and adding z keeps and reflects both",
			By(
				group.RightCancelOn.Read(abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))).At(z, x, y),
				OrderedLeDef,
				AddOrderIff.Read(ordered).At(x, y, z)))
	}),
})}

// OrderMixedTransitive — In an ordered field the weak order followed by the strict order, or the
// strict order followed by the weak order, is the strict order: where the weak step is an equality
// the strict step is the claim, and otherwise the strict order is transitive.
var OrderMixedTransitive = orderMixedTransitiveThm{family.Add(registry.ProofEntry{
	Name: "OrderMixedTransitive",
	Key:  "prop_2a412abb07cc9e95",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
			"z ∈ F.carrier",
		},
		Conclusion: "(ordered_le(lt, x, y) ∧ lt(y, z) ⇒ lt(x, z)) ∧ " +
			"(lt(x, y) ∧ ordered_le(lt, y, z) ⇒ lt(x, z))",
	}, func(
		a *Argument,
		_ *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		ordered OrderedFieldFact[on.F],
		x, y, z *Member[A, on.F],
	) {
		weakFirst := a.Have(
			"a weak step then a strict step is strict",
			"ordered_le(lt, x, y) ∧ lt(y, z) ⇒ lt(x, z)",
			Derive(func(b *Argument) {
				given := b.Conjuncts(
					b.Assume(),
					"x ≤ y",
					"y < z")
				b.Cases(b.Term("x = y"))
				b.When(
					"where x = y the strict step is the claim",
					func(c *Argument, equal Fact) {
						c.Show(
							"x < z",
							By(Normalized, equal, given[1]))
					})
				b.Otherwise(
					"otherwise x < y, and the strict order is transitive",
					func(c *Argument, apart Fact) {
						below := c.Have(
							"x < y",
							"lt(x, y)",
							By(given[0], apart, OrderedLeDef.At(lt, x, y)))
						c.Show(
							"x < z",
							By(below, given[1], Transitive.Read(ordered).At(x, y, z)))
					})
			}))
		strictFirst := a.Have(
			"a strict step then a weak step is strict",
			"lt(x, y) ∧ ordered_le(lt, y, z) ⇒ lt(x, z)",
			Derive(func(b *Argument) {
				given := b.Conjuncts(
					b.Assume(),
					"x < y",
					"y ≤ z")
				b.Cases(b.Term("y = z"))
				b.When(
					"where y = z the strict step is the claim",
					func(c *Argument, equal Fact) {
						c.Show(
							"x < z",
							By(Normalized, equal, given[0]))
					})
				b.Otherwise(
					"otherwise y < z, and the strict order is transitive",
					func(c *Argument, apart Fact) {
						above := c.Have(
							"y < z",
							"lt(y, z)",
							By(given[1], apart, OrderedLeDef.At(lt, y, z)))
						c.Show(
							"x < z",
							By(given[0], above, Transitive.Read(ordered).At(x, y, z)))
					})
			}))
		a.Show(
			"both mixed chains are strict",
			By(weakFirst, strictFirst))
	}),
})}

// LessThanSelfAddLeft — Adding x to y moves y up exactly when x is positive:
// translation by y sends 0 < x to 0 + y < x + y, and 0 + y = y.
var LessThanSelfAddLeft = lessThanSelfAddLeftThm{family.Add(registry.ProofEntry{
	Name: "LessThanSelfAddLeft",
	Key:  "prop_ca6a10abf77d6b79",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
		},
		Conclusion: "lt(y, x + y) ⇔ lt(F.zero, x)",
	}, func(a *Argument, ordered OrderedFieldFact[on.F], x, y *Member[A, on.F]) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		zero := a.MemberOf[on.F](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		shift := a.Have(
			"zero adds nothing to y",
			"F.zero + y = y",
			ByArith(ring, y))
		a.Show(
			"translation by y preserves and reflects 0 < x",
			By(Normalized, shift, AddOrderIff.Read(ordered).At(zero, x, y)))
	}),
})}

// AddPositive — A sum of positive points is positive: adding the positive
// x moves y up to x + y, and y lies above zero.
var AddPositive = addPositiveThm{family.Add(registry.ProofEntry{
	Name: "AddPositive",
	Key:  "prop_1fb34e5da941bdfc",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
			"lt(F.zero, x)",
			"lt(F.zero, y)",
		},
		Conclusion: "lt(F.zero, x + y)",
	}, func(
		a *Argument,
		ordered OrderedFieldFact[on.F],
		x, y *Member[A, on.F],
		xPositive, yPositive Fact,
	) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		zero := a.MemberOf[on.F](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		a.Show(
			"adding the positive x moves y up to x + y, and y lies above zero",
			By(
				xPositive,
				yPositive,
				LessThanSelfAddLeft.Read(ordered).At(x, y),
				Transitive.Read(ordered).At(zero, y, comm_ring.AddIn.Read(ring).At(x, y))))
	}),
})}

// TwoPositive — Two is positive, a sum of the positive one with itself.
var TwoPositive = twoPositiveThm{family.Add(registry.ProofEntry{
	Name: "TwoPositive",
	Key:  "prop_19f4e44256ea8642",
	Build: OrderedFieldOn.Law("lt(F.zero, F.one + F.one)", func(
		a *Argument,
		ordered OrderedFieldFact[on.F],
	) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		one := a.MemberOf[on.F](a.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
		a.Show(
			"one is positive, and so is one plus one",
			By(OnePositive.Read(ordered), AddPositive.Read(ordered).At(one, one)))
	}),
})}

// TwoNonzero — Two is not zero: it is positive, and zero is not.
var TwoNonzero = twoNonzeroThm{family.Add(registry.ProofEntry{
	Name: "TwoNonzero",
	Key:  "prop_3adc425c40be2056",
	Build: OrderedFieldOn.Law("F.one + F.one ≠ F.zero", func(
		a *Argument,
		ordered OrderedFieldFact[on.F],
	) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		zero := a.MemberOf[on.F](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		a.Show(
			"two is positive, and no point lies above itself",
			By(Normalized, TwoPositive.Read(ordered), Irreflexive.Read(ordered).At(zero)))
	}),
})}

// SubPositive — The difference y − x is positive exactly when x lies below
// y: adding −x sends x to 0 and y to y − x, and translation preserves and
// reflects the order.
var SubPositive = subPositiveThm{family.Add(registry.ProofEntry{
	Name: "SubPositive",
	Key:  "prop_2e4ed120d9311338",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
		},
		Conclusion: "lt(F.zero, y - x) ⇔ lt(x, y)",
	}, func(a *Argument, ordered OrderedFieldFact[on.F], x, y *Member[A, on.F]) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		shift := a.Have(
			"adding −x sends x to 0 and y to y − x",
			"x + -x = F.zero ∧ y + -x = y - x",
			ByArith(ring, x, y))
		a.Show(
			"translation by −x preserves and reflects the order",
			By(Normalized, shift, AddOrderIff.Read(ordered).At(x, y, comm_ring.NegIn.Read(ring).At(x))))
	}),
})}

// SubNegative — The difference x − y is negative exactly when x lies below
// y: adding −y sends x to x − y and y to 0, and translation preserves and
// reflects the order.
var SubNegative = subNegativeThm{family.Add(registry.ProofEntry{
	Name: "SubNegative",
	Key:  "prop_f5ab9067c976b38f",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
		},
		Conclusion: "lt(x - y, F.zero) ⇔ lt(x, y)",
	}, func(a *Argument, ordered OrderedFieldFact[on.F], x, y *Member[A, on.F]) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		shift := a.Have(
			"adding −y sends x to x − y and y to 0",
			"x + -y = x - y ∧ y + -y = F.zero",
			ByArith(ring, x, y))
		a.Show(
			"translation by −y preserves and reflects the order",
			By(Normalized, shift, AddOrderIff.Read(ordered).At(x, y, comm_ring.NegIn.Read(ring).At(y))))
	}),
})}

// NegationReversesSign — Negation reverses the order against zero: x is
// negative exactly when −x is positive, and positive exactly when −x is
// negative, since adding −x moves x to 0 and 0 to −x and translation
// preserves and reflects the order.
var NegationReversesSign = negationReversesSignThm{family.Add(registry.ProofEntry{
	Name: "NegationReversesSign",
	Key:  "prop_ef8d32caa6c3670",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
		},
		Conclusion: "(lt(x, F.zero) ⇔ lt(F.zero, -x)) ∧ (lt(F.zero, x) ⇔ lt(-x, F.zero))",
	}, func(a *Argument, ordered OrderedFieldFact[on.F], x *Member[A, on.F]) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		zero := a.MemberOf[on.F](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		minusX := comm_ring.NegIn.Read(ring).At(x)
		translates := a.Have(
			"x + (−x) = 0 and 0 + (−x) = −x",
			"x + -x = F.zero ∧ F.zero + -x = -x",
			ByArith(ring, x))
		a.Show(
			"adding −x to x < 0 or to 0 < x moves x to 0 and 0 to −x, in both directions",
			By(
				Normalized,
				AddOrderIff.Read(ordered).At(x, zero, minusX),
				AddOrderIff.Read(ordered).At(zero, x, minusX),
				translates))
	}),
})}

// SquareNonnegative — Every carrier square is nonnegative: x·x is 0 when
// x = 0 and a product of positives when 0 < x, and when x < 0 it is
// (−x)(−x), a product of positives once negation has made −x positive.
var SquareNonnegative = squareNonnegativeThm{family.Add(registry.ProofEntry{
	Name: "SquareNonnegative",
	Key:  "prop_b8f40f6debad89fc",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
		},
		Conclusion: "ordered_le(lt, F.zero, x * x)",
	}, func(
		a *Argument,
		_ *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		ordered OrderedFieldFact[on.F],
		x *Member[A, on.F],
	) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		zero := a.MemberOf[on.F](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		nonnegative := OrderedLeDef.At(lt, zero, a.TermAs[A]("x * x"))
		negative := a.Assuming(
			a.TermAs[Bool]("lt(x, F.zero)"),
			"if x is not below 0, then x = 0 and x·x = 0·0 = 0, or 0 < x and x·x is a product of positives",
			Given(func(b *Argument, notNegative Fact) {
				b.Show(
					"0 and x are comparable",
					By(
						nonnegative,
						Trichotomy.Read(ordered).At(zero, x),
						notNegative,
						MulPositive.Read(ordered).At(x, x),
						comm_ring.MulLeftZeroOn.Read(ring).At(zero)))
			}))
		minusX := comm_ring.NegIn.Read(ring).At(x)
		positive := a.Have(
			"negation reverses the order against zero, so 0 < −x",
			"lt(F.zero, -x)",
			By(NegationReversesSign.Read(ordered).At(x), negative))
		a.Show(
			"so x·x = (−x)(−x) is a product of positives",
			By(
				nonnegative,
				MulPositive.Read(ordered).At(minusX, minusX),
				positive,
				comm_ring.MulNegNegOn.Read(ring).At(x, x)))
	}),
})}

// SquarePositive — The square of a nonzero point is positive: it is
// nonnegative, and it is not zero, a field having no zero divisors.
var SquarePositive = squarePositiveThm{family.Add(registry.ProofEntry{
	Name: "SquarePositive",
	Key:  "prop_9a4e3c455fb2186c",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"x ≠ F.zero",
		},
		Conclusion: "lt(F.zero, x * x)",
	}, func(
		a *Argument,
		_ *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		ordered OrderedFieldFact[on.F],
		x *Member[A, on.F],
		nonzero Fact,
	) {
		a.Show(
			"x·x is nonnegative, and not zero, as x is not",
			By(
				nonzero,
				SquareNonnegative.Read(ordered).At(x),
				OrderedLeDef.At(lt, a.TermAs[A]("F.zero"), a.TermAs[A]("x * x")),
				field.MulEqZeroOn.Read(FieldOn.Read(ordered)).At(x, x)))
	}),
})}

// SumSquaresZero — Two points whose squares sum to zero are both zero: were
// b not zero, a·a would lie strictly below a·a + b·b = 0 while being
// nonnegative; so b = 0, then a·a = 0, and a = 0.
var SumSquaresZero = sumSquaresZeroThm{family.Add(registry.ProofEntry{
	Name: "SumSquaresZero",
	Key:  "prop_95c3bf3ededa801f",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀a b:A.",
		Hypotheses: []string{
			"a ∈ F.carrier",
			"b ∈ F.carrier",
			"a * a + b * b = F.zero",
		},
		Conclusion: "a = F.zero ∧ b = F.zero",
	}, func(
		arg *Argument,
		_ *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		ordered OrderedFieldFact[on.F],
		a, b *Member[A, on.F],
		sumZero Fact,
	) {
		fieldF := FieldOn.Read(ordered)
		ring := field.RingOn.Read(fieldF)
		zero := arg.TermAs[A]("F.zero")
		aa := arg.TermAs[A]("a * a")
		bb := arg.TermAs[A]("b * b")
		squareMembers := arg.Have(
			"both squares and zero belong to the field",
			"a * a ∈ F.carrier ∧ b * b ∈ F.carrier ∧ F.zero ∈ F.carrier",
			By(
				comm_ring.ZeroIn.Read(ring),
				a,
				b,
				comm_ring.MulIn.Read(ring).At(a, a),
				comm_ring.MulIn.Read(ring).At(b, b)))
		bZero := arg.Have(
			"b is zero",
			"b = F.zero",
			Derive(func(c *Argument) {
				nonzero := c.SupposeNot()
				below := c.Have(
					"a nonzero b puts a·a strictly below a·a + b·b",
					"lt(a * a, a * a + b * b)",
					By(
						nonzero,
						squareMembers,
						SquarePositive.Read(ordered).At(b),
						LessThanSelfAddLeft.Read(ordered).AsFact().At(bb, aa),
						comm_monoid.CommOn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(aa, bb)))
				c.Show(
					"then 0 ≤ a·a < a·a + b·b = 0",
					By(
						below,
						sumZero,
						a,
						squareMembers,
						SquareNonnegative.Read(ordered).At(a),
						OrderMixedTransitive.Read(ordered).AsFact().At(zero, aa, zero),
						Irreflexive.Read(ordered).AsFact().At(zero)))
			}))
		aSquareZero := arg.Have(
			"so the remaining square a·a is zero",
			"a * a = F.zero",
			ByArith(fieldF, Scaled(b, bZero), sumZero, a, b))
		arg.Show(
			"and a field has no nonzero square roots of zero",
			By(bZero, aSquareZero, a, field.MulEqZeroOn.Read(fieldF).At(a, a)))
	}),
})}

// IncreasingMapReflectsOrder — A map f from a set S into an ordered field
// that carries a relation R into the strict order also reflects it, when R
// compares any two points of S (one is R-below the other, or they are equal);
// R need not be an order: were f(x) below f(y) while x is not R-below y, x
// would equal y or lie R-above it, and either way f(x) would lie below itself.
var IncreasingMapReflectsOrder = increasingMapReflectsOrderThm{family.Add(registry.ProofEntry{
	Name: "IncreasingMapReflectsOrder",
	Key:  "prop_d6079c1506b33f50",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀f:(B → A). ∀S:set(B). ∀R:(B → B → bool). ∀x y:B.",
		Hypotheses: []string{
			"∀u v:B. u ∈ S ∧ v ∈ S ⇒ R(u, v) ∨ u = v ∨ R(v, u)",
			"∀u:B. u ∈ S ⇒ f(u) ∈ F.carrier",
			"∀u v:B. u ∈ S ∧ v ∈ S ∧ R(u, v) ⇒ lt(f(u), f(v))",
			"x ∈ S",
			"y ∈ S",
		},
		Conclusion: "lt(f(x), f(y)) ⇔ R(x, y)",
	}, func(
		a *Argument,
		ordered OrderedFieldFact[on.F],
		f *Arrow[B, A],
		S *Expr[Set[B]],
		R *Arrow2[B, B, Bool],
		linear, into, keeps Fact,
		x, y *Expr[B],
		xIn, yIn Fact,
	) {
		fx := a.MemberOf[on.F](f.Apply(x), a.Have(
			"f(x) lies in F",
			"f(x) ∈ F.carrier",
			By(into.At(x), xIn)))
		fy := a.MemberOf[on.F](f.Apply(y), a.Have(
			"f(y) lies in F",
			"f(y) ∈ F.carrier",
			By(into.At(y), yIn)))
		a.Iff()
		a.Forward(
			"were x = y or y below x, f(x) would lie below itself",
			func(b *Argument, below Fact) {
				b.Show(
					"by trichotomy in S, the order kept, transitivity and irreflexivity",
					By(
						below,
						xIn,
						yIn,
						linear.At(x, y),
						keeps.At(y, x),
						Transitive.Read(ordered).At(fx, fy, fx),
						Irreflexive.Read(ordered).At(fx)))
			})
		a.Backward(
			"f keeps the order",
			func(b *Argument, less Fact) {
				b.Show(
					"x < y carried by f",
					By(keeps.At(x, y), xIn, yIn, less))
			})
	}),
})}

// IntermediateValueInjectiveMonotone — a map of an ordered field injective on a set s, which takes
// strictly between two points of s every value strictly between their values, is strictly
// increasing or strictly decreasing on s: a point w of s outside a segment of s has its value
// outside the segment's end values, since inside them the value would be taken a second time,
// inside the segment; so of three points a < b < c of s the pairs (a, b), (b, c) and (a, c) are
// ordered alike by f, then two pairs with one left end are, and through them any two pairs of s.
var IntermediateValueInjectiveMonotone = intermediateValueInjectiveMonotoneThm{family.Add(registry.ProofEntry{
	Name: "IntermediateValueInjectiveMonotone",
	Key:  "prop_644a4f44fef6e6c8",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀f:(A → A). ∀s:set(A).",
		Hypotheses: []string{
			"s ⊆ F.carrier",
			"∀x:A. x ∈ s ⇒ f(x) ∈ F.carrier",
			"injective_on(s, f)",
			"∀x y v:A. " +
				"    x ∈ s ∧ " +
				"    y ∈ s ∧ " +
				"    lt(x, y) ∧ " +
				"    v ∈ F.carrier ∧ " +
				"    (lt(f(x), v) ∧ lt(v, f(y)) ∨ lt(f(y), v) ∧ lt(v, f(x))) ⇒ " +
				"    ∃z:A. z ∈ s ∧ lt(x, z) ∧ lt(z, y) ∧ f(z) = v",
		},
		Conclusion: "(∀x y:A. x ∈ s ∧ y ∈ s ∧ lt(x, y) ⇒ lt(f(x), f(y))) ∨ " +
			"(∀x y:A. x ∈ s ∧ y ∈ s ∧ lt(x, y) ⇒ lt(f(y), f(x)))",
	}, func(
		arg *Argument,
		ordered OrderedFieldFact[on.F],
		f *Arrow[A, A],
		s *Expr[Set[A]],
		inside, into, injective, intermediate Fact,
	) {
		points := arg.Unfolded(inside, set_basic.SubsetDef)
		oneToOne := arg.Unfolded(injective, functions.InjectiveOnDef)
		comparable := Trichotomy.Read(ordered)
		point := func(b *Argument, x *Expr[A], xIn Fact) *Member[A, on.F] {
			return b.MemberOf[on.F](x, GroupPremises(xIn, points.At(x)))
		}
		value := func(b *Argument, x *Expr[A], xIn Fact) *Member[A, on.F] {
			return b.MemberOf[on.F](f.Apply(x), GroupPremises(xIn, into.At(x)))
		}
		outside := arg.Have(
			"a point w of s outside a segment ⟬u, v⟭ of s has its value outside (f(u), f(v))",
			Statement{
				Binders: "∀u v w:A.",
				Hypotheses: []string{
					"u ∈ s",
					"v ∈ s",
					"w ∈ s",
					"lt(u, v)",
					"lt(w, u) ∨ lt(v, w)",
				},
				Conclusion: "¬(lt(f(u), f(w)) ∧ lt(f(w), f(v)) ∨ lt(f(v), f(w)) ∧ lt(f(w), f(u)))",
			},
			Derive(func(b *Argument) {
				u := b.FixAs[A]("u")
				v := b.FixAs[A]("v")
				w := b.FixAs[A]("w")
				given := b.Assume()
				um, vm, wm := point(b, u, given), point(b, v, given), point(b, w, given)
				within := b.SupposeNot()
				z, taken := b.ObtainAs[A](
					"the value f(w) is then taken at a point z of s strictly between u and v",
					"∃z:A. z ∈ s ∧ lt(u, z) ∧ lt(z, v) ∧ f(z) = f(w)",
					By(given, within, intermediate.At(u, v, f.Apply(w)), into.At(w)))
				b.Show(
					"injectivity makes z = w, and w would lie below itself, through u or through v",
					By(
						given,
						taken,
						oneToOne.At(z, w),
						Transitive.Read(ordered).At(wm, um, wm),
						Transitive.Read(ordered).At(wm, vm, wm),
						Irreflexive.Read(ordered).At(wm)))
			}))
		distinct := arg.Have(
			"f takes distinct values at two ordered points of s",
			"∀x y:A. x ∈ s ∧ y ∈ s ∧ lt(x, y) ⇒ f(x) ≠ f(y)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				given := b.Assume()
				b.Show(
					"one value would make x = y by injectivity, and x would lie below itself",
					By(given, oneToOne.At(x, y), Irreflexive.Read(ordered).At(point(b, x, given))))
			}))
		alike := arg.Have(
			"of three points a < b < c of s, the pairs (a, b), (b, c) and (a, c) are ordered alike by f",
			Statement{
				Binders: "∀a b c:A.",
				Hypotheses: []string{
					"a ∈ s",
					"b ∈ s",
					"c ∈ s",
					"lt(a, b)",
					"lt(b, c)",
				},
				Conclusion: "(lt(f(a), f(b)) ⇔ lt(f(b), f(c))) ∧ (lt(f(a), f(b)) ⇔ lt(f(a), f(c)))",
			},
			Derive(func(d *Argument) {
				a := d.FixAs[A]("a")
				b := d.FixAs[A]("b")
				c := d.FixAs[A]("c")
				given := d.Assume()
				apart := d.Have(
					"f takes three distinct values at a, b and c, since a < c as well",
					"f(a) ≠ f(b) ∧ f(b) ≠ f(c) ∧ f(a) ≠ f(c)",
					By(
						given,
						distinct.At(a, b),
						distinct.At(b, c),
						distinct.At(a, c),
						Transitive.Read(ordered).At(point(d, a, given), point(d, b, given), point(d, c, given))))
				fa, fb, fc := value(d, a, given), value(d, b, given), value(d, c, given)
				d.Show(
					"the values are comparable, f(c) lies outside (f(a), f(b)) and f(a) outside (f(b), f(c))",
					By(
						Normalized,
						given,
						apart,
						outside.At(a, b, c),
						outside.At(b, c, a),
						comparable.At(fa, fb),
						comparable.At(fb, fc),
						comparable.At(fa, fc)))
			}))
		sharedLeft := arg.Have(
			"two pairs of s with one left end are ordered alike by f",
			"∀a b c:A. a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ lt(a, b) ∧ lt(a, c) ⇒ (lt(f(a), f(b)) ⇔ lt(f(a), f(c)))",
			Derive(func(d *Argument) {
				a := d.FixAs[A]("a")
				b := d.FixAs[A]("b")
				c := d.FixAs[A]("c")
				given := d.Assume()
				d.Show(
					"the right ends are comparable: a < b < c, a < c < b, or the two pairs are one",
					By(
						given,
						alike.At(a, b, c),
						alike.At(a, c, b),
						comparable.At(point(d, b, given), point(d, c, given))))
			}))
		pairs := arg.Have(
			"any two pairs of s are ordered alike by f",
			Statement{
				Binders: "∀x y u v:A.",
				Hypotheses: []string{
					"x ∈ s",
					"y ∈ s",
					"u ∈ s",
					"v ∈ s",
					"lt(x, y)",
					"lt(u, v)",
				},
				Conclusion: "lt(f(x), f(y)) ⇔ lt(f(u), f(v))",
			},
			Derive(func(d *Argument) {
				x := d.FixAs[A]("x")
				y := d.FixAs[A]("y")
				u := d.FixAs[A]("u")
				v := d.FixAs[A]("v")
				given := d.Assume()
				d.Show(
					"the left ends are comparable: the pair (x, u) or (u, x) links the two pairs, or they share x = u",
					By(
						given,
						sharedLeft.At(x, y, u),
						sharedLeft.At(x, y, v),
						sharedLeft.At(u, v, x),
						alike.At(x, u, v),
						alike.At(u, x, y),
						comparable.At(point(d, x, given), point(d, u, given))))
			}))
		notIncreasing := arg.Unless(
			arg.TermAs[Bool]("∀x y:A. x ∈ s ∧ y ∈ s ∧ lt(x, y) ⇒ lt(f(x), f(y))"),
			"the first alternative holds where f increases every pair of s",
			Given(func(b *Argument, increasing Fact) {
				b.Show(
					"f is strictly increasing on s",
					By(increasing))
			}))
		p, q, reference := arg.Obtain2As[A, A](
			"otherwise f does not increase some pair p < q of s",
			"∃p q:A. p ∈ s ∧ q ∈ s ∧ lt(p, q) ∧ ¬lt(f(p), f(q))",
			By(notIncreasing))
		decreasing := arg.Have(
			"every pair of s is then ordered as p < q, decreasing",
			"∀x y:A. x ∈ s ∧ y ∈ s ∧ lt(x, y) ⇒ lt(f(y), f(x))",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				pair := b.Assume()
				b.Show(
					"f(x) < f(y) fails as f(p) < f(q) does, f(x) ≠ f(y), and the two values are comparable",
					By(
						pair,
						reference,
						pairs.At(x, y, p, q),
						distinct.At(x, y),
						comparable.At(value(b, x, pair), value(b, y, pair))))
			}))
		arg.Show(
			"f is strictly decreasing on s",
			By(decreasing))
	}),
})}

// NegativeIffImageNegative — a ring homomorphism that preserves and reflects the
// order carries negativity both ways, neither side an ordered field: it fixes
// zero, which lies in the carrier, so x lies below zero exactly when its image
// lies below the image of zero.
var NegativeIffImageNegative = negativeIffImageNegativeThm{family.Add(registry.ProofEntry{
	Name: "NegativeIffImageNegative",
	Key:  "prop_2b24b8e9ffab6952",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀G:field_ops(B). " +
			"∀ls:(B → B → bool). " +
			"∀i:(A → B). " +
			"∀x:A.",
		Hypotheses: []string{
			"ring_homomorphism(field_ring(F), field_ring(G), i)",
			"∀u v:A. u ∈ F.carrier ∧ v ∈ F.carrier ⇒ (lt(u, v) ⇔ ls(i(u), i(v)))",
			"x ∈ F.carrier",
		},
		Conclusion: "lt(x, F.zero) ⇔ ls(i(x), G.zero)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		G *Expr[FieldOps[B]],
		ls *Arrow2[B, B, Bool],
		i *Arrow[A, B],
		hom, order Fact,
		x *Expr[A],
		xIn Fact,
	) {
		a.Show(
			"i preserves and reflects the order between x and zero, and fixes zero",
			By(
				Normalized,
				order.At(x, a.TermAs[A]("F.zero")),
				xIn,
				ring_homomorphism.MapZero.Read(hom),
				comm_ring.ZeroIn.Read(ring_homomorphism.Source.Read(hom))))
	}),
})}

// PositiveMulOrderIff — Multiplication by a positive element preserves and
// reflects strict order: for u < v, v + (−u) is positive, so is
// (v + (−u))z, and adding uz to it gives uz < vz; and a map that keeps the
// linear order of the carrier reflects it.
var PositiveMulOrderIff = positiveMulOrderIffThm{family.Add(registry.ProofEntry{
	Name: "PositiveMulOrderIff",
	Key:  "prop_d90b397fe6a953a8",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
			"z ∈ F.carrier",
			"lt(F.zero, z)",
		},
		Conclusion: "lt(x * z, y * z) ⇔ lt(x, y)",
	}, func(
		a *Argument,
		_ *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		ordered OrderedFieldFact[on.F],
		x, y, z *Member[A, on.F],
		positive Fact,
	) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		zero := a.MemberOf[on.F](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		preserves := a.Have(
			"multiplying by z preserves the order",
			"∀u v:A. u ∈ F.carrier ∧ v ∈ F.carrier ∧ lt(u, v) ⇒ lt(u * z, v * z)",
			Derive(func(b *Argument) {
				u := b.FixAs[A]("u")
				v := b.FixAs[A]("v")
				given := b.Conjuncts(
					b.Assume(),
					"u lies in the carrier",
					"v lies in the carrier",
					"u lies below v")
				um, vm := b.MemberOf[on.F](u, given[0]), b.MemberOf[on.F](v, given[1])
				minusU := comm_ring.NegIn.Read(ring).At(um)
				gap := comm_ring.AddIn.Read(ring).At(vm, minusU)
				arithmetic := b.Have(
					"u + (−u) = 0, 0 + uz = uz, and (v + (−u))z + uz = vz",
					"u + -u = F.zero ∧ F.zero + u * z = u * z ∧ (v + -u) * z + u * z = v * z",
					ByArith(ring, um, vm, z))
				gapPositive := b.Have(
					"adding −u to u < v gives 0 < v + (−u)",
					"lt(F.zero, v + -u)",
					By(Normalized, AddPreservesOrder.Read(ordered).At(um, vm, minusU), given[2], arithmetic))
				b.Show(
					"so (v + (−u))z is positive, and adding uz to it gives uz < vz",
					By(
						MulPositive.Read(ordered).At(gap, z),
						gapPositive,
						positive,
						AddPreservesOrder.Read(ordered).At(
							zero,
							comm_ring.MulIn.Read(ring).At(gap, z),
							comm_ring.MulIn.Read(ring).At(um, z)),
						arithmetic))
			}))
		scale := a.TermAs[Fun[A, A]]("λu:A. u * z")
		a.Show(
			"multiplying by z keeps the linear order of the carrier, so it reflects it",
			By(
				IncreasingMapReflectsOrder.Read(ordered).At(scale, a.TermAs[Set[A]]("F.carrier"), lt, x, y),
				Trichotomy.Read(ordered),
				comm_ring.MulIn.Read(ring),
				z,
				preserves,
				x,
				y))
	}),
})}

// PositiveInverse — The inverse of a positive element is positive: x is not
// 0, and multiplied by x the claim 0 < x⁻¹ is the comparison of 0·x = 0
// with x⁻¹x = 1, which holds.
var PositiveInverse = positiveInverseThm{family.Add(registry.ProofEntry{
	Name: "PositiveInverse",
	Key:  "prop_59e7f00deb733549",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"lt(F.zero, x)",
		},
		Conclusion: "lt(F.zero, F.inv(x))",
	}, func(a *Argument, ordered OrderedFieldFact[on.F], x *Member[A, on.F], positive Fact) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		zero := a.MemberOf[on.F](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		nonzero := a.Have(
			"x is not 0, since 0 does not lie below itself",
			"x ≠ F.zero",
			By(Normalized, positive, Irreflexive.Read(ordered).At(zero)))
		a.Show(
			"multiplying by x preserves and reflects the order, and 0·x = 0 lies below x⁻¹x = 1",
			By(
				Normalized,
				PositiveMulOrderIff.Read(ordered).At(zero, field.InvIn.Read(FieldOn.Read(ordered)).At(x), x),
				positive,
				OnePositive.Read(ordered),
				comm_ring.MulLeftZeroOn.Read(ring).At(x),
				field.MulLeftInverseOn.Read(FieldOn.Read(ordered)).At(x),
				nonzero))
	}),
})}

// MultipleOfOnePositive — Every positive natural multiple of one is
// positive: by induction the successor multiples are, 1 = 1 + 0 being
// positive and 0 < p giving 0 < 1 + p, since p = 0 + p < 1 + p; and a
// positive n is the successor of n − 1.
var MultipleOfOnePositive = multipleOfOnePositiveThm{family.Add(registry.ProofEntry{
	Name: "MultipleOfOnePositive",
	Key:  "prop_ed63d9c1edce89de",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"0 < n",
		},
		Conclusion: "lt(F.zero, monoid_pow(F.add, F.zero, F.one, n))",
	}, func(a *Argument, ordered OrderedFieldFact[on.F], n *Expr[Nat], positive Fact) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		additive := comm_ring.AddMonoidOn.Read(ring)
		zero := a.MemberOf[on.F](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		one := a.MemberOf[on.F](a.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
		successors := a.Have(
			"every successor multiple of one is positive",
			"∀m:num. lt(F.zero, monoid_pow(F.add, F.zero, F.one, suc(m)))",
			Derive(func(b *Argument) {
				m := b.Binder("m")
				b.Induct(m)
				b.Base(
					"1 = 1 + 0 is positive",
					By(
						OnePositive.Read(ordered),
						comm_monoid.MonoidPowDef.Inst[A](),
						comm_monoid.RightIdentityOn.Read(additive).At(one)))
				b.Step(
					"0 < p gives 0 < 1 + p, since adding the positive 1 moves p up",
					func(c *Argument, earlier Fact) {
						p := comm_monoid.PowIn.Read(additive).At(one, c.TermAs[Nat]("suc(m)"))
						c.Show(
							"the next multiple of one is 1 + p",
							By(
								earlier,
								comm_monoid.MonoidPowDef.Inst[A](),
								OnePositive.Read(ordered),
								LessThanSelfAddLeft.Read(ordered).At(one, p),
								Transitive.Read(ordered).At(zero, p, comm_ring.AddIn.Read(ring).At(one, p))))
					})
			}))
		predecessor := a.Have(
			"n is the successor of n − 1, being positive",
			"n = suc(n - 1)",
			ByArith(positive))
		a.Show(
			"so n·1 is a successor multiple of one",
			By(Normalized, successors.At(a.TermAs[Nat]("n - 1")), predecessor))
	}),
})}

// IntegerOrderEmbedding — The canonical integer map preserves and reflects
// strict order: for i < j, j = k + i with k a positive natural number, so
// the image of j is k·1 plus the image of i, where k·1 is positive; and a
// map that keeps the linear order of the integers reflects it.
var IntegerOrderEmbedding = integerOrderEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "IntegerOrderEmbedding",
	Key:  "prop_aaf8e189c68a37ee",
	Build: OrderedFieldOn.Law("∀m n:int. "+
		"    (lt(integer_map(field_ring(F), m), integer_map(field_ring(F), n)) ⇔ m < n)", func(
		a *Argument,
		ordered OrderedFieldFact[on.F],
		m, n *Expr[Int],
	) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		additive := comm_ring.AddMonoidOn.Read(ring)
		images := characteristic_zero.IntegerMapInCarrier.Read(ring)
		zero := a.MemberOf[on.F](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		one := a.MemberOf[on.F](a.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
		preserves := a.Have(
			"the integer map preserves the order",
			"∀i j:int. i < j ⇒ lt(integer_map(field_ring(F), i), integer_map(field_ring(F), j))",
			Derive(func(b *Argument) {
				i := b.FixAs[Int]("i")
				b.FixAs[Int]("j")
				less := b.Assume()
				gap := b.Have(
					"j − i is not negative",
					"0 ≤ j - i",
					ByArith(less))
				k, natural := b.ObtainAs[Nat](
					"so j − i is a natural number k",
					"∃k:num. j - i = k",
					By(gap, int_embed.OfNumExists.At(b.TermAs[Int]("j - i"))))
				split := b.Have(
					"j = k + i with k positive",
					"j = k + i ∧ 0 < k",
					ByArith(natural, less, int_embed.OfNumLt.At(b.TermAs[Nat]("0"), k)))
				shifted := b.Have(
					"so the image of j is k·1 plus the image of i",
					"integer_map(field_ring(F), j) = "+
						"monoid_pow(F.add, F.zero, F.one, k) + integer_map(field_ring(F), i)",
					By(
						split,
						characteristic_zero.IntegerMapHom.Read(ring),
						characteristic_zero.IntegerMapOfNum.Read(ring).At(k)))
				imageI := b.MemberOf[on.F](b.TermAs[A]("integer_map(field_ring(F), i)"), images.At(i))
				multiple := comm_monoid.PowIn.Read(additive).At(one, k)
				b.Show(
					"0 < k·1 translated by the image of i",
					By(
						MultipleOfOnePositive.Read(ordered).At(k),
						split,
						AddPreservesOrder.Read(ordered).At(zero, multiple, imageI),
						comm_monoid.LeftIdentityOn.Read(additive).At(imageI),
						shifted))
			}))
		comparable := a.Have(
			"two integers are comparable",
			"∀i j:int. i < j ∨ i = j ∨ j < i",
			Derive(func(b *Argument) {
				b.FixAs[Int]("i")
				b.FixAs[Int]("j")
				b.Show(
					"the integers are linearly ordered",
					ByArith())
			}))
		a.Show(
			"the integer map keeps the linear order of the integers, so it reflects it",
			By(
				IncreasingMapReflectsOrder.Read(ordered).At(
					a.TermAs[Fun[Int, A]]("λi:int. integer_map(field_ring(F), i)"),
					a.TermAs[Set[Int]]("𝕌"),
					a.TermAs[Fun2[Int, Int, Bool]]("λi:int. λj:int. i < j"),
					m,
					n),
				comparable,
				preserves,
				images,
				set_basic.InUniv))
	}),
})}

// CharacteristicZero — An ordered field has characteristic zero: every
// positive natural multiple of one is positive, so none of them is 0.
var CharacteristicZero = characteristicZeroThm{family.Add(registry.ProofEntry{
	Name: "CharacteristicZero",
	Key:  "prop_5df888391f9dbe6e",
	Build: OrderedFieldOn.Law("characteristic_zero(field_ring(F))", func(
		a *Argument,
		ordered OrderedFieldFact[on.F],
	) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		zero := a.MemberOf[on.F](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		a.Show(
			"no positive multiple of one is 0",
			Unfold(comm_ring.CharacteristicZeroDef),
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				positive := b.Assume()
				b.Show(
					"0 < n·1, and 0 does not lie below itself",
					By(MultipleOfOnePositive.Read(ordered).At(n), positive, Irreflexive.Read(ordered).At(zero)))
			}))
	}),
})}

// DenseOrder — Between any two ordered carrier points lies another: the
// midpoint (x + y)/2, since 0 < 2, so that halving preserves the order, and
// halving x + x < y + x and x + y < y + y puts it strictly between x and y.
var DenseOrder = denseOrderThm{family.Add(registry.ProofEntry{
	Name: "DenseOrder",
	Key:  "prop_6f6f617ac1613914",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
			"lt(x, y)",
		},
		Conclusion: "∃z:A. z ∈ F.carrier ∧ lt(x, z) ∧ lt(z, y)",
		Abbrev: Abbrev{
			{Name: "half", Text: "F.inv(F.one + F.one)"},
		},
	}, func(a *Argument, ordered OrderedFieldFact[on.F], x, y *Member[A, on.F], less Fact) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		sum := comm_ring.AddIn.Read(ring)
		zero := a.MemberOf[on.F](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		one := a.MemberOf[on.F](a.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
		two := sum.At(one, one)
		half := field.InvIn.Read(FieldOn.Read(ordered)).At(two)
		twoPositive := a.Have(
			"0 < 1 < 1 + 1",
			"lt(F.zero, F.one + F.one)",
			By(
				LessThanSelfAddLeft.Read(ordered).At(one, one),
				OnePositive.Read(ordered),
				Transitive.Read(ordered).At(zero, one, two)))
		halving := a.Have(
			"1 + 1 is not 0, so it has an inverse",
			"«half» * (F.one + F.one) = F.one",
			By(
				field.MulLeftInverseOn.Read(FieldOn.Read(ordered)).At(two),
				twoPositive,
				Irreflexive.Read(ordered).At(zero)))
		halves := a.Have(
			"halving x + x, y + x and y + y",
			"(x + x) * «half» = x ∧ (y + x) * «half» = (x + y) * «half» ∧ (y + y) * «half» = y",
			ByArith(FieldOn.Read(ordered), Scaled(x, halving), Scaled(y, halving), x, y, half))
		midpoint := comm_ring.MulIn.Read(ring).At(sum.At(x, y), half)
		a.Take(midpoint)
		a.Show(
			"halving x + x < y + x and x + y < y + y, with 0 < "+
				"(1 + 1)⁻¹, puts (x + y)/2 strictly between x and y",
			By(
				halves,
				less,
				twoPositive,
				PositiveInverse.Read(ordered).At(two),
				AddPreservesOrder.Read(ordered).At(x, y, x),
				AddPreservesOrder.Read(ordered).At(x, y, y),
				PositiveMulOrderIff.Read(ordered).At(sum.At(x, x), sum.At(y, x), half),
				PositiveMulOrderIff.Read(ordered).At(sum.At(x, y), sum.At(y, y), half),
				midpoint))
	}),
})}

// NoEndpoints — No point of the carrier is least or greatest: adding the
// positive 1 moves x − 1 up to x, and x up to 1 + x.
var NoEndpoints = noEndpointsThm{family.Add(registry.ProofEntry{
	Name: "NoEndpoints",
	Key:  "prop_6a738e7c23afd608",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
		},
		Conclusion: "(∃y:A. y ∈ F.carrier ∧ lt(y, x)) ∧ (∃z:A. z ∈ F.carrier ∧ lt(x, z))",
	}, func(a *Argument, ordered OrderedFieldFact[on.F], x *Member[A, on.F]) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		one := a.MemberOf[on.F](a.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
		restore := a.Have(
			"adding 1 to x − 1 gives back x",
			"F.one + (x - F.one) = x",
			ByArith(ring, x, one))
		positive := OnePositive.Read(ordered)
		moveUp := LessThanSelfAddLeft.Read(ordered)
		a.Show(
			"x − 1 and 1 + x serve",
			SplitConj(
				Case(
					"x − 1 lies below x",
					Derive(func(b *Argument) {
						below := comm_ring.SubIn.Read(ring).At(x, one)
						b.Take(below)
						b.Show(
							"adding 1 moves x − 1 up to x",
							By(Normalized, moveUp.At(one, below), restore, positive))
					})),
				Case(
					"1 + x lies above x",
					Derive(func(b *Argument) {
						above := comm_ring.AddIn.Read(ring).At(one, x)
						b.Take(above)
						b.Show(
							"adding 1 moves x up to 1 + x",
							By(moveUp.At(one, x), positive, above))
					}))))
	}),
})}

// SignValues — The sign of a point of the carrier is −1, 0 or 1 exactly
// as the point lies below zero, at zero or above it: the definition reads
// the sign off the comparisons of the point with zero, exactly one of
// which holds, and the three values differ.
var SignValues = signValuesThm{family.Add(registry.ProofEntry{
	Name: "SignValues",
	Key:  "prop_525ac96d98eb7804",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
		},
		Conclusion: "(ordered_sign(F, lt, x) = -1 ⇔ lt(x, F.zero)) ∧ " +
			"(ordered_sign(F, lt, x) = 0 ⇔ x = F.zero) ∧ " +
			"(ordered_sign(F, lt, x) = 1 ⇔ lt(F.zero, x))",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		ordered OrderedFieldFact[on.F],
		x *Member[A, on.F],
	) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		zero := a.MemberOf[on.F](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		distinct := a.Have(
			"the values −1, 0 and 1 differ",
			"-1 ≠ int_of_num(0) ∧ -1 ≠ int_of_num(1) ∧ 0 ≠ int_of_num(1)",
			ByArith())
		a.Show(
			"x is below 0, at 0 or above it, and by irreflexivity and transitivity in exactly one way",
			By(
				Normalized,
				OrderedSignDef.At(F, lt, x),
				distinct,
				Trichotomy.Read(ordered).At(x, zero),
				Irreflexive.Read(ordered).At(x),
				Irreflexive.Read(ordered).At(zero),
				Transitive.Read(ordered).At(x, zero, x)))
	}),
})}

// SignMul — The sign of a product is the product of the signs: a zero
// factor makes the product zero; (−x)(−y) = xy makes a product of two
// points on one side of zero positive, and x(−y) = (−x)y = −(xy) makes a
// product of two points on opposite sides negative; and −1, 0 and 1
// multiply as the signs of the cases say.
var SignMul = signMulThm{family.Add(registry.ProofEntry{
	Name: "SignMul",
	Key:  "prop_a29a7ae127a72421",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
			"y ∈ F.carrier",
		},
		Conclusion: "ordered_sign(F, lt, x * y) = ordered_sign(F, lt, x) * ordered_sign(F, lt, y)",
	}, func(a *Argument, ordered OrderedFieldFact[on.F], x, y *Member[A, on.F]) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		negIn := comm_ring.NegIn.Read(ring)
		positive := MulPositive.Read(ordered)
		reverse := NegationReversesSign.Read(ordered)
		zero := a.MemberOf[on.F](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		product := comm_ring.MulIn.Read(ring).At(x, y)
		minusX, minusY := negIn.At(x), negIn.At(y)
		identities := a.Have(
			"a zero factor makes the product zero, and a negation moves out of either factor",
			"x * F.zero = F.zero ∧ "+
				"F.zero * y = F.zero ∧ "+
				"-x * -y = x * y ∧ "+
				"x * -y = -(x * y) ∧ "+
				"-x * y = -(x * y)",
			ByArith(ring, x, y))
		oneSide := a.Have(
			"so xy is positive when x and y lie on one side of zero",
			"(lt(F.zero, x) ∧ lt(F.zero, y) ⇒ lt(F.zero, x * y)) ∧ "+
				"(lt(x, F.zero) ∧ lt(y, F.zero) ⇒ lt(F.zero, x * y))",
			By(identities, positive.At(x, y), positive.At(minusX, minusY), reverse.At(x), reverse.At(y)))
		oppositeSides := a.Have(
			"and negative when they lie on opposite sides",
			"(lt(F.zero, x) ∧ lt(y, F.zero) ⇒ lt(x * y, F.zero)) ∧ "+
				"(lt(x, F.zero) ∧ lt(F.zero, y) ⇒ lt(x * y, F.zero))",
			By(
				Normalized,
				identities,
				positive.At(x, minusY),
				positive.At(minusX, y),
				reverse.At(x),
				reverse.At(y),
				reverse.At(product)))
		byMinusOne := a.Have(
			"−1 times −1, 0 and 1 is 1, 0 and −1",
			"-1 * -1 = int_of_num(1) ∧ -1 * 0 = int_of_num(0) ∧ -1 * 1 = -int_of_num(1)",
			ByArith())
		byZero := a.Have(
			"0 times each sign is 0",
			"0 * -1 = int_of_num(0) ∧ 0 * &0 = int_of_num(0) ∧ 0 * &1 = int_of_num(0)",
			ByArith())
		byOne := a.Have(
			"1 times each sign is that sign",
			"1 * -1 = -int_of_num(1) ∧ 1 * &0 = int_of_num(0) ∧ 1 * &1 = int_of_num(1)",
			ByArith())
		value := SignValues.Read(ordered)
		a.Show(
			"comparing x and y with zero reads the signs of x, y and xy off each case",
			By(
				identities,
				oneSide,
				oppositeSides,
				byMinusOne,
				byZero,
				byOne,
				value.At(x),
				value.At(y),
				value.At(product),
				Trichotomy.Read(ordered).At(x, zero),
				Trichotomy.Read(ordered).At(y, zero)))
	}),
})}

// SignNegOne — The sign of −1 is −1: one is positive, so its negation is
// negative, and the sign of a negative point is −1.
var SignNegOne = signNegOneThm{family.Add(registry.ProofEntry{
	Name: "SignNegOne",
	Key:  "prop_c3ab3e11bfbf34af",
	Build: OrderedFieldOn.Law("ordered_sign(F, lt, -F.one) = -1", func(
		a *Argument,
		ordered OrderedFieldFact[on.F],
	) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		one := a.MemberOf[on.F](a.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
		minusOne := comm_ring.NegIn.Read(ring).At(one)
		a.Show(
			"one is positive, so −1 is negative",
			By(
				OnePositive.Read(ordered),
				NegationReversesSign.Read(ordered).At(one),
				SignValues.Read(ordered).At(minusOne)))
	}),
})}

// SignNeg — The sign of −x is the negation of the sign of x: −x is (−1)·x,
// the sign of a product is the product of the signs, and the sign of −1 is
// −1.
var SignNeg = signNegThm{family.Add(registry.ProofEntry{
	Name: "SignNeg",
	Key:  "prop_f76729034979541c",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ F.carrier",
		},
		Conclusion: "ordered_sign(F, lt, -x) = -ordered_sign(F, lt, x)",
	}, func(a *Argument, ordered OrderedFieldFact[on.F], x *Member[A, on.F]) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		one := a.MemberOf[on.F](a.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
		minusOne := comm_ring.NegIn.Read(ring).At(one)
		a.Show(
			"−x = (−1)·x, whose sign is the sign of −1 times the sign of x",
			ByArith(
				comm_ring.NegOneMulOn.Read(ring).At(x),
				SignMul.Read(ordered).At(minusOne, x),
				SignNegOne.Read(ordered)))
	}),
})}

// SignPow — The sign of a power is the power of the sign: the empty
// product is one, which is positive, and each further factor multiplies the
// sign by the sign of x, the sign of a product being the product of the signs.
var SignPow = signPowThm{family.Add(registry.ProofEntry{
	Name: "SignPow",
	Key:  "prop_d9462cdffec29a6b",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀x:A. ∀n:num.",
		Hypotheses: []string{
			"x ∈ F.carrier",
		},
		Conclusion: "ordered_sign(F, lt, monoid_pow(F.mul, F.one, x, n)) = ordered_sign(F, lt, x) ^ n",
	}, func(a *Argument, ordered OrderedFieldFact[on.F], x *Member[A, on.F], n *Expr[Nat]) {
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		one := a.MemberOf[on.F](a.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
		powers := comm_ring.MulMonoidOn.Read(ring)
		a.Induct(n)
		a.Base(
			"x⁰ is one, which is positive, and the sign to the power 0 is 1",
			Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(int_pow.PowClauses)),
			By(one, OnePositive.Read(ordered), SignValues.Read(ordered).At(one)))
		a.Step(
			"one more factor x multiplies the sign by the sign of x",
			func(b *Argument, earlier Fact) {
				power := comm_monoid.PowIn.Read(powers).At(x, n)
				b.Show(
					"the sign of x · xⁿ is the sign of x times the sign of xⁿ",
					Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(int_pow.PowClauses)),
					By(earlier, SignMul.Read(ordered).At(x, power)))
			})
	}),
})}

// FiniteGreatest — A finite nonempty subset of the carrier has a greatest
// point: adding the points one at a time, each new point is either above
// the greatest point so far, and then above all of them, or not, and then
// at or below it.
var FiniteGreatest = finiteGreatestThm{family.Add(registry.ProofEntry{
	Name: "FiniteGreatest",
	Key:  "prop_d7f4ed546c4f019b",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"finite(s)",
			"s ≠ ∅",
			"s ⊆ F.carrier",
		},
		Conclusion: "∃m:A. m ∈ s ∧ (∀x:A. x ∈ s ⇒ ordered_le(lt, x, m))",
	}, func(
		a *Argument,
		ordered OrderedFieldFact[on.F],
		s *Expr[Set[A]],
		finite, nonempty, inCarrier Fact,
	) {
		// Transitivity and trichotomy, read at the ordered field and installed
		// once, are the facts the set-theoretic closes of the step below cite.
		transitive, comparable :=
			a.Simplified(Transitive.Read(ordered)), a.Simplified(Trichotomy.Read(ordered))
		a.Show(
			"adding the points of s one at a time keeps a greatest point",
			ByInduction(finite_set.FiniteInduct, finite, Generalizing(inCarrier, nonempty), Case(
				"the empty set is excluded",
				Basic()),
				Case(
					"a point added to a nonempty subset of the carrier is "+
						"the new greatest point or leaves the old one greatest",
					Derive(func(b *Argument) {
						// the step reads ordered_le(lt, y, m) as its definition, y = m ∨ lt(y, m),
						// in the strict order the transitivity and comparability laws speak of
						b.Do(Unfold(OrderedLeDef))
						x := b.FixAs[A]("x")
						b.FixAs[Set[A]]("u")
						earlier := b.Assume()
						larger := b.Assume()
						pieces := b.Conjuncts(
							b.Have(
								"x and the points of u lie in the carrier",
								"x ∈ F.carrier ∧ u ⊆ F.carrier",
								BySets(larger)),
							"x lies in the carrier",
							"u lies in the carrier")
						xIn, uIn := pieces[0], pieces[1]
						b.Cases(b.TermAs[Bool]("u = ∅"))
						b.When(
							"x alone is greatest",
							func(c *Argument, empty Fact) {
								c.Take(x)
								c.Show(
									"x is the only point",
									BySets(empty))
							})
						b.Otherwise(
							"compare x with a greatest point m of u",
							func(c *Argument, nonEmpty Fact) {
								m, top := c.Obtain(
									"u has a greatest point m",
									"∃m:A. m ∈ u ∧ (∀y:A. y ∈ u ⇒ y = m ∨ lt(y, m))",
									By(nonEmpty, uIn, earlier))
								c.Cases(c.TermAs[Bool]("lt(m, x)"))
								c.When(
									"x lies above m",
									func(d *Argument, above Fact) {
										d.Take(x)
										belowX := d.Have(
											"by transitivity every point of u lies below x",
											"∀y:A. y ∈ u ⇒ lt(y, x)",
											BySets(transitive, above, xIn, uIn, top))
										d.Show(
											"so x is greatest",
											BySets(belowX))
									})
								c.Otherwise(
									"x does not lie above m",
									func(d *Argument, notAbove Fact) {
										d.Take(m)
										d.Show(
											"by comparability x is m or lies below it, so m stays greatest",
											BySets(notAbove, comparable, xIn, uIn, top))
									})
							})
					}))))
	}),
})}

// IncreasingCutsDef — increasing cuts are carrier points r(0) < r(1) < … <
// r(k − 1), each below every later one: the cut points of a sign table,
// where its open cells meet.
var IncreasingCutsDef = increasingCutsDefThm{family.Define(registry.DefEntry{
	Name:  "IncreasingCutsDef",
	Const: "increasing_cuts",
	Type:  "field_ops(A) → (A → A → bool) → num → (num → A) → bool",
	Key:   "prop_fe027894c9f02a0d",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀k:num. ∀r:(num → A). " +
			"    increasing_cuts(F, lt, k, r) ⇔ " +
			"    (∀i:num. i < k ⇒ r(i) ∈ F.carrier) ∧ (∀i j:num. i < j ∧ j < k ⇒ lt(r(i), r(j)))",
	},
})}

// IncreasingEnumeration — A finite subset of the carrier is listed by a
// strictly increasing sequence: induction taking out a greatest point lists
// the rest and appends that point last.
var IncreasingEnumeration = increasingEnumerationThm{family.Add(registry.ProofEntry{
	Name: "IncreasingEnumeration",
	Key:  "prop_c3a167e8c7cdc75",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"finite(s)",
			"s ⊆ F.carrier",
		},
		Conclusion: "∃k:num. ∃r:(num → A). " +
			"    (∀i:num. i < k ⇒ r(i) ∈ s) ∧ " +
			"    (∀i j:num. i < j ∧ j < k ⇒ lt(r(i), r(j))) ∧ " +
			"    (∀x:A. x ∈ s ⇒ ∃i:num. i < k ∧ x = r(i))",
	}, func(a *Argument, ordered OrderedFieldFact[on.F], s *Expr[Set[A]], finite, inCarrier Fact) {
		a.Show(
			"taking out a greatest point at each stage carries a "+
				"listing to every finite subset of the carrier, s among them",
			ByInduction(finite_set.FiniteInductDelete, finite, Generalizing(inCarrier),
				Case(
					"the empty set is listed by the empty sequence",
					Derive(func(b *Argument) {
						b.Assume()
						b.Take(b.TermAs[Nat]("0"))
						b.Show(
							"no index lies below zero and no point lies in ∅",
							ByArith(set_basic.NotInEmpty))
					})),
				Case(
					"a nonempty finite subset is listed by listing it "+
						"without a greatest point and appending that point",
					Derive(func(b *Argument) {
						t := b.FixAs[Set[A]]("t")
						given := b.Conjuncts(
							b.Assume(),
							"t is finite",
							"t is not empty")
						tIn := b.Assuming(
							b.TermAs[Bool]("t ⊆ F.carrier"),
							"a set reaching outside the carrier has the property vacuously",
							Given(func(c *Argument, outside Fact) {
								c.Show(
									"a point of t outside the carrier serves",
									BySets(outside))
							}))
						m, top := b.Unpack(GroupPremises(given[0], given[1], tIn, FiniteGreatest.Read(ordered).At(t)), "m")
						topParts := b.Conjuncts(
							top,
							"m lies in t",
							"every point of t is at or below m")
						mIn, below := topParts[0], b.Unfolded(topParts[1], OrderedLeDef)
						b.Take(m)
						b.Show(
							"m serves",
							SplitConj(
								Case(
									"m lies in t",
									By(mIn)),
								Case(
									"a listing of t without m extends by m to a listing of t",
									Derive(func(c *Argument) {
										rest := c.Assume()
										// The property's own antecedent, t ⊆ F.carrier, is tIn, already
										// resident: StripImp discharges it, where Assume would find no new
										// hypothesis to bind.
										c.Do(StripImp())
										k, _, listing := c.Obtain2(
											"t without m lies in the carrier, so it is listed by some k and r",
											"∃k:num. ∃r:(num → A). "+
												"    (∀i:num. i < k ⇒ r(i) ∈ delete(t, m)) ∧ "+
												"    (∀i j:num. i < j ∧ j < k ⇒ lt(r(i), r(j))) ∧ "+
												"    (∀y:A. y ∈ delete(t, m) ⇒ ∃i:num. i < k ∧ y = r(i))",
											BySets(tIn, rest))
										parts := c.Conjuncts(
											listing,
											"r lists points of t other than m",
											"r increases",
											"every point of t other than m is listed by r")
										inRest, increasing, coversRest := parts[0], parts[1], parts[2]
										c.Take(c.TermAs[Nat]("k + 1"))
										c.Take(c.TermAs[Fun[Nat, A]]("λi:num. COND(i < k, r(i), m)"))
										inT := c.Have(
											"every point of the extended sequence lies in t",
											"∀i:num. i < k + 1 ⇒ COND(i < k, r(i), m) ∈ t",
											BySets(inRest, mIn))
										extended := c.Have(
											"the extended sequence increases, m lying above every point of r",
											"∀i j:num. i < j ∧ j < k + 1 ⇒ lt(COND(i < k, r(i), m), COND(j < k, r(j), m))",
											Derive(func(d *Argument) {
												d.FixAs[Nat]("i")
												d.FixAs[Nat]("j")
												indices := d.Assume()
												iEarly := d.Have(
													"i comes before the last index",
													"i < k",
													ByArith(indices))
												d.Show(
													"below k the order is r's; at k it is m's",
													BySets(below, increasing, inRest, iEarly, indices))
											}))
										covers := c.Have(
											"every point of t is listed by the extended sequence",
											"∀x:A. x ∈ t ⇒ ∃i:num. i < k + 1 ∧ x = COND(i < k, r(i), m)",
											Derive(func(d *Argument) {
												d.FixAs[A]("x")
												xIn := d.Assume()
												d.Cases(d.TermAs[Bool]("x = m"))
												d.When(
													"m is listed last",
													func(e *Argument, isTop Fact) {
														e.Take(k)
														e.Show(
															"k is the last index",
															ByArith(isTop))
													})
												d.Otherwise(
													"another point is listed where r lists it",
													func(e *Argument, notTop Fact) {
														i, at := e.Obtain(
															"x lies in t without m, so r lists it",
															"∃i:num. i < k ∧ x = r(i)",
															BySets(notTop, coversRest, xIn))
														e.Take(i)
														e.Show(
															"below k the extended sequence is r",
															ByArith(at))
													})
											}))
										c.Show(
											"the three clauses of a listing",
											By(inT, extended, covers))
									}))))
					}))))
	}),
})}

// ConsecutiveIncreasing — a finite sequence of carrier points of an ordered
// field that increases from each index to the next increases throughout, so
// its points are increasing cuts: by induction on the larger index, through
// transitivity at the step.
var ConsecutiveIncreasing = consecutiveIncreasingThm{family.Add(registry.ProofEntry{
	Name: "ConsecutiveIncreasing",
	Key:  "prop_23d9d70907ab7a00",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀n:num. ∀s:(num → A).",
		Hypotheses: []string{
			"∀i:num. i < n ⇒ s(i) ∈ F.carrier",
			"∀i:num. suc(i) < n ⇒ lt(s(i), s(suc(i)))",
		},
		Conclusion: "increasing_cuts(F, lt, n, s)",
	}, func(
		a *Argument,
		ordered OrderedFieldFact[on.F],
		n *Expr[Nat],
		s *Arrow[Nat, A],
		within, consecutive Fact,
	) {
		increasing := a.Have(
			"by induction on the larger index d, s(c) lies below s(d) whenever c < d < n",
			"∀c d:num. c < d ∧ d < n ⇒ lt(s(c), s(d))",
			Derive(func(b *Argument) {
				c := b.FixAs[Nat]("c")
				b.Induct("d")
				b.Base(
					"no index lies below 0",
					func(e *Argument) {
						given := e.Conjuncts(
							e.Assume(),
							"c lies below 0",
							"0 lies below n")
						e.Show(
							"c < 0 is impossible",
							ByArith(given[0]))
					})
				b.Step(
					"s(c) lies below s(d), or c = d, and s(d) below s(d + 1)",
					func(e *Argument, ih Fact) {
						given := e.Conjuncts(
							e.Assume(),
							"c lies below d + 1",
							"d + 1 lies below n")
						d := e.TermAs[Nat]("d")
						next := e.Have(
							"s(d) lies below s(d + 1)",
							"lt(s(d), s(suc(d)))",
							By(consecutive.At(d), given[1]))
						e.Cases(e.TermAs[Bool]("c = d"))
						e.When(
							"c = d: the step itself",
							func(f *Argument, same Fact) {
								f.Show(
									"s(c) = s(d) lies below s(d + 1)",
									By(Normalized, same, next))
							})
						e.Otherwise(
							"c < d: the induction hypothesis, then the step",
							func(f *Argument, distinct Fact) {
								bounds := f.Have(
									"c < d, and c, d and d + 1 lie below n",
									"c < d ∧ d < n ∧ c < n ∧ suc(d) < n",
									ByArith(distinct, given[0], given[1]))
								below := f.Have(
									"s(c) lies below s(d)",
									"lt(s(c), s(d))",
									By(ih, bounds))
								point := func(i *Expr[Nat]) *Member[A, on.F] {
									return f.MemberOf[on.F](s.Apply(i), GroupPremises(bounds, within.At(i)))
								}
								f.Show(
									"by transitivity",
									By(below, next, Transitive.Read(ordered).At(point(c), point(d), point(f.TermAs[Nat]("suc(d)")))))
							})
					})
			}))
		a.Show(
			"the points lie in the carrier and increase",
			By(within, increasing, IncreasingCutsDef))
	}),
})}

// TransportOrderedField — A map one-to-one on the carrier is an
// ordered-field embedding of F into its transported copy: the copy of F
// along i is a field, i a ring isomorphism onto it, so the order carried
// along i makes the copy an ordered field (TransportOrderIsomorphism); and
// the preimage of i(x) is x, so i keeps and reflects the order.
var TransportOrderedField = transportOrderedFieldThm{family.Add(registry.ProofEntry{
	Name: "TransportOrderedField",
	Key:  "prop_412b139a141b1257",
	Reading: "Only injectivity on the source carrier is needed. Every order comparison in " +
		"the transported structure is on the image, where the chosen preimage recovers its source.",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀i:(A → B).",
		Hypotheses: []string{
			"ordered_field_on(F, lt)",
			"injective_on(F.carrier, i)",
		},
		Conclusion: "ordered_field_embedding(F, " +
			"    lt, " +
			"    transport_field(i, F), " +
			"    transport_order(i, F.carrier, lt), " +
			"    i)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		i *Arrow[A, B],
		ordered OrderedFieldFact[on.F],
		injective Fact,
	) {
		carrier := a.TermAs[Set[A]]("F.carrier")
		copyF := a.TermAs[FieldOps[B]]("transport_field(i, F)")
		copyOrder := a.TermAs[Fun2[B, B, Bool]]("transport_order(i, F.carrier, lt)")
		fieldCopy := a.Have(
			"the copy of F along i is a field",
			"field_on(transport_field(i, F))",
			By(FieldOn.Read(ordered), injective, ring_transport.TransportFieldOn.At(i, F)))
		embedding := a.Have(
			"i is a ring homomorphism from F to its copy",
			"ring_homomorphism(field_ring(F), field_ring(transport_field(i, F)), i)",
			By(FieldOn.Read(ordered), injective, ring_transport.TransportFieldHomomorphism.At(i, F)))
		ringF := a.TermAs[module_record.RingOps[A]]("field_ring(F)")
		ringCopy := a.TermAs[module_record.RingOps[B]]("field_ring(transport_field(i, F))")
		isomorphism := a.Have(
			"i is a ring isomorphism from F onto its copy, whose carrier is the image of F's",
			"ring_isomorphism(field_ring(F), field_ring(transport_field(i, F)), i)",
			By(
				embedding,
				injective,
				ring_homomorphism.RingIsomorphismDef.At(ringF, ringCopy, i),
				ring_transport.TransportFieldDef.At(i, F)))
		orderedCopy := a.Have(
			"so the copy, with the order carried along i, is an ordered field",
			"ordered_field_on(transport_field(i, F), transport_order(i, F.carrier, lt))",
			By(fieldCopy, isomorphism, TransportOrderIsomorphism.Read(ordered).At(copyF, i)))
		reflects := a.Have(
			"i keeps and reflects the order, the preimage of i(x) being x",
			Statement{
				Binders: "∀x y:A.",
				Hypotheses: []string{
					"x ∈ F.carrier",
					"y ∈ F.carrier",
				},
				Conclusion: "lt(x, y) ⇔ transport_order(i, F.carrier, lt, i(x), i(y))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				given := b.Conjuncts(
					b.Assume(),
					"x lies in F",
					"y lies in F")
				b.Show(
					"the copy compares i(x) and i(y) at x and y",
					By(
						TransportOrderDef.At(i, carrier, lt, i.Apply(x), i.Apply(y)),
						functions.InverseOnLeft.At(carrier, i, x),
						functions.InverseOnLeft.At(carrier, i, y),
						injective,
						given[0],
						given[1]))
			}))
		a.Show(
			"F and its ordered copy are ordered fields, i a one-to-one "+
				"ring homomorphism keeping and reflecting the order",
			By(
				OrderedEmbeddingDef.At(F, lt, copyF, copyOrder, i),
				ordered,
				orderedCopy,
				embedding,
				injective,
				reflects))
	}),
})}

// TransportOrderIsomorphism — An order is carried along a ring isomorphism
// onto any field: two points of the target are compared by their preimages,
// and the inverse, a ring homomorphism, carries the target's sums, products
// and zero back to the source's, where the order's axioms hold.
var TransportOrderIsomorphism = transportOrderIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "TransportOrderIsomorphism",
	Key:  "prop_8bef60e1c1a51a4a",
	Build: OrderedFieldOn.Law(Statement{
		Binders: "∀G:field_ops(B). ∀i:(A → B).",
		Hypotheses: []string{
			"field_on(G)",
			"ring_isomorphism(field_ring(F), field_ring(G), i)",
		},
		Conclusion: "ordered_field_on(G, transport_order(i, F.carrier, lt))",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		ordered OrderedFieldFact[on.F],
		G *Expr[FieldOps[B]],
		i *Arrow[A, B],
		fieldG field.FieldFact[on.G],
		iso Fact,
	) {
		ringF := a.TermAs[module_record.RingOps[A]]("field_ring(F)")
		ringG := a.TermAs[module_record.RingOps[B]]("field_ring(G)")
		reverse := a.Have(
			"the inverse of i is a ring isomorphism back onto F",
			"ring_isomorphism(field_ring(G), field_ring(F), inverse_on(F.carrier, i))",
			By(iso, ring_homomorphism.IsomorphismInverse.At(ringF, ringG, i)))
		inverse := a.Conjuncts(
			a.Unfolded(reverse, ring_homomorphism.RingIsomorphismDef),
			"The inverse is a homomorphism",
			"The inverse is injective",
			"The inverse covers the source")
		inverseHom, inverseInj := inverse[0], inverse[1]
		a.Show(
			"the target with the order carried along i is an ordered field",
			OrderedFieldOn.Intro(
				Case(
					"The target retains its field structure",
					By(fieldG)),
				Case(
					"The transported order is irreflexive",
					Simp(Fwd(TransportOrderDef)),
					By(Irreflexive.Read(ordered), ring_homomorphism.MapIn.Read(inverseHom))),
				Case(
					"The transported order is transitive",
					Simp(Fwd(TransportOrderDef)),
					By(Transitive.Read(ordered), ring_homomorphism.MapIn.Read(inverseHom))),
				Case(
					"Injectivity turns source trichotomy into target trichotomy",
					Simp(Fwd(TransportOrderDef)),
					By(
						Trichotomy.Read(ordered),
						inverseInj,
						ring_homomorphism.MapIn.Read(inverseHom),
						functions.InjectiveOnDef)),
				Case(
					"The inverse takes target sums to source sums",
					Simp(Fwd(TransportOrderDef)),
					By(
						AddPreservesOrder.Read(ordered),
						ring_homomorphism.MapIn.Read(inverseHom),
						ring_homomorphism.MapAdd.Read(inverseHom))),
				Case(
					"The inverse takes target positive products to source positive products",
					Simp(Fwd(TransportOrderDef)),
					By(
						MulPositive.Read(ordered),
						ring_homomorphism.MapIn.Read(inverseHom),
						ring_homomorphism.MapMul.Read(inverseHom),
						ring_homomorphism.MapZero.Read(inverseHom)))))
	}),
})}

// EuclideanField — An ordered field in which every positive element is a square.
var EuclideanField = euclideanFieldThm{family.DefineStructure(registry.DefEntry{
	Name: "EuclideanField", Const: "euclidean_field", Type: "field_ops(A) → (A → A → bool) → bool",
	Key: "prop_6281d3f0fa01037",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). " +
			"    euclidean_field(F, lt) ⇔ " +
			"    ordered_field_on(F, lt) ∧ " +
			"    (∀a:A. a ∈ F.carrier ∧ lt(F.zero, a) ⇒ ∃b:A. b ∈ F.carrier ∧ F.mul(b, b) = a)",
	},
	Deps: []registry.EntryLike{OrderedFieldOn},
})}

// EuclideanOrderedField — A Euclidean field is an ordered field.
var EuclideanOrderedField = euclideanOrderedFieldThm{family.Add(registry.ProofEntry{
	Name:  "EuclideanOrderedField",
	Key:   "prop_8cd43b44aaef245f",
	Build: EuclideanField.Axiom("ordered_field_on(F, lt)"),
})}

// PositiveIsSquare — Every positive element of a Euclidean field is a square.
var PositiveIsSquare = positiveIsSquareThm{family.Add(registry.ProofEntry{
	Name: "PositiveIsSquare",
	Key:  "prop_c393f56226083ad1",
	Build: EuclideanField.Axiom(Statement{
		Binders: "∀a:A.",
		Hypotheses: []string{
			"a ∈ F.carrier",
			"lt(F.zero, a)",
		},
		Conclusion: "∃b:A. b ∈ F.carrier ∧ b * b = a",
	}),
})}

// PositiveSquareRoot — Every positive element of a Euclidean field has a
// positive square root: a square root r of it is not zero, so r or −r is
// positive, and both square to it.
var PositiveSquareRoot = positiveSquareRootThm{family.Add(registry.ProofEntry{
	Name: "PositiveSquareRoot",
	Key:  "prop_746af0cadd9c2528",
	Build: EuclideanField.Law(Statement{
		Binders: "∀a:A.",
		Hypotheses: []string{
			"a ∈ F.carrier",
			"lt(F.zero, a)",
		},
		Conclusion: "∃b:A. b ∈ F.carrier ∧ lt(F.zero, b) ∧ b * b = a",
	}, func(arg *Argument, euclidean EuclideanFieldFact[on.F], a *Member[A, on.F], positive Fact) {
		ordered := EuclideanOrderedField.Read(euclidean)
		ring := field.RingOn.Read(FieldOn.Read(ordered))
		zero := arg.TermAs[A]("F.zero")
		zeroIn := arg.MemberOf[on.F](zero, comm_ring.ZeroIn.Read(ring))
		r, root := arg.ObtainAs[A](
			"Choose a square root",
			"∃r:A. r ∈ F.carrier ∧ r * r = a",
			By(PositiveIsSquare.Read(euclidean).At(a), positive))
		rootParts := arg.Conjuncts(
			root,
			"The root belongs to the field",
			"Its square is a")
		rm := arg.MemberOf[on.F](r, rootParts[0])
		notPositive := arg.Unless(
			arg.TermAs[Bool]("lt(F.zero, r)"),
			"A positive root already has the required sign",
			Given(func(b *Argument, rPositive Fact) {
				b.Take(r)
				b.Show(
					"The root is positive and squares to a",
					By(rPositive, root))
			}))
		negative := arg.Have(
			"A nonpositive root of a positive element is negative",
			"lt(r, F.zero)",
			By(
				Normalized,
				zeroIn,
				notPositive,
				positive,
				root,
				Trichotomy.Read(ordered).At(zeroIn, rm),
				Irreflexive.Read(ordered).At(zeroIn),
				comm_ring.MulLeftZeroOn.Read(ring).At(zeroIn)))
		negSquare := arg.Have(
			"Negation preserves the square",
			"-r * -r = a",
			By(root, comm_ring.MulNegNegOn.Read(ring).At(rm, rm)))
		arg.Take(arg.TermAs[A]("-r"))
		arg.Show(
			"The negative of this root is positive",
			By(
				negative,
				negSquare,
				root,
				comm_ring.NegIn.Read(ring).At(rm),
				NegationReversesSign.Read(ordered).At(rm)))
	}),
})}

// TransportEuclideanIsomorphism — A Euclidean order is carried along a ring
// isomorphism onto any field: the transported order is an order, and a point
// positive in it has a positive preimage, whose square root i carries to a
// square root of the point.
var TransportEuclideanIsomorphism = transportEuclideanIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "TransportEuclideanIsomorphism",
	Key:  "prop_e40ed3b54fc1c157",
	Build: EuclideanField.Law(Statement{
		Binders: "∀G:field_ops(B). ∀i:(A → B).",
		Hypotheses: []string{
			"field_on(G)",
			"ring_isomorphism(field_ring(F), field_ring(G), i)",
		},
		Conclusion: "euclidean_field(G, transport_order(i, F.carrier, lt))",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		euclidean EuclideanFieldFact[on.F],
		G *Expr[FieldOps[B]],
		i *Arrow[A, B],
		fieldG field.FieldFact[on.G],
		iso Fact,
	) {
		ordered := EuclideanOrderedField.Read(euclidean)
		carrier := a.TermAs[Set[A]]("F.carrier")
		ringF := a.TermAs[module_record.RingOps[A]]("field_ring(F)")
		ringG := a.TermAs[module_record.RingOps[B]]("field_ring(G)")
		reverse := a.Have(
			"the inverse of i is a ring isomorphism back onto F",
			"ring_isomorphism(field_ring(G), field_ring(F), inverse_on(F.carrier, i))",
			By(iso, ring_homomorphism.IsomorphismInverse.At(ringF, ringG, i)))
		forward := a.Conjuncts(
			a.Unfolded(iso, ring_homomorphism.RingIsomorphismDef),
			"The embedding is a homomorphism",
			"The embedding is injective",
			"The embedding covers the target")
		inverse := a.Conjuncts(
			a.Unfolded(reverse, ring_homomorphism.RingIsomorphismDef),
			"The inverse is a homomorphism",
			"The inverse is injective",
			"The inverse covers the source")
		hom, onto, inverseHom := forward[0], forward[2], inverse[0]
		a.Show(
			"the target with the order carried along i is a Euclidean field",
			EuclideanField.Intro(
				Case(
					"The order carried along i makes the target an ordered field",
					By(fieldG, iso, TransportOrderIsomorphism.Read(ordered).At(G, i))),
				Case(
					"Every positive element of G has a square root",
					Derive(func(b *Argument) {
						point := b.FixAs[B]("a")
						positive := b.Assume()
						r, root := b.ObtainAs[A](
							"A source square root of the positive preimage",
							"∃r:A. r ∈ F.carrier ∧ r * r = inverse_on(F.carrier, i, a)",
							By(
								positive,
								PositiveIsSquare.Read(euclidean).AsFact().At(b.TermAs[A]("inverse_on(F.carrier, i, a)")),
								ring_homomorphism.MapIn.Read(inverseHom),
								ring_homomorphism.MapZero.Read(inverseHom),
								TransportOrderDef))
						b.Take(i.Apply(r))
						b.Show(
							"The image square is the original positive element",
							By(
								Normalized,
								onto,
								root,
								positive,
								ring_homomorphism.MapIn.Read(hom),
								ring_homomorphism.MapMul.Read(hom),
								functions.InverseOnRight.At(carrier, i, point)))
					}))))
	}),
})}
