// quotient_ring.go — the chapter: the ring of cosets of an ideal, the
// projection onto it, the number of the cosets, the first isomorphism
// theorem and the isomorphism of two quotients an automorphism induces,
// the domain and the field the cosets form at a prime and at a maximal
// ideal, and the index of an ideal: how it falls as the ideal grows,
// what a finite index makes of a prime ideal and of a chain of ideals, and
// the simple layer above an ideal J inside a larger ideal I in which J has
// finitely many cosets.

package quotient_ring

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_isomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The operations and the records
// ---------------------------------------------------------------------------

// QuotientMulDef — `quotient_mul(add, mul, I, s, t)`: the products of a
// member of s with a member of t, pushed onto a coset by adding I. For
// two cosets of an ideal it is the coset of the product
// (QuotientMulCoset); it chooses no representative.
var QuotientMulDef = quotientMulDefThm{family.Define(registry.DefEntry{
	Name:     "QuotientMulDef",
	Key:      "prop_4c62a523e582e37b",
	Const:    "quotient_mul",
	Type:     "(A → A → A) → (A → A → A) → set(A) → set(A) → set(A) → set(A)",
	Implicit: []string{"add", "mul"},
	Equations: []string{
		"∀add mul:(A → A → A). ∀I s t:set(A). " +
			"    quotient_mul(add, mul, I, s, t) = set_mul(add, set_mul(mul, s, t), I)",
	},
})}

// QuotientSubDef — `quotient_sub(add, neg, s, t)`: s plus the negation
// of t, the quotient group's difference of two cosets.
var QuotientSubDef = quotientSubDefThm{family.Define(registry.DefEntry{
	Name:     "QuotientSubDef",
	Key:      "prop_eab576567e512a3b",
	Const:    "quotient_sub",
	Type:     "(A → A → A) → (A → A) → set(A) → set(A) → set(A)",
	Implicit: []string{"add", "neg"},
	Equations: []string{
		"∀add:(A → A → A). ∀neg:(A → A). ∀s t:set(A). " +
			"    quotient_sub(add, neg, s, t) = set_mul(add, s, set_inv(neg, t))",
	},
})}

// QuotientInvDef — `quotient_inv(add, mul, one, c, I, s)`: the inverse
// of a coset, chosen among the cosets of I in c that multiply s to the
// coset of one; the zero coset I is sent to itself, as a field's
// convention asks. Where no coset inverts s — I not maximal — the
// choice is a set nothing is said about.
var QuotientInvDef = quotientInvDefThm{family.Define(registry.DefEntry{
	Name:     "QuotientInvDef",
	Key:      "prop_9345560ae3034571",
	Const:    "quotient_inv",
	Type:     "(A → A → A) → (A → A → A) → A → set(A) → set(A) → set(A) → set(A)",
	Implicit: []string{"add", "mul", "one"},
	Equations: []string{
		"∀add mul:(A → A → A). ∀one:A. ∀c I s:set(A). " +
			"    quotient_inv(add, mul, one, c, I, s) = " +
			"    COND(s = I, " +
			"        I, " +
			"        εt:set(A). " +
			"            t ∈ left_cosets(add, c, I) ∧ " +
			"            quotient_mul(add, mul, I, t, s) = left_coset(add, one, I))",
	},
	Deps: []registry.EntryLike{QuotientMulDef},
})}

// QuotientDivDef — `quotient_div(add, mul, one, c, I, s, t)`: s times
// the inverse of t.
var QuotientDivDef = quotientDivDefThm{family.Define(registry.DefEntry{
	Name:     "QuotientDivDef",
	Key:      "prop_10c843450bd05a92",
	Const:    "quotient_div",
	Type:     "(A → A → A) → (A → A → A) → A → set(A) → set(A) → set(A) → set(A) → set(A)",
	Implicit: []string{"add", "mul", "one"},
	Equations: []string{
		"∀add mul:(A → A → A). ∀one:A. ∀c I s t:set(A). " +
			"    quotient_div(add, mul, one, c, I, s, t) = " +
			"    quotient_mul(add, mul, I, s, quotient_inv(add, mul, one, c, I, t))",
	},
	Deps: []registry.EntryLike{QuotientMulDef, QuotientInvDef},
})}

// IdealQuotientRingDef — `ideal_quotient_ring(R, I)`: the ring R/I as a
// ring record, the cosets of I under the coset operations, I itself the
// zero and one + I the one.
var IdealQuotientRingDef = idealQuotientRingDefThm{family.Define(registry.DefEntry{
	Name:  "IdealQuotientRingDef",
	Key:   "prop_5e3d80af6e5f77dc",
	Const: "ideal_quotient_ring",
	Type:  "ring_ops(A) → set(A) → ring_ops(set(A))",
	Equations: []string{
		"∀R:ring_ops(A). ∀I:set(A). " +
			"    ideal_quotient_ring(R, I) = " +
			"    mk_ring(set_mul(R.add), " +
			"        I, " +
			"        set_inv(R.neg), " +
			"        quotient_mul(R.add, R.mul, I), " +
			"        left_coset(R.add, R.one, I), " +
			"        quotient_sub(R.add, R.neg), " +
			"        left_cosets(R.add, R.carrier, I))",
	},
	Deps: []registry.EntryLike{QuotientMulDef, QuotientSubDef},
	Reading: "Its operations are the coset operations at I read off the record R, so " +
		"it is a commutative ring when R is one and I an ideal of it; koszul_quotient(R, g) " +
		"is the case I = ideal_span({g}). At I = R.carrier it is the zero ring on one coset; " +
		"at I = {R.zero} its members are the singletons and it is R again. It lives on set(A).",
})}

// IdealQuotientFieldDef — `ideal_quotient_field(R, I)`: the cosets of I
// as a field record, ideal_quotient_ring's six operations with the
// inverse and the division of cosets, a field when I is a maximal ideal.
var IdealQuotientFieldDef = idealQuotientFieldDefThm{family.Define(registry.DefEntry{
	Name:  "IdealQuotientFieldDef",
	Key:   "prop_4723108572ce022b",
	Const: "ideal_quotient_field",
	Type:  "ring_ops(A) → set(A) → field_ops(set(A))",
	Equations: []string{
		"∀R:ring_ops(A). ∀I:set(A). " +
			"    ideal_quotient_field(R, I) = " +
			"    mk_field(set_mul(R.add), " +
			"        I, " +
			"        set_inv(R.neg), " +
			"        quotient_mul(R.add, R.mul, I), " +
			"        left_coset(R.add, R.one, I), " +
			"        quotient_sub(R.add, R.neg), " +
			"        quotient_inv(R.add, R.mul, R.one, R.carrier, I), " +
			"        quotient_div(R.add, R.mul, R.one, R.carrier, I), " +
			"        left_cosets(R.add, R.carrier, I))",
	},
	Deps: []registry.EntryLike{QuotientMulDef, QuotientSubDef, QuotientInvDef, QuotientDivDef},
})}

// IdealQuotientProjectionDef — `ideal_quotient_projection(R, I, a)`: the
// coset a + I; `ideal_quotient_projection(R, I)` is the projection of R
// onto R/I.
var IdealQuotientProjectionDef = idealQuotientProjectionDefThm{family.Define(registry.DefEntry{
	Name:  "IdealQuotientProjectionDef",
	Key:   "prop_349e2e2bc79ac687",
	Const: "ideal_quotient_projection",
	Type:  "ring_ops(A) → set(A) → A → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀I:set(A). ∀a:A. ideal_quotient_projection(R, I, a) = left_coset(R.add, a, I)",
	},
})}

// ---------------------------------------------------------------------------
// The cosets of an ideal
// ---------------------------------------------------------------------------

// IdealSubgroup — an ideal is an additive subgroup: its subset, zero, addition
// and negation closure are exactly the subgroup conditions.
var IdealSubgroup = idealSubgroupThm{family.Add(registry.ProofEntry{
	Name: "IdealSubgroup",
	Key:  "prop_e363a0228c4c96b1",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
		},
		Conclusion: "subgroup(additive_group(R), I)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], I *Expr[Set[A]], ideal Fact) {
			a.Show(
				"the ideal's additive closure makes it a subgroup",
				Unfold(group.SubgroupDef),
				By(
					ring_ideal.IdealSubset.Read(ideal),
					ring_ideal.IdealZero.Read(ideal),
					ring_ideal.IdealAdd.Read(ideal),
					At(ring_ideal.IdealNeg.Read(ring), I)))
		}),
})}

// IdealNormal — an ideal is normal in the additive group: additive
// conjugation fixes each of its elements.
var IdealNormal = idealNormalThm{family.Add(registry.ProofEntry{
	Name: "IdealNormal",
	Key:  "prop_c296bc5a8610668c",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
		},
		Conclusion: "normal_subgroup(additive_group(R), I)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], I *Expr[Set[A]], ideal Fact) {
			conjugation := a.Have(
				"additive conjugation fixes every element",
				"∀g x:A. g ∈ R.carrier ∧ x ∈ R.carrier ⇒ (g + x) + -g = x",
				ByArith(ring))
			a.Show(
				"the ideal is an additive subgroup, and additive conjugation preserves it",
				Unfold(group.NormalSubgroupDef),
				BySets(ring_ideal.IdealSubset.Read(ideal), ideal, IdealSubgroup.Read(ring).At(I), conjugation))
		}),
})}

// CosetEqIff — two cosets by points of c are one coset exactly when the
// points differ by a member of I: read additively, the group's criterion
// asks -x + y of I instead, and x - y and -x + y are each other's
// negations, which an ideal holds together.
var CosetEqIff = cosetEqIffThm{family.Add(registry.ProofEntry{
	Name: "CosetEqIff",
	Key:  "prop_102e313657fc1788",
	Reading: "The cosets are those of the additive group, so the criterion is the coset relation " +
		"of a subgroup read in the ring's notation; the ideal's closure under products is not used.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A). ∀x y:A.",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"x ∈ R.carrier",
			"y ∈ R.carrier",
		},
		Conclusion: "left_coset(R.add, x, I) = left_coset(R.add, y, I) ⇔ x - y ∈ I",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], I *Expr[Set[A]], x, y *Expr[A], given Fact) {
			parts := a.Conjuncts(
				given,
				"I is an ideal",
				"x lies in c",
				"so does y")
			ideal, xIn, yIn := parts[0], parts[1], parts[2]
			additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
			cosets := a.Have(
				"read additively, the cosets agree exactly when -x + y lies in I",
				"left_coset(R.add, x, I) = left_coset(R.add, y, I) ⇔ -x + y ∈ I",
				By(group.LeftCosetEqOn.Read(additive), xIn, yIn, IdealSubgroup.Read(ring), ideal))
			difference := a.Have(
				"x - y is the negation of -x + y",
				"x - y = -(-x + y)",
				ByArith(ring, xIn, yIn))
			sum := a.Have(
				"and -x + y the negation of x - y",
				"-x + y = -(x - y)",
				ByArith(ring, xIn, yIn))
			a.Iff()
			a.Forward(
				"equal cosets put -x + y in I, and with it its negation x - y",
				func(b *Argument, same Fact) {
					b.Show(
						"an ideal holds the negation of a member",
						difference.Rw(),
						By(ring_ideal.IdealNeg.Read(ring), ideal, cosets, same))
				})
			a.Backward(
				"x - y in I puts its negation -x + y in I, so the cosets agree",
				func(b *Argument, inI Fact) {
					negated := b.Have(
						"an ideal holds the negation of a member",
						"-x + y ∈ I",
						sum.Rw(),
						By(ring_ideal.IdealNeg.Read(ring), ideal, inI))
					b.Show(
						"so the cosets agree",
						By(cosets, negated))
				})
		}),
})}

// CosetEqIdealIff — a coset by a point of c is I itself exactly when the
// point lies in I: the ideal is a subgroup of the additive group, where a
// coset by a point of the group is the subgroup exactly when the point
// lies in it.
var CosetEqIdealIff = cosetEqIdealIffThm{family.Add(registry.ProofEntry{
	Name: "CosetEqIdealIff",
	Key:  "prop_aabfa6423073d0dd",
	Reading: "The ideal enters as a subgroup of the additive group on " +
		"c, which puts I inside R.carrier. x ∈ R.carrier is load-bearing: " +
		"off c the addition is unconstrained, and x + I can be I with x ∉ I.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A). ∀x:A.",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"x ∈ R.carrier",
		},
		Conclusion: "left_coset(R.add, x, I) = I ⇔ x ∈ I",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], I *Expr[Set[A]], x *Expr[A], given Fact) {
			parts := a.Conjuncts(
				given,
				"I is an ideal",
				"x lies in c")
			ideal, xIn := parts[0], parts[1]
			additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
			a.Show(
				"in the additive group, the coset of x by the subgroup I is I exactly when x lies in I",
				By(quotient_group.LeftCosetIsSubgroupIffIn.Read(additive), xIn, IdealSubgroup.Read(ring), ideal))
		}),
})}

// QuotientMulCoset — the product of the cosets of x and y is the coset
// of x * y. A point of the product is (x + i) * (y + j) + k with i, j
// and k in I, which multiplies out to x * y plus x * j + y * i + i * j + k,
// a sum of members of I; a point x * y + k of the coset of x * y is the
// product of x and y, each in its own coset, plus k.
var QuotientMulCoset = quotientMulCosetThm{family.Add(registry.ProofEntry{
	Name: "QuotientMulCoset",
	Key:  "prop_9c386c28a55cbd5e",
	Reading: "The forward inclusion uses commutativity, i * y lying in I as y * i; the " +
		"backward one needs x and y each in its own coset, x being x + zero with R.zero ∈ I.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A). ∀x y:A.",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"x ∈ R.carrier",
			"y ∈ R.carrier",
		},
		Conclusion: "quotient_mul(I, left_coset(R.add, x, I), left_coset(R.add, y, I)) = " +
			"left_coset(R.add, x * y, I)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], I *Expr[Set[A]], x, y *Expr[A], given Fact) {
			parts := a.Conjuncts(
				given,
				"I is an ideal",
				"x lies in c",
				"so does y")
			ideal, xIn, yIn := parts[0], parts[1], parts[2]
			additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
			pointwise := a.Have(
				"the product of the two cosets and the coset of x * y have the same points",
				"∀z:A. "+
					"    z ∈ quotient_mul(I, left_coset(R.add, x, I), left_coset(R.add, y, I)) ⇔ "+
					"    z ∈ left_coset(R.add, x * y, I)",
				Derive(func(b *Argument) {
					b.FixAs[A]("z")
					b.Iff()
					b.Forward(
						"a point (x + i) * (y + j) + k of the product is x "+
							"* y plus x * j + y * i + i * j + k, which I holds",
						func(d *Argument, member Fact) {
							_, _, _, point := d.Obtain3As[A, A, A](
								"z is (x + i) * (y + j) + k for some i, j and k in I",
								"∃i j k:A. i ∈ I ∧ j ∈ I ∧ k ∈ I ∧ z = (x + i) * (y + j) + k",
								member.Simp(
									Fwd(QuotientMulDef),
									Fwd(quotient_group.InSetMul),
									Fwd(group.LeftCosetDef),
									Fwd(set_basic.InImage)),
								By(member))
							pieces := d.Conjuncts(
								point,
								"i lies in I",
								"so does j",
								"and so does k",
								"z is (x + i) * (y + j) + k")
							inC := d.Have(
								"i, j and k lie in c, as I does",
								"i ∈ R.carrier ∧ j ∈ R.carrier ∧ k ∈ R.carrier",
								BySets(ring_ideal.IdealSubset, ideal, pieces[0], pieces[1], pieces[2]))
							inI := d.Have(
								"I absorbs the products x * j, y * i and i * j, and holds their sum with k",
								"x * j + y * i + i * j + k ∈ I",
								By(ideal, pieces[0], pieces[1], pieces[2], xIn, yIn, inC, ring_ideal.IdealAdd, ring_ideal.IdealMul))
							regroup := d.Have(
								"z multiplies out as x * y + (x * j + y * i + i * j + k)",
								"z = x * y + (x * j + y * i + i * j + k)",
								pieces[3].Rw(),
								ByArith(ring, xIn, yIn, inC))
							d.Do(Simp(Fwd(group.LeftCosetDef), Fwd(set_basic.InImage)))
							d.Take(d.TermAs[A]("x * j + y * i + i * j + k"))
							d.Show(
								"so z is x * y plus a point of I",
								By(regroup, inI))
						})
					b.Backward(
						"a point x * y + k of the coset of x * y is x times y, each in its own coset, plus k",
						func(d *Argument, member Fact) {
							k, point := d.UnpackAs[A](d.Simplified(
								member,
								Fwd(group.LeftCosetDef),
								Fwd(set_basic.InImage)), "k")
							own := d.Have(
								"x and y each lie in their own coset, I being a subgroup",
								"x ∈ left_coset(R.add, x, I) ∧ y ∈ left_coset(R.add, y, I)",
								By(group.InOwnLeftCosetOn.Read(additive), xIn, yIn, IdealSubgroup.Read(ring), ideal))
							product := d.Have(
								"so x * y lies in the product of the two cosets",
								"x * y ∈ set_mul(left_coset(R.add, x, I), left_coset(R.add, y, I))",
								Simp(Fwd(quotient_group.InSetMul)),
								Witness(x),
								Witness(y),
								By(own))
							// InSetMul opens both set_mul layers of the goal, so the
							// product's membership is read back through it at the close.
							d.Do(Simp(Fwd(QuotientMulDef), Fwd(quotient_group.InSetMul)))
							d.Take(d.TermAs[A]("x * y"))
							d.Take(k)
							d.Show(
								"so z is x * y, a point of that product, plus k",
								By(product, point, quotient_group.InSetMul))
						})
				}))
			a.Show(
				"two sets with the same points are equal",
				By(pointwise, set_basic.Extension))
		}),
})}

// QuotientSubCoset — the difference of the cosets of x and y is the
// coset of x - y: subtracting a coset adds its negations, which in the
// additive group, where I is normal, form the coset of -y; the sum of
// the cosets of x and -y is the coset of x + -y, and x + -y is x - y.
var QuotientSubCoset = quotientSubCosetThm{family.Add(registry.ProofEntry{
	Name: "QuotientSubCoset",
	Key:  "prop_c8bec9ef76da6f6f",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A). ∀x y:A.",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"x ∈ R.carrier",
			"y ∈ R.carrier",
		},
		Conclusion: "quotient_sub(left_coset(R.add, x, I), left_coset(R.add, y, I)) = " +
			"left_coset(R.add, x - y, I)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], I *Expr[Set[A]], x, y *Expr[A], given Fact) {
			parts := a.Conjuncts(
				given,
				"I is an ideal",
				"x lies in c",
				"so does y")
			ideal := parts[0]
			xm, ym := a.MemberOf[on.R](x, parts[1]), a.MemberOf[on.R](y, parts[2])
			negY := comm_ring.NegIn.Read(ring).At(ym)
			additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
			normal := a.Have(
				"I is a normal subgroup of the additive group on c",
				"normal_subgroup(additive_group(R), I)",
				By(IdealNormal.Read(ring), ideal))
			a.Show(
				"subtract by adding the negations of the coset of y, then add two cosets",
				CalcEq(
					Leg(
						a.TermAs[Set[A]](
							"set_mul(R.add, left_coset(R.add, x, I), set_inv(R.neg, left_coset(R.add, y, I)))"),
						"subtracting a coset adds its negations",
						Cite(QuotientSubDef)),
					Leg(
						a.TermAs[Set[A]]("set_mul(R.add, left_coset(R.add, x, I), left_coset(R.add, -y, I))"),
						"the negations of the coset of y are the coset of -y",
						By(quotient_group.LeftCosetInvOn.Read(additive).At(I, ym), normal)),
					Leg(
						a.TermAs[Set[A]]("left_coset(R.add, x + -y, I)"),
						"the sum of two cosets is the coset of the sum",
						By(quotient_group.LeftCosetMulOn.Read(additive).At(I, xm, negY), normal)),
					FinalLeg(
						"and x + -y is x - y",
						By(Normalized, comm_ring.SubAddNegOn.Read(ring).At(xm, ym))),
				))
		}),
})}

// ---------------------------------------------------------------------------
// The quotient ring and its projection
// ---------------------------------------------------------------------------

// QuotientRingOn — the cosets of an ideal form a commutative ring on
// their set. The cosets of I are the image of c under the coset map
// x ↦ x + I, and the map carries the six operations of R to the coset
// operations of the record: the sum and the negation to the quotient
// group's, I being a normal subgroup of the additive group; the product
// and the difference to the coset product and difference
// (QuotientMulCoset, QuotientSubCoset); zero to I; and one to one + I,
// which is the record's one. The image of a commutative ring along a map
// that keeps its six operations is a commutative ring
// (ring_homomorphism.ImageCommRingOn).
var QuotientRingOn = quotientRingOnThm{family.Add(registry.ProofEntry{
	Name: "QuotientRingOn",
	Key:  "prop_ab45d961b2eecf44",
	Reading: "At I = R.carrier there is one coset, R.carrier itself, and the ring on " +
		"{R.carrier} is the zero ring: R.one + R.carrier = R.carrier, which comm_ring_on allows.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
		},
		Conclusion: "comm_ring_on(ideal_quotient_ring(R, I))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], I *Expr[Set[A]], ideal Fact) {
			additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
			within := a.Have(
				"I lies in c",
				"I ⊆ R.carrier",
				By(ring_ideal.IdealSubset, ideal))
			normal := a.Have(
				"I is a normal subgroup of the additive group on c",
				"normal_subgroup(additive_group(R), I)",
				By(IdealNormal.Read(ring), ideal))
			sumLaw := a.Have(
				"the sum of the cosets of x and y is the coset of x + y",
				Statement{
					Binders: "∀x y:A.",
					Hypotheses: []string{
						"x ∈ R.carrier",
						"y ∈ R.carrier",
					},
					Conclusion: "set_mul(R.add, left_coset(R.add, x, I), left_coset(R.add, y, I)) = " +
						"left_coset(R.add, x + y, I)",
				},
				By(quotient_group.LeftCosetMulOn.Read(additive), normal))
			productLaw := a.Have(
				"and their product is the coset of x * y",
				Statement{
					Binders: "∀x y:A.",
					Hypotheses: []string{
						"x ∈ R.carrier",
						"y ∈ R.carrier",
					},
					Conclusion: "quotient_mul(I, left_coset(R.add, x, I), left_coset(R.add, y, I)) = " +
						"left_coset(R.add, x * y, I)",
				},
				By(QuotientMulCoset.Read(ring), ideal))
			negLaw := a.Have(
				"the negations of the coset of x are the coset of -x",
				"∀x:A. x ∈ R.carrier ⇒ set_inv(R.neg, left_coset(R.add, x, I)) = left_coset(R.add, -x, I)",
				By(quotient_group.LeftCosetInvOn.Read(additive), normal))
			differenceLaw := a.Have(
				"the difference of the cosets of x and y is the coset of x - y",
				Statement{
					Binders: "∀x y:A.",
					Hypotheses: []string{
						"x ∈ R.carrier",
						"y ∈ R.carrier",
					},
					Conclusion: "quotient_sub(left_coset(R.add, x, I), left_coset(R.add, y, I)) = " +
						"left_coset(R.add, x - y, I)",
				},
				By(QuotientSubCoset.Read(ring), ideal))
			zeroLaw := a.Have(
				"the coset of zero is I",
				"left_coset(R.add, R.zero, I) = I",
				By(group.LeftCosetOneOn.Read(additive), within))
			image := a.Unfolded(a.Have(
				"the cosets are the image of c under the coset map",
				"image(coset_map(R.add, I), R.carrier) = left_cosets(R.add, R.carrier, I)",
				By(quotient_group.LeftCosetsImage.Read(additive), within)), group.CosetMapDef)
			quotientRing := a.TermAs[RingOps[Set[A]]]("ideal_quotient_ring(R, I)")
			cosetMap := a.TermAs[Fun[A, Set[A]]]("λx:A. left_coset(R.add, x, I)")
			a.Show(
				"the coset map keeps all six operations, one going to one + I, "+
					"the record's one; the image of a commutative ring along it is one",
				By(
					ring_homomorphism.ImageCommRingOn.Read(ring).At(quotientRing, cosetMap),
					image,
					sumLaw,
					zeroLaw,
					negLaw,
					productLaw,
					differenceLaw))
		}),
})}

// ProjectionHomomorphism — the canonical projection is a ring map: its
// values are cosets, and it keeps addition, multiplication and one.
var ProjectionHomomorphism = projectionHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "ProjectionHomomorphism",
	Key:  "prop_420cbc5106d41428",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
		},
		Conclusion: "ring_homomorphism(R, ideal_quotient_ring(R, I), ideal_quotient_projection(R, I))",
	}, func(a *Argument, ring comm_ring.CommRingFact[on.R], I *Expr[Set[A]], ideal Fact) {
		additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
		a.Show(
			"the projection meets each condition of a ring homomorphism",
			Unfold(ring_homomorphism.RingHomomorphism),
			SplitConjAll(
				Case(
					"the source is the given commutative ring",
					By(ring)),
				Case(
					"the cosets form the quotient commutative ring",
					By(ideal, QuotientRingOn.Read(ring).At(I))),
				Case(
					"each point of the carrier projects to a coset",
					Derive(func(b *Argument) {
						x := b.MemberOf[on.R](b.FixAs[A]("x"), b.Assume())
						b.Show(
							"x represents its projected coset",
							Unfold(IdealQuotientProjectionDef),
							By(
								ring_ideal.IdealSubset.Read(ideal),
								quotient_group.LeftCosetInLeftCosets.Read(additive).At(I, x)))
					})),
				Case(
					"the projection keeps addition",
					Derive(func(b *Argument) {
						x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
						points := b.Conjuncts(
							b.Assume(),
							"x lies in the carrier",
							"y lies in the carrier")
						xm, ym := b.MemberOf[on.R](x, points[0]), b.MemberOf[on.R](y, points[1])
						b.Show(
							"adding the two cosets gives the coset of the sum, I being normal in the additive group",
							Unfold(IdealQuotientProjectionDef),
							By(ideal, IdealNormal.Read(ring).At(I), quotient_group.LeftCosetMulOn.Read(additive).At(I, xm, ym)))
					})),
				Case(
					"the projection keeps multiplication",
					Derive(func(b *Argument) {
						x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
						points := b.Conjuncts(
							b.Assume(),
							"x lies in the carrier",
							"y lies in the carrier")
						xm, ym := b.MemberOf[on.R](x, points[0]), b.MemberOf[on.R](y, points[1])
						b.Show(
							"multiplying the two cosets gives the coset of the product",
							Unfold(IdealQuotientProjectionDef),
							By(ideal, QuotientMulCoset.Read(ring).At(I, xm, ym)))
					})),
				Case(
					"the coset of one is the quotient's one",
					Unfold(IdealQuotientProjectionDef)),
			))
	}),
})}

// ProjectionKernel — the kernel of the projection is I: a point of c
// goes to the zero coset exactly when it lies in I.
var ProjectionKernel = projectionKernelThm{family.Add(registry.ProofEntry{
	Name: "ProjectionKernel",
	Key:  "prop_ad3daf8a255fd4c",
	Reading: "I ⊆ R.carrier is what makes the kernel {x " +
		"∈ R.carrier | x + I = I} all of I rather than I ∩ c.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
		},
		Conclusion: "ring_kernel(I, R.carrier, ideal_quotient_projection(R, I)) = I",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], I *Expr[Set[A]], ideal Fact) {
			fibre := a.Have(
				"the points of the carrier going to I are precisely its points in I",
				"∀x:A. x ∈ R.carrier ⇒ (ideal_quotient_projection(R, I, x) = I ⇔ x ∈ I)",
				Derive(func(b *Argument) {
					x := b.MemberOf[on.R](b.FixAs[A]("x"), b.Assume())
					b.Show(
						"the coset is I exactly when its representative lies in I",
						Simp(Fwd(IdealQuotientProjectionDef)),
						By(ideal, CosetEqIdealIff.Read(ring).At(I, x)))
				}))
			a.Show(
				"the kernel consists of exactly the points of I",
				Unfold(ring_homomorphism.RingKernelDef),
				BySets(fibre, ideal, ring_ideal.IdealSubset))
		}),
})}

// IdealQuotientProjection — the projection of a commutative ring onto its
// quotient by an ideal I is a ring homomorphism onto it with kernel I:
// its image is the set of cosets, and the quotient's zero is I.
var IdealQuotientProjection = idealQuotientProjectionThm{family.Add(registry.ProofEntry{
	Name: "IdealQuotientProjection",
	Key:  "prop_82cff083b55683c",
	Reading: "Onto is what this member adds to ProjectionHomomorphism and " +
		"ProjectionKernel: the quotient's carrier is left_cosets, which I ⊆ R.carrier " +
		"makes the image of R.carrier under x ↦ x + I, and that map is the projection.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
		},
		Conclusion: "ring_homomorphism(R, ideal_quotient_ring(R, I), ideal_quotient_projection(R, I)) ∧ " +
			"image(ideal_quotient_projection(R, I), R.carrier) = ideal_quotient_ring(R, I).carrier ∧ " +
			"ring_kernel(ideal_quotient_ring(R, I).zero, R.carrier, ideal_quotient_projection(R, I)) = I",
	}, func(a *Argument, ring comm_ring.CommRingFact[on.R], I *Expr[Set[A]], ideal Fact) {
		additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
		onto := a.Have(
			"the projection's image is the set of cosets",
			"image(ideal_quotient_projection(R, I), R.carrier) = ideal_quotient_ring(R, I).carrier",
			Simp(Fwd(IdealQuotientProjectionDef), Rev(group.CosetMapDef)),
			By(
				Normalized,
				ring_ideal.IdealSubset.Read(ideal),
				quotient_group.LeftCosetsImage.Read(additive).At(I)))
		a.Show(
			"the projection is a ring map onto the quotient with kernel I",
			By(ideal, onto, ProjectionHomomorphism.Read(ring).At(I), ProjectionKernel.Read(ring).At(I)))
	}),
})}

// QuotientCarrierCardLe — the quotient of R by I has no more members
// than R: the quotient carrier is an image of R's carrier.
var QuotientCarrierCardLe = quotientCarrierCardLeThm{family.Add(registry.ProofEntry{
	Name: "QuotientCarrierCardLe",
	Key:  "prop_e073dac1414cd49b",
	Reading: "No hypothesis: the cosets of any set are an image of the " +
		"carrier, whether or not R is a ring and I an ideal. The quotient " +
		"lives on set(A), and its size is bounded by R's carrier, not by A.",
	Build: family.Theorem("∀R:ring_ops(A). ∀I:set(A). "+
		"    card_le(ideal_quotient_ring(R, I).carrier, R.carrier)",
		func(a *Argument, R *Expr[RingOps[A]], I *Expr[Set[A]]) {
			a.Show(
				"the cosets unfold to an image of the carrier, and "+
					"an image is no larger than what it is the image of",
				Simp(Fwd(IdealQuotientRingDef), Fwd(quotient_group.LeftCosetsDef), Fwd(equivalence.QuotientOnDef)),
				Cite(cardinal.CardLeImage.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[Set[A]]())))
		}),
})}

// ---------------------------------------------------------------------------
// The isomorphism theorems
// ---------------------------------------------------------------------------

// QuotientFirstIso — the first isomorphism theorem for rings: a ring map
// ψ from R onto E induces, by its value at a member of each coset, a ring
// isomorphism from R modulo the kernel J of ψ to E, carrying the coset of r
// to ψ(r). Read on the additive groups, ψ is a group homomorphism whose
// kernel is J, so the first isomorphism theorem for groups makes the induced
// map additive, one-to-one on the cosets of J and onto the image of ψ, which
// is E. The rest is checked at representatives: the cosets of x and y
// multiply to the coset of x * y (QuotientMulCoset), which goes to
// ψ(x * y) = ψ(x) * ψ(y), and the coset of one goes to ψ(one), the one of E.
var QuotientFirstIso = quotientFirstIsoThm{family.Add(registry.ProofEntry{
	Name: "QuotientFirstIso",
	Key:  "prop_3c3d69d19d0b4425",
	Reading: "The two rings may sit on different types; the quotient lives on set(A). The " +
		"isomorphism is the named map induced_map(ψ), ψ at the chosen member of a coset, not an " +
		"existential one, so the formula on cosets is what a later statement computes with. Onto " +
		"is load-bearing: without it the map is an isomorphism onto image(ψ, R.carrier) only.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀E:ring_ops(B). ∀ψ:(A → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, E, ψ)",
			"image(ψ, R.carrier) = E.carrier",
		},
		Conclusion: "ring_isomorphism(ideal_quotient_ring(R, ring_kernel(E.zero, R.carrier, ψ)), " +
			"    E, " +
			"    induced_map(ψ)) ∧ " +
			"(∀r:A. " +
			"    r ∈ R.carrier ⇒ " +
			"    induced_map(ψ, ideal_quotient_projection(R, ring_kernel(E.zero, R.carrier, ψ), r)) = ψ(r))",
	}, func(a *Argument, R *Expr[RingOps[A]], E *Expr[RingOps[B]], ψ *Arrow[A, B], hom, onto Fact) {
		ring := ring_homomorphism.Source.Read(hom)
		additiveHom := ring_homomorphism.AdditiveHomomorphism.Read(hom)
		ideal := ring_homomorphism.KernelIdeal.Read(hom)
		kernel := a.Have(
			"read on the additive groups, the kernel of ψ is J: "+
				"both are the points of R.carrier that ψ sends to E.zero",
			"group_kernel(E.zero, R.carrier, ψ) = ring_kernel(E.zero, R.carrier, ψ)",
			By(group_homomorphism.GroupKernelDef, ring_homomorphism.RingKernelDef))
		formula := a.Have(
			"the induced map takes the coset of r to ψ(r), as it does for the additive groups",
			Statement{
				Binders: "∀r:A.",
				Hypotheses: []string{
					"r ∈ R.carrier",
				},
				Conclusion: "induced_map(ψ, left_coset(R.add, r, ring_kernel(E.zero, R.carrier, ψ))) = ψ(r)",
			},
			By(Normalized, quotient_group.InducedMapCoset.Read(additiveHom), kernel))
		isomorphism := a.Have(
			"read additively, the induced map is the first isomorphism theorem's "+
				"isomorphism of the cosets of J onto the image of ψ, E.carrier",
			"group_isomorphism(quotient_group(additive_group(R), ring_kernel(E.zero, R.carrier, ψ)), "+
				"    restrict_group(additive_group(E), E.carrier), "+
				"    induced_map(ψ))",
			By(Normalized, quotient_group.FirstIsomorphism.Read(additiveHom), kernel, onto))
		additiveMap := group_homomorphism.IsomorphismHomomorphism.Read(isomorphism)
		additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
		one := a.TermAs[A]("R.one")
		a.Show(
			"the induced map meets each condition of a ring isomorphism, and takes the projection of r to ψ(r)",
			Unfold(ring_homomorphism.RingIsomorphismDef),
			// The ring-map conditions are read off the goal alone, so the
			// hypothesis on ψ stays whole for the readings the cases take at it.
			Simp(Fwd(ring_homomorphism.RingHomomorphism)),
			SplitConjAll(
				Case(
					"the cosets of the ideal J form a commutative ring",
					By(QuotientRingOn.Read(ring), ideal)),
				Case(
					"E is a commutative ring",
					By(ring_homomorphism.Target.Read(hom))),
				Case(
					"a coset goes into E, as it does for the additive groups",
					By(group_homomorphism.MapIn.Read(additiveMap))),
				Case(
					"the sum of two cosets goes to the sum of their values, as it does for the additive groups",
					By(group_homomorphism.MapMul.Read(additiveMap))),
				Case(
					"the product of two cosets goes to the product of their values, checked at representatives",
					Simp(
						Fwd(quotient_group.ForallInLeftCosetsPair.Read(additive)),
						Fwd(ring_ideal.IdealSubset.Read(ideal))),
					Derive(func(b *Argument) {
						x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
						points := b.Conjuncts(
							b.Assume(),
							"x lies in R.carrier",
							"y lies in R.carrier")
						xm, ym := b.MemberOf[on.Any](x, points[0]), b.MemberOf[on.Any](y, points[1])
						product := comm_ring.MulIn.Read(ring).At(xm, ym)
						b.Show(
							"multiply at representatives, then let ψ keep the product",
							CalcEq(
								Leg(
									b.TermAs[B]("induced_map(ψ, left_coset(R.add, x * y, ring_kernel(E.zero, R.carrier, ψ)))"),
									"the cosets of x and y multiply to the coset of x * y",
									By(
										ideal,
										QuotientMulCoset.Read(ring).At(b.TermAs[Set[A]]("ring_kernel(E.zero, R.carrier, ψ)"), xm, ym))),
								Leg(
									b.TermAs[B]("ψ(x * y)"),
									"which the induced map sends to ψ(x * y)",
									By(product, formula.At(product))),
								FinalLeg(
									"and ψ(x * y) is ψ(x) * ψ(y), the values at the cosets of x and y",
									By(xm, ym, formula.At(x), formula.At(y), ring_homomorphism.MapMul.Read(hom).At(xm, ym))),
							))
					})),
				Case(
					"the coset of one goes to ψ(one), the one of E",
					By(ring_homomorphism.MapOne.Read(hom), comm_ring.OneIn.Read(ring), formula.At(one))),
				Case(
					"one-to-one on the cosets of J, as for the additive groups",
					By(group_homomorphism.IsomorphismInjective.Read(isomorphism))),
				Case(
					"onto E, as for the additive groups",
					By(group_homomorphism.IsomorphismSurjective.Read(isomorphism))),
				Case(
					"the projection of r is its coset, which goes to ψ(r)",
					By(formula, IdealQuotientProjectionDef)),
			))
	}),
})}

// KernelQuotientImage — a ring map identifies the source modulo its kernel with
// its image, a subring of the target: the first isomorphism theorem read at the
// map onto its image.
var KernelQuotientImage = kernelQuotientImageThm{family.Add(registry.ProofEntry{
	Name: "KernelQuotientImage",
	Key:  "prop_6eed7e3aaf062d79",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(B). ∀φ:(A → B).",
		Hypotheses: []string{
			"ring_homomorphism(R, T, φ)",
		},
		Conclusion: "subring(T, image(φ, R.carrier)) ∧ " +
			"ring_isomorphism(ideal_quotient_ring(R, ring_kernel(T.zero, R.carrier, φ)), " +
			"    restrict_ring(T, image(φ, R.carrier)), " +
			"    induced_map(φ)) ∧ " +
			"(∀r:A. " +
			"    r ∈ R.carrier ⇒ " +
			"    induced_map(φ, ideal_quotient_projection(R, ring_kernel(T.zero, R.carrier, φ), r)) = φ(r))",
	}, func(a *Argument, R *Expr[RingOps[A]], T *Expr[RingOps[B]], φ *Arrow[A, B], hom Fact) {
		values := a.TermAs[Set[B]]("image(φ, R.carrier)")
		imageRing := a.TermAs[RingOps[B]]("restrict_ring(T, image(φ, R.carrier))")
		sub := a.Have(
			"the image is a subring",
			"subring(T, image(φ, R.carrier))",
			By(hom, ring_homomorphism.ImageSubring.At(R, T, φ)))
		corestricted := a.Have(
			"φ is a ring map onto its image",
			"ring_homomorphism(R, restrict_ring(T, image(φ, R.carrier)), φ)",
			By(
				hom,
				sub,
				ring_homomorphism.RingHomCorestrict.At(R, T, φ, values),
				At(set_image.FunInImage, φ, a.TermAs[Set[A]]("R.carrier"))))
		a.Show(
			"the first isomorphism theorem at the map onto its image",
			By(sub, corestricted, QuotientFirstIso.At(R, imageRing, φ)))
	}),
})}

// QuotientAutoIso — a ring automorphism α of R carrying the ideal J₁ onto
// the ideal J₂ induces a ring isomorphism from R/J₁ to R/J₂, carrying the
// coset of r to the coset of α(r): the first isomorphism theorem at ψ, the
// projection onto R/J₂ after α. ψ is a ring map, onto R/J₂ since α is onto
// R.carrier and the projection onto the cosets, and its kernel is J₁: r goes
// to the zero coset J₂ when α(r) lies in J₂ = α(J₁), which, α being
// one-to-one on R.carrier, is when r lies in J₁.
var QuotientAutoIso = quotientAutoIsoThm{family.Add(registry.ProofEntry{
	Name: "QuotientAutoIso",
	Key:  "prop_7dae80fabd139cb4",
	Reading: "The isomorphism is the named map induced by r ↦ α(r) + J₂, the projection " +
		"after α, at the chosen member of a coset. Injectivity of α is load-bearing: without it " +
		"the kernel of r ↦ α(r) + J₂ is the preimage of J₂ under α, which can be strictly larger " +
		"than J₁. Both ideals are hypotheses, though the second follows from the first through α.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀α:(A → A). ∀J₁ J₂:set(A).",
		Hypotheses: []string{
			"ring_isomorphism(R, R, α)",
			"ring_ideal(R, J₁)",
			"ring_ideal(R, J₂)",
			"image(α, J₁) = J₂",
		},
		Conclusion: "ring_isomorphism(ideal_quotient_ring(R, J₁), " +
			"    ideal_quotient_ring(R, J₂), " +
			"    induced_map(«ψ»)) ∧ " +
			"(∀r:A. " +
			"    r ∈ R.carrier ⇒ " +
			"    induced_map(«ψ», ideal_quotient_projection(R, J₁, r)) = " +
			"    ideal_quotient_projection(R, J₂, α(r)))",
		Abbrev: Abbrev{
			{Name: "ψ", Text: "λx:A. ideal_quotient_projection(R, J₂, α(x))"},
		},
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		α *Arrow[A, A],
		J1, J2 *Expr[Set[A]],
		iso, ideal1, ideal2, carries Fact,
	) {
		parts := a.Conjuncts(
			a.Unfolded(iso, ring_homomorphism.RingIsomorphismDef),
			"α is a ring map of R to itself",
			"one-to-one on R.carrier",
			"and onto R.carrier")
		hom, injective, onto := parts[0], parts[1], parts[2]
		ring := ring_homomorphism.Source.Read(hom)
		projection := IdealQuotientProjection.Read(ring).At(J2)
		carrier := a.TermAs[Set[A]]("R.carrier")
		quotient := a.TermAs[RingOps[Set[A]]]("ideal_quotient_ring(R, J₂)")
		toCosets := a.TermAs[Fun[A, Set[A]]]("ideal_quotient_projection(R, J₂)")
		ψ := a.TermAs[Fun[A, Set[A]]]("«ψ»")
		composite := a.Have(
			"ψ, the projection onto R/J₂ after α, is a ring map",
			"ring_homomorphism(R, ideal_quotient_ring(R, J₂), «ψ»)",
			By(hom, ideal2, projection, ring_homomorphism.RingHomCompose.At(R, R, quotient, α, toCosets)))
		ontoQuotient := a.Have(
			"ψ is onto R/J₂",
			"image(«ψ», R.carrier) = ideal_quotient_ring(R, J₂).carrier",
			CalcEq(
				Leg(
					a.TermAs[Set[Set[A]]]("image(ideal_quotient_projection(R, J₂), image(α, R.carrier))"),
					"the image under the projection after α is the projection's image of α's",
					Simp(Rev(set_image.ImageCompose), Fwd(functions.ComposeApply))),
				Leg(
					a.TermAs[Set[Set[A]]]("image(ideal_quotient_projection(R, J₂), R.carrier)"),
					"α is onto R.carrier",
					onto.Rw()),
				FinalLeg(
					"and the projection is onto the cosets",
					By(ideal2, projection)),
			))
		cosets := a.Have(
			"the coset of a point of R.carrier is the zero coset J₂ exactly when the point lies in J₂",
			"∀y:A. y ∈ R.carrier ⇒ (ideal_quotient_projection(R, J₂, y) = J₂ ⇔ y ∈ J₂)",
			Simp(Fwd(IdealQuotientProjectionDef)),
			By(ideal2, CosetEqIdealIff.Read(ring)))
		pullback := a.Have(
			"α carries a point of R.carrier into J₂ = α(J₁) exactly when the point lies in J₁",
			"∀x:A. x ∈ R.carrier ⇒ (α(x) ∈ J₂ ⇔ x ∈ J₁)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xIn := b.Assume()
				b.Iff()
				b.Forward(
					"α(x) lies in J₂ = α(J₁), so it is α(y) for some y in J₁",
					func(c *Argument, inJ2 Fact) {
						y, preimage := c.UnpackAs[A](c.Simplified(inJ2, Rev(carries), Fwd(set_basic.InImage)), "y")
						c.Show(
							"y lies in R.carrier with x, and α is one-to-one there, so x is y, a point of J₁",
							By(
								preimage,
								xIn,
								ring_ideal.IdealSubset.Read(ideal1),
								set_basic.SubsetDef.At(J1, carrier),
								c.Unfolded(injective, functions.InjectiveOnDef).At(x, y)))
					})
				b.Backward(
					"α carries a point of J₁ into α(J₁), which is J₂",
					func(c *Argument, inJ1 Fact) {
						c.Show(
							"so α(x) lies in J₂",
							carries.RwRev(),
							By(inJ1, set_image.FunInImage.At(α, J1, x)))
					})
			}))
		kernel := a.Have(
			"so ψ sends a point of R.carrier to the zero coset exactly when it lies in J₁: its kernel is J₁",
			"ring_kernel(ideal_quotient_ring(R, J₂).zero, R.carrier, «ψ») = J₁",
			Unfold(ring_homomorphism.RingKernelDef),
			BySets(cosets, pullback, ring_homomorphism.MapIn.Read(hom), ring_ideal.IdealSubset.Read(ideal1)))
		a.Show(
			"the first isomorphism theorem at ψ, whose kernel is J₁",
			kernel.RwRev(),
			By(composite, ontoQuotient, QuotientFirstIso.At(R, quotient, ψ)))
	}),
})}

// ---------------------------------------------------------------------------
// Prime and maximal ideals
// ---------------------------------------------------------------------------

// QuotientDomain — the cosets of a prime ideal form an integral domain:
// they form a commutative ring, the coset of one is not the zero coset p
// because p does not hold one, and a vanishing product of two cosets is
// the coset of a product of representatives lying in p, so p holds a
// factor and that factor's coset is the zero coset.
var QuotientDomain = quotientDomainThm{family.Add(registry.ProofEntry{
	Name: "QuotientDomain",
	Key:  "prop_99330ab767e6e347",
	Reading: "Properness of p gives one + p ≠ p; primality is " +
		"used only at representatives in c, which every coset has.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:set(A).",
		Hypotheses: []string{
			"prime_ideal(R, p)",
		},
		Conclusion: "integral_domain_on(ideal_quotient_ring(R, p))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p *Expr[Set[A]], prime Fact) {
			ideal := a.Have(
				"a prime ideal is an ideal",
				"ring_ideal(R, p)",
				By(ring_ideal.PrimeIdealIdeal, prime))
			quotient := a.Have(
				"so its cosets form a commutative ring",
				"comm_ring_on(ideal_quotient_ring(R, p))",
				By(QuotientRingOn.Read(ring), ideal))
			one := a.MemberOf[on.R](a.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring))
			oneApart := a.Have(
				"the coset of one is not the zero coset p, since p does not hold one",
				"left_coset(R.add, R.one, p) ≠ p",
				By(ideal, ring_ideal.PrimeIdealProper.Read(prime), CosetEqIdealIff.Read(ring).At(p, one)))
			within := a.Have(
				"p lies in c",
				"p ⊆ R.carrier",
				By(ring_ideal.IdealSubset, ideal))
			additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
			noZeroDivisors := a.Have(
				"a product of two cosets is p only when one of them is p",
				Statement{
					Binders: "∀s t:set(A).",
					Hypotheses: []string{
						"s ∈ left_cosets(R.add, R.carrier, p)",
						"t ∈ left_cosets(R.add, R.carrier, p)",
					},
					Conclusion: "quotient_mul(p, s, t) = p ⇒ s = p ∨ t = p",
				},
				Simp(Fwd(quotient_group.ForallInLeftCosetsPair.Read(additive)), Fwd(within)),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					points := b.Assume()
					b.Show(
						"the product of the cosets of x and y is the coset of x * y, "+
							"which is p exactly when p holds x * y; p, prime, then holds x or y",
						Simp(
							Fwd(QuotientMulCoset.Read(ring)),
							Fwd(CosetEqIdealIff.Read(ring)),
							Fwd(comm_ring.MulIn.Read(ring))),
						By(ring_ideal.PrimeIdealPrime, prime, points))
				}))
			a.Show(
				"so the cosets of p form an integral domain",
				By(integral_domain.IntegralDomainOn, quotient, oneApart, noZeroDivisors))
		}),
})}

// QuotientInverseExists — outside a maximal ideal every coset has an
// inverse among the cosets: x is a unit modulo m, and the coset of its
// inverse v multiplies the coset of x to the coset of one.
var QuotientInverseExists = quotientInverseExistsThm{family.Add(registry.ProofEntry{
	Name: "QuotientInverseExists",
	Key:  "prop_27667ea2b14a15cf",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀m:set(A). ∀x:A.",
		Hypotheses: []string{
			"maximal_ideal(R, m)",
			"x ∈ R.carrier",
			"x ∉ m",
		},
		Conclusion: "∃t:set(A). " +
			"    t ∈ left_cosets(R.add, R.carrier, m) ∧ " +
			"    quotient_mul(m, t, left_coset(R.add, x, m)) = left_coset(R.add, R.one, m)",
	}, func(
		a *Argument,
		ring comm_ring.CommRingFact[on.R],
		m *Expr[Set[A]],
		maximal Fact,
		x *Member[A, on.R],
		outside Fact,
	) {
		ideal := a.Have(
			"a maximal ideal is an ideal",
			"ring_ideal(R, m)",
			By(ring_ideal.MaximalIdealIdeal, maximal))
		v, inverse := a.ObtainAs[A](
			"x is a unit modulo m",
			"∃v:A. v ∈ R.carrier ∧ v * x - R.one ∈ m",
			By(maximal, outside, ring_ideal.MaximalUnitModulo.Read(ring).At(m, x)))
		parts := a.Conjuncts(
			inverse,
			"v lies in the carrier",
			"v * x differs from one by a member of m")
		vIn, congruent := parts[0], parts[1]
		vm := a.MemberOf[on.R](v, vIn)
		product := comm_ring.MulIn.Read(ring).At(vm, x)
		one := a.MemberOf[on.R](a.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring))
		equalsOne := a.Have(
			"the coset of v * x equals the coset of one",
			"left_coset(R.add, v * x, m) = left_coset(R.add, R.one, m)",
			By(ideal, congruent, CosetEqIff.Read(ring).At(m, product, one)))
		inverts := a.Have(
			"so the coset of v inverts the coset of x",
			"quotient_mul(m, left_coset(R.add, v, m), left_coset(R.add, x, m)) = left_coset(R.add, R.one, m)",
			Simp(Fwd(QuotientMulCoset.Read(ring))),
			By(equalsOne))
		additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
		a.Show(
			"the coset of v is such a coset",
			Witness(a.TermAs[Set[A]]("left_coset(R.add, v, m)")),
			By(
				ring_ideal.IdealSubset.Read(ideal),
				quotient_group.LeftCosetInLeftCosets.Read(additive).At(m, vm),
				inverts))
	}),
})}

// QuotientInvCoset — the inverse chosen for the coset of a point outside
// a maximal ideal is itself a coset and inverts the given one: the given
// coset is not m, so the definition takes its choice, and
// QuotientInverseExists fills the choice set, whose members do both.
var QuotientInvCoset = quotientInvCosetThm{family.Add(registry.ProofEntry{
	Name: "QuotientInvCoset",
	Key:  "prop_20b33b3d412ba146",
	Reading: "x ∉ m is what makes the coset of x differ from m, so the definition's choice " +
		"is taken rather than its zero branch; maximality is what makes the choice non-empty.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀m:set(A). ∀x:A.",
		Hypotheses: []string{
			"maximal_ideal(R, m)",
			"x ∈ R.carrier",
			"x ∉ m",
		},
		Conclusion: "quotient_inv(R.carrier, m, left_coset(R.add, x, m)) ∈ " +
			"left_cosets(R.add, R.carrier, m) ∧ " +
			"quotient_mul(m, quotient_inv(R.carrier, m, left_coset(R.add, x, m)), left_coset(R.add, x, m)) = " +
			"left_coset(R.add, R.one, m)",
	}, func(
		a *Argument,
		ring comm_ring.CommRingFact[on.R],
		m *Expr[Set[A]],
		maximal Fact,
		x *Member[A, on.R],
		outside Fact,
	) {
		apart := a.Have(
			"the coset of x is not the zero coset",
			"left_coset(R.add, x, m) ≠ m",
			By(
				Normalized,
				ring_ideal.MaximalIdealIdeal.Read(maximal),
				outside,
				CosetEqIdealIff.Read(ring).At(m, x)))
		_, selected := a.ObtainChosen(
			"x lies outside the maximal ideal m, so its coset has an inverse coset",
			"∃t:set(A). "+
				"    t ∈ left_cosets(R.add, R.carrier, m) ∧ "+
				"    quotient_mul(m, t, left_coset(R.add, x, m)) = left_coset(R.add, R.one, m)",
			maximal,
			outside,
			QuotientInverseExists.Read(ring).At(m, x))
		a.Show(
			"the nonzero coset takes the definition's choice, a coset "+
				"that inverts it by the two halves of its specification",
			Simp(Fwd(QuotientInvDef)),
			By(apart, selected))
	}),
})}

// IdealQuotientFieldRing — the ring of the quotient field is the quotient
// ring, for every ring record and every set: forgetting the inverse and
// the division of ideal_quotient_field leaves the cosets of I under the
// six coset operations, which are ideal_quotient_ring's.
var IdealQuotientFieldRing = idealQuotientFieldRingThm{family.Add(registry.ProofEntry{
	Name: "IdealQuotientFieldRing",
	Key:  "prop_d758cc115c683873",
	Build: family.Theorem("∀R:ring_ops(A). ∀I:set(A). "+
		"    field_ring(ideal_quotient_field(R, I)) = ideal_quotient_ring(R, I)",
		func(a *Argument, R *Expr[RingOps[A]], I *Expr[Set[A]]) {
			a.Show(
				"unfolded, both records are packed from the same seven parts",
				Simp(Fwd(field.FieldRingDef.Inst[Set[A]]()), Fwd(IdealQuotientFieldDef), Fwd(IdealQuotientRingDef)),
				Basic())
		}),
})}

// QuotientFieldOn — the cosets of a maximal ideal form a field on their
// set: the quotient ring's nonzero cosets have the chosen inverse
// cosets, and the zero coset is its own inverse.
var QuotientFieldOn = quotientFieldOnThm{family.Add(registry.ProofEntry{
	Name: "QuotientFieldOn",
	Key:  "prop_3ad6922c0aeffe4c",
	Reading: "The R.zero coset is m itself, so inv(R.zero) = R.zero is the definition's " +
		"COND at s = m, and R.one + m ≠ m is R.one ∉ m. Maximality is what keeps the ε inside " +
		"the cosets: at an ideal that is not maximal it may return a set that is no coset.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀m:set(A).",
		Hypotheses: []string{
			"maximal_ideal(R, m)",
		},
		Conclusion: "field_on(ideal_quotient_field(R, m))",
	}, func(a *Argument, ring comm_ring.CommRingFact[on.R], m *Expr[Set[A]], maximal Fact) {
		ideal := a.Have(
			"a maximal ideal is an ideal",
			"ring_ideal(R, m)",
			By(ring_ideal.MaximalIdealIdeal, maximal))
		within := a.Have(
			"m lies in the carrier",
			"m ⊆ R.carrier",
			By(ring_ideal.IdealSubset, ideal))
		quotient := a.Have(
			"the field record has the quotient's commutative ring",
			"comm_ring_on(field_ring(ideal_quotient_field(R, m)))",
			Simp(Fwd(IdealQuotientFieldRing)),
			By(QuotientRingOn.Read(ring), ideal))
		inverseZero := a.Have(
			"the inverse of the zero coset is the zero coset",
			"quotient_inv(R.carrier, m, m) = m",
			Simp(Fwd(QuotientInvDef)),
			Basic())
		additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
		inverseClosed := a.Have(
			"the inverse of every coset is a coset",
			Statement{
				Binders: "∀s:set(A).",
				Hypotheses: []string{
					"s ∈ left_cosets(R.add, R.carrier, m)",
				},
				Conclusion: "quotient_inv(R.carrier, m, s) ∈ left_cosets(R.add, R.carrier, m)",
			},
			Simp(Fwd(quotient_group.ForallInLeftCosets.Read(additive)), Fwd(within)),
			Derive(func(b *Argument) {
				x := b.MemberOf[on.R](b.FixAs[A]("x"), b.Assume())
				b.Cases(b.TermAs[Bool]("x ∈ m"))
				b.When(
					"a representative in m gives the zero coset",
					func(c *Argument, inIdeal Fact) {
						zeroCoset := c.Have(
							"the coset of x is m",
							"left_coset(R.add, x, m) = m",
							By(ideal, inIdeal, CosetEqIdealIff.Read(ring).At(m, x)))
						c.Show(
							"its inverse is the zero coset, which belongs to the carrier",
							Simp(Fwd(zeroCoset), Fwd(inverseZero)),
							By(comm_ring.ZeroIn.Read(quotient)))
					})
				b.Otherwise(
					"a representative outside m has a chosen inverse coset",
					func(c *Argument, outside Fact) {
						c.Show(
							"the chosen inverse belongs to the quotient carrier",
							By(maximal, outside, QuotientInvCoset.Read(ring).At(m, x)))
					})
			}))
		one := a.MemberOf[on.R](a.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring))
		oneApart := a.Have(
			"one is not the zero coset, since a maximal ideal does not contain one",
			"left_coset(R.add, R.one, m) ≠ m",
			By(ideal, ring_ideal.MaximalIdealProper.Read(maximal), CosetEqIdealIff.Read(ring).At(m, one)))
		inverseLaw := a.Have(
			"each nonzero coset satisfies the left inverse law",
			Statement{
				Binders: "∀s:set(A).",
				Hypotheses: []string{
					"s ∈ left_cosets(R.add, R.carrier, m)",
				},
				Conclusion: "s ≠ m ⇒ " +
					"quotient_mul(m, quotient_inv(R.carrier, m, s), s) = left_coset(R.add, R.one, m)",
			},
			Simp(Fwd(quotient_group.ForallInLeftCosets.Read(additive)), Fwd(within)),
			Derive(func(b *Argument) {
				x := b.MemberOf[on.R](b.FixAs[A]("x"), b.Assume())
				b.Show(
					"a nonzero coset has its representative outside m, so its chosen inverse inverts it",
					Simp(Fwd(CosetEqIdealIff.Read(ring))),
					By(maximal, QuotientInvCoset.Read(ring).At(m, x)))
			}))
		division := a.Have(
			"division is multiplication by the inverse",
			Statement{
				Binders: "∀s t:set(A).",
				Hypotheses: []string{
					"s ∈ left_cosets(R.add, R.carrier, m)",
					"t ∈ left_cosets(R.add, R.carrier, m)",
				},
				Conclusion: "quotient_div(R.carrier, m, s, t) = quotient_mul(m, s, quotient_inv(R.carrier, m, t))",
			},
			Simp(Fwd(QuotientDivDef)),
			Basic())
		quotientField := a.TermAs[field.FieldOps[Set[A]]]("ideal_quotient_field(R, m)")
		a.Show(
			"the quotient operations satisfy all field axioms",
			By(
				field.FieldOn.At(quotientField),
				quotient,
				inverseClosed,
				oneApart,
				inverseLaw,
				inverseZero,
				division))
	}),
})}

// ---------------------------------------------------------------------------
// The index of an ideal
// ---------------------------------------------------------------------------
//
// The index of an ideal is the number of its cosets in the carrier, its
// index as a subgroup of the additive group.

// IdealIndexDef — `ideal_index(R, I)`: the number of cosets of I in R's
// carrier, counted by card.
var IdealIndexDef = idealIndexDefThm{family.Define(registry.DefEntry{
	Name:  "IdealIndexDef",
	Key:   "prop_8b8da95df7675af3",
	Const: "ideal_index",
	Type:  "ring_ops(A) → set(A) → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀I:set(A). ideal_index(R, I) = card(left_cosets(R.add, R.carrier, I))",
	},
	Reading: "It is the number of cosets only when there are finitely many: " +
		"card is a fold, and of an infinite set it says nothing, so a statement " +
		"about the index carries finite(left_cosets(R.add, R.carrier, I)) beside it.",
})}

// FiniteQuotientAboveIdeal — an ideal above an ideal of finite index has
// finite index: both are additive subgroups, and multiplicativity of
// the index, [R:I] = [R:J]·[J:I], carries finiteness from I to J.
var FiniteQuotientAboveIdeal = finiteQuotientAboveIdealThm{family.Add(registry.ProofEntry{
	Name: "FiniteQuotientAboveIdeal",
	Key:  "prop_4bdb0bce11acdd4c",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀I J:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"ring_ideal(R, J)",
			"I ⊆ J",
			"finite(left_cosets(R.add, R.carrier, I))",
		},
		Conclusion: "finite(left_cosets(R.add, R.carrier, J))",
	}, func(a *Argument, R comm_ring.CommRingFact[on.R], I, J *Expr[Set[A]], hypotheses Fact) {
		parts := a.Conjuncts(
			hypotheses,
			"I is an ideal",
			"J is an ideal",
			"I lies in J",
			"R modulo I is finite")
		idealI, idealJ, inclusion, finiteI := parts[0], parts[1], parts[2], parts[3]
		additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(R))
		a.Show(
			"finite index passes from I to J",
			By(
				finiteI,
				idealI,
				IdealSubgroup.Read(R).At(I),
				group.SubgroupOne.At(a.TermAs[group.GroupOps[A]]("additive_group(R)"), I),
				idealJ,
				IdealSubgroup.Read(R).At(J),
				inclusion,
				quotient_group.IndexMultiplicative.Read(additive).At(I, J)))
	}),
})}

// StrictIdealInclusionLowersIndex — strictly enlarging an ideal of finite
// index lowers its index: on the two additive subgroups,
// [R:I] = [R:J]·[J:I] with [J:I] > 1 when I ≠ J, so [R:J] < [R:I].
var StrictIdealInclusionLowersIndex = strictIdealInclusionLowersIndexThm{family.Add(registry.ProofEntry{
	Name: "StrictIdealInclusionLowersIndex",
	Key:  "prop_5233badfc373879d",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀I J:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"ring_ideal(R, J)",
			"I ⊆ J",
			"I ≠ J",
			"finite(left_cosets(R.add, R.carrier, I))",
		},
		Conclusion: "ideal_index(R, J) < ideal_index(R, I)",
	}, func(a *Argument, R comm_ring.CommRingFact[on.R], I, J *Expr[Set[A]], hypotheses Fact) {
		parts := a.Conjuncts(
			hypotheses,
			"I is an ideal",
			"J is an ideal",
			"I lies in J",
			"I differs from J",
			"R modulo I is finite")
		idealI, idealJ, inclusion, strict, finiteI := parts[0], parts[1], parts[2], parts[3], parts[4]
		additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(R))
		a.Show(
			"strict enlargement lowers the finite index",
			Unfold(IdealIndexDef),
			By(
				finiteI,
				idealI,
				IdealSubgroup.Read(R).At(I),
				idealJ,
				IdealSubgroup.Read(R).At(J),
				inclusion,
				strict,
				quotient_group.StrictInclusionLowersIndex.Read(additive).At(I, J)))
	}),
})}

// FiniteIndexPrimeMaximal — a prime ideal of finite index is maximal: the
// quotient by p is a finite integral domain, so each of its nonzero cosets
// has an inverse (integral_domain.FiniteDomainIsField), and the inverse of
// x + p, for x in a larger ideal J outside p, puts one in J.
var FiniteIndexPrimeMaximal = finiteIndexPrimeMaximalThm{family.Add(registry.ProofEntry{
	Name: "FiniteIndexPrimeMaximal",
	Key:  "prop_9b5ce7fafa993513",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀p:set(A).",
		Hypotheses: []string{
			"prime_ideal(R, p)",
			"finite(left_cosets(R.add, R.carrier, p))",
		},
		Conclusion: "maximal_ideal(R, p)",
	}, func(a *Argument, R comm_ring.CommRingFact[on.R], p *Expr[Set[A]], hypotheses Fact) {
		parts := a.Conjuncts(
			hypotheses,
			"p is prime",
			"R modulo p is finite")
		prime, finite := parts[0], parts[1]
		ideal := a.Have(
			"the prime is an ideal",
			"ring_ideal(R, p)",
			By(ring_ideal.PrimeIdealIdeal.Read(prime)))
		domain := a.Have(
			"the prime quotient is an integral domain",
			"integral_domain_on(ideal_quotient_ring(R, p))",
			By(prime, QuotientDomain.Read(R).At(p)))
		r := a.TermAs[RingOps[A]]("R")
		inverses := a.Have(
			"the quotient is a finite integral domain, so every nonzero element has an inverse",
			Statement{
				Binders: "∀u:set(A).",
				Hypotheses: []string{
					"u ∈ ideal_quotient_ring(R, p).carrier",
					"u ≠ ideal_quotient_ring(R, p).zero",
				},
				Conclusion: "∃v:set(A). " +
					"    v ∈ ideal_quotient_ring(R, p).carrier ∧ " +
					"    ideal_quotient_ring(R, p).mul(u, v) = ideal_quotient_ring(R, p).one",
			},
			By(finite, IdealQuotientRingDef.At(r, p), integral_domain.FiniteDomainIsField.Read(domain)))
		cosetInverses := a.Have(
			"every coset other than p has an inverse coset",
			Statement{
				Binders: "∀u:set(A).",
				Hypotheses: []string{
					"u ∈ left_cosets(R.add, R.carrier, p)",
					"u ≠ p",
				},
				Conclusion: "∃v:set(A). " +
					"    v ∈ left_cosets(R.add, R.carrier, p) ∧ quotient_mul(p, u, v) = left_coset(R.add, R.one, p)",
			},
			By(inverses, IdealQuotientRingDef.At(r, p)))
		additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(R))
		above := a.Have(
			"every ideal above p is p or contains one",
			"∀J:set(A). ring_ideal(R, J) ∧ p ⊆ J ⇒ J = p ∨ R.one ∈ J",
			Derive(func(b *Argument) {
				J := b.FixAs[Set[A]]("J")
				given := b.Assume()
				larger := b.Conjuncts(
					given,
					"J is an ideal",
					"p lies in J")
				idealJ, inclusion := larger[0], larger[1]
				proper := b.Unless(
					b.Term("J = p"),
					"the ideal is p",
					Given(func(c *Argument, equal Fact) {
						c.Show(
							"J is p, the first alternative",
							By(Normalized, equal))
					}))
				x, outside := b.ObtainAs[A](
					"J has an element outside p",
					"∃x:A. x ∈ J ∧ x ∉ p",
					BySets(proper, inclusion))
				xInR := b.Have(
					"the chosen element lies in the carrier",
					"x ∈ R.carrier",
					BySets(outside, ring_ideal.IdealSubset.Read(idealJ)))
				xm := b.MemberOf[on.R](x, xInR)
				coset := b.TermAs[Set[A]]("left_coset(R.add, x, p)")
				cosetIn := b.Have(
					"its coset lies in the quotient",
					"left_coset(R.add, x, p) ∈ left_cosets(R.add, R.carrier, p)",
					By(xm, ring_ideal.IdealSubset.Read(ideal), quotient_group.InLeftCosets.Read(additive).At(p, coset)))
				cosetNonzero := b.Have(
					"its coset is nonzero",
					"left_coset(R.add, x, p) ≠ p",
					By(Normalized, ideal, outside, CosetEqIdealIff.Read(R).At(p, xm)))
				v, inverse := b.ObtainAs[Set[A]](
					"take an inverse coset",
					"∃v:set(A). "+
						"    v ∈ left_cosets(R.add, R.carrier, p) ∧ "+
						"    quotient_mul(p, left_coset(R.add, x, p), v) = left_coset(R.add, R.one, p)",
					By(cosetIn, cosetNonzero, cosetInverses.At(coset)))
				y, representative := b.ObtainAs[A](
					"choose a representative of the inverse coset",
					"∃y:A. v = left_coset(R.add, y, p) ∧ y ∈ R.carrier",
					By(
						inverse,
						ring_ideal.IdealSubset.Read(ideal),
						quotient_group.InLeftCosets.Read(additive).At(p, v)))
				yInR := b.Conjuncts(
					representative,
					"v is the coset of y",
					"y lies in the carrier")[1]
				ym := b.MemberOf[on.R](y, yInR)
				sameCoset := b.Have(
					"the product represents one",
					"left_coset(R.add, x * y, p) = left_coset(R.add, R.one, p)",
					By(representative, inverse, ideal, QuotientMulCoset.Read(R).At(p, xm, ym)))
				product := comm_ring.MulIn.Read(R).At(xm, ym)
				oneInR := b.Have(
					"one lies in the carrier",
					"R.one ∈ R.carrier",
					By(comm_ring.OneIn.Read(R)))
				one := b.MemberOf[on.R](b.TermAs[A]("R.one"), oneInR)
				difference := b.Have(
					"the product differs from one by an element of p",
					"x * y - R.one ∈ p",
					By(ideal, sameCoset, CosetEqIff.Read(R).At(p, product, one)))
				xInJ := b.Conjuncts(
					outside,
					"x lies in J",
					"x is outside p")[0]
				yx, excess := b.TermAs[A]("y * x"), b.TermAs[A]("x * y - R.one")
				negated := b.TermAs[A]("-(x * y - R.one)")
				productInJ := b.Have(
					"J contains the product",
					"y * x ∈ J",
					By(ym, xInJ, ring_ideal.IdealMul.Read(idealJ).AsFact().At(y, x)))
				negative := b.Have(
					"J contains the negative difference",
					"-(x * y - R.one) ∈ J",
					BySets(inclusion, difference, idealJ, ring_ideal.IdealNeg.Read(R).At(J, excess)))
				sum := b.Have(
					"the two elements sum to one",
					"y * x + -(x * y - R.one) = R.one",
					ByArith(R, xm, ym))
				b.Show(
					"the larger ideal contains one",
					By(productInJ, negative, sum, ring_ideal.IdealAdd.Read(idealJ).AsFact().At(yx, negated)))
			}))
		a.Show(
			"the prime satisfies the maximal ideal criterion",
			Unfold(ring_ideal.MaximalIdealDef),
			By(ideal, above, ring_ideal.PrimeIdealProper.Read(prime)))
	}),
})}

// FiniteIndexChainStabilizes — an increasing chain of ideals above an ideal
// of finite index stabilizes: every ideal of the chain has finite index, and
// strict growth past the ideal of least index would lower that index.
var FiniteIndexChainStabilizes = finiteIndexChainStabilizesThm{family.Add(registry.ProofEntry{
	Name: "FiniteIndexChainStabilizes",
	Key:  "prop_8fcb1e51230888f7",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀I:set(A). ∀C:(num → set(A)).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"finite(left_cosets(R.add, R.carrier, I))",
			"I ⊆ C(0)",
			"∀n:num. ring_ideal(R, C(n)) ∧ C(n) ⊆ C(n + 1)",
		},
		Conclusion: "∃N:num. ∀n:num. N ≤ n ⇒ C(n) = C(N)",
	}, func(
		a *Argument,
		R comm_ring.CommRingFact[on.R],
		I *Expr[Set[A]],
		C *Arrow[Nat, Set[A]],
		h Fact,
	) {
		parts := a.Conjuncts(
			h,
			"I is an ideal",
			"R modulo I is finite",
			"I lies in the first ideal",
			"the ideals form an increasing chain")
		idealI, finiteI, first, chain := parts[0], parts[1], parts[2], parts[3]
		monotone := a.Have(
			"later ideals contain earlier ideals",
			"∀m n:num. m ≤ n ⇒ C(m) ⊆ C(n)",
			By(chain, At(order.IncreasingFromSteps, C)))
		included := a.Have(
			"every chain ideal contains I",
			"∀n:num. I ⊆ C(n)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				later := b.Have(
					"n comes no earlier than 0",
					"0 ≤ n",
					ByArith())
				b.Show(
					"I lies in C(0), which lies in C(n)",
					BySets(first, later, monotone.At(b.Ctx().Nat(0), n)))
			}))
		finiteIndex := a.Have(
			"all chain ideals have finite index",
			"∀n:num. finite(left_cosets(R.add, R.carrier, C(n)))",
			a.ForEach(func(n *Expr[Nat]) Action {
				return By(
					idealI,
					chain.At(n),
					included.At(n),
					finiteI,
					FiniteQuotientAboveIdeal.Read(R).At(I, C.Apply(n)))
			}))
		attained := a.Have(
			"the chain attains some index, C(0) its own",
			"∃k i:num. ideal_index(R, C(i)) = k",
			Derive(func(b *Argument) {
				b.Take(b.TermAs[Nat]("ideal_index(R, C(0))"))
				b.Take(b.Ctx().Nat(0))
				b.Show(
					"C(0) attains its own index",
					Basic())
			}))
		N, least := a.ObtainAs[Nat](
			"some C(N) has the least index in the chain",
			"∃N:num. ∀j:num. ideal_index(R, C(N)) ≤ ideal_index(R, C(j))",
			By(
				attained,
				nat_order.WellOrdering.At(a.TermAs[Set[Nat]]("λk:num. ∃i:num. ideal_index(R, C(i)) = k")),
				nat_order.NotLessThan))
		a.Take(N)
		n := a.FixAs[Nat]("n")
		after := a.Assume()
		different := a.SupposeNot()
		falling := a.Have(
			"strict growth would lower the index",
			"ideal_index(R, C(n)) < ideal_index(R, C(N))",
			By(
				chain.At(N),
				chain.At(n),
				after,
				monotone.At(N, n),
				different,
				finiteIndex.At(N),
				StrictIdealInclusionLowersIndex.Read(R).At(C.Apply(N), C.Apply(n))))
		a.Show(
			"an index below the least contradicts minimality",
			ByArith(falling, least.At(n)))
	}),
})}

// FiniteQuotientHasSimpleLayer — a strict inclusion J ⊆ I of ideals with
// finitely many cosets of J in I has a simple layer above J: among the
// ideals strictly above J and inside I, choose one of greatest index in I;
// an ideal strictly between J and it would have a greater index still.
var FiniteQuotientHasSimpleLayer = finiteQuotientHasSimpleLayerThm{family.Add(registry.ProofEntry{
	Name: "FiniteQuotientHasSimpleLayer",
	Key:  "prop_9f72ccd171d3255",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀I J:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"ring_ideal(R, J)",
			"J ⊆ I",
			"J ≠ I",
			"finite(left_cosets(R.add, I, J))",
		},
		Conclusion: "∃H:set(A). ideal_cover(R, J, H) ∧ H ⊆ I",
		Abbrev: Abbrev{
			{Name: "G", Text: "restrict_group(additive_group(R), I)"},
		},
	}, func(a *Argument, R comm_ring.CommRingFact[on.R], I, J *Expr[Set[A]], h Fact) {
		parts := a.Conjuncts(
			h,
			"I is an ideal",
			"J is an ideal",
			"J lies in I",
			"the inclusion is strict",
			"I/J is finite")
		idealI, idealJ, jInI, strict, finiteIJ := parts[0], parts[1], parts[2], parts[3], parts[4]
		additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(R))
		additiveGroup := a.TermAs[group.GroupOps[A]]("additive_group(R)")
		groupI := a.Have(
			"addition on I is a group",
			"group_on(«G»)",
			By(idealI, IdealSubgroup.Read(R).At(I), group.SubgroupGroupOn.Read(additive).At(I)))
		subgroupWithin := a.Have(
			"every ideal inside I is an additive subgroup of I",
			"∀K:set(A). ring_ideal(R, K) ∧ K ⊆ I ⇒ subgroup(«G», K)",
			Derive(func(b *Argument) {
				K := b.FixAs[Set[A]]("K")
				guard := b.Assume()
				b.Show(
					"an ideal is an additive subgroup of R, and one lying in I is a subgroup of I",
					By(guard, IdealSubgroup.Read(R).At(K), group_isomorphism.SubgroupRestrict.At(additiveGroup, I, K)))
			}))
		subJ := a.Have(
			"J is a subgroup of I under addition",
			"subgroup(«G», J)",
			By(subgroupWithin.At(J), idealJ, jInI))

		candidates := a.TermAs[Fun[Nat, Bool]](
			"λn:num. ∃H:set(A). ring_ideal(R, H) ∧ J ⊆ H ∧ H ⊆ I ∧ J ≠ H ∧ card(left_cosets(R.add, I, H)) = n")
		attained := a.Have(
			"I itself is a strict intermediate ideal, so some index in I is attained",
			"∃n:num. ∃H:set(A). ring_ideal(R, H) ∧ J ⊆ H ∧ H ⊆ I ∧ J ≠ H ∧ card(left_cosets(R.add, I, H)) = n",
			Derive(func(b *Argument) {
				b.Take(b.TermAs[Nat]("card(left_cosets(R.add, I, I))"))
				b.Take(I)
				b.Show(
					"I is a strict intermediate ideal above J",
					By(idealI, jInI, strict, set_order.SubsetRefl.At(I)))
			}))
		bounded := a.Have(
			"the index of J in I bounds every such index",
			"∃M:num. ∀n:num. "+
				"    (∃H:set(A). "+
				"        ring_ideal(R, H) ∧ J ⊆ H ∧ H ⊆ I ∧ J ≠ H ∧ card(left_cosets(R.add, I, H)) = n) ⇒ "+
				"    n ≤ M",
			Derive(func(b *Argument) {
				bound := b.TermAs[Nat]("card(left_cosets(R.add, I, J))")
				b.Take(bound)
				n := b.FixAs[Nat]("n")
				H, chosen := b.UnpackAs[Set[A]](b.Assume(), "H")
				hParts := b.Conjuncts(
					chosen,
					"H is an ideal",
					"J lies in H",
					"H lies in I",
					"J differs from H",
					"I/H has cardinality n")
				subH := b.Have(
					"H is a subgroup of I under addition",
					"subgroup(«G», H)",
					By(subgroupWithin.At(H), hParts[0], hParts[2]))
				lower := b.Have(
					"enlarging J strictly to H lowers the index",
					"card(left_cosets(R.add, I, H)) < card(left_cosets(R.add, I, J))",
					By(
						subJ,
						subH,
						hParts[1],
						hParts[3],
						finiteIJ,
						quotient_group.StrictInclusionLowersIndex.Read(groupI).At(J, H)))
				below := b.Have(
					"so n lies below the index of J",
					"n < card(left_cosets(R.add, I, J))",
					By(Normalized, lower, hParts[4]))
				b.Show(
					"and n is at most that index",
					By(below, nat_order.LessEqOfLessThan.At(n, bound)))
			}))
		m, greatestData := a.ObtainAs[Nat](
			"choose the greatest such index",
			"∃m:num. "+
				"    (∃H:set(A). "+
				"        ring_ideal(R, H) ∧ J ⊆ H ∧ H ⊆ I ∧ J ≠ H ∧ card(left_cosets(R.add, I, H)) = m) ∧ "+
				"    (∀n:num. "+
				"        (∃K:set(A). "+
				"            ring_ideal(R, K) ∧ J ⊆ K ∧ K ⊆ I ∧ J ≠ K ∧ card(left_cosets(R.add, I, K)) = n) ⇒ "+
				"        n ≤ m)",
			By(attained, bounded, nat_order.MaximumExists.At(candidates)),
			Named("m"))
		greatestParts := a.Conjuncts(
			greatestData,
			"an ideal attains m",
			"no strict intermediate ideal has a greater index in I")
		H, chosenH := a.UnpackAs[Set[A]](greatestParts[0], "H")
		hParts := a.Conjuncts(
			chosenH,
			"H is an ideal",
			"J lies in H",
			"H lies in I",
			"J differs from H",
			"I/H has cardinality m")
		idealH, jInH, hInI, strictH, countH := hParts[0], hParts[1], hParts[2], hParts[3], hParts[4]
		subH := a.Have(
			"H is a subgroup of I under addition",
			"subgroup(«G», H)",
			By(subgroupWithin.At(H), idealH, hInI))
		noIntermediate := a.Have(
			"the greatest index leaves no ideal between J and H",
			"∀K:set(A). ring_ideal(R, K) ∧ J ⊆ K ∧ K ⊆ H ⇒ K = J ∨ K = H",
			Derive(func(b *Argument) {
				K := b.FixAs[Set[A]]("K")
				guard := b.Assume()
				neither := b.SupposeNot()
				notEndpoints := b.Have(
					"then K differs from both endpoints",
					"K ≠ J ∧ K ≠ H",
					By(Normalized, neither))
				kInI := b.Have(
					"K lies in I",
					"K ⊆ I",
					BySets(guard, hInI))
				subK := b.Have(
					"K is a subgroup of I under addition",
					"subgroup(«G», K)",
					By(subgroupWithin.At(K), guard, kInI))
				split := b.Have(
					"the index of J in I splits at K",
					"(finite(left_cosets(R.add, I, J)) ⇔ "+
						"    finite(left_cosets(R.add, I, K)) ∧ finite(left_cosets(R.add, K, J))) ∧ "+
						"(finite(left_cosets(R.add, I, J)) ⇒ "+
						"    card(left_cosets(R.add, I, J)) = "+
						"    card(left_cosets(R.add, I, K)) * card(left_cosets(R.add, K, J)))",
					By(
						subK,
						guard,
						group.SubgroupOne.Read(subJ),
						quotient_group.IndexMultiplicative.Read(groupI).At(J, K)))
				greater := b.Have(
					"enlarging K strictly to H lowers the index",
					"card(left_cosets(R.add, I, H)) < card(left_cosets(R.add, I, K))",
					By(
						subK,
						subH,
						guard,
						notEndpoints,
						split,
						finiteIJ,
						quotient_group.StrictInclusionLowersIndex.Read(groupI).At(K, H)))
				exceeds := b.Have(
					"so the index of K exceeds m",
					"m < card(left_cosets(R.add, I, K))",
					By(Normalized, greater, countH))
				candidate := b.Have(
					"K is a strict intermediate ideal with that index",
					"∃K₁:set(A). "+
						"    ring_ideal(R, K₁) ∧ "+
						"    J ⊆ K₁ ∧ "+
						"    K₁ ⊆ I ∧ "+
						"    J ≠ K₁ ∧ "+
						"    card(left_cosets(R.add, I, K₁)) = card(left_cosets(R.add, I, K))",
					Derive(func(c *Argument) {
						c.Take(K)
						c.Show(
							"K is an admissible strict intermediate ideal",
							By(Normalized, guard, kInI, notEndpoints))
					}))
				index := b.TermAs[Nat]("card(left_cosets(R.add, I, K))")
				b.Show(
					"this contradicts the greatest choice of m",
					By(greatestParts[1].At(index), candidate, exceeds, nat_order.NotLessEq.At(index, m)))
			}))
		a.Take(H)
		a.Show(
			"H is a simple layer above J",
			By(idealJ, idealH, jInH, strictH, noIntermediate, hInI, ring_ideal.IdealCoverDef))
	}),
})}

// IdealsAboveFiniteIndex — only finitely many ideals lie above an ideal of
// finite index: an ideal above I is the union of the cosets of I inside it,
// and the cosets of I form a finite set, which has finitely many subsets.
var IdealsAboveFiniteIndex = idealsAboveFiniteIndexThm{family.Add(registry.ProofEntry{
	Name: "IdealsAboveFiniteIndex",
	Key:  "prop_8af01b46d30c5de0",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀I:set(A).",
		Hypotheses: []string{"ring_ideal(R, I)", "finite(left_cosets(R.add, R.carrier, I))"},
		Conclusion: "finite({J:set(A) | ring_ideal(R, J) ∧ I ⊆ J})",
		Abbrev: Abbrev{
			{Name: "unions", Text: "image(λS:set(set(A)). ⋃S, " +
				"    {S:set(set(A)) | S ⊆ left_cosets(R.add, R.carrier, I)})"},
		},
	},
		func(a *Argument, R comm_ring.CommRingFact[on.R], I *Expr[Set[A]], ideal, finiteCosets Fact) {
			ring := a.TermAs[RingOps[A]]("R")
			additive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(R))
			subgroup := a.Have(
				"I is an additive subgroup of R",
				"subgroup(additive_group(R), I)",
				By(ideal, IdealSubgroup.Read(R).At(I)))
			inCarrier := a.Have(
				"I lies in R",
				"I ⊆ R.carrier",
				By(ideal, ring_ideal.IdealSubset.At(ring, I)))
			cover := a.Have(
				"each element of an ideal above I lies in a coset of I inside that ideal",
				Statement{
					Binders:    "∀J:set(A). ∀x:A.",
					Hypotheses: []string{"ring_ideal(R, J)", "I ⊆ J", "x ∈ J"},
					Conclusion: "∃c:set(A). c ∈ left_cosets(R.add, R.carrier, I) ∧ c ⊆ J ∧ x ∈ c",
				},
				Derive(func(b *Argument) {
					J := b.FixAs[Set[A]]("J")
					x := b.FixAs[A]("x")
					given := b.Conjuncts(
						b.Assume(),
						"J is an ideal",
						"J contains I",
						"x lies in J")
					inRing := b.Have(
						"x lies in R",
						"x ∈ R.carrier",
						BySets(given[0], given[2], ring_ideal.IdealSubset.At(ring, J)))
					inJ := b.Have(
						"the coset of x stays in J, which is closed under addition",
						"left_coset(R.add, x, I) ⊆ J",
						BySets(
							given[0],
							given[1],
							given[2],
							At(ring_ideal.IdealAdd, ring, J),
							group.LeftCosetDef.At(a.TermAs[Fun2[A, A, A]]("R.add"), x, I)))
					own := b.Have(
						"x lies in its own coset",
						"x ∈ left_coset(R.add, x, I)",
						By(inRing, subgroup, group.InOwnLeftCosetOn.Read(additive).AsFact().At(x, I)))
					member := b.Have(
						"and the coset is one of the cosets of I",
						"left_coset(R.add, x, I) ∈ left_cosets(R.add, R.carrier, I)",
						By(inRing, inCarrier, quotient_group.LeftCosetInLeftCosets.Read(additive).AsFact().At(I, x)))
					b.Take(b.TermAs[Set[A]]("left_coset(R.add, x, I)"))
					b.Show(
						"the coset of x is the coset sought",
						By(member, inJ, own))
				}))
			union := a.Have(
				"so an ideal above I is the union of the cosets inside it",
				Statement{
					Binders:    "∀J:set(A).",
					Hypotheses: []string{"ring_ideal(R, J)", "I ⊆ J"},
					Conclusion: "J = ⋃{c:set(A) | c ∈ left_cosets(R.add, R.carrier, I) ∧ c ⊆ J}",
				},
				Derive(func(b *Argument) {
					J := b.FixAs[Set[A]]("J")
					given := b.Conjuncts(
						b.Assume(),
						"J is an ideal",
						"J contains I")
					covered := b.Have(
						"the cosets inside J cover it",
						"∀x:A. x ∈ J ⇒ ∃c:set(A). c ∈ left_cosets(R.add, R.carrier, I) ∧ c ⊆ J ∧ x ∈ c",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							inJ := c.Assume()
							c.Show(
								"this is the coset of x",
								By(given[0], given[1], inJ, cover.At(J, x)))
						}))
					b.Show(
						"a union of subsets of J covering J is J",
						BySets(covered))
				}))
			captured := a.Have(
				"so an ideal above I is the union of some set of cosets",
				"∀J:set(A). ring_ideal(R, J) ∧ I ⊆ J ⇒ J ∈ «unions»",
				Derive(func(b *Argument) {
					J := b.FixAs[Set[A]]("J")
					given := b.Conjuncts(
						b.Assume(),
						"J is an ideal",
						"J contains I")
					b.Do(Simp(Fwd(set_basic.InImage)))
					b.Take(b.TermAs[Set[Set[A]]]("{c:set(A) | c ∈ left_cosets(R.add, R.carrier, I) ∧ c ⊆ J}"))
					inside := b.Have(
						"the cosets inside J are cosets",
						"{c:set(A) | c ∈ left_cosets(R.add, R.carrier, I) ∧ c ⊆ J} ⊆ left_cosets(R.add, R.carrier, I)",
						BySets())
					b.Show(
						"J is their union",
						By(given[0], given[1], union.At(J), inside))
				}))
			finiteUnions := a.Have(
				"finitely many sets of cosets have finitely many unions",
				"finite(«unions»)",
				By(
					finiteCosets,
					finite_set.FinitePowerset.At(a.TermAs[Set[Set[A]]]("left_cosets(R.add, R.carrier, I)")),
					finite_set.FiniteImage.At(
						a.TermAs[Fun[Set[Set[A]], Set[A]]]("λS:set(set(A)). ⋃S"),
						a.TermAs[Set[Set[Set[A]]]]("{S:set(set(A)) | S ⊆ left_cosets(R.add, R.carrier, I)}"))))
			inside := a.Have(
				"the ideals above I are among those unions",
				"{J:set(A) | ring_ideal(R, J) ∧ I ⊆ J} ⊆ «unions»",
				BySets(captured))
			a.Show(
				"a subset of a finite set is finite",
				By(
					finiteUnions,
					inside,
					finite_set.FiniteSubset.At(
						a.TermAs[Set[Set[A]]]("{J:set(A) | ring_ideal(R, J) ∧ I ⊆ J}"),
						a.TermAs[Set[Set[A]]]("«unions»"))))
		}),
})}
