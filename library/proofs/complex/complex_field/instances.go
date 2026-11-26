// instances.go — ℂ is a field: the instances the abstract chapters
// read, built up in the order the structures nest. Each equational
// axiom is proved the same way: ComplexEq turns it into the two
// equations between its parts, the definitions compute each part, and
// what is left is arithmetic of reals. The sub-structures and the
// definitions are cited, and the left inverse is an argument. Then the
// structures that read that field: ℂ is an integral domain of characteristic
// zero, and the embedding of ℝ is a ring homomorphism. Last, Π read as the
// module chapter's fold at ℂ's multiplication.

package complex_field

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// MulMonoid — complex multiplication, with one, is a commutative
// monoid.
var MulMonoid = mulMonoidThm{family.Add(registry.ProofEntry{
	Name: "MulMonoid",
	Key:  "prop_71e48627ff26c409",
	Build: family.Instance(comm_monoid.CommMonoid, "comm_monoid(complex_mul, complex_of_real(&1))",
		Case(
			"multiplication commutes",
			Simp(Parts, Fwd(ComplexMulDef)),
			ByArith()),
		Case(
			"multiplication associates",
			Simp(Parts, Fwd(ComplexMulDef)),
			ByArith()),
		Case(
			"one is a left identity",
			Simp(Parts, Fwd(ComplexMulDef), Fwd(ComplexOfRealDef)),
			ByArith())),
})}

// AddGroup — complex addition, with zero and negation, is an abelian
// group.
var AddGroup = addGroupThm{family.Add(registry.ProofEntry{
	Name: "AddGroup",
	Key:  "prop_3d1ac261632d8a82",
	Build: family.Instance(abelian_group.AbelianGroup, "abelian_group(additive_group(complex_ring))",
		Case(
			"addition, zero and negation form a group",
			Unfold(group.Group),
			SplitConjAll(
				Case(
					"addition associates",
					Simp(Parts, Fwd(ComplexAddDef)),
					ByArith()),
				Case(
					"zero is a left identity",
					Simp(Parts, Fwd(ComplexAddDef), Fwd(ComplexOfRealDef)),
					ByArith()),
				Case(
					"negation is a left inverse",
					Simp(Parts, Fwd(ComplexAddDef), Fwd(ComplexNegDef), Fwd(ComplexOfRealDef)),
					ByArith()))),
		Case(
			"addition commutes",
			Simp(Parts, Fwd(ComplexAddDef)),
			ByArith())),
})}

// CommRing — ℂ is a commutative ring: the two structures above, joined
// by distributivity, and subtraction as its definition spells it.
var CommRing = commRingThm{family.Add(registry.ProofEntry{
	Name: "CommRing",
	Key:  "prop_174b933bdeb4e5fe",
	Build: family.Instance(comm_ring.CommRing,
		"comm_ring(complex_ring)",
		Case(
			"the additive group",
			Cite(AddGroup)),
		Case(
			"the multiplicative monoid",
			Cite(MulMonoid)),
		Case(
			"multiplication distributes over addition",
			Simp(Parts, Fwd(ComplexAddDef), Fwd(ComplexMulDef)),
			ByArith()),
		Case(
			"subtraction is addition of the negation",
			Cite(ComplexSubDef))),
})}

// CommRingOn — ℂ is a commutative ring on its carrier, the whole type:
// the ring restricted to 𝕌 is the ring itself, so the whole-type ring
// is the ring on its carrier. A chapter that reads the laws of a ring on
// a set reads them at ℂ through this instance.
var CommRingOn = commRingOnThm{family.Add(registry.ProofEntry{
	Name: "CommRingOn",
	Key:  "prop_5a4ab64e28ad247f",
	Build: family.Theorem("comm_ring_on(complex_ring)", func(a *Argument) {
		whole := a.Have(
			"ℂ's ring restricted to the whole type is ℂ's ring",
			"restrict_ring(complex_ring, 𝕌) = complex_ring",
			Simp(Fwd(module_record.RestrictRingDef), Fwd(ComplexRingDef)),
			Refl())
		a.Show(
			"so ℂ's ring laws hold on its carrier",
			By(Normalized, comm_ring.CommRingOnUniverse, CommRing, whole))
	}),
})}

// Field — ℂ is a field. The ring is the instance above; one is not
// zero because the real parts differ; the inverse of zero is zero
// because every quotient by zero is zero; division is its definition.
// The one real argument is the left inverse: a nonzero x has parts that
// are not both zero, so the sum of their squares is not zero and times
// its own inverse is one — which is the real part of inv(x) * x, while
// the imaginary part cancels.
var Field = fieldThm{family.Add(registry.ProofEntry{
	Name: "Field",
	Key:  "prop_a3b7c712f7aefae9",
	Build: family.Instance(field.Field,
		"field(complex_field_ops)",
		Case(
			"the commutative ring: the field's ring is the ring of "+
				"complex numbers, both packing the same operations on 𝕌",
			By(CommRing, field.FieldRingDef, ComplexRingDef)),
		Case(
			"one is not zero: the real parts differ",
			Simp(Parts, Fwd(ComplexOfRealDef)),
			ByArith()),
		Case(
			"a nonzero complex number has a left inverse",
			Derive(func(b *Argument) {
				b.FixAs[Complex]("x")
				nonzero := b.Assume()
				zeroParts := b.Have(
					"a number whose parts are both zero is zero",
					"re(x) = &0 ∧ im(x) = &0 ⇒ x = complex_of_real(&0)",
					Simp(Parts, Fwd(ComplexOfRealDef)),
					Basic())
				sum := b.Have(
					"so the parts of x are not both zero, and neither is the sum of their squares",
					"re(x) * re(x) + im(x) * im(x) ≠ &0",
					By(nonzero, zeroParts, real_order_ring.SumSquaresEqZero))
				cancel := b.Have(
					"that sum times its inverse is one",
					"(re(x) * re(x) + im(x) * im(x)) * real_inv(re(x) * re(x) + im(x) * im(x)) = &1",
					By(sum, field.MulRightInverse.Read(real_field.Field)))
				b.Show(
					"the real part of inv(x) * x is that sum over itself, and the imaginary part cancels",
					Simp(Parts, Fwd(ComplexMulDef), Fwd(ComplexInvDef), Fwd(ComplexOfRealDef)),
					ByArith(cancel))
			})),
		Case(
			"the inverse of zero is zero: every quotient by zero is zero",
			Simp(Parts, Fwd(ComplexInvDef), Fwd(ComplexOfRealDef)),
			ByArith()),
		Case(
			"division is multiplication by the inverse",
			Cite(ComplexDivDef))),
})}

// FieldOn — ℂ is a field on its carrier, the whole type: a field
// restricted to 𝕌 is a field on 𝕌, and ℂ's field operations already
// carry 𝕌 as their carrier, so restricting them changes nothing. A
// chapter that reads the laws of a field on a set reads them at ℂ
// through this instance.
var FieldOn = fieldOnThm{family.Add(registry.ProofEntry{
	Name: "FieldOn",
	Key:  "prop_f15c24f22a5cac28",
	Build: family.Theorem("field_on(complex_field_ops)", func(a *Argument) {
		F := a.TermAs[field.FieldOps[Complex]]("complex_field_ops")
		a.Show(
			"ℂ's field restricted to 𝕌 is a field on 𝕌, and the restriction is ℂ's field itself",
			By(
				Field,
				field.FieldOnUniverse.At(F),
				field.RestrictFieldDef.At(F, a.TermAs[Set[Complex]]("𝕌")),
				ComplexFieldOpsDef))
	}),
})}

// ComplexIntegralDomain — ℂ is an integral domain on the whole type: its ring is
// commutative, one is not zero, and a field has no zero divisors.
var ComplexIntegralDomain = complexIntegralDomainThm{family.Add(registry.ProofEntry{
	Name: "ComplexIntegralDomain",
	Key:  "prop_95c86aaf5b3c757a",
	Build: family.Instance(integral_domain.IntegralDomainOn,
		"integral_domain_on(complex_ring)",
		Case(
			"the complex ring is commutative on its carrier",
			Cite(CommRingOn)),
		Case(
			"one is not zero: the real parts differ",
			Simp(Parts, Fwd(ComplexOfRealDef)),
			ByArith()),
		Case(
			"a field has no zero divisors",
			By(field.MulEqZero.Read(Field)))),
})}

// ComplexCharacteristicZero — ℂ has characteristic zero: n ones sum to the numeral
// n, and the embedding of ℝ keeps it away from zero for n positive.
var ComplexCharacteristicZero = complexCharacteristicZeroThm{family.Add(registry.ProofEntry{
	Name: "ComplexCharacteristicZero",
	Key:  "prop_4a066feb29e7a4cc",
	Build: family.Theorem(
		"characteristic_zero(complex_ring)",
		func(arg *Argument) {
			arg.Do(
				Unfold(comm_ring.CharacteristicZeroDef),
				Simp(Fwd(ComplexRingDef), Fwd(AddPowOne)))
			arg.FixAs[Nat]("n")
			positive := arg.Assume()
			arg.Show(
				"the numeral n is not zero, in ℝ or in its image",
				ByArith(positive, OfRealInjective.At(arg.TermAs[Real]("&n"), arg.TermAs[Real]("&0"))))
		}),
})}

// OfRealRingHomomorphism — the embedding of ℝ is a ring homomorphism into ℂ:
// both rings are rings on the whole type, and the embedding keeps the sum and
// the product, the one of ℂ being the embedded one of ℝ.
var OfRealRingHomomorphism = ofRealRingHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "OfRealRingHomomorphism",
	Key:  "prop_98ee5ddd040b784b",
	Build: family.Instance(ring_homomorphism.RingHomomorphism,
		"ring_homomorphism(real_ring, complex_ring, complex_of_real)",
		Case(
			"ℝ is a commutative ring on its carrier",
			Cite(real_ring.CommRingOn)),
		Case(
			"so is ℂ",
			Cite(CommRingOn)),
		Case(
			"every complex number lies in ℂ's carrier",
			By(set_basic.InUniv.Inst[Complex]())),
		Case(
			"the embedding keeps the sum",
			By(OfRealAdd)),
		Case(
			"and the product",
			By(OfRealMul))),
})}

// ComplexProductModuleSum — a finite product in ℂ's multiplicative monoid is the
// usual product: the module chapter's fold from a monoid's identity is the
// iterated operation, and `complex_product` is that operation at complex
// multiplication.
var ComplexProductModuleSum = complexProductModuleSumThm{family.Add(registry.ProofEntry{
	Name: "ComplexProductModuleSum",
	Key:  "prop_26e2b3a8555cfbcd",
	Build: family.Theorem(Statement{
		Binders:    "∀f:(A → complex). ∀s:set(A).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "module_sum(complex_mul, complex_of_real(&1), s, f) = product(s, f)",
	}, func(a *Argument, f *Arrow[A, Complex], s *Expr[Set[A]], finite Fact) {
		a.Show(
			"Π is the iterated operation at complex multiplication, which the fold is",
			Unfold(ComplexProductDef),
			By(finite, module.ModuleSumIteratedOp.Read(MulMonoid).At(s, f)))
	}),
})}
