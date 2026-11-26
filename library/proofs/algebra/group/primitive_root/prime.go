// prime.go — the units mod a prime form a cyclic group, by counting the
// solutions of x ^ d = 1 in a field of p elements.

package primitive_root

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/cyclic_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/units_mod"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_congruence"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/nat_num/totient"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// ResidueRootsBound — mod a prime p, at most d residues a below p satisfy
// a ^ d ≡ 1 (mod p). In a field F of p elements, which has characteristic
// p, the map a ↦ ā sending a residue to the image of the integer a is
// one-to-one on the solutions, since integers with the same image are
// congruent mod p, and sends each solution to a root of x ^ d = 1, of which
// F has at most d (finite_field.RootsOfUnityBound). The integers modulo p
// are such a field.
var ResidueRootsBound = residueRootsBoundThm{family.Add(registry.ProofEntry{
	Name: "ResidueRootsBound",
	Key:  "prop_a6dbf383db4e6478",
	Build: family.Sections(Statement{
		Binders: "∀p d:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"0 < d",
		},
		Conclusion: "finite(«solutions») ∧ card(«solutions») ≤ d",
		Abbrev: Abbrev{
			{Name: "solutions", Text: "{a:num | a < p ∧ a ^ d ≡ 1 (mod p)}"},
			{Name: "inField", Text: "λa:num. integer_map(field_ring(F), a)"},
			{Name: "roots", Text: "{x:A | x ∈ F.carrier ∧ monoid_pow(F.mul, F.one, x, d) = F.one}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		inAnyField := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀p d:num.",
			Hypotheses: []string{
				"nat_prime(p)",
				"has_size(F.carrier, p)",
				"0 < d",
			},
			Conclusion: "finite(«solutions») ∧ card(«solutions») ≤ d",
		}, func(arg *Argument, F field.FieldFact[on.F], p, d *Expr[Nat], prime, size, positive Fact) {
			ring := field.RingOn.Read(F)
			solutions := arg.TermAs[Set[Nat]]("«solutions»")
			toField := arg.TermAs[Fun[Nat, A]]("«inField»")
			characteristic := arg.Have(
				"F has characteristic p",
				"field_characteristic(F, p)",
				By(prime, size, finite_field.PrimeSizeCharacteristic.Read(F).At(p)))
			oneToOne := arg.Have(
				"two solutions with the same image are congruent mod p, "+
					"and two residues below p that are congruent are equal",
				"injective_on(«solutions», «inField»)",
				Unfold(functions.InjectiveOnDef),
				Derive(func(b *Argument) {
					x, y := b.FixAs[Nat]("x"), b.FixAs[Nat]("y")
					same := b.Assume()
					b.Show(
						"equal images make the integers x and y congruent mod p, so x ≡ y, and both lie below p",
						By(
							characteristic,
							same,
							finite_field.IntegerMapEqIff.Read(F).At(p, b.TermAs[Int]("x"), b.TermAs[Int]("y")),
							int_congruence.OfNumCongruent.At(x, y, p),
							nat_congruence.CongDef.At(x, y, p),
							nat_div_mod.ModInjectiveBelow.At(x, y, p)))
				}))
			toRoot := arg.Have(
				"a solution maps to a root of x ^ d = 1",
				"∀a:num. a ^ d ≡ 1 (mod p) ⇒ monoid_pow(F.mul, F.one, «inField»(a), d) = F.one",
				Derive(func(b *Argument) {
					a := b.FixAs[Nat]("a")
					solves := b.Assume()
					b.Show(
						"the d-th power of the image of a is the image of a "+
							"^ d, congruent to 1 mod p, and one is the image of 1",
						By(
							characteristic,
							solves,
							ring_homomorphism.MapOne.Read(characteristic_zero.IntegerMapHomomorphism.Read(ring)),
							characteristic_zero.IntegerMapPow.Read(ring).At(b.TermAs[Int]("a"), d),
							int_pow.OfNumPow.At(a, d),
							int_congruence.OfNumCongruent.At(b.TermAs[Nat]("a ^ d"), b.TermAs[Nat]("1"), p),
							finite_field.IntegerMapEqIff.Read(F).At(
								p,
								b.TermAs[Int]("a ^ d"),
								b.TermAs[Int]("1"))))
				}))
			into := arg.Have(
				"so the image of the solutions lies among the roots of x ^ d = 1 in F",
				"image(«inField», «solutions») ⊆ «roots»",
				BySets(characteristic_zero.IntegerMapInCarrier.Read(ring), toRoot))
			finite := arg.Have(
				"the solutions lie below p, and finitely many numbers do",
				"finite(«solutions»)",
				BySets(
					finite_set.FiniteSubset.At(solutions, arg.TermAs[Set[Nat]]("{x:num | x < p}")),
					num_segment.FiniteBelowStrict.At(p)))
			arg.Show(
				"the solutions are as many as their images, which are among the at most d roots of x ^ d = 1",
				ByArith(
					finite,
					positive,
					oneToOne,
					into,
					finite_field.RootsOfUnityBound.Read(F).At(d),
					cardinality.CardImageInj.At(toField, solutions),
					cardinality.CardSubset.At(
						arg.TermAs[Set[A]]("image(«inField», «solutions»)"), arg.TermAs[Set[A]]("«roots»"))))
		})
		return ctx.Theorem(headline, func(a *Argument, p, d *Expr[Nat], prime, positive Fact) {
			a.Show(
				"the integers modulo p are a field with p elements",
				By(
					prime,
					positive,
					finite_field.PrimeFieldOn.At(p),
					finite_field.FiniteFieldDef,
					At(
						inAnyField,
						a.TermAs[field.FieldOps[Set[Int]]](
							"ideal_quotient_field(int_ring, ideal_span(int_ring, {int_of_num(p)}))"),
						p,
						d)))
		})
	}),
})}

// UnitsModPrimeCyclic — the units mod a prime p form a cyclic group: a
// primitive root mod p exists. The units form a finite group, and for every
// d > 0 a unit x with x ^ d the identity is a residue below p with
// x ^ d ≡ 1 (mod p), of which there are at most d (ResidueRootsBound); so
// the counting criterion (cyclic_group.CyclicCriterion) applies.
var UnitsModPrimeCyclic = unitsModPrimeCyclicThm{family.Add(registry.ProofEntry{
	Name: "UnitsModPrimeCyclic",
	Key:  "prop_4446dbe424e30e53",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
		},
		Conclusion: "cyclic_group(units_mod(p))",
		Abbrev: Abbrev{
			{Name: "roots", Text: "λd:num. " +
				"    {x:num | " +
				"        x ∈ units_mod(p).carrier ∧ " +
				"        monoid_pow(units_mod(p).mul, units_mod(p).one, x, d) = units_mod(p).one}"},
		},
	}, func(a *Argument, p *Expr[Nat], prime Fact) {
		units := a.Have(
			"the units mod p form an abelian group, a prime being at least 2 and so positive",
			"abelian_group_on(units_mod(p))",
			ByArith(prime, units_mod.AbelianGroupOn.At(p), nat_prime.PrimeAtLeastTwo.At(p)))
		bound := a.Have(
			"for every d > 0, at most d units x have x ^ d the identity",
			"∀d:num. 0 < d ⇒ card(«roots»(d)) ≤ d",
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				positive := b.Assume()
				within := b.Have(
					"such a unit is a residue below p with x ^ d ≡ 1 (mod p): the "+
						"group's power is the residue of x ^ d, its identity that of 1",
					"«roots»(d) ⊆ {a:num | a < p ∧ a ^ d ≡ 1 (mod p)}",
					Simp(
						Fwd(units_mod.UnitsPowMod),
						Fwd(units_mod.UnitsModDef),
						Fwd(group.GroupCarrierDef),
						Fwd(group.GroupOneDef)),
					BySets(nat_congruence.CongDef))
				b.Show(
					"and at most d residues below p solve a ^ d ≡ 1 (mod p)",
					By(
						prime,
						positive,
						within,
						ResidueRootsBound.At(p, d),
						cardinality.CardSubset,
						nat_order.LessEqTrans))
			}))
		a.Show(
			"the φ(p) units are finitely many, and a finite group with "+
				"at most d solutions of x ^ d = 1 for every d > 0 is cyclic",
			By(
				cyclic_group.CyclicCriterion.Read(abelian_group.GroupOn.Read(units)),
				units_mod.CarrierHasSize.At(p),
				cardinality.HasSizeDef,
				bound))
	}),
})}

// PrimitiveRootModPrime — a primitive root mod p exists: some g prime to p
// has g ^ e ≡ 1 (mod p) exactly when p − 1 divides e. A generator g of the
// cyclic group of units mod p has as its order the size of the subgroup it
// generates, all p − 1 units; the group's power of g is the residue of
// g ^ e, so g ^ e ≡ 1 exactly when that order divides e.
var PrimitiveRootModPrime = primitiveRootModPrimeThm{family.Add(registry.ProofEntry{
	Name: "PrimitiveRootModPrime",
	Key:  "prop_70cb4acfd4e7afe4",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
		},
		Conclusion: "∃g:num. ¬(p ∣ g) ∧ (∀e:num. g ^ e ≡ 1 (mod p) ⇔ p - 1 ∣ e)",
	}, func(a *Argument, p *Expr[Nat], prime Fact) {
		g, generator := a.ObtainAs[Nat](
			"the units mod p are cyclic: some unit g generates them",
			"∃g:num. g ∈ units_mod(p).carrier ∧ units_mod(p).carrier = cyclic_subgroup(units_mod(p), g)",
			By(prime, UnitsModPrimeCyclic.At(p), cyclic_group.CyclicGroupDef))
		parts := a.Conjuncts(
			generator,
			"g is a unit",
			"g generates the units")
		units := a.Have(
			"the units mod p form an abelian group, a prime being at least 2 and so positive",
			"abelian_group_on(units_mod(p))",
			ByArith(prime, units_mod.AbelianGroupOn.At(p), nat_prime.PrimeAtLeastTwo.At(p)))
		grp := abelian_group.GroupOn.Read(units)
		gm := a.MemberOf[on.Any](g, parts[0])
		order := a.Have(
			"the order of g is the size of the subgroup it generates, all p − 1 units",
			"group_element_order(units_mod(p), g) = p - 1",
			ByArith(
				prime,
				parts[1],
				cyclic_group.CardCyclicSubgroup.Read(grp).At(gm),
				cyclic_group.FiniteOrderPositive.Read(grp),
				units_mod.CarrierHasSize,
				cardinality.HasSizeDef,
				totient.TotientPrime.At(p)))
		residue := a.Unfolded(parts[0], units_mod.UnitsModDef)
		a.Take(g)
		a.Show(
			"g is prime to p, and its order is p − 1",
			SplitConj(
				Case(
					"a unit mod p is a residue prime to p",
					By(Normalized, residue, prime, nat_prime.PrimeCoprimeIffNotDivides, nat_gcd.CoprimeSym.At(g, p))),
				Case(
					"g ^ e is the group's e-th power of g, the identity exactly when the order p − 1 divides e",
					Derive(func(b *Argument) {
						e := b.FixAs[Nat]("e")
						b.Show(
							"by the order's divisibility law, read at the residues",
							By(
								order,
								gm,
								cyclic_group.OrderDividesIff.Read(grp).At(gm, e),
								units_mod.UnitsPowMod.At(p, g, e),
								units_mod.UnitsModDef,
								group.GroupOneDef,
								nat_congruence.CongDef.At(b.TermAs[Nat]("g ^ e"), b.TermAs[Nat]("1"), p)))
					}))))
	}),
})}
