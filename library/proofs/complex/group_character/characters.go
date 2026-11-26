// characters.go — the characters of a finite abelian group: they carry
// products to products, their values are roots of unity, they are closed
// under products and conjugates, a character of a subgroup extends to the
// group, a character separates any element from the identity, and the two
// orthogonality relations give their number.

package group_character

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/roots_of_unity"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/cyclic_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_isomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_polynomial"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// CharacterMul — a homomorphism from a group to the nonzero complex numbers
// carries the product of two points of the carrier to the product of their
// values in ℂ: it is the homomorphism's own law, where the product of the
// nonzero complex numbers is complex multiplication.
var CharacterMul = characterMulThm{family.Add(registry.ProofEntry{
	Name: "CharacterMul",
	Key:  "prop_3d3fdd3199409b7d",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀χ:(A → complex). ∀x y:A.",
		Hypotheses: []string{
			"group_homomorphism(G, field_units(complex_field_ops), χ)",
			"x ∈ G.carrier",
			"y ∈ G.carrier",
		},
		Conclusion: "χ(x * y) = χ(x) * χ(y)",
	},
		func(
			a *Argument,
			G *Expr[GroupOps[A]],
			χ *Arrow[A, Complex],
			x, y *Expr[A],
			hom, xIn, yIn Fact,
		) {
			units := a.TermAs[GroupOps[Complex]]("field_units(complex_field_ops)")
			a.Show(
				"χ carries the product to the product of nonzero complex numbers, which is complex multiplication",
				By(hom, xIn, yIn, group_homomorphism.MapMul.At(G, units, χ, x, y), roots_of_unity.FieldUnitsDef))
		}),
})}

// CharacterUnitModulus — on the carrier of a finite group, a homomorphism
// into the nonzero complex numbers takes values among the roots of unity
// of order dividing the group size.
var CharacterUnitModulus = characterUnitModulusThm{family.Add(registry.ProofEntry{
	Name: "CharacterUnitModulus",
	Key:  "prop_4add9408ab0f2e7",
	Reading: "Finiteness is needed: x ↦ 2ˣ on the integers under addition has no value " +
		"of modulus 1 but at 0. The values off the carrier are not read, so it holds for " +
		"any homomorphism into the nonzero complex numbers, a character among them.",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀χ:(A → complex). ∀x:A.",
		Hypotheses: []string{
			"group_homomorphism(G, field_units(complex_field_ops), χ)",
			"finite(G.carrier)",
			"x ∈ G.carrier",
		},
		Conclusion: "χ(x) ^ card(G.carrier) = &1 ∧ |χ(x)| = &1",
	},
		func(
			a *Argument,
			G *Expr[GroupOps[A]],
			χ *Arrow[A, Complex],
			x *Expr[A],
			hom, finite, xIn Fact,
		) {
			units := a.TermAs[GroupOps[Complex]]("field_units(complex_field_ops)")
			carrier := a.TermAs[Set[A]]("G.carrier")
			n := a.TermAs[Nat]("card(G.carrier)")
			value := χ.Apply(x)
			power := a.Have(
				"x^|G| = 1, so χ(x)^|G| = 1",
				"χ(x) ^ card(G.carrier) = &1",
				CalcEq(
					Leg(
						a.TermAs[Complex]("χ(monoid_pow(G.mul, G.one, x, card(G.carrier)))"),
						"χ carries the group power to the power of its value",
						By(xIn, hom, group_homomorphism.MapPow.At(G, units, χ, x, n))),
					Leg(
						a.TermAs[Complex]("χ(G.one)"),
						"x raised to the group size is the identity",
						By(
							finite,
							xIn,
							hom,
							group_homomorphism.Source.At(G, units, χ),
							cyclic_group.PowCardIsOne.At(G, x))),
					FinalLeg(
						"χ sends the identity to 1",
						By(hom, group_homomorphism.MapOne.At(G, units, χ)))))
			nonzero := a.Have(
				"the carrier has nonzero size because it contains x",
				"card(G.carrier) ≠ 0",
				By(Normalized, finite, xIn, cardinality.CardEqZero.At(carrier), set_basic.NotInEmpty.At(x)))
			a.Do(SplitConj(
				Case(
					"the character value raised to the group size is 1",
					By(power)),
				Case(
					"so it is a root of unity of nonzero order, which has modulus 1",
					By(power, nonzero, complex_abs.AbsRootOfUnity.At(value, n)))))
		}),
})}

// CharacterConjugateInverse — on the carrier of a finite group, the
// conjugate of a homomorphism's value into the nonzero complex numbers is
// its inverse, and is the value at the inverse point: the value has
// modulus 1 (CharacterUnitModulus), so its product with its conjugate is
// the square of its modulus, 1, and the homomorphism sends x⁻¹ to the
// inverse of the value at x.
var CharacterConjugateInverse = characterConjugateInverseThm{family.Add(registry.ProofEntry{
	Name: "CharacterConjugateInverse",
	Key:  "prop_de60042da0c5d9ac",
	Reading: "So the conjugate of a character of a finite group is its " +
		"inverse under the pointwise product, and is the character x ↦ χ(x⁻¹).",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀χ:(A → complex). ∀x:A.",
		Hypotheses: []string{
			"group_homomorphism(G, field_units(complex_field_ops), χ)",
			"finite(G.carrier)",
			"x ∈ G.carrier",
		},
		Conclusion: "χ(x) * conj(χ(x)) = &1 ∧ χ(G.inv(x)) = conj(χ(x))",
	},
		func(
			a *Argument,
			G *Expr[GroupOps[A]],
			χ *Arrow[A, Complex],
			x *Expr[A],
			hom, finite, xIn Fact,
		) {
			units := a.TermAs[GroupOps[Complex]]("field_units(complex_field_ops)")
			value := χ.Apply(x)
			conjugate := a.TermAs[Complex]("conj(χ(x))")
			modulus := a.Have(
				"the value has modulus 1",
				"|χ(x)| = &1",
				By(hom, finite, xIn, CharacterUnitModulus.At(G, χ, x)))
			product := a.Have(
				"the value times its conjugate is the square of its modulus, which is 1",
				"χ(x) * conj(χ(x)) = &1",
				ByArith(modulus, complex_abs.AbsSquare.At(value), complex_field.MulConj.At(value)))
			inverse := a.Have(
				"so the conjugate is the complex inverse of the value",
				"complex_inv(χ(x)) = conj(χ(x))",
				By(product, field.InvRightUnique.Read(complex_field.Field).At(value, conjugate)))
			a.Do(SplitConj(
				Case(
					"the conjugate is the inverse of the value",
					By(product)),
				Case(
					"χ sends x⁻¹ to the inverse of its value at x",
					By(Normalized, hom, xIn, inverse, group_homomorphism.MapInv.At(G, units, χ, x)))))
		}),
})}

// TrivialCharacter — the function that is 1 on a group's carrier and 0 off
// it is a character.
var TrivialCharacter = trivialCharacterThm{family.Add(registry.ProofEntry{
	Name:    "TrivialCharacter",
	Key:     "prop_4c306ccbabc95219",
	Reading: "Every group has it, including the trivial group, where it is the only character.",
	Build: family.Theorem(Statement{
		Binders:    "∀G:group_ops(A).",
		Hypotheses: []string{"group_on(G)"},
		Conclusion: "group_character(G, " +
			"    λx:A. COND(x ∈ G.carrier, complex_of_real(&1), complex_of_real(&0)))",
	},
		func(a *Argument, source group.GroupFact[on.G]) {
			F := a.TermAs[field.FieldOps[Complex]]("complex_field_ops")
			units := a.TermAs[GroupOps[Complex]]("field_units(complex_field_ops)")
			a.Do(
				Simp(Fwd(GroupCharacterDef)),
				SplitConj(
					Case(
						"the function is a homomorphism into the nonzero complex numbers",
						group_homomorphism.GroupHomomorphism.Intro(
							Case(
								"the source is the given group",
								By(source)),
							Case(
								"ℂ is a field on its carrier, so its nonzero numbers form a multiplicative group",
								By(
									complex_field.FieldOn,
									abelian_group.GroupOn.At(units),
									roots_of_unity.FieldUnitsAbelianGroupOn.At(F))),
							Case(
								"the function sends each point of the carrier to the nonzero value 1",
								Derive(func(b *Argument) {
									b.FixAs[A]("x")
									member := b.Assume()
									b.Show(
										"1 belongs to the target carrier",
										BySets(member, field.OneNotZero.Read(complex_field.Field)))
								})),
							Case(
								"the function preserves products on the carrier",
								Derive(func(b *Argument) {
									x := b.FixAs[A]("x")
									y := b.FixAs[A]("y")
									members := b.Assume()
									one := b.TermAs[Complex]("complex_of_real(&1)")
									b.Show(
										"the carrier contains the product, and 1 times 1 is 1",
										By(
											members,
											group.MulIn.Read(source).AsFact().At(x, y),
											comm_monoid.LeftIdentity.Read(complex_field.MulMonoid).At(one)))
								})))),
					Case(
						"the function vanishes off the carrier",
						Derive(func(b *Argument) {
							b.FixAs[A]("x")
							outside := b.Assume()
							b.Show(
								"the conditional takes its zero branch",
								By(outside))
						}))))
		}),
})}

// CharacterClosure — the product of two characters and the conjugate of a
// character are characters.
var CharacterClosure = characterClosureThm{family.Add(registry.ProofEntry{
	Name: "CharacterClosure",
	Key:  "prop_b819e120b3bd2e3b",
	Reading: "Neither finiteness nor commutativity is asked of G: products and conjugates of " +
		"homomorphisms into the nonzero complex numbers are such homomorphisms, and both stay 0 off " +
		"the carrier. On a finite group the conjugate is the inverse (CharacterConjugateInverse), " +
		"and the characters are a group under the pointwise product with TrivialCharacter as identity.",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀χ ψ:(A → complex).",
		Hypotheses: []string{
			"group_character(G, χ)",
			"group_character(G, ψ)",
		},
		Conclusion: "group_character(G, λx:A. χ(x) * ψ(x)) ∧ group_character(G, λx:A. conj(χ(x)))",
	},
		func(
			a *Argument,
			G *Expr[GroupOps[A]],
			χ, ψ *Arrow[A, Complex],
			χCharacter, ψCharacter Fact,
		) {
			units := a.TermAs[GroupOps[Complex]]("field_units(complex_field_ops)")
			zero := a.TermAs[Real]("&0")
			χLaws := a.Conjuncts(
				a.Unfolded(χCharacter, GroupCharacterDef),
				"χ is a homomorphism into the nonzero complex numbers",
				"χ vanishes off the carrier")
			χHom, χVanishes := χLaws[0], χLaws[1]
			ψHom := a.Have(
				"ψ is a homomorphism into the nonzero complex numbers",
				"group_homomorphism(G, field_units(complex_field_ops), ψ)",
				By(ψCharacter, GroupCharacterDef.At(G, ψ)))
			source := a.Have(
				"the source is a group",
				"group_on(G)",
				By(χHom, group_homomorphism.Source.At(G, units, χ)))
			target := a.Have(
				"the nonzero complex numbers form the target group",
				"group_on(field_units(complex_field_ops))",
				By(χHom, group_homomorphism.Target.At(G, units, χ)))
			a.Do(SplitConj(
				Case(
					"the pointwise product is a character",
					Simp(Fwd(GroupCharacterDef)),
					SplitConj(
						Case(
							"the product is a homomorphism into the nonzero complex numbers",
							group_homomorphism.GroupHomomorphism.Intro(
								Case(
									"the same source group",
									By(source)),
								Case(
									"the same target group",
									By(target)),
								Case(
									"the product takes values in the target carrier",
									Derive(func(b *Argument) {
										x := b.FixAs[A]("x")
										xIn := b.Assume()
										b.Show(
											"the target carrier is closed under multiplication",
											By(
												target,
												xIn,
												χHom,
												ψHom,
												group_homomorphism.MapIn.At(G, units, χ, x),
												group_homomorphism.MapIn.At(G, units, ψ, x),
												group.MulIn.At(units, χ.Apply(x), ψ.Apply(x))))
									})),
								Case(
									"the product preserves multiplication",
									Derive(func(b *Argument) {
										x := b.FixAs[A]("x")
										y := b.FixAs[A]("y")
										members := b.Assume()
										b.Show(
											"χ and ψ each carry the product to the product, and the middle factors commute",
											CalcEq(
												Leg(
													b.TermAs[Complex]("(χ(x) * χ(y)) * (ψ(x) * ψ(y))"),
													"χ and ψ each carry the product to the product",
													By(members, χHom, ψHom, CharacterMul.At(G, χ, x, y), CharacterMul.At(G, ψ, x, y))),
												FinalLeg(
													"the middle factors commute",
													ByArith())))
									})))),
						Case(
							"the product vanishes off the carrier",
							Derive(func(b *Argument) {
								x := b.FixAs[A]("x")
								outside := b.Assume()
								b.Show(
									"the first factor vanishes",
									By(
										Normalized,
										outside,
										χVanishes.At(x),
										comm_ring.MulLeftZero.Read(complex_field.CommRing).At(ψ.Apply(x))))
							})))),
				Case(
					"the pointwise conjugate is a character",
					Simp(Fwd(GroupCharacterDef)),
					SplitConj(
						Case(
							"the conjugate is a homomorphism into the nonzero complex numbers",
							group_homomorphism.GroupHomomorphism.Intro(
								Case(
									"the same source group",
									By(source)),
								Case(
									"the same target group",
									By(target)),
								Case(
									"the conjugate takes values in the target carrier",
									Derive(func(b *Argument) {
										x := b.FixAs[A]("x")
										xIn := b.Assume()
										b.Show(
											"conjugation is an involution fixing zero, so it preserves nonzero values",
											BySets(
												xIn,
												χHom,
												group_homomorphism.MapIn.At(G, units, χ, x),
												complex_field.ConjOfReal.At(zero),
												complex_field.ConjConj.At(χ.Apply(x))))
									})),
								Case(
									"the conjugate preserves multiplication",
									Derive(func(b *Argument) {
										x := b.FixAs[A]("x")
										y := b.FixAs[A]("y")
										members := b.Assume()
										b.Show(
											"χ carries the product to the product, and conjugation distributes over it",
											By(
												Normalized,
												members,
												χHom,
												CharacterMul.At(G, χ, x, y),
												complex_field.ConjMul.At(χ.Apply(x), χ.Apply(y))))
									})))),
						Case(
							"the conjugate vanishes off the carrier",
							Derive(func(b *Argument) {
								x := b.FixAs[A]("x")
								outside := b.Assume()
								b.Show(
									"conjugation fixes the zero value",
									By(Normalized, outside, χVanishes.At(x), complex_field.ConjOfReal.At(zero)))
							}))))))
		}),
})}

// CharactersFinite — a finite group has finitely many characters: on the
// carrier a character takes values among the n-th roots of unity, of which
// a field has finitely many (finite_field.RootsOfUnityBound), and off it the
// value 0, and only finitely many functions do both.
var CharactersFinite = charactersFiniteThm{family.Add(registry.ProofEntry{
	Name:    "CharactersFinite",
	Key:     "prop_24313f02d8bd3c3b",
	Reading: "A record that fails the group laws has no characters.",
	Build: family.Theorem(Statement{
		Binders:    "∀G:group_ops(A).",
		Hypotheses: []string{"finite(G.carrier)"},
		Conclusion: "finite({χ:(A → complex) | group_character(G, χ)})",
	},
		func(a *Argument, G *Expr[GroupOps[A]], finiteCarrier Fact) {
			carrier := a.TermAs[Set[A]]("G.carrier")
			n, exponent := a.LetAs[Nat]("n", "COND(card(G.carrier) = 0, 1, card(G.carrier))")
			positive := a.Have(
				"choose exponent 1 for an empty carrier, so the exponent is positive",
				"0 < n",
				Simp(Fwd(exponent)),
				CondRewrite(),
				ByArith())
			Z, roots := a.LetAs[Set[Complex]]("Z", "{z:complex | z ^ n = &1}")
			finiteRoots := a.Have(
				"a field has at most n nth roots of unity, so they are finitely many",
				"finite(Z)",
				By(
					positive,
					roots,
					complex_field.ComplexFieldOpsDef,
					set_basic.InUniv,
					finite_field.RootsOfUnityBound.Read(complex_field.FieldOn).At(n)))
			zero := a.TermAs[Complex]("complex_of_real(&0)")
			S, functionSpace := a.LetAs[Set[Fun[A, Complex]]](
				"S",
				"{ψ:(A → complex) | "+
					"    (∀x:A. x ∈ G.carrier ⇒ ψ(x) ∈ Z) ∧ (∀x:A. x ∉ G.carrier ⇒ ψ(x) = complex_of_real(&0))}")
			finiteSpace := a.Have(
				"only finitely many functions take values in Z on the carrier and equal zero elsewhere",
				"finite(S)",
				By(finiteCarrier, finiteRoots, functionSpace, cardinality.FiniteFunspace.At(carrier, Z, zero)))
			conditions := a.Have(
				"every character satisfies the two conditions of the finite function space",
				Statement{
					Binders:    "∀ψ:(A → complex).",
					Hypotheses: []string{"group_character(G, ψ)"},
					Conclusion: "(∀x:A. x ∈ G.carrier ⇒ ψ(x) ∈ Z) ∧ (∀x:A. x ∉ G.carrier ⇒ ψ(x) = complex_of_real(&0))",
				},
				Derive(func(b *Argument) {
					ψ := b.FixAs[Fun[A, Complex]]("ψ")
					character := b.Assume()
					b.Do(SplitConj(
						Case(
							"on the carrier, a character value is an nth root of unity",
							Derive(func(c *Argument) {
								x := c.FixAs[A]("x")
								xIn := c.Assume()
								groupSize := c.Have(
									"the carrier contains x, so n is the group size",
									"n = card(G.carrier)",
									By(
										Normalized,
										finiteCarrier,
										xIn,
										exponent,
										cardinality.CardEqZero.At(carrier),
										set_basic.NotInEmpty.At(x)))
								unitPower := c.Have(
									"the character value raised to n is 1",
									"ψ(x) ^ n = complex_of_real(&1)",
									By(
										Normalized,
										groupSize,
										finiteCarrier,
										xIn,
										character,
										GroupCharacterDef.At(G, ψ),
										CharacterUnitModulus.At(G, ψ, x)))
								c.Show(
									"so the value lies in Z",
									BySets(roots, unitPower))
							})),
						Case(
							"off the carrier, the character is zero by definition",
							By(character, GroupCharacterDef.At(G, ψ)))))
				}))
			contained := a.Have(
				"all characters lie in the finite function space",
				"{ψ:(A → complex) | group_character(G, ψ)} ⊆ S",
				BySets(functionSpace, conditions))
			characters := a.TermAs[Set[Fun[A, Complex]]]("{ψ:(A → complex) | group_character(G, ψ)}")
			a.Show(
				"the set of characters is finite as a subset of S",
				By(finiteSpace, contained, finite_set.FiniteSubset.At(characters, S)))
		}),
})}

// CyclicCharacter — in a finite group, the subgroup generated by an
// element other than the identity has a character that is not 1 at that
// element: with m > 1 the order of x, x^k ↦ e^{2πik/m} is a character of
// ⟨x⟩, its value at x a root of unity other than 1.
var CyclicCharacter = cyclicCharacterThm{family.Add(registry.ProofEntry{
	Name:    "CyclicCharacter",
	Key:     "prop_3ec1689ec7453bcb",
	Reading: "restrict_group(G, K) is G's operations on the carrier K, the group a subgroup is.",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀x:A.",
		Hypotheses: []string{
			"group_on(G)",
			"finite(G.carrier)",
			"x ∈ G.carrier",
			"x ≠ G.one",
		},
		Conclusion: "∃χ:(A → complex). " +
			"    group_character(restrict_group(G, cyclic_subgroup(G, x)), χ) ∧ χ(x) ≠ &1",
	},
		func(
			a *Argument,
			G *Expr[GroupOps[A]],
			x *Expr[A],
			grp group.GroupFact[on.G],
			finite, xIn, distinct Fact,
		) {
			m, orderDef := a.LetAs[Nat]("m", "group_element_order(G, x)")
			P, powerMap := a.LetAs[Fun[Nat, A]]("P", "λk:num. monoid_pow(G.mul, G.one, x, k)")
			firstPower := a.Have(
				"the first power is the generator itself",
				"P(1) = x",
				By(Normalized, powerMap, xIn, group.PowOne.Read(grp).AsFact().At(x)))
			positive := a.Have(
				"the generator has positive order in the finite group",
				"0 < m",
				By(Normalized, xIn, finite, orderDef, cyclic_group.FiniteOrderPositive.Read(grp).AsFact().At(x)))
			larger := a.Have(
				"the generator has order greater than 1",
				"1 < m",
				Derive(func(b *Argument) {
					notOne := b.Have(
						"order 1 would make the generator equal to the identity",
						"m ≠ 1",
						By(Normalized, distinct, firstPower, orderDef, powerMap, cyclic_group.PowOrderIsOne.At(G, x)))
					b.Show(
						"a positive natural number different from 1 exceeds 1",
						ByArith(notOne, positive))
				}))
			θ, angle := a.LetAs[Real]("θ", "(&2 * π) / &m")
			bounds := a.Have(
				"the divided angle is positive and at most π",
				"&0 < θ ∧ θ ≤ π",
				ByArith(larger, angle, real_trigonometry.PiBounds))
			fullTurn := a.Have(
				"multiplying the angle by m restores a full turn",
				"&m * θ = &2 * π",
				ByArith(positive, angle))
			w, polar := a.LetAs[Complex]("w", "complex(cos(θ), sin(θ))")
			realZero := a.TermAs[Real]("&0")
			realOne := a.TermAs[Real]("&1")
			cosine := a.TermAs[Real]("cos(θ)")
			sine := a.TermAs[Real]("sin(θ)")
			wPeriod := a.Have(
				"the mth power of w is 1",
				"w ^ m = complex_of_real(&1)",
				Derive(func(b *Argument) {
					endpoint := b.Have(
						"cosine and sine return to their values at zero after a full turn",
						"cos(&2 * π) = &1 ∧ sin(&2 * π) = &0",
						ByArith(
							real_trigonometry.CosPeriodic.At(realZero),
							real_trigonometry.SinPeriodic.At(realZero),
							real_trigonometry.CosZero,
							real_trigonometry.SinZero))
					b.Show(
						"De Moivre's formula multiplies the angle by m",
						By(
							Normalized,
							polar,
							fullTurn,
							endpoint,
							complex_polynomial.DeMoivre.At(m, θ),
							complex_field.ComplexOfRealDef.At(realOne)))
				}))
			wNotOne := a.Have(
				"the chosen root differs from 1",
				"w ≠ complex_of_real(&1)",
				Derive(func(b *Argument) {
					equal := b.SupposeNot()
					parts := b.Have(
						"equality to 1 would make cosine 1 and sine 0",
						"cos(θ) = &1 ∧ sin(θ) = &0",
						By(
							Normalized,
							equal,
							polar,
							complex_field.ComplexOfRealDef.At(realOne),
							At(complex_field.ComplexData.Inj, cosine, sine, realOne, realZero)))
					atPi := b.Have(
						"sine is positive in the interior of this angle interval, so θ would equal π",
						"θ = π",
						ByArith(parts, bounds, real_trigonometry.SinPositivePi.At(θ)))
					b.Show(
						"cosine at π is −1",
						ByArith(parts, atPi, real_trigonometry.CosPi))
				}))
			wNonzero := a.Have(
				"the unit-circle point is nonzero",
				"w ≠ complex_of_real(&0)",
				Derive(func(b *Argument) {
					equal := b.SupposeNot()
					parts := b.Have(
						"zero would make both coordinates vanish",
						"cos(θ) = &0 ∧ sin(θ) = &0",
						By(
							Normalized,
							equal,
							polar,
							complex_field.ComplexOfRealDef.At(realZero),
							At(complex_field.ComplexData.Inj, cosine, sine, realZero, realZero)))
					b.Show(
						"the sum of their squares is 1",
						ByArith(parts, real_trigonometry.SinSquareAddCosSquare.At(θ)))
				}))
			K, subgroup := a.LetAs[Set[A]]("K", "cyclic_subgroup(G, x)")
			B, short := a.LetAs[Set[Nat]]("B", "{k:num | k < m}")
			_, representative := a.LetAs[Fun[A, Nat]]("r", "inverse_on(B, P)")
			χ, definition := a.LetAs[Fun[A, Complex]]("χ", "λy:A. COND(y ∈ K, w ^ r(y), complex_of_real(&0))")
			image := a.Have(
				"the subgroup consists of powers with exponent below m",
				"K = image(P, B)",
				By(
					xIn,
					positive,
					orderDef,
					subgroup,
					powerMap,
					short,
					cyclic_group.CyclicSubgroupPowersBelowOrder.Read(grp).AsFact().At(x)))
			injective := a.Have(
				"the powers with exponent below m are distinct",
				"injective_on(B, P)",
				By(xIn, orderDef, powerMap, short, cyclic_group.PowersBelowOrderInjective.Read(grp).AsFact().At(x)))
			represented := a.Have(
				"the inverse map recovers an exponent representing each subgroup element",
				"∀y:A. y ∈ K ⇒ P(r(y)) = y",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					inK := b.Assume()
					b.Show(
						"P applied to the chosen exponent returns the element",
						By(Normalized, inK, image, representative, functions.InverseOnRight.At(B, P, y)))
				}))
			shortValues := a.Have(
				"the character sends short powers of x to the corresponding powers of w",
				"∀k:num. k ∈ B ⇒ χ(P(k)) = w ^ k",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					inB := b.Assume()
					inK := b.Have(
						"the power with exponent k is in the subgroup",
						"P(k) ∈ K",
						By(Normalized, inB, image, set_image.FunInImage.At(P, B, k)))
					exponent := b.Have(
						"the inverse reads k from its power",
						"r(P(k)) = k",
						By(Normalized, inB, injective, representative, functions.InverseOnLeft.At(B, P, k)))
					b.Show(
						"the character therefore takes the value w to the power k",
						By(inK, exponent, definition))
				}))
			multiplication := complex_field.MulMonoid
			allValues := a.Have(
				"all powers reduce to their short representatives under both bases",
				"∀k:num. χ(P(k)) = w ^ k",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					quotient := b.TermAs[Nat]("div(k, m)")
					remainder := b.TermAs[Nat]("rem(k, m)")
					multiple := b.TermAs[Nat]("m * div(k, m)")
					division := b.Have(
						"division writes k as a multiple of m plus a short remainder",
						"k = m * div(k, m) + rem(k, m) ∧ rem(k, m) < m",
						ByArith(positive, nat_div_mod.Division.At(k, m)))
					inB := b.Have(
						"the remainder belongs to the set of short exponents",
						"rem(k, m) ∈ B",
						BySets(division, short))
					sourcePower := b.Have(
						"the original power equals the power at the remainder",
						"P(k) = P(rem(k, m))",
						By(Normalized, xIn, orderDef, powerMap, cyclic_group.PowRemOrder.Read(grp).AsFact().At(x, k)))
					unitMultiple := b.Have(
						"each multiple of m gives the unit power of w",
						"w ^ (m * div(k, m)) = complex_of_real(&1)",
						By(
							wPeriod,
							comm_monoid.PowPow.Read(multiplication).At(w, m, quotient),
							comm_monoid.IdentityPow.Read(multiplication).At(quotient)))
					targetPower := b.Have(
						"the power of w likewise equals its power at the remainder",
						"w ^ k = w ^ rem(k, m)",
						By(
							division,
							unitMultiple,
							comm_monoid.PowAdd.Read(multiplication).At(w, multiple, remainder),
							comm_monoid.LeftIdentity.Read(multiplication).At(b.TermAs[Complex]("w ^ rem(k, m)"))))
					b.Show(
						"the character's short-power formula now applies to any power",
						By(inB, sourcePower, targetPower, shortValues.At(remainder)))
				}))
			source := a.Have(
				"the cyclic subgroup carries the restricted group law",
				"group_on(restrict_group(G, K))",
				By(
					Normalized,
					xIn,
					subgroup,
					cyclic_group.CyclicSubgroupSubgroup.Read(grp).AsFact().At(x),
					group.SubgroupGroupOn.Read(grp).At(K)))
			F := a.TermAs[field.FieldOps[Complex]]("complex_field_ops")
			units := a.TermAs[GroupOps[Complex]]("field_units(complex_field_ops)")
			target := a.Have(
				"the units of ℂ's field, the nonzero complex numbers, form a group",
				"group_on(field_units(complex_field_ops))",
				By(
					complex_field.FieldOn,
					abelian_group.GroupOn.At(units),
					roots_of_unity.FieldUnitsAbelianGroupOn.At(F)))
			values := a.Have(
				"on the subgroup the conditional selects the power of w",
				"∀y:A. y ∈ K ⇒ χ(y) = w ^ r(y)",
				Derive(func(b *Argument) {
					b.FixAs[A]("y")
					inK := b.Assume()
					b.Show(
						"the subgroup condition selects the first branch",
						By(inK, definition))
				}))
			a.Take(χ)
			a.Do(SplitConj(
				Case(
					"χ is a character on the cyclic subgroup",
					Simp(Fwd(GroupCharacterDef)),
					SplitConj(
						Case(
							"χ is a homomorphism to the nonzero complex numbers",
							group_homomorphism.GroupHomomorphism.Intro(
								Case(
									"the source is the restricted group",
									By(source)),
								Case(
									"the target is the group of nonzero complex numbers",
									By(target)),
								Case(
									"each value on the subgroup is nonzero",
									Derive(func(b *Argument) {
										y := b.FixAs[A]("y")
										inK := b.Assume()
										b.Show(
											"a power of the nonzero point w is nonzero",
											BySets(
												inK,
												wNonzero,
												values.At(y),
												field.PowEqZero.Read(complex_field.Field).At(w, b.TermAs[Nat]("r(y)"))))
									})),
								Case(
									"χ preserves the product",
									Derive(func(b *Argument) {
										y := b.FixAs[A]("y")
										z := b.FixAs[A]("z")
										both := b.Assume()
										j := b.TermAs[Nat]("r(y)")
										k := b.TermAs[Nat]("r(z)")
										product := b.Have(
											"the product of subgroup elements adds the exponents of their representatives",
											"P(r(y) + r(z)) = G.mul(y, z)",
											By(
												Normalized,
												both,
												xIn,
												represented.At(y),
												represented.At(z),
												powerMap,
												group.PowAdd.Read(grp).AsFact().At(x, j, k)))
										b.Show(
											"the same addition of exponents multiplies the powers of w",
											By(
												both,
												product,
												allValues.At(b.TermAs[Nat]("r(y) + r(z)")),
												values.At(y),
												values.At(z),
												comm_monoid.PowAdd.Read(multiplication).At(w, j, k)))
									})))),
						Case(
							"the values off the subgroup are zero",
							Derive(func(b *Argument) {
								b.FixAs[A]("y")
								outside := b.Assume()
								b.Show(
									"the conditional selects zero there",
									By(outside, definition))
							})))),
				Case(
					"the value at the generator is w, which differs from 1",
					By(
						Normalized,
						firstPower,
						wNotOne,
						allValues.At(a.TermAs[Nat]("1")),
						comm_monoid.PowOne.Read(multiplication).At(w)))))
		}),
})}

// CharacterExtendsOneStep — a character χ of a subgroup K of a finite
// abelian group extends to a subgroup that contains K and a given element
// x, taking at x any value w whose d-th power is χ(x^d), where x^j lies in
// K exactly when d divides j: u·xⁱ ↦ χ(u)·wⁱ on K·⟨x⟩ does not depend on
// how an element is written so, and is a character extending χ.
var CharacterExtendsOneStep = characterExtendsOneStepThm{family.Add(registry.ProofEntry{
	Name: "CharacterExtendsOneStep",
	Key:  "prop_5bd8a0e50f19f7b",
	Reading: "Commutativity is used to make the products k·xʲ a subgroup and χ′ multiplicative on " +
		"them. The condition on w is the one χ′ cannot avoid: xᵈ lies in K, so χ′(x)ᵈ must be χ(xᵈ).",
	Build: family.Sections(Statement{
		Binders: "∀G:group_ops(A). ∀K:set(A). ∀χ:(A → complex). ∀x:A. ∀d:num. ∀w:complex.",
		Hypotheses: []string{
			"abelian_group_on(G)",
			"finite(G.carrier)",
			"subgroup(G, K)",
			"group_character(restrict_group(G, K), χ)",
			"x ∈ G.carrier",
			"∀j:num. monoid_pow(G.mul, G.one, x, j) ∈ K ⇔ d ∣ j",
			"w ^ d = χ(monoid_pow(G.mul, G.one, x, d))",
		},
		Conclusion: "∃K':set(A). ∃χ':(A → complex). " +
			"    subgroup(G, K') ∧ " +
			"    K ⊆ K' ∧ " +
			"    x ∈ K' ∧ " +
			"    group_character(restrict_group(G, K'), χ') ∧ " +
			"    (∀y:A. y ∈ K ⇒ χ'(y) = χ(y)) ∧ " +
			"    χ'(x) = w",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			adjoin := ctx.Lemma(Statement{
				Binders: "∀G:group_ops(A). ∀K:set(A). ∀x:A.",
				Hypotheses: []string{
					"abelian_group_on(G)",
					"finite(G.carrier)",
					"subgroup(G, K)",
					"x ∈ G.carrier",
				},
				Conclusion: "subgroup(G, «L») ∧ " +
					"K ⊆ «L» ∧ " +
					"x ∈ «L» ∧ " +
					"(∀y:A. y ∈ «L» ⇒ ∃u:A. ∃i:num. u ∈ K ∧ y = u * monoid_pow(G.mul, G.one, x, i)) ∧ " +
					"(∀u:A. ∀i:num. u ∈ K ⇒ u * monoid_pow(G.mul, G.one, x, i) ∈ «L»)",
				Abbrev: Abbrev{{Name: "L", Text: "set_mul(G.mul, K, cyclic_subgroup(G, x))"}},
			}, func(
				a *Argument, G *Expr[GroupOps[A]], K *Expr[Set[A]], x *Expr[A],
				abelian abelian_group.AbelianGroupFact[on.G], finite, subgroup, xIn Fact,
			) {
				grp := abelian_group.GroupOn.Read(abelian)
				one := a.TermAs[A]("G.one")
				_, powers := a.LetAs[Fun[Nat, A]]("P", "λj:num. monoid_pow(G.mul, G.one, x, j)")
				identityIn := a.Have(
					"the subgroup contains the identity",
					"G.one ∈ K",
					By(subgroup, group.SubgroupOne.At(G, K)))
				subset := a.Have(
					"K lies in the carrier of G",
					"K ⊆ G.carrier",
					By(subgroup, group.SubgroupSubset.At(G, K)))
				C, cyclic := a.LetAs[Set[A]]("C", "cyclic_subgroup(G, x)")
				_, products := a.LetAs[Set[A]]("L", "set_mul(G.mul, K, C)")
				cyclicSubgroup := a.Have(
					"the powers generate a subgroup",
					"subgroup(G, C)",
					By(Normalized, xIn, cyclic, cyclic_group.CyclicSubgroupSubgroup.Read(grp).AsFact().At(x)))
				cyclicSubset := a.Have(
					"C lies in the carrier of G",
					"C ⊆ G.carrier",
					By(cyclicSubgroup, group.SubgroupSubset.At(G, C)))
				conjugates := a.Have(
					"K normalizes C, the premise under which K·C is a subgroup: "+
						"conjugation by an element of K fixes each element of C",
					"∀u v:A. u ∈ K ∧ v ∈ C ⇒ u * v * G.inv(u) ∈ C",
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						v := b.FixAs[A]("v")
						both := b.Conjuncts(
							b.Assume(),
							"u lies in K",
							"v lies in C")
						fixed := b.Have(
							"commute u past v and cancel u against its inverse",
							"u * v * G.inv(u) = v",
							By(
								Normalized,
								both[0],
								both[1],
								subset,
								cyclicSubset,
								abelian_group.CommOn.Read(abelian).AsFact().At(u, v),
								group.MulInvCancelRightOn.Read(grp).AsFact().At(u, v),
								set_basic.SubsetDef))
						b.Show(
							"the conjugate is in C",
							By(Normalized, both[1], fixed))
					}))
				lSubgroup := a.Have(
					"the product of these subgroups is a subgroup",
					"subgroup(G, L)",
					By(
						Normalized,
						subgroup,
						cyclicSubgroup,
						conjugates,
						products,
						group_isomorphism.SetMulSubgroup.Read(grp).AsFact().At(K, C)))
				powersInC := a.Have(
					"every power of x lies in C",
					"∀i:num. P(i) ∈ C",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("i")
						b.Show(
							"each power is in the defining set",
							BySets(cyclic, powers, cyclic_group.CyclicSubgroupDef.At(G, x)))
					}))
				positiveElementOrder := a.Have(
					"x has positive order in the finite group",
					"0 < group_element_order(G, x)",
					By(finite, xIn, cyclic_group.FiniteOrderPositive.Read(grp).AsFact().At(x)))
				cyclicImage := a.Have(
					"C is the image of the powers below the order of x",
					"C = image(P, {i:num | i < group_element_order(G, x)})",
					By(
						xIn,
						positiveElementOrder,
						powers,
						cyclic,
						cyclic_group.CyclicSubgroupPowersBelowOrder.Read(grp).AsFact().At(x)))
				isPower := a.Have(
					"each element of C is a power",
					"∀v:A. v ∈ C ⇒ ∃i:num. v = P(i)",
					Derive(func(b *Argument) {
						b.FixAs[A]("v")
						inC := b.Assume()
						b.Show(
							"take a preimage in the power map",
							BySets(inC, cyclicImage))
					}))
				decomposition := a.Have(
					"every element of L factors as a member of K and a power of x",
					"∀y:A. y ∈ L ⇒ ∃u:A. ∃i:num. u ∈ K ∧ y = u * P(i)",
					Derive(func(b *Argument) {
						b.FixAs[A]("y")
						inL := b.Assume()
						u, v, factors := b.Obtain2As[A, A](
							"factor the element across K and C",
							"∃u v:A. u ∈ K ∧ v ∈ C ∧ y = u * v",
							By(inL, products, quotient_group.InSetMul))
						parts := b.Conjuncts(
							factors,
							"first factor in K",
							"second factor in C",
							"product equals y")
						i, power := b.ObtainAs[Nat](
							"write the second factor as a power",
							"∃i:num. v = P(i)",
							By(parts[1], isPower.At(v)))
						b.Take(u)
						b.Take(i)
						b.Show(
							"combine the two factors",
							By(Normalized, parts[0], power, parts[2]))
					}))
				productIn := a.Have(
					"all such products lie in L",
					"∀u:A. ∀i:num. u ∈ K ⇒ u * P(i) ∈ L",
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						i := b.FixAs[Nat]("i")
						inK := b.Assume()
						factors := b.Have(
							"the factors lie in K and C",
							"∃k v:A. k ∈ K ∧ v ∈ C ∧ u * P(i) = k * v",
							Witness(u),
							Witness(b.TermAs[A]("P(i)")),
							By(inK, powersInC.At(i)))
						b.Show(
							"apply membership in the set product",
							By(
								products,
								factors,
								quotient_group.InSetMul.At(
									b.TermAs[Op[A]]("G.mul"), K, C, b.TermAs[A]("u * P(i)"))))
					}))
				powerOne := a.Have(
					"the first power is x",
					"P(1) = x",
					By(Normalized, powers, xIn, group.PowOne.Read(grp).AsFact().At(x)))
				included := a.Have(
					"K lies in L, C containing the identity",
					"K ⊆ L",
					By(
						Normalized,
						subgroup,
						cyclicSubgroup,
						products,
						group_isomorphism.SubsetSetMulLeft.Read(grp).AsFact().At(K, C)))
				contains := a.Have(
					"L contains x using the first power",
					"x ∈ L",
					By(
						Normalized,
						identityIn,
						powerOne,
						xIn,
						productIn.At(one, a.TermAs[Nat]("1")),
						group.LeftIdentityOn.Read(grp).AsFact().At(x)))
				a.Show(
					"L is a subgroup containing K and x, and its elements are the products u·P(i)",
					By(powers, lSubgroup, included, contains, decomposition, productIn))
			})
			return ctx.Theorem(headline, func(
				a *Argument, G *Expr[GroupOps[A]], K *Expr[Set[A]], χ *Arrow[A, Complex], x *Expr[A],
				d *Expr[Nat], w *Expr[Complex],
				abelian abelian_group.AbelianGroupFact[on.G], finite, subgroup, character, xIn, period, root Fact,
			) {
				grp := abelian_group.GroupOn.Read(abelian)
				R := a.TermAs[GroupOps[A]]("restrict_group(G, K)")
				units := a.TermAs[GroupOps[Complex]]("field_units(complex_field_ops)")
				zero := a.TermAs[Nat]("0")
				n := a.TermAs[Nat]("card(G.carrier)")
				multiplication := complex_field.MulMonoid
				_, powers := a.LetAs[Fun[Nat, A]]("P", "λj:num. monoid_pow(G.mul, G.one, x, j)")
				identityIn := a.Have(
					"the subgroup contains the identity",
					"G.one ∈ K",
					By(subgroup, group.SubgroupOne.At(G, K)))
				orderPower := a.Have(
					"the group order gives the identity power",
					"P(card(G.carrier)) = G.one",
					By(Normalized, finite, xIn, powers, cyclic_group.PowCardIsOne.Read(grp).AsFact().At(x)))
				dividesOrder := a.Have(
					"the period divides the group order",
					"d ∣ card(G.carrier)",
					By(Normalized, identityIn, orderPower, powers, period.At(n)))
				positiveOrder := a.Have(
					"the finite group has positive order",
					"0 < card(G.carrier)",
					By(finite_group.CarrierCardPositive.Read(grp), finite))
				positive := a.Have(
					"the period is positive",
					"0 < d",
					ByArith(positiveOrder, dividesOrder, nat_divides.ZeroDivides.At(n)))
				pd := a.TermAs[A]("P(d)")
				periodIn := a.Have(
					"the period power lies in K",
					"P(d) ∈ K",
					By(powers, period.At(d), nat_divides.DividesRefl.At(d)))
				subset := a.Have(
					"K lies in the carrier of G",
					"K ⊆ G.carrier",
					By(subgroup, group.SubgroupSubset.At(G, K)))
				hom := a.Have(
					"χ maps the restricted group into the nonzero complex numbers",
					"group_homomorphism(restrict_group(G, K), field_units(complex_field_ops), χ)",
					By(character, GroupCharacterDef.At(R, χ)))

				generated := a.Conjuncts(
					GroupPremises(abelian, finite, subgroup, xIn, At(adjoin, G, K, x)),
					"K·⟨x⟩ is a subgroup of G",
					"K·⟨x⟩ contains K",
					"K·⟨x⟩ contains x",
					"every element of K·⟨x⟩ is a product u·xⁱ with u ∈ K",
					"every such product lies in K·⟨x⟩")
				lSubgroup, included, contains := generated[0], generated[1], generated[2]
				decomposition, productIn := generated[3], generated[4]
				L, _ := a.LetAs[Set[A]]("L", "set_mul(G.mul, K, cyclic_subgroup(G, x))")
				powersInG := a.Have(
					"every power of x lies in G",
					"∀i:num. P(i) ∈ G.carrier",
					Derive(func(b *Argument) {
						i := b.FixAs[Nat]("i")
						b.Show(
							"use closure of the group under powers",
							By(Normalized, xIn, powers, group.PowIn.Read(grp).AsFact().At(x, i)))
					}))
				powerZero := a.Have(
					"the zeroth power is the identity",
					"P(0) = G.one",
					By(powers, comm_monoid.MonoidPowDef))

				knownPowers := a.Have(
					"χ(P(j)) = wʲ whenever P(j) lies in K",
					"∀j:num. P(j) ∈ K ⇒ χ(P(j)) = w ^ j",
					Derive(func(b *Argument) {
						j := b.FixAs[Nat]("j")
						inK := b.Assume()
						m, multiple := b.ObtainAs[Nat](
							"the exponent is a multiple of the period",
							"∃m:num. j = d * m",
							By(inK, powers, period.At(j), nat_divides.DividesFactor.At(d, j)))
						raised := b.Have(
							"raise the period power to the cofactor in the restricted group",
							"P(j) = monoid_pow(restrict_group(G, K).mul, restrict_group(G, K).one, P(d), m)",
							By(
								Normalized,
								multiple,
								xIn,
								powers,
								group.PowPow.Read(grp).AsFact().At(x, d, m),
								group.RestrictGroupDef))
						value := b.Have(
							"χ carries the power to the same power of the known value",
							"χ(P(j)) = χ(P(d)) ^ m",
							By(
								raised,
								hom,
								periodIn,
								group_homomorphism.MapPow.At(R, units, χ, pd, m),
								group.RestrictGroupDef,
								roots_of_unity.FieldUnitsDef))
						b.Show(
							"the root raised to d then m gives the required power",
							By(
								multiple,
								powers,
								root,
								value,
								comm_monoid.PowPow.Read(multiplication).At(w, d, m),
								complex_field.CommRingOn))
					}))
				χNonzero := a.Have(
					"χ is nonzero on K",
					"∀u:A. u ∈ K ⇒ χ(u) ≠ complex_of_real(&0)",
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						inK := b.Assume()
						inUnits := b.Have(
							"the homomorphism maps u to a nonzero complex number",
							"χ(u) ∈ 𝕌 ∖ {complex_of_real(&0)}",
							By(inK, hom, group_homomorphism.MapIn.At(R, units, χ, u), group.RestrictGroupDef))
						b.Show(
							"so χ(u) is not 0",
							BySets(inUnits))
					}))
				wNonzero := a.Have(
					"w is not 0: |w| ^ d is |χ(x^d)|, which is not 0, while 0 ^ d is 0 for the positive d",
					"w ≠ complex_of_real(&0)",
					ByArith(
						positive,
						powers,
						root,
						periodIn,
						χNonzero.At(pd),
						complex_abs.AbsPow.At(w, d),
						complex_abs.AbsEqZero.At(w),
						complex_abs.AbsEqZero.At(χ.Apply(pd)),
						real_pow.ZeroPow.At(d)))
				wPowersNonzero := a.Have(
					"all powers of w are nonzero",
					"∀j:num. w ^ j ≠ complex_of_real(&0)",
					Derive(func(b *Argument) {
						j := b.FixAs[Nat]("j")
						b.Show(
							"only zero can have a zero power",
							By(wNonzero, field.PowEqZero.Read(complex_field.Field).At(w, j)))
					}))
				ordered := a.Have(
					"equal decompositions with ordered exponents assign equal values",
					"∀u v:A. ∀i j:num. u ∈ K ∧ v ∈ K ∧ i ≤ j ∧ u * P(i) = v * P(j) ⇒ χ(u) * w ^ i = χ(v) * w ^ j",
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						v := b.FixAs[A]("v")
						i := b.FixAs[Nat]("i")
						b.FixAs[Nat]("j")
						parts := b.Conjuncts(
							b.Assume(),
							"u is in K",
							"v is in K",
							"the exponents are ordered",
							"the group products agree")
						ui, vi, le, same := parts[0], parts[1], parts[2], parts[3]
						r, difference := b.LetAs[Nat]("r", "j - i")
						pi, pr := b.TermAs[A]("P(i)"), b.TermAs[A]("P(r)")
						index := b.Have(
							"add the difference to the smaller exponent",
							"j = r + i",
							ByArith(le, difference))
						power := b.Have(
							"split the larger power",
							"P(j) = P(r) * P(i)",
							By(Normalized, index, xIn, powers, group.PowAdd.Read(grp).AsFact().At(x, r, i)))
						uIn := b.Have(
							"u lies in G",
							"u ∈ G.carrier",
							BySets(ui, subset))
						vIn := b.Have(
							"v lies in G",
							"v ∈ G.carrier",
							BySets(vi, subset))
						vpr := b.TermAs[A]("v * P(r)")
						vprIn := b.Have(
							"v times the difference power lies in G",
							"v * P(r) ∈ G.carrier",
							By(vIn, powersInG.At(r), group.MulIn.Read(grp).AsFact().At(v, pr)))
						common := b.Have(
							"the equal products have a common right factor",
							"u * P(i) = v * P(r) * P(i)",
							By(
								same,
								power,
								vIn,
								powersInG.At(r),
								powersInG.At(i),
								group.AssocOn.Read(grp).AsFact().At(v, pr, pi)))
						cancel := b.Have(
							"cancel the smaller power",
							"u = v * P(r)",
							By(common, uIn, vprIn, powersInG.At(i), group.RightCancelOn.Read(grp).AsFact().At(pi, u, vpr)))
						inv := b.TermAs[A]("G.inv(v)")
						inverseEq := b.Have(
							"isolate the difference power",
							"G.inv(v) * u = P(r)",
							By(Normalized, cancel, vIn, powersInG.At(r), group.InvMulCancelLeftOn.Read(grp).AsFact().At(v, pr)))
						inverseIn := b.Have(
							"K contains the inverse of v",
							"G.inv(v) ∈ K",
							By(subgroup, vi, group.SubgroupInv.At(G, K, v)))
						differenceIn := b.Have(
							"the difference power is a product of two members of K",
							"P(r) ∈ K",
							By(Normalized, subgroup, ui, inverseIn, inverseEq, group.SubgroupMul.At(G, K, inv, u)))
						value := b.Have(
							"apply χ to the equality after cancellation",
							"χ(u) = χ(v) * χ(P(r))",
							By(cancel, hom, vi, differenceIn, CharacterMul.At(R, χ, v, pr), group.RestrictGroupDef))
						valueAtDifference := b.Have(
							"χ at the difference power is the corresponding power of w",
							"χ(P(r)) = w ^ r",
							By(differenceIn, knownPowers.At(r)))
						powerOfW := b.Have(
							"w to j factors in the same way",
							"w ^ j = w ^ r * w ^ i",
							By(index, comm_monoid.PowAdd.Read(multiplication).At(w, r, i), complex_field.CommRingOn))
						b.Show(
							"the assigned values agree by associativity",
							Simp(Fwd(value), Fwd(valueAtDifference), Fwd(powerOfW)),
							ByArith())
					}))
				unique := a.Have(
					"the assigned value is independent of the decomposition",
					"∀u v:A. ∀i j:num. u ∈ K ∧ v ∈ K ∧ u * P(i) = v * P(j) ⇒ χ(u) * w ^ i = χ(v) * w ^ j",
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						v := b.FixAs[A]("v")
						i := b.FixAs[Nat]("i")
						j := b.FixAs[Nat]("j")
						both := b.Conjuncts(
							b.Assume(),
							"u lies in K",
							"v lies in K",
							"the products agree")
						b.Show(
							"one of the two orders on i and j applies",
							By(
								both[0],
								both[1],
								both[2],
								ordered.At(u, v, i, j),
								ordered.At(v, u, j, i),
								nat_order.LessEqTotal.At(i, j)))
					}))

				V, represents := a.LetAs[Fun[A, Fun[Complex, Bool]]]("V",
					"λy:A. λz:complex. ∃u:A. ∃i:num. u ∈ K ∧ y = u * P(i) ∧ z = χ(u) * w ^ i")
				total := a.Have(
					"a decomposition supplies a value for every element of L",
					"∀y:A. y ∈ L ⇒ ∃z:complex. V(y, z)",
					Derive(func(b *Argument) {
						y := b.FixAs[A]("y")
						inL := b.Assume()
						u, i, factors := b.Obtain2As[A, Nat](
							"choose a decomposition",
							"∃u:A. ∃i:num. u ∈ K ∧ y = u * P(i)",
							By(inL, powers, decomposition.At(y)))
						parts := b.Conjuncts(
							factors,
							"the first factor lies in K",
							"the product represents y")
						b.Take(b.TermAs[Complex]("χ(u) * w ^ i"))
						b.Show(
							"this value is represented by the same factors",
							Simp(Fwd(represents)),
							Witness(u),
							Witness(i),
							By(parts[0], parts[1]))
					}))
				_, chosen := a.ObtainAs[Fun[A, Complex]](
					"choose a value function on L",
					"∃f:(A → complex). ∀y:A. y ∈ L ⇒ V(y, f(y))",
					By(total, functions.ChooseOn.At(V, L)))
				extension, extensionDef := a.LetAs[Fun[A, Complex]]("extension",
					"λy:A. COND(y ∈ L, f(y), complex_of_real(&0))")
				values := a.Have(
					"the extension takes the value associated with any decomposition",
					"∀u:A. ∀i:num. u ∈ K ⇒ extension(u * P(i)) = χ(u) * w ^ i",
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						i := b.FixAs[Nat]("i")
						inK := b.Assume()
						y := b.TermAs[A]("u * P(i)")
						inL := b.Have(
							"this product lies in L",
							"u * P(i) ∈ L",
							By(Normalized, inK, powers, productIn.At(u, i)))
						v, j, factors := b.Obtain2As[A, Nat](
							"the chosen value comes from some decomposition",
							"∃v:A. ∃j:num. v ∈ K ∧ u * P(i) = v * P(j) ∧ f(u * P(i)) = χ(v) * w ^ j",
							By(Normalized, inL, represents, chosen.At(y)))
						parts := b.Conjuncts(
							factors,
							"the first factor lies in K",
							"the products agree",
							"the chosen value")
						value := b.Have(
							"any two decompositions give the same value",
							"f(u * P(i)) = χ(u) * w ^ i",
							By(inK, parts[0], parts[1], parts[2], unique.At(u, v, i, j)))
						b.Show(
							"the conditional selects that value on L",
							By(inL, extensionDef, value))
					}))
				vanishes := a.Have(
					"the extension vanishes off L",
					"∀y:A. y ∉ L ⇒ extension(y) = complex_of_real(&0)",
					Derive(func(b *Argument) {
						b.FixAs[A]("y")
						outside := b.Assume()
						b.Show(
							"the conditional selects zero off L",
							By(outside, extensionDef))
					}))
				S := a.TermAs[GroupOps[A]]("restrict_group(G, L)")
				source := a.Have(
					"the restricted group on L is a group",
					"group_on(restrict_group(G, L))",
					By(lSubgroup, group.SubgroupGroupOn.Read(grp).AsFact().At(L)))
				target := a.Have(
					"the nonzero complex numbers form the target group",
					"group_on(field_units(complex_field_ops))",
					By(hom, group_homomorphism.Target.At(R, units, χ)))
				maps := a.Have(
					"each value on L is a nonzero complex number",
					"∀y:A. y ∈ L ⇒ extension(y) ∈ field_units(complex_field_ops).carrier",
					Derive(func(b *Argument) {
						y := b.FixAs[A]("y")
						inL := b.Assume()
						u, i, factors := b.Obtain2As[A, Nat](
							"choose a decomposition of y",
							"∃u:A. ∃i:num. u ∈ K ∧ y = u * P(i)",
							By(inL, powers, decomposition.At(y)))
						parts := b.Conjuncts(
							factors,
							"the first factor lies in K",
							"the product represents y")
						value := b.Have(
							"evaluate the extension at y",
							"extension(y) = χ(u) * w ^ i",
							By(parts[0], parts[1], values.At(u, i)))
						nonzero := b.Have(
							"both factors of the value are nonzero",
							"extension(y) ≠ complex_of_real(&0)",
							By(
								value,
								parts[0],
								χNonzero.At(u),
								wPowersNonzero.At(i),
								field.MulEqZero.Read(complex_field.Field).At(χ.Apply(u), b.TermAs[Complex]("w ^ i"))))
						b.Show(
							"a nonzero complex value lies in the target carrier",
							BySets(nonzero))
					}))
				multiplies := a.Have(
					"the extension preserves products in L",
					"∀y z:A. y ∈ L ∧ z ∈ L ⇒ extension(y * z) = extension(y) * extension(z)",
					Derive(func(b *Argument) {
						y := b.FixAs[A]("y")
						z := b.FixAs[A]("z")
						both := b.Conjuncts(
							b.Assume(),
							"y lies in L",
							"z lies in L")
						u, i, left := b.Obtain2As[A, Nat](
							"decompose y",
							"∃u:A. ∃i:num. u ∈ K ∧ y = u * P(i)",
							By(both[0], powers, decomposition.At(y)))
						v, j, right := b.Obtain2As[A, Nat](
							"decompose z",
							"∃v:A. ∃j:num. v ∈ K ∧ z = v * P(j)",
							By(both[1], powers, decomposition.At(z)))
						yp := b.Conjuncts(
							left,
							"first factor of y in K",
							"product representing y")
						zp := b.Conjuncts(
							right,
							"first factor of z in K",
							"product representing z")
						pi, pj := b.TermAs[A]("P(i)"), b.TermAs[A]("P(j)")
						ij := b.TermAs[Nat]("i + j")
						uv := b.TermAs[A]("u * v")
						vpj := b.TermAs[A]("v * P(j)")
						pipj := b.TermAs[A]("P(i) * P(j)")
						uIn := b.Have(
							"u lies in G",
							"u ∈ G.carrier",
							BySets(yp[0], subset))
						vIn := b.Have(
							"v lies in G",
							"v ∈ G.carrier",
							BySets(zp[0], subset))
						vpjIn := b.Have(
							"v times the second power lies in G",
							"v * P(j) ∈ G.carrier",
							By(vIn, powersInG.At(j), group.MulIn.Read(grp).AsFact().At(v, pj)))
						pipjIn := b.Have(
							"the product of the powers lies in G",
							"P(i) * P(j) ∈ G.carrier",
							By(powersInG.At(i), powersInG.At(j), group.MulIn.Read(grp).AsFact().At(pi, pj)))
						power := b.Have(
							"multiplying powers adds exponents",
							"P(i + j) = P(i) * P(j)",
							By(Normalized, xIn, powers, group.PowAdd.Read(grp).AsFact().At(x, i, j)))
						first := b.Have(
							"insert the decompositions and reassociate",
							"y * z = u * (P(i) * (v * P(j)))",
							By(yp[1], zp[1], uIn, powersInG.At(i), vpjIn, group.AssocOn.Read(grp).AsFact().At(u, pi, vpj)))
						middle := b.Have(
							"commute the two middle factors",
							"u * (P(i) * (v * P(j))) = u * (v * (P(i) * P(j)))",
							By(
								vIn,
								powersInG.At(i),
								powersInG.At(j),
								comm_monoid.LeftCommOn.Read(abelian_group.MonoidOn.Read(abelian)).AsFact().At(pi, v, pj)))
						last := b.Have(
							"combine the K factors and the two powers",
							"u * (v * (P(i) * P(j))) = u * v * P(i + j)",
							By(uIn, vIn, pipjIn, power, group.AssocOn.Read(grp).AsFact().At(u, v, pipj)))
						product := b.Have(
							"the decomposition of the product has exponent i + j",
							"y * z = u * v * P(i + j)",
							By(first, middle, last))
						uvIn := b.Have(
							"the first factor of the product lies in K",
							"u * v ∈ K",
							By(subgroup, yp[0], zp[0], group.SubgroupMul.At(G, K, u, v)))
						leftValue := b.Have(
							"evaluate the extension at y",
							"extension(y) = χ(u) * w ^ i",
							By(yp[0], yp[1], values.At(u, i)))
						rightValue := b.Have(
							"evaluate the extension at z",
							"extension(z) = χ(v) * w ^ j",
							By(zp[0], zp[1], values.At(v, j)))
						productValue := b.Have(
							"evaluate the extension at the product",
							"extension(y * z) = χ(u * v) * w ^ (i + j)",
							By(uvIn, product, values.At(uv, ij)))
						χProduct := b.Have(
							"χ preserves the product of the K factors",
							"χ(u * v) = χ(u) * χ(v)",
							By(hom, yp[0], zp[0], CharacterMul.At(R, χ, u, v), group.RestrictGroupDef))
						wProduct := b.Have(
							"the powers of w multiply when their exponents add",
							"w ^ (i + j) = w ^ i * w ^ j",
							By(comm_monoid.PowAdd.Read(multiplication).At(w, i, j)))
						b.Show(
							"the same four complex factors occur on each side",
							Simp(Fwd(leftValue), Fwd(rightValue), Fwd(productValue), Fwd(χProduct), Fwd(wProduct)),
							ByArith())
					}))
				agrees := a.Have(
					"on K the extension agrees with χ",
					"∀y:A. y ∈ K ⇒ extension(y) = χ(y)",
					Derive(func(b *Argument) {
						y := b.FixAs[A]("y")
						inK := b.Assume()
						asProduct := b.Have(
							"the zeroth power leaves y fixed",
							"y * P(0) = y",
							By(
								Normalized,
								inK,
								powerZero,
								subset,
								set_basic.SubsetDef,
								group.RightIdentityOn.Read(grp).AsFact().At(y)))
						b.Show(
							"the power of w at exponent zero is one",
							By(
								Normalized,
								inK,
								asProduct,
								values.At(y, zero),
								comm_monoid.MonoidPowDef,
								comm_monoid.RightIdentity.Read(multiplication).At(χ.Apply(y)),
								complex_field.CommRingOn))
					}))
				extendedHom := a.Have(
					"the extension is a homomorphism from the restricted group into the nonzero complex numbers",
					"group_homomorphism(restrict_group(G, L), field_units(complex_field_ops), extension)",
					By(
						source,
						target,
						maps,
						multiplies,
						group_homomorphism.GroupHomomorphism.At(S, units, extension),
						group.RestrictGroupDef,
						roots_of_unity.FieldUnitsDef))
				extendedCharacter := a.Have(
					"the homomorphism vanishes outside L and is a character",
					"group_character(restrict_group(G, L), extension)",
					By(extendedHom, vanishes, GroupCharacterDef.At(S, extension), group.RestrictGroupDef))
				one := a.TermAs[A]("G.one")
				identityValue := a.Have(
					"χ sends the identity to 1",
					"χ(G.one) = complex_of_real(&1)",
					By(hom, group_homomorphism.MapOne.At(R, units, χ), group.RestrictGroupDef))
				generator := a.Have(
					"x is the identity times its first power",
					"G.one * P(1) = x",
					By(
						Normalized,
						powers,
						xIn,
						group.PowOne.Read(grp).AsFact().At(x),
						group.LeftIdentityOn.Read(grp).AsFact().At(x)))
				atGenerator := a.Have(
					"so the extension takes the value χ(1) · w¹ = w at x",
					"extension(x) = w",
					By(
						Normalized,
						identityIn,
						generator,
						identityValue,
						values.At(one, a.TermAs[Nat]("1")),
						comm_monoid.PowOne.Read(multiplication).At(w),
						comm_monoid.LeftIdentity.Read(multiplication).At(w)))
				a.Take(L)
				a.Take(extension)
				a.Show(
					"L contains K and x, the character on L extends χ, and its value at x is w",
					By(lSubgroup, included, contains, extendedCharacter, agrees, atGenerator))
			})
		}),
})}

// CharacterExtends — every character of a subgroup of a finite abelian
// group extends to a character of the group.
var CharacterExtends = characterExtendsThm{family.Add(registry.ProofEntry{
	Name: "CharacterExtends",
	Key:  "prop_9024f0077889582d",
	Reading: "Each step adjoins a point x through CharacterExtendsOneStep at a " +
		"d-th root of χ(xᵈ) (complex_polynomial.UnitPowerRoot). The root is where ℂ " +
		"enters: a field without enough roots of unity would not extend the character.",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀K:set(A). ∀χ:(A → complex).",
		Hypotheses: []string{
			"abelian_group_on(G)",
			"finite(G.carrier)",
			"subgroup(G, K)",
			"group_character(restrict_group(G, K), χ)",
		},
		Conclusion: "∃χ':(A → complex). group_character(G, χ') ∧ ∀y:A. y ∈ K ⇒ χ'(y) = χ(y)",
		Abbrev: Abbrev{
			{
				Name: "extends",
				Text: "λH:set(A). " +
					"    subgroup(G, H) ∧ " +
					"    K ⊆ H ∧ " +
					"    (∃ψ:(A → complex). group_character(restrict_group(G, H), ψ) ∧ (∀y:A. y ∈ K ⇒ ψ(y) = χ(y)))",
			},
		},
	},
		func(
			a *Argument,
			G *Expr[GroupOps[A]],
			K *Expr[Set[A]],
			χ *Arrow[A, Complex],
			abelian abelian_group.AbelianGroupFact[on.G],
			finite, subgroup, character Fact,
		) {
			S, familyDef := a.LetAs[Set[Set[A]]]("S", "{L:set(A) | «extends»(L)}")
			members := a.Have(
				"the family consists of subgroups containing K on which χ has an extension",
				"∀L:set(A). L ∈ S ⇔ «extends»(L)",
				BySets(familyDef))
			base := a.Have(
				"the original subgroup belongs to the family, with χ as its own extension",
				"K ∈ S",
				Simp(Fwd(members)),
				SplitConjAll(
					Case(
						"K is a subgroup",
						By(subgroup)),
					Case(
						"K contains itself",
						By(set_order.SubsetRefl.At(K))),
					Case(
						"χ agrees with itself on K",
						Witness(χ),
						By(character))))
			bounded := a.Have(
				"every subgroup in the family is a subset of the group carrier",
				"S ⊆ {L:set(A) | L ⊆ G.carrier}",
				BySets(members, group.SubgroupSubset.Inst[A]().At(G)))
			carrier := a.TermAs[Set[A]]("G.carrier")
			powerset := a.TermAs[Set[Set[A]]]("{L:set(A) | L ⊆ G.carrier}")
			finiteFamily := a.Have(
				"the family is finite because the group carrier is finite",
				"finite(S)",
				By(finite, bounded, finite_set.FinitePowerset.At(carrier), finite_set.FiniteSubset.At(S, powerset)))
			inclusion := a.TermAs[Fun2[Set[A], Set[A], Bool]]("λs:set(A). λt:set(A). s ⊆ t")
			L, maximal := a.ObtainAs[Set[A]](
				"choose an inclusion-maximal subgroup carrying an extension",
				"∃L:set(A). maximal(λs:set(A). λt:set(A). s ⊆ t, S, L)",
				By(
					finiteFamily,
					base,
					set_basic.NotInEmpty.At(K),
					order.SubsetPreorder,
					order.FiniteMaximal.At(inclusion, S)))
			maximality := a.Conjuncts(
				a.Unfolded(maximal, order.MaximalDef),
				"L belongs to the family",
				"every member containing L is contained in L")
			extension := a.Have(
				"the maximal subgroup contains K and carries an extension of χ",
				"«extends»(L)",
				By(maximality[0], members.At(L)))
			extensionLaws := a.Conjuncts(
				extension,
				"L is a subgroup",
				"K lies in L",
				"there is an extension of χ on L")
			LSubgroup, KInL := extensionLaws[0], extensionLaws[1]
			ψ, onL := a.UnpackAs[Fun[A, Complex]](extensionLaws[2], "ψ")
			lawsOnL := a.Conjuncts(
				onL,
				"ψ is a character on L",
				"ψ agrees with χ on K")
			ψCharacter, ψAgrees := lawsOnL[0], lawsOnL[1]
			grp := abelian_group.GroupOn.Read(abelian)
			n := a.TermAs[Nat]("card(G.carrier)")
			restricted := a.TermAs[GroupOps[A]]("restrict_group(G, L)")
			finiteL := a.Have(
				"L is finite, a subset of the finite carrier",
				"finite(L)",
				By(finite, LSubgroup, group.SubgroupSubset.At(G, L), finite_set.FiniteSubset.At(L, carrier)))
			identityIn := a.Have(
				"L contains the identity",
				"G.one ∈ L",
				By(LSubgroup, group.SubgroupOne.At(G, L)))
			positiveOrder := a.Have(
				"the finite group has positive order",
				"0 < card(G.carrier)",
				By(finite_group.CarrierCardPositive.Read(grp), finite))
			allPoints := a.Have(
				"the maximal subgroup contains the group carrier",
				"G.carrier ⊆ L",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					d, period := b.ObtainAs[Nat](
						"the powers of x in L are those at the multiples of some d",
						"∃d:num. ∀j:num. monoid_pow(G.mul, G.one, x, j) ∈ L ⇔ d ∣ j",
						By(xIn, LSubgroup, group.PowInSubgroupIffDivides.Read(grp).AsFact().At(x, L)))
					power := b.TermAs[A]("monoid_pow(G.mul, G.one, x, d)")
					dividesOrder := b.Have(
						"d divides the order of G, x raised to it being the identity, which lies in L",
						"d ∣ card(G.carrier)",
						By(finite, xIn, identityIn, cyclic_group.PowCardIsOne.Read(grp).AsFact().At(x), period.At(n)))
					positive := b.Have(
						"so d is positive",
						"0 < d",
						ByArith(positiveOrder, dividesOrder, nat_divides.ZeroDivides.At(n)))
					modulus := b.Have(
						"ψ has modulus 1 at x ^ d, a point of L",
						"|ψ(monoid_pow(G.mul, G.one, x, d))| = &1",
						By(
							ψCharacter,
							finiteL,
							period.At(d),
							nat_divides.DividesRefl.At(d),
							GroupCharacterDef.At(restricted, ψ),
							CharacterUnitModulus.At(restricted, ψ, power),
							group.RestrictGroupDef))
					w, root := b.ObtainAs[Complex](
						"take a d-th root w of ψ(x ^ d)",
						"∃w:complex. w ^ d = ψ(monoid_pow(G.mul, G.one, x, d))",
						By(
							positive,
							modulus,
							complex_polynomial.UnitPowerRoot.At(d, b.TermAs[Complex]("ψ(monoid_pow(G.mul, G.one, x, d))"))))
					M, θ, larger := b.Obtain2As[Set[A], Fun[A, Complex]](
						"extend ψ to a subgroup containing L and x",
						"∃M:set(A). ∃θ:(A → complex). "+
							"    subgroup(G, M) ∧ "+
							"    L ⊆ M ∧ "+
							"    x ∈ M ∧ "+
							"    group_character(restrict_group(G, M), θ) ∧ "+
							"    (∀y:A. y ∈ L ⇒ θ(y) = ψ(y))",
						By(
							abelian,
							finite,
							LSubgroup,
							ψCharacter,
							xIn,
							period,
							root,
							CharacterExtendsOneStep.At(G, L, ψ, x, d, w)))
					largerLaws := b.Conjuncts(
						larger,
						"M is a subgroup",
						"L lies in M",
						"x lies in M",
						"θ is a character on M",
						"θ agrees with ψ on L")
					LInM := largerLaws[1]
					admissible := b.Have(
						"the larger subgroup still belongs to the family",
						"M ∈ S",
						Simp(Fwd(members)),
						SplitConjAll(
							Case(
								"M is a subgroup",
								By(largerLaws[0])),
							Case(
								"K lies in M through L",
								BySets(KInL, LInM)),
							Case(
								"θ extends χ from K to M",
								Witness(θ),
								SplitConj(
									Case(
										"θ is a character on M",
										By(largerLaws[3])),
									Case(
										"the extensions agree on K through ψ",
										Derive(func(c *Argument) {
											y := c.FixAs[A]("y")
											yIn := c.Assume()
											c.Show(
												"θ agrees with ψ at y because K lies in L, and ψ agrees with χ there",
												BySets(yIn, KInL, ψAgrees.At(y), largerLaws[4].At(y)))
										}))))))
					b.Show(
						"maximality gives M ⊆ L, so x lies in L",
						BySets(largerLaws[2], admissible, LInM, maximality[1].At(M)))
				}))
			restriction := a.TermAs[GroupOps[A]]("restrict_group(G, L)")
			whole := a.Have(
				"L is the whole carrier and the restriction keeps every group operation",
				"restrict_group(G, L) = G",
				By(
					allPoints,
					LSubgroup,
					group.SubgroupSubset.At(G, L),
					set_order.SubsetAntisym.At(L, carrier),
					Inst(group.GroupOpsData.Ext, TypeBinder.BindA[A]()).At(restriction, G)))
			a.Show(
				"ψ is the required character of G and agrees with χ on K",
				Witness(ψ),
				By(Normalized, ψAgrees, whole, ψCharacter))
		}),
})}

// SeparatingCharacter — in a finite abelian group, every element other
// than the identity has a character that is not 1 at it.
var SeparatingCharacter = separatingCharacterThm{family.Add(registry.ProofEntry{
	Name:    "SeparatingCharacter",
	Key:     "prop_8f054a1eb2a05ed4",
	Reading: "It fails for non-abelian groups: every character is 1 on commutators.",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀x:A.",
		Hypotheses: []string{
			"abelian_group_on(G)",
			"finite(G.carrier)",
			"x ∈ G.carrier",
			"x ≠ G.one",
		},
		Conclusion: "∃χ:(A → complex). group_character(G, χ) ∧ χ(x) ≠ &1",
	},
		func(
			a *Argument,
			G *Expr[GroupOps[A]],
			x *Expr[A],
			abelian abelian_group.AbelianGroupFact[on.G],
			finite, xIn, distinct Fact,
		) {
			K := a.TermAs[Set[A]]("cyclic_subgroup(G, x)")
			point := a.MemberOf[on.G](x, xIn)
			grp := abelian_group.GroupOn.Read(abelian)
			generator := a.Have(
				"the cyclic subgroup contains x as its first power",
				"x ∈ cyclic_subgroup(G, x)",
				Simp(Fwd(cyclic_group.CyclicSubgroupDef)),
				BySets(group.PowOne.Read(grp).At(point)))
			ψ, cyclic := a.ObtainAs[Fun[A, Complex]](
				"a character of the cyclic subgroup separates x from the identity",
				"∃ψ:(A → complex). group_character(restrict_group(G, cyclic_subgroup(G, x)), ψ) ∧ ψ(x) ≠ &1",
				By(finite, distinct, CyclicCharacter.Read(grp).At(point)))
			cyclicLaws := a.Conjuncts(
				cyclic,
				"ψ is a character of the cyclic subgroup",
				"ψ(x) differs from 1")
			χ, extends := a.ObtainAs[Fun[A, Complex]](
				"extend ψ to a character of G agreeing with ψ on the cyclic subgroup",
				"∃χ:(A → complex). group_character(G, χ) ∧ (∀y:A. y ∈ cyclic_subgroup(G, x) ⇒ χ(y) = ψ(y))",
				By(
					finite,
					cyclicLaws[0],
					cyclic_group.CyclicSubgroupSubgroup.Read(grp).At(point),
					CharacterExtends.Read(abelian).At(K, ψ)))
			extension := a.Conjuncts(
				extends,
				"χ is a character of G",
				"χ agrees with ψ on the cyclic subgroup")
			a.Show(
				"the extension has the same value at x, which differs from 1",
				Witness(χ),
				By(Normalized, cyclicLaws[1], extension[0], generator, extension[1].At(x)))
		}),
})}

// CharacterSum — the values on a finite group's carrier of a homomorphism
// into the nonzero complex numbers add up to the size of the group when
// they are all 1 and to 0 otherwise: a homomorphism that is 1 on the
// carrier sums to the size of the carrier, and one with χ(y) ≠ 1 at a
// point y has its sum S unchanged by translation by y, which permutes the
// carrier, so S = χ(y)·S and S = 0.
var CharacterSum = characterSumThm{family.Add(registry.ProofEntry{
	Name: "CharacterSum",
	Key:  "prop_98cc6a2561a1a60",
	Reading: "This is the first orthogonality relation, holding in any finite " +
		"group, abelian or not. The values off the carrier are not read, so it holds " +
		"for any homomorphism into the nonzero complex numbers, a character among them.",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀χ:(A → complex).",
		Hypotheses: []string{
			"group_homomorphism(G, field_units(complex_field_ops), χ)",
			"finite(G.carrier)",
		},
		Conclusion: "Σ_{x∈G.carrier} χ(x) = " +
			"COND(∀x:A. x ∈ G.carrier ⇒ χ(x) = &1, complex_of_real(&(card(G.carrier))), complex_of_real(&0))",
	},
		func(a *Argument, G *Expr[GroupOps[A]], χ *Arrow[A, Complex], hom, finite Fact) {
			carrier := a.TermAs[Set[A]]("G.carrier")
			complexAdd := a.TermAs[Op[Complex]]("complex_add")
			addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
			a.Cases(a.Term("∀x:A. x ∈ G.carrier ⇒ χ(x) = &1"))
			a.When(
				"where χ is 1 on the carrier, the sum counts the carrier",
				func(b *Argument, trivial Fact) {
					b.Show(
						"the sum is that of 1 over the carrier, which is its size",
						CalcEq(
							Leg(
								b.TermAs[Complex]("Σ_{x∈G.carrier} &1"),
								"χ is 1 at each point of the carrier",
								By(trivial, addition, monoidal.Congruence)),
							Leg(
								b.TermAs[Complex]("complex_of_real(Σ_{x∈G.carrier} &1)"),
								"the embedding of ℝ in ℂ carries finite sums to sums",
								By(finite, complex_field.OfRealSum.At(carrier, b.TermAs[Fun[A, Real]]("λx:A. &1")))),
							Leg(
								b.TermAs[Complex]("complex_of_real(&(card(G.carrier)))"),
								"the real sum of 1 over the carrier counts it",
								By(Normalized, finite, real_sum.CardAsSum.At(carrier))),
							FinalLeg(
								"which is the condition's first value",
								By(trivial))))
				})
			a.Otherwise(
				"where χ is not 1 at some point of the carrier, translation by that point fixes the sum",
				func(b *Argument, nontrivial Fact) {
					_, picked := b.Obtain(
						"take y in the carrier with χ(y) ≠ 1",
						"∃y:A. y ∈ G.carrier ∧ χ(y) ≠ &1",
						By(nontrivial))
					parts := b.Conjuncts(
						picked,
						"y lies in the carrier",
						"and χ(y) is not 1")
					yIn, notOne := parts[0], parts[1]
					isGroup := group_homomorphism.Source.Read(hom)
					product := b.Have(
						"χ carries y·x to χ(y)·χ(x)",
						"∀x:A. x ∈ G.carrier ⇒ χ(y * x) = χ(y) * χ(x)",
						By(hom, yIn, CharacterMul))
					translated := b.Have(
						"so multiplying the sum by χ(y) leaves it as it is",
						"Σ_{x∈G.carrier} χ(x) = χ(y) * Σ_{x∈G.carrier} χ(x)",
						CalcEq(
							Leg(
								b.TermAs[Complex]("Σ_{x∈G.carrier} χ(y * x)"),
								"x ↦ y·x permutes the carrier, x ↦ y⁻¹·x taking each point back",
								By(
									yIn,
									monoidal.Reindex.At(
										complexAdd,
										carrier,
										carrier,
										b.TermAs[Fun[A, Complex]]("λx:A. χ(y * x)"),
										χ,
										b.TermAs[Fun[A, A]]("λx:A. y * x"),
										b.TermAs[Fun[A, A]]("λx:A. G.inv(y) * x")),
									addition,
									group.MulIn.Read(isGroup),
									group.InvIn.Read(isGroup),
									group.MulInvCancelLeftOn.Read(isGroup),
									group.InvMulCancelLeftOn.Read(isGroup))),
							Leg(
								b.TermAs[Complex]("Σ_{x∈G.carrier} χ(y) * χ(x)"),
								"by the product law at each point of the carrier",
								By(product, addition, monoidal.Congruence)),
							FinalLeg(
								"χ(y) comes out of the sum, multiplication by it keeping 0 and sums",
								By(
									finite,
									monoidal.Homomorphic.At(
										complexAdd,
										complexAdd,
										b.TermAs[Fun[Complex, Complex]]("λz:complex. χ(y) * z"),
										carrier,
										χ),
									addition,
									comm_ring.NeutralAdd.Read(complex_field.CommRing),
									comm_ring.LeftDistrib.Read(complex_field.CommRing),
									comm_ring.MulRightZero.Read(complex_field.CommRing)))))
					factored := b.Have(
						"so (χ(y) − 1)·S = 0 for the sum S",
						"(χ(y) - &1) * Σ_{x∈G.carrier} χ(x) = &0",
						ByArith(translated))
					vanishes := b.Have(
						"and χ(y) − 1 is not 0, so the sum is 0",
						"Σ_{x∈G.carrier} χ(x) = &0",
						ByArith(factored, notOne))
					b.Show(
						"which is the condition's second value",
						By(nontrivial, vanishes))
				})
		}),
})}

// CharacterSumOverCharacters — in a finite abelian group, the values at x
// of all the characters add up to their number when x is the identity and
// to 0 otherwise.
var CharacterSumOverCharacters = characterSumOverCharactersThm{family.Add(registry.ProofEntry{
	Name:    "CharacterSumOverCharacters",
	Key:     "prop_1d36b1c619bb58fb",
	Reading: "This is the second orthogonality relation, and the one that needs the group abelian.",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A). ∀x:A.",
		Hypotheses: []string{
			"abelian_group_on(G)",
			"finite(G.carrier)",
			"x ∈ G.carrier",
		},
		Conclusion: "Σ_{χ∈{χ:(A → complex) | group_character(G, χ)}} χ(x) = " +
			"COND(x = G.one, " +
			"    complex_of_real(&(card({χ:(A → complex) | group_character(G, χ)}))), " +
			"    complex_of_real(&0))",
	},
		func(
			a *Argument,
			G *Expr[GroupOps[A]],
			x *Expr[A],
			abelian abelian_group.AbelianGroupFact[on.G],
			finite, xIn Fact,
		) {
			T, characters := a.LetAs[Set[Fun[A, Complex]]]("T", "{χ:(A → complex) | group_character(G, χ)}")
			finiteCharacters := a.Have(
				"there are finitely many characters",
				"finite(T)",
				By(finite, characters, CharactersFinite.At(G)))
			member := a.Have(
				"membership in T is the character condition",
				"∀χ:(A → complex). χ ∈ T ⇔ group_character(G, χ)",
				BySets(characters))
			complexAdd := a.TermAs[Op[Complex]]("complex_add")
			evaluation := a.TermAs[Fun[Fun[A, Complex], Complex]]("λχ:(A → complex). χ(x)")
			ring := complex_field.CommRing
			addition := comm_ring.MonoidalAdd.Read(ring)
			zero := comm_ring.NeutralAdd.Read(ring)
			a.Cases(a.TermAs[Bool]("x = G.one"))
			a.When(
				"at the identity the sum counts the characters",
				func(b *Argument, identity Fact) {
					units := b.TermAs[GroupOps[Complex]]("field_units(complex_field_ops)")
					allOne := b.Have(
						"each character sends the group identity to 1",
						"∀χ:(A → complex). χ ∈ T ⇒ χ(x) = complex_of_real(&1)",
						Derive(func(c *Argument) {
							χ := c.FixAs[Fun[A, Complex]]("χ")
							inT := c.Assume()
							c.Show(
								"a character is a homomorphism to the nonzero complex numbers",
								By(
									Normalized,
									identity,
									inT,
									member.At(χ),
									GroupCharacterDef.At(G, χ),
									group_homomorphism.MapOne.At(G, units, χ)))
						}))
					b.Show(
						"the sum of the constant 1 is the number of characters",
						CalcEq(
							Leg(
								b.TermAs[Complex]("Σ_{χ∈T} complex_of_real(&1)"),
								"every summand is 1",
								By(
									allOne,
									monoidal.Congruence.At(complexAdd, T, evaluation,
										b.TermAs[Fun[Fun[A, Complex], Complex]]("λχ:(A → complex). complex_of_real(&1)")),
									addition)),
							Leg(
								b.TermAs[Complex]("complex_of_real(Σ_{χ∈T} &1)"),
								"the real embedding preserves the sum of ones",
								By(
									finiteCharacters,
									complex_field.OfRealSum.At(T, b.TermAs[Fun[Fun[A, Complex], Real]]("λχ:(A → complex). &1")))),
							Leg(
								b.TermAs[Complex]("complex_of_real(&card(T))"),
								"the real sum of ones counts the characters",
								By(Normalized, finiteCharacters, real_sum.CardAsSum.At(T))),
							FinalLeg(
								"the identity condition selects this count",
								By(identity))))
				})
			a.Otherwise(
				"away from the identity a separating character forces the sum to vanish",
				func(b *Argument, distinct Fact) {
					ψ, separating := b.ObtainAs[Fun[A, Complex]](
						"choose a character whose value at x differs from 1",
						"∃ψ:(A → complex). group_character(G, ψ) ∧ ψ(x) ≠ &1",
						By(abelian, finite, xIn, distinct, SeparatingCharacter.At(G, x)))
					chosen := b.Conjuncts(
						separating,
						"ψ is a character",
						"ψ(x) differs from 1")
					ψCharacter, ψNotOne := chosen[0], chosen[1]
					conjugate := b.TermAs[Fun[A, Complex]]("λy:A. conj(ψ(y))")
					conjugateCharacter := b.Have(
						"the pointwise conjugate of ψ is also a character",
						"group_character(G, λy:A. conj(ψ(y)))",
						By(ψCharacter, CharacterClosure.At(G, ψ, ψ)))
					mulψ, multiply := b.LetAs[Fun[Fun[A, Complex], Fun[A, Complex]]](
						"mulψ", "λχ:(A → complex). λy:A. ψ(y) * χ(y)")
					mulConjψ, multiplyConjugate := b.LetAs[Fun[Fun[A, Complex], Fun[A, Complex]]](
						"mulConjψ", "λχ:(A → complex). λy:A. conj(ψ(y)) * χ(y)")
					closed := b.Have(
						"both pointwise multiplication maps preserve the character set",
						"∀χ:(A → complex). χ ∈ T ⇒ mulψ(χ) ∈ T ∧ mulConjψ(χ) ∈ T",
						Derive(func(c *Argument) {
							χ := c.FixAs[Fun[A, Complex]]("χ")
							inT := c.Assume()
							χCharacter := c.Have(
								"χ is a character",
								"group_character(G, χ)",
								By(inT, member.At(χ)))
							c.Do(SplitConj(
								Case(
									"the product with ψ is a character",
									By(
										Normalized,
										χCharacter,
										ψCharacter,
										multiply,
										member.At(c.TermAs[Fun[A, Complex]]("mulψ(χ)")),
										CharacterClosure.At(G, ψ, χ))),
								Case(
									"the product with the conjugate of ψ is a character",
									By(
										Normalized,
										χCharacter,
										conjugateCharacter,
										multiplyConjugate,
										member.At(c.TermAs[Fun[A, Complex]]("mulConjψ(χ)")),
										CharacterClosure.At(G, conjugate, χ)))))
						}))
					inverses := b.Have(
						"the two maps undo each other pointwise on every character",
						"∀χ:(A → complex). χ ∈ T ⇒ ∀y:A. mulConjψ(mulψ(χ), y) = χ(y) ∧ mulψ(mulConjψ(χ), y) = χ(y)",
						Derive(func(c *Argument) {
							χ := c.FixAs[Fun[A, Complex]]("χ")
							inT := c.Assume()
							y := c.FixAs[A]("y")
							c.Do(Simp(Fwd(multiply), Fwd(multiplyConjugate)))
							c.Cases(c.TermAs[Bool]("y ∈ G.carrier"))
							c.When(
								"on the carrier, the two factors multiply to 1",
								func(d *Argument, yIn Fact) {
									unitAtY := d.Have(
										"on a finite group the conjugate of ψ(y) is its inverse",
										"ψ(y) * conj(ψ(y)) = complex_of_real(&1)",
										By(finite, yIn, ψCharacter, GroupCharacterDef.At(G, ψ), CharacterConjugateInverse.At(G, ψ, y)))
									d.Show(
										"multiplying by these factors leaves χ(y) unchanged in either order",
										ByArith(Scaled(d.TermAs[Complex]("χ(y)"), unitAtY)))
								})
							c.Otherwise(
								"off the carrier, χ is zero",
								func(d *Argument, outside Fact) {
									vanishing := d.Have(
										"χ(y) is zero by the character condition",
										"χ(y) = complex_of_real(&0)",
										By(outside, inT, member.At(χ), GroupCharacterDef.At(G, χ)))
									d.Show(
										"both products retain this zero value",
										ByArith(vanishing))
								})
						}))
					fixed := b.Have(
						"multiplication by ψ(x) leaves the sum fixed",
						"ψ(x) * (Σ_{χ∈T} χ(x)) = Σ_{χ∈T} χ(x)",
						CalcEq(
							Leg(
								b.TermAs[Complex]("Σ_{χ∈T} ψ(x) * χ(x)"),
								"multiplication by ψ(x) preserves sums and zero",
								By(
									finiteCharacters,
									monoidal.Homomorphic.At(
										complexAdd,
										complexAdd,
										b.TermAs[Fun[Complex, Complex]]("λz:complex. ψ(x) * z"),
										T,
										evaluation),
									addition,
									zero,
									comm_ring.LeftDistrib.Read(ring),
									comm_ring.MulRightZero.Read(ring))),
							FinalLeg(
								"multiplying by ψ permutes the characters, undone by "+
									"multiplying by conj ψ, and evaluation at x gives the summands",
								By(
									inverses,
									closed,
									multiply,
									monoidal.Reindex.At(
										complexAdd,
										T,
										T,
										b.TermAs[Fun[Fun[A, Complex], Complex]]("λχ:(A → complex). ψ(x) * χ(x)"),
										evaluation,
										mulψ,
										mulConjψ),
									addition))))
					factored := b.Have(
						"the sum is annihilated by ψ(x) minus 1",
						"(ψ(x) - complex_of_real(&1)) * (Σ_{χ∈T} χ(x)) = complex_of_real(&0)",
						ByArith(fixed))
					vanishes := b.Have(
						"the multiplier is nonzero, so the sum is zero",
						"Σ_{χ∈T} χ(x) = complex_of_real(&0)",
						ByArith(ψNotOne, factored))
					b.Show(
						"the nonidentity condition selects zero",
						By(distinct, vanishes))
				})
		}),
})}

// CharacterCount — a finite abelian group has as many characters as
// elements.
var CharacterCount = characterCountThm{family.Add(registry.ProofEntry{
	Name: "CharacterCount",
	Key:  "prop_c93e74b486aca37e",
	Build: family.Theorem(Statement{
		Binders: "∀G:group_ops(A).",
		Hypotheses: []string{
			"abelian_group_on(G)",
			"finite(G.carrier)",
		},
		Conclusion: "card({χ:(A → complex) | group_character(G, χ)}) = card(G.carrier)",
	},
		func(a *Argument, G *Expr[GroupOps[A]], abelian abelian_group.AbelianGroupFact[on.G], finite Fact) {
			carrier := a.TermAs[Set[A]]("G.carrier")
			one := a.TermAs[A]("G.one")
			grp := abelian_group.GroupOn.Read(abelian)
			T, characters := a.LetAs[Set[Fun[A, Complex]]]("T", "{χ:(A → complex) | group_character(G, χ)}")
			ε, trivial := a.LetAs[Fun[A, Complex]](
				"ε",
				"λy:A. COND(y ∈ G.carrier, complex_of_real(&1), complex_of_real(&0))")
			finiteCharacters := a.Have(
				"the character set is finite",
				"finite(T)",
				By(finite, characters, CharactersFinite.At(G)))
			member := a.Have(
				"a member of T is a character of G",
				"∀χ:(A → complex). χ ∈ T ⇔ group_character(G, χ)",
				BySets(characters))
			trivialIn := a.Have(
				"the trivial character belongs to T",
				"ε ∈ T",
				By(trivial, member.At(ε), TrivialCharacter.Read(grp)))
			trivialOn := a.Have(
				"the trivial character is 1 on the carrier",
				"∀y:A. y ∈ G.carrier ⇒ ε(y) = complex_of_real(&1)",
				Derive(func(b *Argument) {
					b.FixAs[A]("y")
					yIn := b.Assume()
					b.Show(
						"the conditional takes the value 1",
						By(yIn, trivial))
				}))
			unique := a.Have(
				"a character is trivial exactly when it is 1 throughout the carrier",
				"∀χ:(A → complex). χ ∈ T ⇒ ((∀y:A. y ∈ G.carrier ⇒ χ(y) = complex_of_real(&1)) ⇔ χ = ε)",
				Derive(func(b *Argument) {
					χ := b.FixAs[Fun[A, Complex]]("χ")
					inT := b.Assume()
					b.Iff()
					b.Forward(
						"a character that is 1 on the carrier agrees with ε at every point",
						func(c *Argument, allOne Fact) {
							c.Do(Funext())
							y := c.FixAs[A]("y")
							c.Cases(c.TermAs[Bool]("y ∈ G.carrier"))
							c.When(
								"on the carrier both values are 1",
								func(d *Argument, yIn Fact) {
									d.Show(
										"the values agree at y",
										By(Normalized, yIn, allOne.At(y), trivialOn.At(y)))
								})
							c.Otherwise(
								"off the carrier both values are zero",
								func(d *Argument, outside Fact) {
									d.Show(
										"χ vanishes there by the character condition",
										By(outside, inT, member.At(χ), trivial, GroupCharacterDef.At(G, χ)))
								})
						})
					b.Backward(
						"ε sends each point of the carrier to 1",
						func(c *Argument, equal Fact) {
							c.Show(
								"the same holds for χ",
								By(Normalized, equal, trivialOn))
						})
				}))
			complexAdd := a.TermAs[Op[Complex]]("complex_add")
			addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
			zero := comm_ring.NeutralAdd.Read(complex_field.CommRing)
			innerAtElement := a.Have(
				"the sum over characters counts them at the identity and is zero elsewhere",
				Statement{
					Binders:    "∀x:A.",
					Hypotheses: []string{"x ∈ G.carrier"},
					Conclusion: "(Σ_{χ∈T} χ(x)) = " +
						"COND(x = G.one, complex_of_real(&card(T)), neutral_elem(complex_add))",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					b.Show(
						"the second orthogonality relation gives the sum at x",
						By(abelian, finite, xIn, characters, zero, CharacterSumOverCharacters.At(G, x)))
				}))
			innerAtCharacter := a.Have(
				"the sum over group elements counts them at the trivial character and is zero otherwise",
				Statement{
					Binders:    "∀χ:(A → complex).",
					Hypotheses: []string{"χ ∈ T"},
					Conclusion: "(Σ_{x∈G.carrier} χ(x)) = " +
						"COND(χ = ε, complex_of_real(&card(G.carrier)), neutral_elem(complex_add))",
				},
				Derive(func(b *Argument) {
					χ := b.FixAs[Fun[A, Complex]]("χ")
					inT := b.Assume()
					b.Show(
						"the first orthogonality relation singles out the character that is 1 on the carrier",
						By(
							inT,
							finite,
							member.At(χ),
							unique.At(χ),
							GroupCharacterDef.At(G, χ),
							CharacterSum.At(G, χ),
							zero))
				}))
			elementsFirst := a.Have(
				"summing the character sums over group elements counts the characters",
				"(Σ_{x∈G.carrier} (Σ_{χ∈T} χ(x))) = complex_of_real(&card(T))",
				CalcEq(
					Leg(
						a.TermAs[Complex](
							"Σ_{x∈G.carrier} COND(x = G.one, complex_of_real(&card(T)), neutral_elem(complex_add))"),
						"replace each inner sum using the second orthogonality relation",
						By(
							innerAtElement,
							monoidal.Congruence.At(
								complexAdd,
								carrier,
								a.TermAs[Fun[A, Complex]]("λx:A. Σ_{χ∈T} χ(x)"),
								a.TermAs[Fun[A, Complex]](
									"λx:A. COND(x = G.one, complex_of_real(&card(T)), neutral_elem(complex_add))")),
							addition)),
					FinalLeg(
						"the group identity is in the carrier and is the only contributing point",
						By(
							group.OneIn.Read(grp),
							addition,
							monoidal.Delta.At(
								complexAdd, carrier, a.TermAs[Fun[A, Complex]]("λx:A. complex_of_real(&card(T))"), one)))))
			charactersFirst := a.Have(
				"summing the group sums over characters counts the group elements",
				"(Σ_{χ∈T} (Σ_{x∈G.carrier} χ(x))) = complex_of_real(&card(G.carrier))",
				CalcEq(
					Leg(
						a.TermAs[Complex](
							"Σ_{χ∈T} COND(χ = ε, complex_of_real(&card(G.carrier)), neutral_elem(complex_add))"),
						"replace each inner sum using the first orthogonality relation",
						By(
							innerAtCharacter,
							monoidal.Congruence.At(
								complexAdd,
								T,
								a.TermAs[Fun[Fun[A, Complex], Complex]]("λχ:(A → complex). Σ_{x∈G.carrier} χ(x)"),
								a.TermAs[Fun[Fun[A, Complex], Complex]](
									"λχ:(A → complex). COND(χ = ε, complex_of_real(&card(G.carrier)), neutral_elem(complex_add))")),
							addition)),
					FinalLeg(
						"the trivial character is in the character set and is the only contributing term",
						By(
							trivialIn,
							addition,
							monoidal.Delta.At(
								complexAdd,
								T,
								a.TermAs[Fun[Fun[A, Complex], Complex]]("λχ:(A → complex). complex_of_real(&card(G.carrier))"),
								ε)))))
			swap := a.Have(
				"the finite double sum is independent of the summation order",
				"(Σ_{x∈G.carrier} (Σ_{χ∈T} χ(x))) = (Σ_{χ∈T} (Σ_{x∈G.carrier} χ(x)))",
				By(
					finite,
					finiteCharacters,
					addition,
					monoidal.Swap.At(
						complexAdd,
						carrier,
						T,
						a.TermAs[Fun2[A, Fun[A, Complex], Complex]]("λx:A. λχ:(A → complex). χ(x)"))))
			sameCount := a.Have(
				"the two evaluations are the two cardinalities embedded in ℂ",
				"complex_of_real(&card(T)) = complex_of_real(&card(G.carrier))",
				By(elementsFirst, charactersFirst, swap))
			a.Show(
				"both embeddings are injective, so the cardinalities agree",
				By(
					sameCount,
					complex_field.OfRealInjective.At(a.TermAs[Real]("&card(T)"), a.TermAs[Real]("&card(G.carrier)")),
					real_construction.OfNumEq.At(a.TermAs[Nat]("card(T)"), a.TermAs[Nat]("card(G.carrier)"))))
		}),
})}
