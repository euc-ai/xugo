// characters.go — the Dirichlet characters modulo q: their values, their
// correspondence with the characters of the units mod q, their number,
// the sum of a character over a period, the bound on its partial sums,
// the orthogonality relation over the characters, and the real ones.

package dirichlet_character

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/roots_of_unity"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/units_mod"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/complex/group_character"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/totient"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// CharacterMul — a Dirichlet character is completely multiplicative: it
// carries every product to the product of its values, the first law of
// the definition.
var CharacterMul = characterMulThm{family.Add(registry.ProofEntry{
	Name: "CharacterMul",
	Key:  "prop_e69d3375886e5dac",
	Build: family.Theorem(Statement{
		Binders:    "∀q m n:num. ∀χ:(num → complex).",
		Hypotheses: []string{"dirichlet_character(q, χ)"},
		Conclusion: "χ(m * n) = χ(m) * χ(n)",
	}, func(a *Argument, q, m, n *Expr[Nat], χ *Arrow[Nat, Complex], character Fact) {
		a.Show(
			"complete multiplicativity is the first law of the definition",
			By(character, DirichletCharacterDef.At(q, χ)))
	}),
})}

// CharacterPeriodic — a Dirichlet character mod q has period q, the
// second law of the definition.
var CharacterPeriodic = characterPeriodicThm{family.Add(registry.ProofEntry{
	Name: "CharacterPeriodic",
	Key:  "prop_2cc29f93175ef038",
	Build: family.Theorem(Statement{
		Binders:    "∀q n:num. ∀χ:(num → complex).",
		Hypotheses: []string{"dirichlet_character(q, χ)"},
		Conclusion: "χ(n + q) = χ(n)",
	}, func(a *Argument, q, n *Expr[Nat], χ *Arrow[Nat, Complex], character Fact) {
		a.Show(
			"the period is the second law of the definition",
			By(character, DirichletCharacterDef.At(q, χ)))
	}),
})}

// CharacterEqZero — a Dirichlet character mod q vanishes exactly at the
// numbers not coprime to q, the third law of the definition.
var CharacterEqZero = characterEqZeroThm{family.Add(registry.ProofEntry{
	Name: "CharacterEqZero",
	Key:  "prop_4bca0d8de2e68540",
	Build: family.Theorem(Statement{
		Binders:    "∀q n:num. ∀χ:(num → complex).",
		Hypotheses: []string{"dirichlet_character(q, χ)"},
		Conclusion: "χ(n) = &0 ⇔ ¬nat_coprime(n, q)",
	}, func(a *Argument, q, n *Expr[Nat], χ *Arrow[Nat, Complex], character Fact) {
		a.Show(
			"where the character vanishes is the third law of the definition",
			By(character, DirichletCharacterDef.At(q, χ)))
	}),
})}

// CharacterAtOne — a Dirichlet character is 1 at 1.
var CharacterAtOne = characterAtOneThm{family.Add(registry.ProofEntry{
	Name: "CharacterAtOne",
	Key:  "prop_5d2345867d9943e4",
	Build: family.Theorem(Statement{
		Binders:    "∀q:num. ∀χ:(num → complex).",
		Hypotheses: []string{"dirichlet_character(q, χ)"},
		Conclusion: "χ(1) = &1",
	}, func(a *Argument, q *Expr[Nat], χ *Arrow[Nat, Complex], character Fact) {
		one := a.TermAs[Nat]("1")
		nonzero := a.Have(
			"1 is coprime to the modulus, so χ(1) ≠ 0",
			"χ(1) ≠ &0",
			By(character, CharacterEqZero.At(q, one, χ), nat_gcd.OneCoprime.At(q)))
		idempotent := a.Have(
			"multiplicativity at 1 makes the value idempotent",
			"χ(1) * χ(1) = χ(1)",
			By(Normalized, character, CharacterMul.At(q, one, one, χ), nat_arith.MulOne.At(one)))
		valueAtOne := χ.Apply(one)
		complexOne := a.TermAs[Complex]("&1")
		a.Show(
			"cancel the nonzero factor χ(1)",
			By(
				nonzero,
				idempotent,
				comm_monoid.RightIdentity.Read(complex_field.MulMonoid).At(valueAtOne),
				integral_domain.MulCancelLeft.Read(complex_field.ComplexIntegralDomain).AsFact().
					At(valueAtOne, valueAtOne, complexOne),
				set_basic.InUniv))
	}),
})}

// periodMultiple — a function of period q takes the same value at r and
// at r plus any multiple of q.
var periodMultiple = periodMultipleThm{family.Add(registry.ProofEntry{
	Name: "periodMultiple",
	Key:  "prop_cd8a6bd1143bba8",
	Build: family.Theorem(Statement{
		Binders:    "∀q r k:num. ∀χ:(num → complex).",
		Hypotheses: []string{"∀x:num. χ(x + q) = χ(x)"},
		Conclusion: "χ(k * q + r) = χ(r)",
	}, func(a *Argument, q, r, k *Expr[Nat], χ *Arrow[Nat, Complex], periodic Fact) {
		a.Induct(k)
		a.Base(
			"zero shifts leave the input unchanged",
			Simp(Fwd(nat_arith.MulLeftZeroClause), Fwd(nat_arith.AddLeftZeroClause)),
			Refl())
		a.Step(
			"one further shift is one period",
			func(b *Argument, ih Fact) {
				offset := b.Have(
					"the successor offset adds one more period",
					"suc(k) * q + r = k * q + r + q",
					Simp(Fwd(nat_arith.Mul)),
					ByArith())
				b.Do(By(Normalized, offset, periodic.At(b.TermAs[Nat]("k * q + r")), ih))
			})
	}),
})}

// CharacterCongruent — a Dirichlet character mod q takes equal values at
// numbers congruent mod q.
var CharacterCongruent = characterCongruentThm{family.Add(registry.ProofEntry{
	Name:    "CharacterCongruent",
	Key:     "prop_9f8b213a6a448c",
	Reading: "q > 0 keeps the statement off the reading of a congruence modulo 0.",
	Build: family.Theorem(Statement{
		Binders: "∀q m n:num. ∀χ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"m ≡ n (mod q)",
		},
		Conclusion: "χ(m) = χ(n)",
	}, func(
		a *Argument,
		q, m, n *Expr[Nat],
		χ *Arrow[Nat, Complex],
		character, qPositive, congruent Fact,
	) {
		periodic := a.Have(
			"χ has period q",
			"∀x:num. χ(x + q) = χ(x)",
			By(character, CharacterPeriodic))
		atRemainder := a.Have(
			"division removes a multiple of the period",
			"∀x:num. χ(x) = χ(rem(x, q))",
			Derive(func(b *Argument) {
				x := b.FixAs[Nat]("x")
				remainder := b.TermAs[Nat]("rem(x, q)")
				quotient := b.TermAs[Nat]("div(x, q)")
				b.Do(By(
					Normalized,
					qPositive,
					periodic,
					nat_order.PosIffNonzero.At(q),
					nat_div_mod.Division.At(x, q),
					periodMultiple.At(q, remainder, quotient, χ)))
			}))
		a.Show(
			"the two remainders agree",
			By(congruent, atRemainder.At(m), atRemainder.At(n), nat_congruence.CongDef.At(m, n, q)))
	}),
})}

// CharacterPow — a Dirichlet character carries powers to powers.
var CharacterPow = characterPowThm{family.Add(registry.ProofEntry{
	Name: "CharacterPow",
	Key:  "prop_b2f7f8d77b749c02",
	Build: family.Theorem(Statement{
		Binders:    "∀q n k:num. ∀χ:(num → complex).",
		Hypotheses: []string{"dirichlet_character(q, χ)"},
		Conclusion: "χ(n ^ k) = χ(n) ^ k",
	}, func(a *Argument, q, n, k *Expr[Nat], χ *Arrow[Nat, Complex], character Fact) {
		a.Induct(k)
		a.Base(
			"zero powers reduce to the character at one",
			Simp(Fwd(nat_arith.NatPow), Fwd(comm_monoid.MonoidPowDef.Inst[Complex]())),
			By(character, CharacterAtOne.At(q, χ)))
		a.Step(
			"multiplicativity carries the extra factor",
			func(b *Argument, ih Fact) {
				b.Do(Simp(Fwd(nat_arith.NatPow), Fwd(comm_monoid.MonoidPowDef.Inst[Complex]())))
				b.Do(By(ih, character, CharacterMul.At(q, n, b.TermAs[Nat]("n ^ k"), χ)))
			})
	}),
})}

// CharacterUnitModulus — at a number coprime to q a Dirichlet character
// has modulus 1, and its φ(q)-th power is 1.
var CharacterUnitModulus = characterUnitModulusThm{family.Add(registry.ProofEntry{
	Name: "CharacterUnitModulus",
	Key:  "prop_a234418597f6d63e",
	Build: family.Theorem(Statement{
		Binders: "∀q n:num. ∀χ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"nat_coprime(n, q)",
		},
		Conclusion: "|χ(n)| = &1 ∧ χ(n) ^ totient(q) = &1",
	}, func(a *Argument, q, n *Expr[Nat], χ *Arrow[Nat, Complex], character, qPositive, coprime Fact) {
		exponent := a.TermAs[Nat]("totient(q)")
		naturalPower := a.TermAs[Nat]("n ^ totient(q)")
		powerOne := a.Have(
			"n^φ(q) ≡ 1 (mod q), so χ(n)^φ(q) = 1",
			"χ(n) ^ totient(q) = &1",
			CalcEq(
				Leg(
					a.TermAs[Complex]("χ(n ^ totient(q))"),
					"χ carries powers to powers",
					By(character, CharacterPow.At(q, n, exponent, χ))),
				Leg(
					a.TermAs[Complex]("χ(1)"),
					"Euler's congruence n^φ(q) ≡ 1 (mod q), and χ takes equal values at congruent numbers",
					By(
						character,
						qPositive,
						coprime,
						units_mod.Euler.At(q, n),
						CharacterCongruent.At(q, naturalPower, a.TermAs[Nat]("1"), χ))),
				FinalLeg(
					"χ is 1 at 1",
					By(character, CharacterAtOne.At(q, χ)))))
		exponentNonzero := a.Have(
			"the totient of the positive modulus is nonzero",
			"totient(q) ≠ 0",
			By(qPositive, totient.TotientPositive.At(q), nat_order.PosIffNonzero.At(exponent)))
		a.Do(SplitConj(
			Case(
				"so χ(n) is a root of unity of nonzero order, which has modulus 1",
				By(powerOne, exponentNonzero, complex_abs.AbsRootOfUnity.At(χ.Apply(n), exponent))),
			Case(
				"the totient-th power is one",
				By(powerOne))))
	}),
})}

// CharacterAbsLessEqOne — a Dirichlet character is bounded by 1.
var CharacterAbsLessEqOne = characterAbsLessEqOneThm{family.Add(registry.ProofEntry{
	Name: "CharacterAbsLessEqOne",
	Key:  "prop_4fe517a22b3306f0",
	Build: family.Theorem(Statement{
		Binders: "∀q n:num. ∀χ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
		},
		Conclusion: "|χ(n)| ≤ &1",
	}, func(a *Argument, q, n *Expr[Nat], χ *Arrow[Nat, Complex], character, qPositive Fact) {
		a.Cases(a.TermAs[Bool]("nat_coprime(n, q)"))
		a.When(
			"at a coprime input the modulus is one",
			func(b *Argument, coprime Fact) {
				b.Do(By(
					Normalized,
					character,
					qPositive,
					coprime,
					CharacterUnitModulus.At(q, n, χ),
					real_order_ring.LessEqRefl.At(b.TermAs[Real]("&1"))))
			})
		a.Otherwise(
			"off the coprime inputs the character vanishes",
			func(b *Argument, notCoprime Fact) {
				b.Do(By(
					notCoprime,
					character,
					CharacterEqZero.At(q, n, χ),
					complex_abs.AbsEqZero.At(χ.Apply(n)),
					real_order_ring.ZeroLessEqOne))
			})
	}),
})}

// PrincipalCharacter — the function that is 1 at the numbers coprime to q
// and 0 elsewhere is a Dirichlet character mod q.
var PrincipalCharacter = principalCharacterThm{family.Add(registry.ProofEntry{
	Name: "PrincipalCharacter",
	Key:  "prop_ebd932cef661fc4e",
	Reading: "This is the principal character mod q, for every " +
		"q: at q = 1 the constant 1, at q = 0 the indicator of 1.",
	Build: family.Theorem(
		"∀q:num. "+
			"    dirichlet_character(q, "+
			"        λn:num. COND(nat_coprime(n, q), complex_of_real(&1), complex_of_real(&0)))",
		func(a *Argument, q *Expr[Nat]) {
			a.Do(Unfold(DirichletCharacterDef), SplitConj(
				Case(
					"the indicator is multiplicative and periodic",
					SplitConj(
						Case(
							"a product is coprime exactly when both factors are",
							Derive(func(b *Argument) {
								m := b.FixAs[Nat]("m")
								n := b.FixAs[Nat]("n")
								b.Do(By(
									Normalized,
									nat_gcd.CoprimeMul.At(m, n, q),
									comm_ring.MulLeftZero.Read(complex_field.CommRing),
									comm_ring.MulRightZero.Read(complex_field.CommRing),
									comm_monoid.RightIdentity.Read(complex_field.MulMonoid).At(b.TermAs[Complex]("&1"))))
							})),
						Case(
							"adding the modulus preserves the remainder and coprimality",
							Derive(func(b *Argument) {
								n := b.FixAs[Nat]("n")
								b.Do(By(
									Normalized,
									nat_div_mod.ModAddModRight.At(n, q, q),
									nat_div_mod.ModRefl.At(q),
									nat_arith.AddZero.At(n),
									nat_gcd.CoprimeLMod.At(b.TermAs[Nat]("n + q"), q),
									nat_gcd.CoprimeLMod.At(n, q)))
							})))),
				Case(
					"only the non-coprime inputs receive zero",
					StripQuant(),
					By(integral_domain.OneNotZero.Read(complex_field.ComplexIntegralDomain)))))
		}),
})}

// CharacterClosure — the product of two Dirichlet characters mod q and the
// conjugate of one are characters mod q.
var CharacterClosure = characterClosureThm{family.Add(registry.ProofEntry{
	Name: "CharacterClosure",
	Key:  "prop_7bbb84cef425f351",
	Reading: "With PrincipalCharacter as the identity and the conjugate as the inverse " +
		"— χ corresponds to a character of the units mod q (CharacterIffGroupCharacter), " +
		"whose conjugate is its inverse (group_character.CharacterConjugateInverse) — the " +
		"characters mod q are a group under the pointwise product.",
	Build: family.Theorem(Statement{
		Binders: "∀q:num. ∀χ ψ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"dirichlet_character(q, ψ)",
		},
		Conclusion: "dirichlet_character(q, λn:num. χ(n) * ψ(n)) ∧ " +
			"dirichlet_character(q, λn:num. conj(χ(n)))",
	}, func(a *Argument, q *Expr[Nat], χ, ψ *Arrow[Nat, Complex], χCharacter, ψCharacter Fact) {
		product := Case(
			"the pointwise product is a character",
			Simp(Fwd(DirichletCharacterDef)),
			SplitConj(
				Case(
					"the product inherits multiplicativity and the period",
					SplitConj(
						Case(
							"the product is completely multiplicative",
							Derive(func(b *Argument) {
								m := b.FixAs[Nat]("m")
								n := b.FixAs[Nat]("n")
								regrouped := b.Have(
									"regroup the two character values at each input",
									"(χ(m) * χ(n)) * (ψ(m) * ψ(n)) = (χ(m) * ψ(m)) * (χ(n) * ψ(n))",
									ByArith())
								b.Do(By(
									χCharacter,
									ψCharacter,
									CharacterMul.At(q, m, n, χ),
									CharacterMul.At(q, m, n, ψ),
									regrouped))
							})),
						Case(
							"both factors have the same period",
							Derive(func(b *Argument) {
								n := b.FixAs[Nat]("n")
								b.Do(By(
									Normalized,
									χCharacter,
									ψCharacter,
									CharacterPeriodic.At(q, n, χ),
									CharacterPeriodic.At(q, n, ψ)))
							})))),
				Case(
					"a product vanishes exactly when one factor vanishes",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.Do(By(
							Normalized,
							χCharacter,
							ψCharacter,
							CharacterEqZero.At(q, n, χ),
							CharacterEqZero.At(q, n, ψ),
							field.MulEqZero.Read(complex_field.Field).At(χ.Apply(n), ψ.Apply(n))))
					}))))
		conjugate := Case(
			"the pointwise conjugate is a character",
			Simp(Fwd(DirichletCharacterDef)),
			SplitConj(
				Case(
					"the conjugate inherits multiplicativity and the period",
					SplitConj(
						Case(
							"conjugation respects multiplication",
							Derive(func(b *Argument) {
								m := b.FixAs[Nat]("m")
								n := b.FixAs[Nat]("n")
								b.Do(By(
									Normalized,
									χCharacter,
									CharacterMul.At(q, m, n, χ),
									complex_field.ConjMul.At(χ.Apply(m), χ.Apply(n))))
							})),
						Case(
							"conjugation preserves the period",
							Derive(func(b *Argument) {
								n := b.FixAs[Nat]("n")
								b.Do(By(Normalized, χCharacter, CharacterPeriodic.At(q, n, χ)))
							})))),
				Case(
					"the conjugate vanishes exactly off the coprime inputs",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.Show(
							"conjugation is an involution fixing zero",
							By(
								χCharacter,
								CharacterEqZero.At(q, n, χ),
								complex_field.ConjConj.At(χ.Apply(n)),
								complex_field.ConjOfReal.At(b.TermAs[Real]("&0"))))
					}))))
		a.Do(SplitConj(product, conjugate))
	}),
})}

// CharacterIffGroupCharacter — the Dirichlet characters mod q are the
// characters of the group of units mod q, read at a number's residue and
// extended by 0 to the numbers not coprime to q.
var CharacterIffGroupCharacter = characterIffGroupCharacterThm{family.Add(registry.ProofEntry{
	Name: "CharacterIffGroupCharacter",
	Key:  "prop_bdcccfdb3f731ba7",
	Reading: "ω is determined by χ — it is χ on the carrier and 0 off it — so the " +
		"correspondence is one to one (ExtensionBijective), which is what carries the " +
		"count and the orthogonality of group characters to Dirichlet characters.",
	Build: family.Sections(Statement{
		Binders:    "∀q:num. ∀χ:(num → complex).",
		Hypotheses: []string{"0 < q"},
		Conclusion: "dirichlet_character(q, χ) ⇔ " +
			"∃ω:(num → complex). " +
			"    group_character(units_mod(q), ω) ∧ " +
			"    χ = (λn:num. COND(nat_coprime(n, q), ω(rem(n, q)), complex_of_real(&0)))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		unitProduct := ctx.Lemma(
			"∀q x y:num. units_mod(q).mul(x, y) = rem(x * y, q)",
			func(a *Argument, q, x, y *Expr[Nat]) {
				a.Show(
					"the group operation multiplies and reduces modulo q",
					By(units_mod.UnitsModDef, group.GroupMulDef.Inst[Nat]()))
			})
		restrict := ctx.Lemma(Statement{
			Binders: "∀q:num. ∀χ:(num → complex).",
			Hypotheses: []string{
				"0 < q",
				"dirichlet_character(q, χ)",
			},
			Conclusion: "group_character(units_mod(q), λn:num. COND(n ∈ units_mod(q).carrier, χ(n), &0))",
		}, func(a *Argument, q *Expr[Nat], χ *Arrow[Nat, Complex], qPositive, character Fact) {
			units := a.TermAs[group.GroupOps[Nat]]("units_mod(q)")
			complexField := a.TermAs[field.FieldOps[Complex]]("complex_field_ops")
			complexUnits := a.TermAs[group.GroupOps[Complex]]("field_units(complex_field_ops)")
			a.Do(Unfold(group_character.GroupCharacterDef), SplitConj(
				Case(
					"the restriction is a homomorphism",
					Unfold(group_homomorphism.GroupHomomorphism),
					SplitConjAll(
						Case(
							"the units mod q form a group",
							By(qPositive, units_mod.AbelianGroupOn.At(q), abelian_group.GroupOn.At(units))),
						Case(
							"ℂ is a field on its carrier, so its nonzero numbers form a multiplicative group",
							By(
								complex_field.FieldOn,
								abelian_group.GroupOn.At(complexUnits),
								roots_of_unity.FieldUnitsAbelianGroupOn.At(complexField))),
						Case(
							"on unit residues the restriction is nonzero",
							Derive(func(b *Argument) {
								x := b.FixAs[Nat]("x")
								member := b.Assume()
								coprime := b.Have(
									"a unit is coprime to the modulus",
									"nat_coprime(x, q)",
									BySets(member))
								nonzero := b.Have(
									"χ is nonzero at this unit",
									"χ(x) ≠ &0",
									By(coprime, character, CharacterEqZero.At(q, x, χ)))
								b.Do(BySets(member, nonzero))
							})),
						Case(
							"reduction modulo q preserves the value at a product",
							Derive(func(b *Argument) {
								x := b.FixAs[Nat]("x")
								y := b.FixAs[Nat]("y")
								members := b.Assume()
								inCarrier := b.Conjuncts(
									members,
									"the first input is a unit",
									"the second input is a unit")
								coprime := b.Have(
									"the product of two units is coprime to the modulus",
									"nat_coprime(x * y, q)",
									BySets(inCarrier[0], inCarrier[1], nat_gcd.CoprimeMul.At(x, y, q)))
								product := b.TermAs[Nat]("x * y")
								residue := b.TermAs[Nat]("rem(x * y, q)")
								productIn := b.Have(
									"the reduced product belongs to the source group",
									"rem(x * y, q) ∈ units_mod(q).carrier",
									By(qPositive, coprime, units_mod.ResidueIn.At(q, product)))
								sameValue := b.Have(
									"χ takes the same value at the product and its residue",
									"χ(rem(x * y, q)) = χ(x * y)",
									By(
										qPositive,
										character,
										nat_congruence.ResidueCongruent.At(product, q),
										CharacterCongruent.At(q, residue, product, χ)))
								b.Do(By(
									Normalized,
									inCarrier[0],
									inCarrier[1],
									productIn,
									sameValue,
									character,
									CharacterMul.At(q, x, y, χ)))
							})))),
				Case(
					"off the unit residues the restriction takes the zero branch",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("x")
						outside := b.Assume()
						b.Do(By(outside))
					}))))
		})
		extend := ctx.Lemma(Statement{
			Binders: "∀q:num. ∀ω:(num → complex).",
			Hypotheses: []string{
				"0 < q",
				"group_character(units_mod(q), ω)",
			},
			Conclusion: "dirichlet_character(q, λn:num. COND(nat_coprime(n, q), ω(rem(n, q)), &0))",
		}, func(a *Argument, q *Expr[Nat], ω *Arrow[Nat, Complex], qPositive, character Fact) {
			units := a.TermAs[group.GroupOps[Nat]]("units_mod(q)")
			complexUnits := a.TermAs[group.GroupOps[Complex]]("field_units(complex_field_ops)")
			characterDef := group_character.GroupCharacterDef.At(units, ω)
			a.Do(Unfold(DirichletCharacterDef), SplitConjAll(
				Case(
					"the extension is completely multiplicative",
					Derive(func(b *Argument) {
						m := b.FixAs[Nat]("m")
						n := b.FixAs[Nat]("n")
						mRem := b.TermAs[Nat]("rem(m, q)")
						nRem := b.TermAs[Nat]("rem(n, q)")
						coprimeProduct := nat_gcd.CoprimeMul.At(m, n, q)
						b.Cases(b.TermAs[Bool]("nat_coprime(m, q) ∧ nat_coprime(n, q)"))
						b.When(
							"when both factors are coprime, use the homomorphism",
							func(c *Argument, coprime Fact) {
								mIn := c.Have(
									"the first residue is a unit",
									"rem(m, q) ∈ units_mod(q).carrier",
									By(qPositive, coprime, units_mod.ResidueIn.At(q, m)))
								nIn := c.Have(
									"the second residue is a unit",
									"rem(n, q) ∈ units_mod(q).carrier",
									By(qPositive, coprime, units_mod.ResidueIn.At(q, n)))
								multiplicative := c.Have(
									"ω multiplies the two unit residues",
									"ω(units_mod(q).mul(rem(m, q), rem(n, q))) = ω(rem(m, q)) * ω(rem(n, q))",
									By(character, mIn, nIn, characterDef, group_character.CharacterMul.At(units, ω, mRem, nRem)))
								c.Do(By(
									coprime,
									coprimeProduct,
									multiplicative,
									At(unitProduct, q, mRem, nRem),
									nat_div_mod.ModMulMod.At(m, n, q)))
							})
						b.Otherwise(
							"if a factor is not coprime, both sides vanish",
							func(c *Argument, outside Fact) {
								left := c.TermAs[Complex]("COND(nat_coprime(m, q), ω(rem(m, q)), &0)")
								right := c.TermAs[Complex]("COND(nat_coprime(n, q), ω(rem(n, q)), &0)")
								c.Do(By(
									outside,
									coprimeProduct,
									comm_ring.MulLeftZero.Read(complex_field.CommRing).At(right),
									comm_ring.MulRightZero.Read(complex_field.CommRing).At(left)))
							})
					})),
				Case(
					"adding the modulus leaves the residue and coprimality unchanged",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						sameResidue := b.Have(
							"the remainder has period q",
							"rem(n + q, q) = rem(n, q)",
							By(
								Normalized,
								nat_div_mod.ModAddModRight.At(n, q, q),
								nat_div_mod.ModRefl.At(q),
								nat_arith.AddZero.At(n)))
						b.Do(By(
							Normalized,
							sameResidue,
							nat_gcd.CoprimeLMod.At(b.TermAs[Nat]("n + q"), q),
							nat_gcd.CoprimeLMod.At(n, q)))
					})),
				Case(
					"the extension vanishes precisely off the coprime inputs",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.Cases(b.TermAs[Bool]("nat_coprime(n, q)"))
						b.When(
							"a unit residue maps into the nonzero complex numbers",
							func(c *Argument, coprime Fact) {
								imageIn := c.Have(
									"the image lies in the target group",
									"ω(rem(n, q)) ∈ field_units(complex_field_ops).carrier",
									By(
										qPositive,
										coprime,
										character,
										units_mod.ResidueIn.At(q, n),
										characterDef,
										group_homomorphism.MapIn.At(units, complexUnits, ω, c.TermAs[Nat]("rem(n, q)"))))
								c.Do(BySets(imageIn))
							})
						b.Otherwise(
							"a non-coprime input takes the zero branch",
							func(c *Argument, outside Fact) {
								c.Do(By(outside))
							})
					}))))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			q *Expr[Nat],
			χ *Arrow[Nat, Complex],
			qPositive Fact,
		) {
			a.Iff()
			a.Forward(
				"restrict χ to the unit residues and recover χ by extension",
				func(b *Argument, character Fact) {
					b.Take(b.TermAs[Fun[Nat, Complex]]("λn:num. COND(n ∈ units_mod(q).carrier, χ(n), &0)"))
					b.Do(SplitConj(
						Case(
							"the restriction is a group character",
							By(qPositive, character, At(restrict, q, χ))),
						Case(
							"the extension agrees with χ at every input",
							Funext(),
							Derive(func(c *Argument) {
								n := c.FixAs[Nat]("n")
								c.Cases(c.TermAs[Bool]("nat_coprime(n, q)"))
								c.When(
									"at a coprime input use the value at its unit residue",
									func(d *Argument, coprime Fact) {
										residue := d.TermAs[Nat]("rem(n, q)")
										member := d.Have(
											"the residue is a unit",
											"rem(n, q) ∈ units_mod(q).carrier",
											By(qPositive, coprime, units_mod.ResidueIn.At(q, n)))
										sameValue := d.Have(
											"χ is constant on the congruence class",
											"χ(rem(n, q)) = χ(n)",
											By(
												qPositive,
												character,
												nat_congruence.ResidueCongruent.At(n, q),
												CharacterCongruent.At(q, residue, n, χ)))
										d.Do(By(coprime, member, sameValue))
									})
								c.Otherwise(
									"at a non-coprime input χ and its extension vanish",
									func(d *Argument, outside Fact) {
										d.Do(By(outside, character, CharacterEqZero.At(q, n, χ)))
									})
							}))))
				})
			a.Backward(
				"the extension of a group character is Dirichlet",
				func(b *Argument, exists Fact) {
					ω, correspondence := b.UnpackAs[Fun[Nat, Complex]](exists, "ω")
					parts := b.Conjuncts(
						correspondence,
						"ω is a group character",
						"χ is its extension")
					b.Do(By(qPositive, parts[0], parts[1], At(extend, q, ω)))
				})
		})
	}),
})}

// ExtensionBijective — extending a character of the units mod q by 0 to
// the numbers not coprime to q is a bijection from the characters of the
// units onto the Dirichlet characters mod q: every Dirichlet character is
// such an extension (CharacterIffGroupCharacter), and an extension keeps
// the character's values on the units, off which every character is 0.
var ExtensionBijective = extensionBijectiveThm{family.Add(registry.ProofEntry{
	Name: "ExtensionBijective",
	Key:  "prop_2844f66249e07e4c",
	Build: family.Theorem(Statement{
		Binders:    "∀q:num.",
		Hypotheses: []string{"0 < q"},
		Conclusion: "image(«extendCharacter», «unitCharacters») = «dirichletCharacters» ∧ " +
			"injective_on(«unitCharacters», «extendCharacter»)",
		Abbrev: Abbrev{
			{Name: "unitCharacters", Text: "{ω:(num → complex) | group_character(units_mod(q), ω)}"},
			{Name: "dirichletCharacters", Text: "{χ:(num → complex) | dirichlet_character(q, χ)}"},
			{Name: "extendCharacter", Text: "λω:(num → complex). λx:num. " +
				"    COND(nat_coprime(x, q), ω(rem(x, q)), &0)"},
		},
	}, func(a *Argument, q *Expr[Nat], qPositive Fact) {
		inputType := TypeBinder.BindA[Fun[Nat, Complex]]()
		outputType := TypeBinder.BindB[Fun[Nat, Complex]]()
		units := a.TermAs[group.GroupOps[Nat]]("units_mod(q)")
		a.Do(SplitConj(
			Case(
				"the Dirichlet characters are exactly the extensions of unit-group characters",
				Simp(
					Fwd(set_basic.Extension.Inst[Fun[Nat, Complex]]()),
					Fwd(set_basic.InImage.Inst(inputType, outputType))),
				Derive(func(b *Argument) {
					χ := b.FixAs[Fun[Nat, Complex]]("χ")
					b.Do(BySets(qPositive, CharacterIffGroupCharacter.At(q, χ)))
				})),
			Case(
				"the extension determines the original character",
				Simp(Fwd(functions.InjectiveOnDef.Inst(inputType, outputType))),
				Derive(func(b *Argument) {
					ω := b.FixAs[Fun[Nat, Complex]]("ω")
					ψ := b.FixAs[Fun[Nat, Complex]]("ψ")
					given := b.Assume()
					b.Do(Funext())
					n := b.FixAs[Nat]("n")
					conditions := b.Conjuncts(
						given,
						"ω belongs to the unit characters",
						"ψ belongs to the unit characters",
						"the two extensions agree")
					ωIn, ψIn, sameExtension := conditions[0], conditions[1], conditions[2]
					b.Cases(b.TermAs[Bool]("n ∈ units_mod(q).carrier"))
					b.When(
						"on a unit residue an extension keeps the original value",
						func(c *Argument, member Fact) {
							unit := c.Have(
								"the unit residue lies below q and is coprime to q",
								"n < q ∧ nat_coprime(n, q)",
								BySets(member))
							c.Do(By(sameExtension, unit, nat_div_mod.ModLessThan.At(n, q)))
						})
					b.Otherwise(
						"off the carrier both group characters vanish",
						func(c *Argument, outside Fact) {
							characters := c.Have(
								"both inputs are group characters",
								"group_character(units_mod(q), ω) ∧ group_character(units_mod(q), ψ)",
								BySets(ωIn, ψIn))
							c.Do(By(
								outside,
								characters,
								group_character.GroupCharacterDef.At(units, ω),
								group_character.GroupCharacterDef.At(units, ψ)))
						})
				}))))
	}),
})}

// CharacterCount — there are φ(q) Dirichlet characters mod q.
var CharacterCount = characterCountThm{family.Add(registry.ProofEntry{
	Name: "CharacterCount",
	Key:  "prop_2cca2dc1005bdee8",
	Build: family.Theorem(Statement{
		Binders:    "∀q:num.",
		Hypotheses: []string{"0 < q"},
		Conclusion: "finite({χ:(num → complex) | dirichlet_character(q, χ)}) ∧ " +
			"card({χ:(num → complex) | dirichlet_character(q, χ)}) = totient(q)",
		Abbrev: Abbrev{
			{Name: "unitCharacters", Text: "{ω:(num → complex) | group_character(units_mod(q), ω)}"},
			{Name: "dirichletCharacters", Text: "{χ:(num → complex) | dirichlet_character(q, χ)}"},
			{Name: "extendCharacter", Text: "λω:(num → complex). λx:num. " +
				"    COND(nat_coprime(x, q), ω(rem(x, q)), &0)"},
		},
	}, func(a *Argument, q *Expr[Nat], qPositive Fact) {
		units := a.TermAs[group.GroupOps[Nat]]("units_mod(q)")
		carrier := a.TermAs[Set[Nat]]("units_mod(q).carrier")
		unitCount := a.TermAs[Nat]("totient(q)")
		carrierSize := a.Have(
			"the group of units has φ(q) elements",
			"finite(units_mod(q).carrier) ∧ card(units_mod(q).carrier) = totient(q)",
			By(units_mod.CarrierHasSize.At(q), cardinality.HasSizeDef.At(carrier, unitCount)))
		unitCharacters := a.TermAs[Set[Fun[Nat, Complex]]]("«unitCharacters»")
		characterSize := a.Have(
			"the finite abelian group has as many characters as elements",
			"has_size(«unitCharacters», totient(q))",
			By(
				qPositive,
				carrierSize,
				units_mod.AbelianGroupOn.At(q),
				group_character.CharacterCount.At(units),
				group_character.CharactersFinite.At(units),
				cardinality.HasSizeDef.At(unitCharacters, unitCount)))
		extend := a.TermAs[Fun[Fun[Nat, Complex], Fun[Nat, Complex]]]("«extendCharacter»")
		dirichletCharacters := a.TermAs[Set[Fun[Nat, Complex]]]("«dirichletCharacters»")
		a.Show(
			"the extension is a bijection onto the Dirichlet characters, so they have the same number",
			By(
				qPositive,
				ExtensionBijective.At(q),
				characterSize,
				cardinality.HasSizeImageInj.At(extend, unitCharacters, unitCount),
				cardinality.HasSizeDef.At(dirichletCharacters, unitCount)))
	}),
})}

// CharacterSumOverResidues — over a period, a Dirichlet character sums to
// φ(q) if it is principal and to 0 otherwise.
var CharacterSumOverResidues = characterSumOverResiduesThm{family.Add(registry.ProofEntry{
	Name: "CharacterSumOverResidues",
	Key:  "prop_feb9eb949f91a878",
	Build: family.Theorem(Statement{
		Binders: "∀q:num. ∀χ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
		},
		Conclusion: "Σ_{n∈«periodResidues»} χ(n) = " +
			"COND(∀n:num. nat_coprime(n, q) ⇒ χ(n) = &1, complex_of_real(&(totient(q))), complex_of_real(&0))",
		Abbrev: Abbrev{
			{Name: "unitResidues", Text: "units_mod(q).carrier"},
			{Name: "periodResidues", Text: "{x:num | x < q}"},
		},
	}, func(a *Argument, q *Expr[Nat], χ *Arrow[Nat, Complex], character, qPositive Fact) {
		ω, correspondence := a.ObtainAs[Fun[Nat, Complex]](
			"take the corresponding character of the units",
			"∃ω:(num → complex). "+
				"    group_character(units_mod(q), ω) ∧ χ = λx:num. COND(nat_coprime(x, q), ω(rem(x, q)), &0)",
			By(qPositive, character, CharacterIffGroupCharacter.At(q, χ)))
		parts := a.Conjuncts(
			correspondence,
			"ω is a character on the units",
			"χ is the extension of ω")
		groupCharacter, extension := parts[0], parts[1]
		units := a.TermAs[group.GroupOps[Nat]]("units_mod(q)")
		carrier := a.TermAs[Set[Nat]]("«unitResidues»")
		period := a.TermAs[Set[Nat]]("«periodResidues»")
		exponent := a.TermAs[Nat]("totient(q)")
		complexAdd := a.TermAs[Op[Complex]]("complex_add")
		unitMembership := a.Have(
			"membership means being a coprime residue",
			"∀x:num. x ∈ «unitResidues» ⇔ x < q ∧ nat_coprime(x, q)",
			StripQuant(),
			BySets())
		coprimeValue := a.Have(
			"at a coprime input the extension uses the group value at its residue",
			"∀x:num. nat_coprime(x, q) ⇒ χ(x) = ω(rem(x, q))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("x")
				coprime := b.Assume()
				b.Do(By(coprime, extension))
			}))
		carrierValues := a.Have(
			"the two characters agree on the unit residues",
			"∀x:num. x ∈ «unitResidues» ⇒ χ(x) = ω(x)",
			Derive(func(b *Argument) {
				x := b.FixAs[Nat]("x")
				inCarrier := b.Assume()
				bounds := b.Have(
					"a unit residue lies below the modulus and is coprime to it",
					"x < q ∧ nat_coprime(x, q)",
					BySets(inCarrier))
				b.Do(By(Normalized, bounds, coprimeValue.At(x), nat_div_mod.ModLessThan.At(x, q)))
			}))
		insidePeriod := a.Have(
			"the units lie in the period",
			"«unitResidues» ⊆ «periodResidues»",
			BySets())
		omitted := a.Have(
			"the omitted summands are the additive identity",
			"∀x:num. x ∈ «periodResidues» ∧ x ∉ «unitResidues» ⇒ χ(x) = neutral_elem(complex_add)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("x")
				outside := b.Assume()
				notCoprime := b.Have(
					"a residue outside the units is not coprime to the modulus",
					"¬nat_coprime(x, q)",
					BySets(outside))
				b.Do(By(notCoprime, extension, comm_ring.NeutralAdd.Read(complex_field.CommRing)))
			}))
		principality := a.Have(
			"being principal is equivalent to being one on the units",
			"(∀x:num. nat_coprime(x, q) ⇒ χ(x) = &1) ⇔ (∀x:num. x ∈ «unitResidues» ⇒ ω(x) = &1)",
			Derive(func(b *Argument) {
				b.Iff()
				b.Forward(
					"principality gives one at each unit residue",
					func(c *Argument, principal Fact) {
						x := c.FixAs[Nat]("x")
						inCarrier := c.Assume()
						c.Do(By(Normalized, inCarrier, unitMembership.At(x), carrierValues.At(x), principal.At(x)))
					})
				b.Backward(
					"the value at each coprime input comes from a unit residue",
					func(c *Argument, trivial Fact) {
						x := c.FixAs[Nat]("x")
						coprime := c.Assume()
						c.Do(By(
							Normalized,
							coprime,
							qPositive,
							coprimeValue.At(x),
							units_mod.ResidueIn.At(q, x),
							trivial.At(c.TermAs[Nat]("rem(x, q)"))))
					})
			}))
		size := a.Have(
			"the group of units is finite of size φ(q)",
			"finite(«unitResidues») ∧ card(«unitResidues») = totient(q)",
			By(units_mod.CarrierHasSize.At(q), cardinality.HasSizeDef.At(carrier, exponent)))
		a.Show(
			"reduce the period sum to the finite group sum",
			CalcEq(
				Leg(
					a.TermAs[Complex]("Σ_{x∈«unitResidues»} χ(x)"),
					"omit the zero summands",
					By(insidePeriod, omitted, monoidal.Superset.At(complexAdd, carrier, period, χ))),
				Leg(
					a.TermAs[Complex]("Σ_{x∈«unitResidues»} ω(x)"),
					"the character values agree on the units",
					By(
						carrierValues,
						comm_ring.MonoidalAdd.Read(complex_field.CommRing),
						monoidal.Congruence.At(complexAdd, carrier, χ, ω))),
				Leg(
					a.TermAs[Complex]("COND(∀x:num. x ∈ «unitResidues» ⇒ ω(x) = &1, "+
						"    complex_of_real(&(card(«unitResidues»))), "+
						"    &0)"),
					"apply the finite group character sum formula",
					By(
						groupCharacter,
						size,
						group_character.GroupCharacterDef.At(units, ω),
						group_character.CharacterSum.At(units, ω))),
				FinalLeg(
					"the two conditions agree and the carrier has size φ(q)",
					By(principality, size))))
	}),
})}

// CharacterPartialSumsBounded — the partial sums of a non-principal
// Dirichlet character mod q are bounded by φ(q): the whole periods in
// 1 .. N sum to 0 and cancel, and the tail left over has at most φ(q)
// terms at numbers coprime to q, each of modulus 1, the others being 0.
var CharacterPartialSumsBounded = characterPartialSumsBoundedThm{family.Add(registry.ProofEntry{
	Name: "CharacterPartialSumsBounded",
	Key:  "prop_f7d39ddffd36b87e",
	Reading: "The third hypothesis says χ is not principal. For " +
		"the principal character the partial sums grow like N·φ(q)/q.",
	Build: family.Sections(Statement{
		Binders: "∀q N:num. ∀χ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ &1",
		},
		Conclusion: "|Σ_{n∈1 .. N} χ(n)| ≤ &(totient(q))",
		Abbrev: Abbrev{
			{Name: "periodResidues", Text: "{x:num | x < q}"},
			{Name: "interior", Text: "1 .. q - 1"},
			{Name: "tail", Text: "1 .. rem(N, q)"},
			{Name: "tailUnits", Text: "(1 .. rem(N, q)) ∩ units_mod(q).carrier"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		monoidalAddition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
		additiveMonoid := abelian_group.Monoid.Read(complex_field.AddGroup)
		neutral := comm_ring.NeutralAdd.Read(complex_field.CommRing)
		concatenate := ctx.Lemma(
			"∀m r:num. ∀f:(num → complex). "+
				"    Σ_{x∈1 .. m + r} f(x) = (Σ_{x∈1 .. m} f(x)) + (Σ_{x∈m + 1 .. m + r} f(x))",
			func(a *Argument, m, r *Expr[Nat], f *Arrow[Nat, Complex]) {
				one := a.TermAs[Nat]("1")
				split := a.TermAs[Nat]("m + 1")
				end := a.TermAs[Nat]("m + r")
				first := a.TermAs[Set[Nat]]("1 .. m")
				last := a.TermAs[Set[Nat]]("m + 1 .. m + r")
				disjoint := a.Have(
					"successive intervals are disjoint",
					"disjoint(1 .. m, m + 1 .. m + r)",
					ByArith(num_segment.Disjoint.At(one, m, split, end)))
				partition := a.Have(
					"the two intervals partition the prefix",
					"1 .. m + r = union(1 .. m, m + 1 .. m + r)",
					ByArith(num_segment.AddSplit.At(one, m, r)))
				add := a.TermAs[Op[Complex]]("complex_add")
				a.Show(
					"sum over the disjoint union",
					By(
						partition,
						disjoint,
						monoidalAddition,
						num_segment.Finite.At(one, m),
						num_segment.Finite.At(split, end),
						monoidal.Union.At(add, first, last, f)))
			})
		translate := ctx.Lemma(Statement{
			Binders:    "∀q k r:num. ∀χ:(num → complex).",
			Hypotheses: []string{"∀x:num. χ(x + q) = χ(x)"},
			Conclusion: "Σ_{x∈k * q + 1 .. k * q + r} χ(x) = Σ_{x∈1 .. r} χ(x)",
		}, func(a *Argument, q, k, r *Expr[Nat], χ *Arrow[Nat, Complex], periodic Fact) {
			unchanged := a.Have(
				"translation by a multiple of the period preserves every summand",
				"∀x:num. 1 ≤ x ∧ x ≤ r ⇒ χ(x + k * q) = χ(x)",
				Derive(func(b *Argument) {
					x := b.FixAs[Nat]("x")
					b.Assume()
					b.Do(By(
						Normalized,
						periodic,
						periodMultiple.At(q, x, k, χ),
						nat_arith.AddSym.At(x, b.TermAs[Nat]("k * q"))))
				}))
			one := a.TermAs[Nat]("1")
			offset := a.TermAs[Nat]("k * q")
			add := a.TermAs[Op[Complex]]("complex_add")
			shiftedValues := a.TermAs[Fun[Nat, Complex]]("λx:num. χ(x + k * q)")
			a.Show(
				"move the interval back by the offset",
				CalcEq(
					Leg(
						a.TermAs[Complex]("Σ_{x∈1 .. r} χ(x + k * q)"),
						"reindex by translation",
						By(
							monoidalAddition,
							monoidal.Shift.At(add, one, r, offset, χ),
							nat_arith.AddSym.At(one, offset),
							nat_arith.AddSym.At(r, offset))),
					FinalLeg(
						"the summands are unchanged",
						By(unchanged, monoidalAddition, monoidal.IntervalCongruence.At(add, one, r, shiftedValues, χ)))))
		})
		fullBlocks := ctx.Lemma(Statement{
			Binders:    "∀q k:num. ∀χ:(num → complex).",
			Hypotheses: []string{"∀x:num. χ(x + q) = χ(x)", "(Σ_{x∈1 .. q} χ(x)) = &0"},
			Conclusion: "(Σ_{x∈1 .. k * q} χ(x)) = &0",
		}, func(
			a *Argument,
			q, k *Expr[Nat],
			χ *Arrow[Nat, Complex],
			periodic, periodZero Fact,
		) {
			add := a.TermAs[Op[Complex]]("complex_add")
			zero := a.TermAs[Complex]("&0")
			a.Induct(k)
			a.Base(
				"zero full periods give the empty sum",
				By(
					monoidalAddition,
					neutral,
					nat_arith.MulLeftZeroClause.At(q),
					nat_arith.OneNotZero,
					monoidal.IntervalClauses.At(add, χ)))
			a.Step(
				"the next full period has zero sum",
				func(b *Argument, previous Fact) {
					b.Do(Simp(Fwd(nat_arith.Mul)))
					end := b.TermAs[Nat]("k * q")
					b.Do(By(
						periodZero,
						previous,
						periodic,
						At(concatenate, end, q, χ),
						At(translate, q, k, q, χ),
						comm_monoid.RightIdentity.Read(additiveMonoid).At(zero)))
				})
		})
		return ctx.Theorem(headline, func(a *Argument, q, N *Expr[Nat], χ *Arrow[Nat, Complex],
			character, qPositive, nonprincipal Fact) {
			zero := a.TermAs[Nat]("0")
			one := a.TermAs[Nat]("1")
			add := a.TermAs[Op[Complex]]("complex_add")
			beforeEnd := a.TermAs[Nat]("q - 1")
			interiorSum := a.TermAs[Complex]("Σ_{x∈«interior»} χ(x)")
			periodResiduesZero := a.Have(
				"a nonprincipal character sums to zero over the residues",
				"Σ_{x∈«periodResidues»} χ(x) = &0",
				By(nonprincipal, qPositive, character, CharacterSumOverResidues.At(q, χ)))
			periodic := a.Have(
				"χ has period q",
				"∀x:num. χ(x + q) = χ(x)",
				By(character, CharacterPeriodic))
			endpoints := a.Have(
				"the period endpoints have the same character value",
				"χ(q) = χ(0)",
				By(Normalized, periodic.At(zero), nat_arith.AddLeftZeroClause.At(q)))
			leftPeel := a.Have(
				"the residue sum consists of the value at zero and the interior sum",
				"Σ_{x∈«periodResidues»} χ(x) = χ(0) + Σ_{x∈«interior»} χ(x)",
				By(
					qPositive,
					monoidalAddition,
					nat_order.PosIffNonzero.At(q),
					num_segment.BelowStrict.At(q),
					nat_order.ZeroLessEq.At(beforeEnd),
					monoidal.PeelLeft.At(add, zero, beforeEnd, χ),
					nat_arith.AddLeftZeroClause.At(one)))
			periodZero := a.Have(
				"replacing the zero endpoint by the modulus preserves the period sum",
				"Σ_{x∈1 .. q} χ(x) = &0",
				By(
					qPositive,
					endpoints,
					leftPeel,
					periodResiduesZero,
					monoidalAddition,
					nat_order.PosIffNonzero.At(q),
					nat_order.OneLessEqIffNonzero.At(q),
					monoidal.PeelRight.At(add, q, one, χ),
					comm_monoid.Comm.Read(additiveMonoid).At(χ.Apply(zero), interiorSum)))
			quotient := a.TermAs[Nat]("div(N, q)")
			remainder := a.TermAs[Nat]("rem(N, q)")
			blockEnd := a.TermAs[Nat]("div(N, q) * q")
			division := a.Have(
				"division writes N as full periods followed by a shorter tail",
				"N = div(N, q) * q + rem(N, q) ∧ rem(N, q) < q",
				By(qPositive, nat_order.PosIffNonzero.At(q), nat_div_mod.Division.At(N, q)))
			tailSum := a.TermAs[Complex]("Σ_{x∈«tail»} χ(x)")
			reduced := a.Have(
				"discard the full periods and bring the tail back to its residues",
				"Σ_{x∈1 .. N} χ(x) = Σ_{x∈«tail»} χ(x)",
				By(
					periodZero,
					periodic,
					division,
					At(concatenate, blockEnd, remainder, χ),
					At(translate, q, quotient, remainder, χ),
					At(fullBlocks, q, quotient, χ),
					comm_monoid.LeftIdentity.Read(additiveMonoid).At(tailSum)))
			units := a.TermAs[Set[Nat]]("units_mod(q).carrier")
			tail := a.TermAs[Set[Nat]]("«tail»")
			support := a.TermAs[Set[Nat]]("«tailUnits»")
			unitCount := a.TermAs[Nat]("totient(q)")
			subsets := a.Have(
				"the tail units belong to the tail and to the full group of units",
				"«tailUnits» ⊆ «tail» ∧ «tailUnits» ⊆ units_mod(q).carrier",
				BySets())
			size := a.Have(
				"the tail has at most φ(q) unit residues",
				"finite(«tailUnits») ∧ card(«tailUnits») ≤ totient(q)",
				By(
					subsets,
					units_mod.CarrierHasSize.At(q),
					cardinality.HasSizeDef.At(units, unitCount),
					finite_set.FiniteSubset.At(support, units),
					cardinality.CardSubset.At(support, units)))
			omitted := a.Have(
				"the omitted terms contribute the additive identity",
				"∀x:num. x ∈ «tail» ∧ x ∉ «tailUnits» ⇒ χ(x) = neutral_elem(complex_add)",
				Derive(func(b *Argument) {
					x := b.FixAs[Nat]("x")
					outside := b.Assume()
					below := b.Have(
						"the tail residue lies below the modulus",
						"x < q",
						ByArith(division, outside, num_segment.Membership.At(x, one, remainder)))
					notCoprime := b.Have(
						"an omitted residue is not a unit",
						"¬nat_coprime(x, q)",
						BySets(below, outside))
					b.Do(By(notCoprime, character, CharacterEqZero.At(q, x, χ), neutral))
				}))
			restricted := a.Have(
				"only the unit summands remain",
				"Σ_{x∈«tail»} χ(x) = Σ_{x∈«tailUnits»} χ(x)",
				By(subsets, omitted, monoidal.Superset.At(add, support, tail, χ)))
			modulusOne := a.Have(
				"each remaining summand has modulus one",
				"∀x:num. x ∈ «tailUnits» ⇒ |χ(x)| = &1",
				Derive(func(b *Argument) {
					x := b.FixAs[Nat]("x")
					member := b.Assume()
					coprime := b.Have(
						"the unit residue is coprime to the modulus",
						"nat_coprime(x, q)",
						BySets(member))
					b.Do(By(qPositive, coprime, character, CharacterUnitModulus.At(q, x, χ)))
				}))
			absValues := a.TermAs[Fun[Nat, Real]]("λx:num. |χ(x)|")
			unitValue := a.TermAs[Fun[Nat, Real]]("λx:num. &1")
			moduliSum := a.Have(
				"summing the moduli counts the unit residues",
				"Σ_{x∈«tailUnits»} |χ(x)| = &(card(«tailUnits»))",
				By(
					modulusOne,
					size,
					real_sum.Congruence.At(support, absValues, unitValue),
					real_sum.CardAsSum.At(support)))
			triangle := a.Have(
				"the triangle inequality bounds the sum by the number of unit residues",
				"|Σ_{x∈«tailUnits»} χ(x)| ≤ &(card(«tailUnits»))",
				By(size, moduliSum, complex_series.AbsSumLessEq.At(support, χ)))
			count := a.TermAs[Nat]("card(«tailUnits»)")
			a.Show(
				"the cardinality bound gives the partial sum estimate",
				By(
					reduced,
					restricted,
					triangle,
					size,
					real_construction.OfNumLessEq.At(count, unitCount),
					real_construction.LessEqTrans.At(
						a.TermAs[Real]("|Σ_{x∈«tailUnits»} χ(x)|"), a.TermAs[Real]("&(card(«tailUnits»))"),
						a.TermAs[Real]("&(totient(q))"))))
		})
	}),
})}

// CharacterOrthogonality — over the Dirichlet characters mod q, the values
// conj(χ(a))·χ(n) add up to φ(q) when n ≡ a mod q and to 0 otherwise, for
// a coprime to q: for n coprime to q the sum is reindexed over the
// characters ω of the units mod q, where the summand is ω(a⁻¹n), and the
// second orthogonality relation of the units decides it; otherwise every
// χ(n) is 0.
var CharacterOrthogonality = characterOrthogonalityThm{family.Add(registry.ProofEntry{
	Name: "CharacterOrthogonality",
	Key:  "prop_f25437c17a50a361",
	Reading: "This is the relation that picks one residue class out of a " +
		"sum over all numbers; a must be coprime to q, or every conj(χ(a)) is 0.",
	Build: family.Theorem(Statement{
		Binders: "∀q a n:num.",
		Hypotheses: []string{
			"0 < q",
			"nat_coprime(a, q)",
		},
		Conclusion: "Σ_{χ∈{χ:(num → complex) | dirichlet_character(q, χ)}} conj(χ(a)) * χ(n) = " +
			"COND(n ≡ a (mod q), complex_of_real(&(totient(q))), complex_of_real(&0))",
		Abbrev: Abbrev{
			{Name: "unitCharacters", Text: "{ω:(num → complex) | group_character(units_mod(q), ω)}"},
			{Name: "dirichletCharacters", Text: "{χ:(num → complex) | dirichlet_character(q, χ)}"},
			{Name: "extendCharacter", Text: "λω:(num → complex). λx:num. " +
				"    COND(nat_coprime(x, q), ω(rem(x, q)), &0)"},
			{Name: "dirichletSummand", Text: "λχ:(num → complex). conj(χ(a)) * χ(n)"},
			{Name: "unitOffset", Text: "units_mod(q).mul(units_mod(q).inv(rem(a, q)), rem(n, q))"},
			{Name: "unitSummand", Text: "λω:(num → complex). ω(«unitOffset»)"},
			{Name: "extendedSummand", Text: "λω:(num → complex). " +
				"    conj(«extendCharacter»(ω)(a)) * «extendCharacter»(ω)(n)"},
		},
	}, func(arg *Argument, q, a, n *Expr[Nat], qPositive, aCoprime Fact) {
		// The Argument is arg: the statement binds a.
		monoidalAddition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
		neutral := comm_ring.NeutralAdd.Read(complex_field.CommRing)
		groupUnits := arg.TermAs[group.GroupOps[Nat]]("units_mod(q)")
		aRem := arg.TermAs[Nat]("rem(a, q)")
		nRem := arg.TermAs[Nat]("rem(n, q)")
		complexAdd := arg.TermAs[Op[Complex]]("complex_add")
		dirichletCharacters := arg.TermAs[Set[Fun[Nat, Complex]]]("«dirichletCharacters»")
		dirichletSummand := arg.TermAs[Fun[Fun[Nat, Complex], Complex]]("«dirichletSummand»")
		arg.Cases(arg.TermAs[Bool]("nat_coprime(n, q)"))
		arg.When(
			"when n is a unit modulo q, sum over the characters of the unit group",
			func(b *Argument, nCoprime Fact) {
				groupOn := b.Have(
					"the units modulo q form a group",
					"group_on(units_mod(q))",
					By(qPositive, units_mod.AbelianGroupOn.At(q), abelian_group.GroupOn.At(groupUnits)))
				carrier := b.TermAs[Set[Nat]]("units_mod(q).carrier")
				size := b.Have(
					"the unit group has φ(q) elements",
					"finite(units_mod(q).carrier) ∧ card(units_mod(q).carrier) = totient(q)",
					By(units_mod.CarrierHasSize.At(q), cardinality.HasSizeDef.At(carrier, b.TermAs[Nat]("totient(q)"))))
				aIn := b.Have(
					"the residue of a is a unit",
					"rem(a, q) ∈ units_mod(q).carrier",
					By(qPositive, aCoprime, units_mod.ResidueIn.At(q, a)))
				nIn := b.Have(
					"the residue of n is a unit",
					"rem(n, q) ∈ units_mod(q).carrier",
					By(qPositive, nCoprime, units_mod.ResidueIn.At(q, n)))
				aInverse := b.TermAs[Nat]("units_mod(q).inv(rem(a, q))")
				inverseIn := b.Have(
					"the inverse of the first residue is a unit",
					"units_mod(q).inv(rem(a, q)) ∈ units_mod(q).carrier",
					By(groupOn, aIn, group.InvIn.At(groupUnits, aRem)))
				offset := b.TermAs[Nat]("«unitOffset»")
				offsetIn := b.Have(
					"the inverse of the first residue times the second lies in the carrier",
					"«unitOffset» ∈ units_mod(q).carrier",
					By(groupOn, inverseIn, nIn, group.MulIn.At(groupUnits, aInverse, nRem)))
				offsetIdentity := b.Have(
					"the offset is the identity exactly when the two residues agree",
					"«unitOffset» = units_mod(q).one ⇔ n ≡ a (mod q)",
					By(
						groupOn,
						aIn,
						nIn,
						group.InvMulEqOneOn.At(groupUnits, aRem, nRem),
						nat_congruence.CongDef.At(n, a, q)))
				unitCharacters := b.TermAs[Set[Fun[Nat, Complex]]]("«unitCharacters»")
				extension := b.TermAs[Fun[Fun[Nat, Complex], Fun[Nat, Complex]]]("«extendCharacter»")
				extendedSummand := b.TermAs[Fun[Fun[Nat, Complex], Complex]]("«extendedSummand»")
				unitSummand := b.TermAs[Fun[Fun[Nat, Complex], Complex]]("«unitSummand»")
				sumOnImage := b.Have(
					"reindex the sum along the injective extension",
					"Σ_{χ∈image(«extendCharacter», «unitCharacters»)} conj(χ(a)) * χ(n) = "+
						"iterated_op(complex_add, «unitCharacters», o(«dirichletSummand», «extendCharacter»))",
					By(
						qPositive,
						ExtensionBijective.At(q),
						monoidalAddition,
						monoidal.Image.At(complexAdd, extension, dirichletSummand, unitCharacters)))
				composed := b.Have(
					"the composed summand evaluates the extended character",
					"o(«dirichletSummand», «extendCharacter») = «extendedSummand»",
					Unfold(functions.ComposeApply))
				agree := b.Have(
					"each summand is the group character evaluated at the offset",
					"∀ω:(num → complex). ω ∈ «unitCharacters» ⇒ «extendedSummand»(ω) = «unitSummand»(ω)",
					Derive(func(c *Argument) {
						ω := c.FixAs[Fun[Nat, Complex]]("ω")
						member := c.Assume()
						character := c.Have(
							"ω is a group character",
							"group_character(units_mod(q), ω)",
							BySets(member))
						hom := c.Have(
							"ω is a homomorphism into the nonzero complex numbers",
							"group_homomorphism(units_mod(q), field_units(complex_field_ops), ω)",
							By(character, group_character.GroupCharacterDef.At(groupUnits, ω)))
						c.Show(
							"ω sends the offset to ω(a⁻¹)·ω(n), and ω(a⁻¹) is the conjugate of ω(a)",
							By(
								size,
								aCoprime,
								nCoprime,
								aIn,
								nIn,
								inverseIn,
								hom,
								group_character.CharacterConjugateInverse.At(groupUnits, ω, aRem),
								group_character.CharacterMul.At(groupUnits, ω, aInverse, nRem)))
					}))
				count := b.Have(
					"there are φ(q) unit-group characters",
					"card(«unitCharacters») = totient(q)",
					By(qPositive, size, units_mod.AbelianGroupOn.At(q), group_character.CharacterCount.At(groupUnits)))
				b.Show(
					"evaluate the sum over the characters of the unit group",
					CalcEq(
						Leg(
							b.TermAs[Complex]("Σ_{ω∈«unitCharacters»} conj(«extendCharacter»(ω)(a)) * «extendCharacter»(ω)(n)"),
							"replace Dirichlet characters by extensions of group characters",
							By(qPositive, ExtensionBijective.At(q), sumOnImage, composed)),
						Leg(
							b.TermAs[Complex]("Σ_{ω∈«unitCharacters»} ω(«unitOffset»)"),
							"replace each summand by its group value at the offset",
							By(
								agree,
								monoidalAddition,
								monoidal.Congruence.At(complexAdd, unitCharacters, extendedSummand, unitSummand))),
						Leg(
							b.TermAs[Complex](
								"COND(«unitOffset» = units_mod(q).one, complex_of_real(&(card(«unitCharacters»))), &0)"),
							"sum the group characters at the offset",
							By(
								qPositive,
								size,
								offsetIn,
								units_mod.AbelianGroupOn.At(q),
								group_character.CharacterSumOverCharacters.At(groupUnits, offset))),
						FinalLeg(
							"use the congruence condition and the character count",
							By(offsetIdentity, count))))
			})
		arg.Otherwise(
			"when n is outside the units, all summands vanish",
			func(b *Argument, nNotCoprime Fact) {
				notCongruent := b.Have(
					"congruent inputs have the same coprimality",
					"¬(n ≡ a (mod q))",
					By(
						Normalized,
						aCoprime,
						nNotCoprime,
						nat_congruence.CongDef.At(n, a, q),
						nat_gcd.CoprimeLMod.At(n, q),
						nat_gcd.CoprimeLMod.At(a, q)))
				summandsZero := b.Have(
					"each character vanishes at n",
					"∀χ:(num → complex). χ ∈ «dirichletCharacters» ⇒ «dirichletSummand»(χ) = neutral_elem(complex_add)",
					Derive(func(c *Argument) {
						χ := c.FixAs[Fun[Nat, Complex]]("χ")
						member := c.Assume()
						zero := c.Have(
							"a Dirichlet character is zero off the coprime inputs",
							"χ(n) = &0",
							BySets(nNotCoprime, member, CharacterEqZero.At(q, n, χ)))
						c.Do(By(
							Normalized,
							zero,
							neutral,
							comm_ring.MulRightZero.Read(complex_field.CommRing).At(c.TermAs[Complex]("conj(χ(a))"))))
					}))
				sumZero := b.Have(
					"the sum of these zero summands is zero",
					"Σ_{χ∈«dirichletCharacters»} conj(χ(a)) * χ(n) = neutral_elem(complex_add)",
					By(
						summandsZero,
						monoidalAddition,
						monoidal.EqNeutral.At(complexAdd, dirichletCharacters, dirichletSummand)))
				b.Do(By(notCongruent, sumZero, neutral))
			})
	}),
})}

// RealCharacterValues — a real-valued Dirichlet character takes only the
// values 0, 1 and −1.
var RealCharacterValues = realCharacterValuesThm{family.Add(registry.ProofEntry{
	Name: "RealCharacterValues",
	Key:  "prop_21f74a273ee19472",
	Build: family.Theorem(Statement{
		Binders: "∀q n:num. ∀χ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"0 < q",
			"∀m:num. im(χ(m)) = &0",
		},
		Conclusion: "χ(n) = &0 ∨ χ(n) = &1 ∨ χ(n) = -&1",
	}, func(
		a *Argument,
		q, n *Expr[Nat],
		χ *Arrow[Nat, Complex],
		character, qPositive, realValued Fact,
	) {
		a.Cases(a.TermAs[Bool]("nat_coprime(n, q)"))
		a.When(
			"at a coprime input the real value has modulus one",
			func(b *Argument, coprime Fact) {
				value := χ.Apply(n)
				realPart := b.TermAs[Real]("re(χ(n))")
				embedded := b.TermAs[Complex]("complex_of_real(re(χ(n)))")
				asReal := b.Have(
					"zero imaginary part identifies the value with its embedded real part",
					"χ(n) = complex_of_real(re(χ(n)))",
					By(
						realValued.At(n),
						complex_field.ComplexEq.At(value, embedded),
						complex_field.PartsOfReal.At(realPart)))
				absOne := b.Have(
					"the real part has absolute value one",
					"|re(χ(n))| = &1",
					By(
						Normalized,
						character,
						qPositive,
						coprime,
						asReal,
						CharacterUnitModulus.At(q, n, χ),
						complex_abs.AbsOfReal.At(realPart)))
				one := b.TermAs[Real]("&1")
				b.Show(
					"absolute value one leaves the two signs",
					By(
						asReal,
						absOne,
						real_sgn_abs.RealAbsDef.At(realPart),
						real_ring.NegEq.At(realPart, one),
						complex_field.OfRealNeg.At(one)))
			})
		a.Otherwise(
			"off the coprime inputs the character vanishes",
			func(b *Argument, notCoprime Fact) {
				b.Do(By(notCoprime, character, CharacterEqZero.At(q, n, χ)))
			})
	}),
})}

// NonRealCharacterSquare — the square of a Dirichlet character that is
// not real-valued is not principal.
var NonRealCharacterSquare = nonRealCharacterSquareThm{family.Add(registry.ProofEntry{
	Name: "NonRealCharacterSquare",
	Key:  "prop_3e59673eb535f71f",
	Reading: "This is what the 3-4-1 inequality needs of a " +
		"non-real character: the L-series of its square converges at 1.",
	Build: family.Theorem(Statement{
		Binders: "∀q:num. ∀χ:(num → complex).",
		Hypotheses: []string{
			"dirichlet_character(q, χ)",
			"∃n:num. im(χ(n)) ≠ &0",
		},
		Conclusion: "∃n:num. nat_coprime(n, q) ∧ χ(n) * χ(n) ≠ &1",
	}, func(a *Argument, q *Expr[Nat], χ *Arrow[Nat, Complex], character, nonreal Fact) {
		n, imNonzero := a.UnpackAs[Nat](nonreal, "n")
		a.Take(n)
		a.Do(SplitConj(
			Case(
				"a nonzero imaginary part forces coprimality",
				By(
					Normalized,
					imNonzero,
					character,
					CharacterEqZero.At(q, n, χ),
					complex_field.PartsOfReal.At(a.TermAs[Real]("&0")))),
			Case(
				"a square of one would force a real value",
				Derive(func(b *Argument) {
					squareIsOne := b.SupposeNot()
					factorProduct := b.Have(
						"the difference of squares factors to zero",
						"(χ(n) - &1) * (χ(n) + &1) = &0",
						ByArith(squareIsOne))
					roots := b.Have(
						"one factor vanishes, so χ(n) is 1 or −1",
						"χ(n) = &1 ∨ χ(n) = -&1",
						ByArith(factorProduct))
					one := b.TermAs[Real]("&1")
					b.Show(
						"both roots have zero imaginary part",
						By(
							Normalized,
							imNonzero,
							roots,
							complex_field.PartsOfReal.At(one),
							complex_field.PartsOfReal.At(b.TermAs[Real]("-&1")),
							complex_field.OfRealNeg.At(one)))
				}))))
	}),
})}
