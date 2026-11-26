// monomials.go — facts about monomials: a monomial of S is nonzero at
// finitely many variables, all of them in S, and so a monomial of every set
// containing S; the monomial of a variable is one at that variable and zero
// elsewhere, and a monomial of S when the variable lies in S; lowering an
// exponent by at most itself and raising it again gives the monomial back;
// two monomials of S add to a monomial of S; a finitely supported monomial
// has finitely many monomials below it, over which a double sum may be
// regrouped; and the monomials of degree d in the variables 0, …, n number
// binomial(d + n, n).

package polynomial_algebra

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/binomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The variables of a monomial
// ---------------------------------------------------------------------------

// MonomialsMember — an exponent function is a monomial of S exactly when
// it is nonzero at finitely many variables, all of them in S: the
// membership law of monomials(S), as function_module.FiniteSuppMember is
// the free module's.
var MonomialsMember = monomialsMemberThm{family.Add(registry.ProofEntry{
	Name: "MonomialsMember",
	Key:  "prop_5d9cbe823e0e43cd",
	Build: family.Theorem("∀S:set(D). ∀m:(D → num). "+
		"    m ∈ monomials(S) ⇔ finite(fun_support(0, m)) ∧ fun_support(0, m) ⊆ S",
		func(a *Argument, S *Expr[Set[D]], m *Arrow[D, Nat]) {
			a.Show(
				"m is nonzero only at members of S exactly when every variable where it is nonzero lies in S",
				Simp(Fwd(MonomialsDef), Fwd(function_module.FiniteSupportDef)),
				BySets())
		}),
})}

// MonomialSupport — a monomial of S is nonzero at finitely many variables,
// all of them in S: the two conditions of monomials(S), read off
// MonomialsMember.
var MonomialSupport = monomialSupportThm{family.Add(registry.ProofEntry{
	Name: "MonomialSupport",
	Key:  "prop_2e435da052fb10e9",
	Build: family.Theorem(Statement{
		Binders:    "∀S:set(D). ∀m:(D → num).",
		Hypotheses: []string{"m ∈ monomials(S)"},
		Conclusion: "finite(fun_support(0, m)) ∧ (∀y:D. m(y) ≠ 0 ⇒ y ∈ S)",
	},
		func(a *Argument, S *Expr[Set[D]], m *Arrow[D, Nat], monomial Fact) {
			a.Show(
				"m is finitely supported and nonzero only at members of S",
				BySets(monomial, MonomialsMember))
		}),
})}

// MonomialsSubset — more variables, more monomials: a monomial of S is
// nonzero only at variables of S, so only at variables of any T that
// contains S, and its support stays finite.
var MonomialsSubset = monomialsSubsetThm{family.Add(registry.ProofEntry{
	Name: "MonomialsSubset",
	Key:  "prop_d7e5c405eb6530d7",
	Build: family.Theorem(Statement{
		Binders:    "∀S T:set(D).",
		Hypotheses: []string{"S ⊆ T"},
		Conclusion: "monomials(S) ⊆ monomials(T)",
	},
		func(a *Argument, S, T *Expr[Set[D]], sub Fact) {
			a.Show(
				"an exponent function nonzero only at variables of S is nonzero only at variables of T",
				Simp(Fwd(MonomialsDef)),
				BySets(sub))
		}),
})}

// ---------------------------------------------------------------------------
// The monomial of a variable
// ---------------------------------------------------------------------------

// MonomialVarValues — the monomial of x has exponent one at x and zero
// at every other variable: it is the delta at x with values 1 and 0.
var MonomialVarValues = monomialVarValuesThm{family.Add(registry.ProofEntry{
	Name: "MonomialVarValues",
	Key:  "prop_b37088bd98c22822",
	Build: family.Theorem("∀x:D. monomial_var(x, x) = 1 ∧ (∀y:D. y ≠ x ⇒ monomial_var(x, y) = 0)",
		func(a *Argument, x *Expr[D]) {
			// Unfolded, the exponent at x is COND(x = x, 1, 0), which is 1.
			a.Do(Unfold(MonomialVarDef), Unfold(free_module.DeltaAtDef))
			a.FixAs[D]("y")
			other := a.Assume()
			a.Show(
				"the delta at x is 0 at a variable other than x",
				By(other))
		}),
})}

// MonomialVarIn — the monomial of a variable x of S is a monomial of S: it
// is nonzero at x alone, so its variables lie in the finite set {x}, inside
// S.
var MonomialVarIn = monomialVarInThm{family.Add(registry.ProofEntry{
	Name: "MonomialVarIn",
	Key:  "prop_3ac02252f2efade",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(D). ∀x:D.",
		Hypotheses: []string{
			"x ∈ S",
		},
		Conclusion: "monomial_var(x) ∈ monomials(S)",
	},
		func(a *Argument, S *Expr[Set[D]], x *Expr[D], xIn Fact) {
			a.Show(
				"the monomial of x is nonzero at x alone, so its variables are finitely many, all in S",
				BySets(
					xIn,
					MonomialsMember.At(S, a.TermAs[Fun[D, Nat]]("monomial_var(x)")),
					MonomialVarValues.At(x),
					finite_set.FiniteSing.At(x),
					finite_set.FiniteSubset.At(
						a.TermAs[Set[D]]("fun_support(0, λy:D. monomial_var(x, y))"), a.TermAs[Set[D]]("{x}"))))
		}),
})}

// MonomialLowerRaise — lowering the exponent of m at x by c and raising it
// again restores m when c ≤ m(x): at x the exponent is m(x) − c + c, and at
// every other variable c times the monomial of x is zero.
var MonomialLowerRaise = monomialLowerRaiseThm{family.Add(registry.ProofEntry{
	Name: "MonomialLowerRaise",
	Key:  "prop_190da45039c1c536",
	Build: family.Theorem(Statement{
		Binders:    "∀m:(D → num). ∀x:D. ∀c:num.",
		Hypotheses: []string{"c ≤ m(x)"},
		Conclusion: "(λy:D. m(y) - c * monomial_var(x, y) + c * monomial_var(x, y)) = m",
	},
		func(a *Argument, m *Arrow[D, Nat], x *Expr[D], c *Expr[Nat], bounded Fact) {
			a.Do(Funext())
			a.FixAs[D]("y")
			a.Cases(a.TermAs[Bool]("y = x"))
			a.When(
				"at x at most the exponent m(x) is taken",
				func(b *Argument, same Fact) {
					b.Do(same.Rw())
					b.Show(
						"so m(x) − c + c = m(x)",
						ByArith(bounded, MonomialVarValues.At(x)))
				})
			a.Otherwise(
				"elsewhere nothing is taken or given",
				func(b *Argument, other Fact) {
					vanishes := b.Have(
						"the monomial of x is zero at y",
						"monomial_var(x, y) = 0",
						By(other, MonomialVarValues.At(x)))
					b.Show(
						"so the exponent is m(y)",
						ByArith(vanishes))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Sums of monomials, and the monomials below a monomial
// ---------------------------------------------------------------------------

// MonomialAddIn — the sum of two monomials of S is a monomial of S: its
// exponent at a variable is nonzero exactly where one of the two is, so
// its variables are the union of theirs, finitely many and all in S.
var MonomialAddIn = monomialAddInThm{family.Add(registry.ProofEntry{
	Name: "MonomialAddIn",
	Key:  "prop_e132b7dbf30280f5",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(D). ∀m₁ m₂:(D → num).",
		Hypotheses: []string{
			"m₁ ∈ monomials(S)",
			"m₂ ∈ monomials(S)",
		},
		Conclusion: "(λx:D. m₁(x) + m₂(x)) ∈ monomials(S)",
	},
		func(a *Argument, S *Expr[Set[D]], m1, m2 *Arrow[D, Nat], first, second Fact) {
			supports := a.Have(
				"m₁ and m₂ are nonzero at finitely many variables, all of them in S",
				"finite(fun_support(0, m₁)) ∧ "+
					"fun_support(0, m₁) ⊆ S ∧ "+
					"finite(fun_support(0, m₂)) ∧ "+
					"fun_support(0, m₂) ⊆ S",
				By(first, second, MonomialsMember.At(S, m1), MonomialsMember.At(S, m2)))
			exponents := a.Have(
				"an exponent of m₁ + m₂ is nonzero exactly where one of m₁, m₂ is",
				"∀x:D. m₁(x) + m₂(x) ≠ 0 ⇔ m₁(x) ≠ 0 ∨ m₂(x) ≠ 0",
				ByArith())
			union := a.Have(
				"so the variables of m₁ + m₂ are those of m₁ together with those of m₂",
				"fun_support(0, λx:D. m₁(x) + m₂(x)) = fun_support(0, m₁) ∪ fun_support(0, m₂)",
				BySets(exponents))
			support1, support2 := a.TermAs[Set[D]]("fun_support(0, m₁)"), a.TermAs[Set[D]]("fun_support(0, m₂)")
			a.Show(
				"finitely many, as a union of two finite sets, and all of them in S",
				Simp(Fwd(MonomialsMember)),
				By(
					union,
					supports,
					finite_set.FiniteUnionImp.At(support1, support2),
					set_order.UnionSubset.At(support1, support2, S)))
		}),
})}

// MonomialsBelowFinite — a finitely supported monomial has finitely many
// monomials below it, exponent by exponent: the exponents of m are
// bounded by some n, and a monomial below m is a map from the support of
// m into 0 .. n, zero off the support, of which there are finitely many.
var MonomialsBelowFinite = monomialsBelowFiniteThm{family.Add(registry.ProofEntry{
	Name: "MonomialsBelowFinite",
	Key:  "prop_c85d1ed0a5353283",
	Build: family.Theorem(Statement{
		Binders:    "∀m:(D → num).",
		Hypotheses: []string{"finite_support(0, m)"},
		Conclusion: "finite(«below»)",
		Abbrev: Abbrev{
			{Name: "maps", Text: "{h:(D → num) | " +
				"    (∀x:D. x ∈ fun_support(0, m) ⇒ h(x) ∈ 0 .. n) ∧ (∀x:D. x ∉ fun_support(0, m) ⇒ h(x) = 0)}"},
		},
	},
		func(a *Argument, m *Arrow[D, Nat], finiteSupport Fact) {
			zero := a.TermAs[Nat]("0")
			support := a.TermAs[Set[D]]("fun_support(0, m)")
			supportFinite := a.Have(
				"m is nonzero at finitely many variables",
				"finite(fun_support(0, m))",
				By(finiteSupport, function_module.FiniteSupportDef))
			n, bounded := a.ObtainAs[Nat](
				"the exponents of m have a common bound n",
				"∃n:num. ∀x:D. m(x) ≤ n",
				Derive(func(b *Argument) {
					n, imageBounded := b.ObtainAs[Nat](
						"the finitely many values of m on its support lie in some 0 .. n",
						"∃n:num. image(m, fun_support(0, m)) ⊆ 0 .. n",
						By(supportFinite, num_segment.FiniteIffBounded, finite_set.FiniteImage))
					b.Take(n)
					b.FixAs[D]("x")
					onSupport := b.Have(
						"a nonzero exponent of m is a value of m on its support",
						"m(x) ≠ 0 ⇒ m(x) ∈ 0 .. n",
						BySets(imageBounded))
					b.Show(
						"so every exponent of m, the zero ones too, is at most n",
						By(Normalized, onSupport, nat_order.ZeroLessEq.At(n)))
				}))
			pointwise := a.Have(
				"an exponent below m is at most n, and zero where m is",
				"∀h:(D → num). ∀x:D. h(x) ≤ m(x) ⇒ h(x) ≤ n ∧ (m(x) = 0 ⇒ h(x) = 0)",
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("h")
					x := b.FixAs[D]("x")
					b.Show(
						"by the bound on m(x)",
						ByArith(bounded.At(x), b.Assume()))
				}))
			maps := a.TermAs[Set[Fun[D, Nat]]]("«maps»")
			below := a.Have(
				"so a monomial below m maps the support of m into 0 .. n and is zero off it",
				"«below» ⊆ «maps»",
				BySets(pointwise, nat_order.ZeroLessEq))
			mapsFinite := a.Have(
				"the maps from the finite support into the finite 0 .. n, zero off the support, are finitely many",
				"finite(«maps»)",
				By(
					supportFinite,
					cardinality.FiniteFunspace.At(support, a.TermAs[Set[Nat]]("0 .. n"), zero),
					num_segment.Finite.At(zero, n)))
			a.Show(
				"and so are the monomials below m",
				By(mapsFinite, below, finite_set.FiniteSubset.At(a.TermAs[Set[Fun[D, Nat]]]("«below»"), maps)))
		}),
})}

// MonomialTriangleSwap — a finite sum over the monomials i ≤ k ≤ m below a
// finitely supported m, grouped by k, is the same sum grouped by i, the
// second monomial running as k = i + j over the offsets j ≤ m − i, all
// comparisons exponent by exponent. Padded by M.zero off the triangle, G
// fills the square of the monomials below m, where the two sums
// interchange (ModuleSumSwap). The padded row at k sums to the row of the
// triangle, the padding adding nothing off the monomials below k; the
// padded column at i sums to the column read from the diagonal, the
// padding adding nothing off the shifts i + j of the offsets, every k
// between i and m being the shift of k − i, and adding i telling the
// offsets apart.
var MonomialTriangleSwap = monomialTriangleSwapThm{family.Add(registry.ProofEntry{
	Name: "MonomialTriangleSwap",
	Key:  "prop_460204a26ba67a5d",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀m:(D → num). ∀G:((D → num) → (D → num) → B).",
		Hypotheses: []string{
			"finite_support(0, m)",
			"∀i k:(D → num). (∀x:D. i(x) ≤ k(x)) ∧ (∀x:D. k(x) ≤ m(x)) ⇒ G(i, k) ∈ M.carrier",
		},
		Conclusion: "module_sum(M.add, " +
			"    M.zero, " +
			"    «below», " +
			"    λk:(D → num). " +
			"        module_sum(M.add, M.zero, {i:(D → num) | ∀x:D. i(x) ≤ k(x)}, λi:(D → num). G(i, k))) = " +
			"module_sum(M.add, " +
			"    M.zero, " +
			"    «below», " +
			"    λi:(D → num). " +
			"        module_sum(M.add, " +
			"            M.zero, " +
			"            {j:(D → num) | ∀x:D. j(x) ≤ m(x) - i(x)}, " +
			"            λj:(D → num). G(i, λx:D. i(x) + j(x))))",
		Abbrev: Abbrev{
			{Name: "offsets", Text: "{j:(D → num) | ∀x:D. j(x) ≤ m(x) - i(x)}"},
			{Name: "shifts", Text: "image(λj:(D → num). λx:D. i(x) + j(x), «offsets»)"},
		},
	},
		func(
			a *Argument,
			vectors module.ModuleFact[on.R, on.M],
			m *Arrow[D, Nat],
			G *Arrow2[Fun[D, Nat], Fun[D, Nat], B],
			finiteM, onTriangle Fact,
		) {
			below := a.TermAs[Set[Fun[D, Nat]]]("«below»")
			finiteBelow := a.Have(
				"the monomials below m are finitely many",
				"finite(«below»)",
				By(finiteM, MonomialsBelowFinite.At(m)))
			padded := a.Have(
				"padded by M.zero off the triangle, G lies in M on the whole square of the monomials below m",
				"∀k i:(D → num). k ∈ «below» ∧ i ∈ «below» ⇒ COND(∀x:D. i(x) ≤ k(x), G(i, k), M.zero) ∈ M.carrier",
				BySets(onTriangle, group.OneIn.Read(module.AddGroupOn.Read(vectors))))
			rows := a.Have(
				"the row of the triangle at k below m is the padded row summed over the monomials below m",
				Statement{
					Binders: "∀k:(D → num).",
					Hypotheses: []string{
						"∀x:D. k(x) ≤ m(x)",
					},
					Conclusion: "module_sum(M.add, " +
						"    M.zero, " +
						"    {i:(D → num) | ∀x:D. i(x) ≤ k(x)}, " +
						"    λi:(D → num). G(i, k)) = " +
						"module_sum(M.add, M.zero, «below», λi:(D → num). COND(∀x:D. i(x) ≤ k(x), G(i, k), M.zero))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("k")
					kBelow := b.Assume()
					upToK := b.TermAs[Set[Fun[D, Nat]]]("{i:(D → num) | ∀x:D. i(x) ≤ k(x)}")
					row := b.TermAs[Fun[Fun[D, Nat], B]]("λi:(D → num). COND(∀x:D. i(x) ≤ k(x), G(i, k), M.zero)")
					inside := b.Have(
						"a monomial below k is below m",
						"{i:(D → num) | ∀x:D. i(x) ≤ k(x)} ⊆ «below»",
						BySets(kBelow, nat_order.LessEqTrans))
					b.Show(
						"the padding adds nothing to the row",
						CalcEq(
							Leg(
								b.TermAs[B](
									"module_sum(M.add, "+
										"    M.zero, "+
										"    {i:(D → num) | ∀x:D. i(x) ≤ k(x)}, "+
										"    λi:(D → num). COND(∀x:D. i(x) ≤ k(x), G(i, k), M.zero))"),
								"below k the padded row is the row",
								By(module.ModuleSumCongruence)),
							FinalLeg(
								"and off the monomials below k it is M.zero",
								By(
									finiteBelow,
									inside,
									padded,
									kBelow,
									module.ModuleSumSupport.Read(vectors).At(below, upToK, row))),
						))
				}))
			columns := a.Have(
				"the padded column at i below m, summed over the monomials "+
					"below m, is the column of the triangle read from the diagonal",
				Statement{
					Binders: "∀i:(D → num).",
					Hypotheses: []string{
						"∀x:D. i(x) ≤ m(x)",
					},
					Conclusion: "module_sum(M.add, " +
						"    M.zero, " +
						"    «below», " +
						"    λk:(D → num). COND(∀x:D. i(x) ≤ k(x), G(i, k), M.zero)) = " +
						"module_sum(M.add, M.zero, «offsets», λj:(D → num). G(i, λx:D. i(x) + j(x)))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[D, Nat]]("i")
					iBelow := b.Assume()
					offsets, shifts := b.TermAs[Set[Fun[D, Nat]]]("«offsets»"), b.TermAs[Set[Fun[D, Nat]]]("«shifts»")
					shift := b.TermAs[Fun[Fun[D, Nat], Fun[D, Nat]]]("λj:(D → num). λx:D. i(x) + j(x)")
					column := b.TermAs[Fun[Fun[D, Nat], B]]("λk:(D → num). COND(∀x:D. i(x) ≤ k(x), G(i, k), M.zero)")
					forth := b.Have(
						"the shift i + j of an offset j ≤ m − i is at most m, and so is the offset",
						"∀j:(D → num). (∀x:D. j(x) ≤ m(x) - i(x)) ⇒ (∀x:D. i(x) + j(x) ≤ m(x)) ∧ (∀x:D. j(x) ≤ m(x))",
						ByArith(iBelow))
					back := b.Have(
						"every k between i and m is the shift of its offset k − i",
						"∀k:(D → num). (∀x:D. i(x) ≤ k(x)) ∧ (∀x:D. k(x) ≤ m(x)) ⇒ k ∈ «shifts»",
						Derive(func(c *Argument) {
							c.FixAs[Fun[D, Nat]]("k")
							bounds := c.Assume()
							recovered := c.Have(
								"i plus k − i is k",
								"(λx:D. i(x) + (k(x) - i(x))) = k",
								Funext(),
								ByArith(bounds))
							within := c.Have(
								"and k − i is at most m − i",
								"∀x:D. k(x) - i(x) ≤ m(x) - i(x)",
								ByArith(bounds))
							c.Show(
								"so k is the shift of an offset",
								By(
									within,
									recovered,
									set_image.FunInImage.At(shift, offsets, c.TermAs[Fun[D, Nat]]("λx:D. k(x) - i(x)"))))
						}))
					inside := b.Have(
						"so the shifts are among the monomials below m",
						"«shifts» ⊆ «below»",
						BySets(forth))
					vanishes := b.Have(
						"and the padded column is M.zero at a monomial "+
							"below m that is no shift, which does not lie above i",
						"∀k:(D → num). k ∈ «below» ∧ k ∉ «shifts» ⇒ COND(∀x:D. i(x) ≤ k(x), G(i, k), M.zero) = M.zero",
						BySets(back))
					offsetsBelow := b.Have(
						"an offset is itself below m",
						"«offsets» ⊆ «below»",
						BySets(forth))
					finiteOffsets := b.Have(
						"so the offsets are finitely many",
						"finite(«offsets»)",
						By(finiteBelow, offsetsBelow, finite_set.FiniteSubset.At(offsets, below)))
					apart := b.Have(
						"adding i tells the offsets apart",
						"injective_on(«offsets», λj:(D → num). λx:D. i(x) + j(x))",
						Simp(Fwd(functions.InjectiveOnDef)),
						By(nat_arith.AddEqLCancel))
					atShifts := b.Have(
						"the padded column lies in M at every shift",
						Statement{
							Binders: "∀j:(D → num).",
							Hypotheses: []string{
								"j ∈ «offsets»",
							},
							Conclusion: "COND(∀x:D. i(x) ≤ i(x) + j(x), G(i, λx:D. i(x) + j(x)), M.zero) ∈ M.carrier",
						},
						BySets(padded, forth, iBelow))
					b.Show(
						"the padding adds nothing to the column, read from the diagonal",
						CalcEq(
							Leg(
								b.TermAs[B](
									"module_sum(M.add, M.zero, «shifts», λk:(D → num). COND(∀x:D. i(x) ≤ k(x), G(i, k), M.zero))"),
								"off the shifts the padded column is M.zero",
								By(
									finiteBelow,
									padded,
									vanishes,
									iBelow,
									inside,
									module.ModuleSumSupport.Read(vectors).At(below, shifts, column))),
							Leg(
								b.TermAs[B](
									"module_sum(M.add, "+
										"    M.zero, "+
										"    «offsets», "+
										"    λj:(D → num). COND(∀x:D. i(x) ≤ i(x) + j(x), G(i, λx:D. i(x) + j(x)), M.zero))"),
								"reindex along the shift, which tells the offsets apart",
								By(finiteOffsets, apart, atShifts, module.ModuleSumImage.Read(vectors).At(offsets, shift, column))),
							FinalLeg(
								"i ≤ i + j, so at every shift the padded column is G itself",
								Simp(Fwd(nat_order.LessEqAdd)),
								Basic()),
						))
				}))
			square := a.TermAs[Fun2[Fun[D, Nat], Fun[D, Nat], B]](
				"λk:(D → num). λi:(D → num). COND(∀x:D. i(x) ≤ k(x), G(i, k), M.zero)")
			a.Show(
				"both sides sum the padding over the square, by rows and by columns",
				CalcEq(
					Leg(
						a.TermAs[B](
							"module_sum(M.add, "+
								"    M.zero, "+
								"    «below», "+
								"    λk:(D → num). "+
								"        module_sum(M.add, "+
								"            M.zero, "+
								"            «below», "+
								"            λi:(D → num). COND(∀x:D. i(x) ≤ k(x), G(i, k), M.zero)))"),
						"pad every row",
						By(rows, module.ModuleSumCongruence)),
					Leg(
						a.TermAs[B](
							"module_sum(M.add, "+
								"    M.zero, "+
								"    «below», "+
								"    λi:(D → num). "+
								"        module_sum(M.add, "+
								"            M.zero, "+
								"            «below», "+
								"            λk:(D → num). COND(∀x:D. i(x) ≤ k(x), G(i, k), M.zero)))"),
						"the two sums over the square interchange",
						By(finiteBelow, padded, module.ModuleSumSwap.Read(vectors).At(below, below, square))),
					FinalLeg(
						"and every padded column is the column read from the diagonal",
						By(columns, module.ModuleSumCongruence)),
				))
		}),
})}

// ---------------------------------------------------------------------------
// The monomials of one degree
// ---------------------------------------------------------------------------

// MonomialsOfDegreeCount — there are binomial(d + n, n) monomials of degree
// d in the variables 0, …, n. By induction on n and, inside it, on d. In one
// variable X₀^d is the only monomial of degree d, and in degree zero the
// constant monomial is the only one. A monomial of degree d + 1 in the
// variables up to n + 1 has exponent zero at n + 1, and is then a monomial
// of degree d + 1 in the variables up to n, or a positive one there, and
// lowering that exponent by one gives a monomial of degree d, raising it
// again giving the monomial back; Pascal's rule adds the two counts.
var MonomialsOfDegreeCount = monomialsOfDegreeCountThm{family.Add(registry.ProofEntry{
	Name: "MonomialsOfDegreeCount",
	Key:  "prop_8975aeff063adf7f",
	Build: family.Theorem(Statement{
		Binders:    "∀n d:num.",
		Conclusion: "has_size(«degree»(n, d), binomial(d + n, n))",
		Abbrev: Abbrev{
			{Name: "degree", Text: "λn:num. λd:num. " +
				"    {m:(num → num) | m ∈ monomials({i:num | i ≤ n}) ∧ nat_sum({i:num | i ≤ n}, m) = d}"},
			{Name: "positiveAtLast", Text: "λn:num. λd:num. " +
				"    {m:(num → num) | " +
				"        (m ∈ monomials({i:num | i ≤ suc(n)}) ∧ nat_sum({i:num | i ≤ suc(n)}, m) = d) ∧ " +
				"        m(suc(n)) ≠ 0}"},
			{Name: "raised", Text: "λj:num. λm:(num → num). λy:num. COND(y = j, m(j) + 1, m(y))"},
			{Name: "lowered", Text: "λj:num. λm:(num → num). λy:num. COND(y = j, m(j) - 1, m(y))"},
		},
	},
		func(a *Argument) {
			bounded := a.Have(
				"a monomial in the variables up to n is an exponent function vanishing above n",
				"∀n:num. ∀m:(num → num). m ∈ monomials({i:num | i ≤ n}) ⇔ (∀x:num. n < x ⇒ m(x) = 0)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.FixAs[Fun[Nat, Nat]]("m")
					b.Iff()
					b.Forward(
						"a nonzero exponent of a monomial sits at a variable up to n",
						func(c *Argument, monomial Fact) {
							c.Show(
								"so above n every exponent is zero",
								BySets(monomial, MonomialsDef, nat_order.NotLessThan))
						})
					b.Backward(
						"an exponent function vanishing above n is supported among the variables up to n",
						func(c *Argument, vanishing Fact) {
							support := c.Have(
								"its nonzero exponents sit at the variables up to n",
								"fun_support(0, m) ⊆ {i:num | i ≤ n}",
								BySets(vanishing, nat_order.NotLessThan))
							finite := c.Have(
								"which are finitely many",
								"finite(fun_support(0, m))",
								By(support, finite_set.FiniteSubset, num_segment.FiniteBelow))
							c.Show(
								"a finitely supported exponent function nonzero only at the variables up to n",
								Unfold(MonomialsDef),
								Unfold(function_module.FiniteSupportDef),
								BySets(finite, support))
						})
				}))
			lastTerm := a.Have(
				"summing over the variables up to n + 1 adds the exponent at n + 1",
				"∀n:num. ∀m:(num → num). "+
					"    nat_sum({i:num | i ≤ suc(n)}, m) = nat_sum({i:num | i ≤ n}, m) + m(suc(n))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.FixAs[Fun[Nat, Nat]]("m")
					b.Show(
						"over the interval 0 .. n + 1 the last term splits off",
						Simp(Fwd(num_segment.Below), Fwd(nat_sum.IntervalClauses), Fwd(nat_order.ZeroLessEq)),
						Basic())
				}))
			replaced := a.Have(
				"with its exponent at n + 1 replaced by e, an exponent function sums to its sum up to n plus e",
				"∀n e:num. ∀m:(num → num). "+
					"    nat_sum({i:num | i ≤ suc(n)}, λy:num. COND(y = suc(n), e, m(y))) = "+
					"    nat_sum({i:num | i ≤ n}, m) + e",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.FixAs[Nat]("e")
					m := b.FixAs[Fun[Nat, Nat]]("m")
					replacement := b.TermAs[Fun[Nat, Nat]]("λy:num. COND(y = suc(n), e, m(y))")
					unchanged := b.Have(
						"up to n the replacement changes no exponent",
						"∀x:num. x ∈ {i:num | i ≤ n} ⇒ COND(x = suc(n), e, m(x)) = m(x)",
						BySets(nat_order.LessThanSucIffLessEq, nat_order.LessThanIrrefl))
					b.Show(
						"so the sums up to n agree, and the last term is e",
						By(
							unchanged,
							lastTerm.At(n, replacement),
							nat_sum.Congruence.At(b.TermAs[Set[Nat]]("{i:num | i ≤ n}"), replacement, m)))
				}))
			atZero := a.Have(
				"in the one variable 0 the sum of the exponents is the exponent at 0",
				"∀m:(num → num). nat_sum({i:num | i ≤ 0}, m) = m(0)",
				Simp(Fwd(num_segment.Below), Fwd(nat_sum.IntervalPoint)),
				Basic())
			constantOnly := a.Have(
				"in degree zero the constant monomial is the only one",
				"∀n:num. «degree»(n, 0) = {λi:num. 0}",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"its exponents vanish above n, and up to n because they sum to zero",
						BySets(
							bounded.At(n),
							At(nat_sum.EqZero, b.TermAs[Set[Nat]]("{i:num | i ≤ n}")),
							num_segment.FiniteBelow.At(n),
							nat_order.NotLessThan))
				}))
			oneVariable := a.Have(
				"in the one variable 0, X₀^d is the only monomial of degree d",
				"∀d:num. «degree»(0, d) = {λi:num. COND(i = 0, d, 0)}",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("d")
					b.Show(
						"its exponents vanish past 0, and the exponent at 0 is the whole degree",
						BySets(bounded.At(b.TermAs[Nat]("0")), atZero, nat_order.PosIffNonzero))
				}))
			lastZero := a.Have(
				"a monomial up to n + 1 with exponent zero at n + 1 is a monomial up to n, of the same degree",
				"∀n d:num. ∀m:(num → num). "+
					"    (m ∈ monomials({i:num | i ≤ suc(n)}) ∧ nat_sum({i:num | i ≤ suc(n)}, m) = d) ∧ "+
					"    m(suc(n)) = 0 ⇔ "+
					"    m ∈ monomials({i:num | i ≤ n}) ∧ nat_sum({i:num | i ≤ n}, m) = d",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.FixAs[Nat]("d")
					m := b.FixAs[Fun[Nat, Nat]]("m")
					vanishing := b.Have(
						"m vanishes above n exactly when it vanishes above n + 1 and at n + 1",
						"(∀x:num. n < x ⇒ m(x) = 0) ⇔ (∀x:num. suc(n) < x ⇒ m(x) = 0) ∧ m(suc(n)) = 0",
						Derive(func(c *Argument) {
							c.Iff()
							c.Forward(
								"what vanishes above n vanishes past n + 1 and at n + 1, both above n",
								func(e *Argument, above Fact) {
									e.Show(
										"n + 1 and every point past it lie above n",
										SplitConj(
											Case(
												"a point past n + 1 lies above n",
												e.ForEach(func(x *Expr[Nat]) Action { return ByArith(above.At(x)) })),
											Case(
												"n + 1 lies above n",
												ByArith(above.At(e.TermAs[Nat]("suc(n)"))))))
								})
							c.Backward(
								"what vanishes past n + 1 and at n + 1 vanishes above n",
								func(e *Argument, given Fact) {
									parts := e.Conjuncts(
										given,
										"m vanishes past n + 1",
										"and at n + 1")
									x := e.FixAs[Nat]("x")
									e.Cases(e.Term("x = suc(n)"))
									e.When(
										"at n + 1 it vanishes by the second",
										func(f *Argument, at Fact) {
											f.Show(
												"m(x) = m(n + 1) = 0",
												By(Normalized, at, parts[1]))
										})
									e.Otherwise(
										"a point above n other than n + 1 lies past n + 1",
										func(f *Argument, off Fact) {
											f.Show(
												"so m vanishes there by the first",
												ByArith(off, parts[0].At(x)))
										})
								})
						}))
					b.Show(
						"both vanish above n as m does, and the sums agree when the exponent at n + 1 is zero",
						By(
							vanishing,
							bounded.At(n, m),
							bounded.At(b.TermAs[Nat]("suc(n)"), m),
							lastTerm.At(n, m),
							nat_arith.AddZero.At(b.TermAs[Nat]("nat_sum({i:num | i ≤ n}, m)"))))
				}))
			raising := a.Have(
				"raising the exponent at n + 1 of a monomial of degree d gives one of degree d + 1, nonzero there",
				Statement{
					Binders: "∀n d:num. ∀m:(num → num).",
					Hypotheses: []string{
						"m ∈ monomials({i:num | i ≤ suc(n)})",
						"nat_sum({i:num | i ≤ suc(n)}, m) = d",
					},
					Conclusion: "(«raised»(suc(n), m) ∈ monomials({i:num | i ≤ suc(n)}) ∧ " +
						"    nat_sum({i:num | i ≤ suc(n)}, «raised»(suc(n), m)) = suc(d)) ∧ " +
						"«raised»(suc(n), m, suc(n)) ≠ 0",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.FixAs[Nat]("d")
					m := b.FixAs[Fun[Nat, Nat]]("m")
					given := b.Assume()
					next := b.TermAs[Nat]("suc(n)")
					b.Show(
						"the raised monomial vanishes where m does, sums to one more, and is positive at n + 1",
						SplitConjAll(
							Case(
								"above n + 1 it agrees with m, which vanishes there",
								By(
									given,
									bounded.At(next, m),
									bounded.At(next, b.TermAs[Fun[Nat, Nat]]("«raised»(suc(n), m)")),
									nat_order.LessThanIrrefl)),
							Case(
								"its exponents sum to those of m plus one",
								ByArith(given, lastTerm.At(n, m), replaced.At(n, b.TermAs[Nat]("m(suc(n)) + 1"), m))),
							Case(
								"its exponent at n + 1 is that of m plus one",
								ByArith())))
				}))
			lowering := a.Have(
				"lowering the positive exponent at n + 1 of a monomial of "+
					"degree d + 1 gives one of degree d, which raising gives back",
				Statement{
					Binders: "∀n d:num. ∀m:(num → num).",
					Hypotheses: []string{
						"m ∈ monomials({i:num | i ≤ suc(n)})",
						"nat_sum({i:num | i ≤ suc(n)}, m) = suc(d)",
						"m(suc(n)) ≠ 0",
					},
					Conclusion: "(«lowered»(suc(n), m) ∈ monomials({i:num | i ≤ suc(n)}) ∧ " +
						"    nat_sum({i:num | i ≤ suc(n)}, «lowered»(suc(n), m)) = d) ∧ " +
						"m = «raised»(suc(n), «lowered»(suc(n), m))",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.FixAs[Nat]("d")
					m := b.FixAs[Fun[Nat, Nat]]("m")
					given := b.Assume()
					next := b.TermAs[Nat]("suc(n)")
					b.Show(
						"the lowered monomial vanishes where m does, sums to one less, and raising it restores m",
						SplitConjAll(
							Case(
								"above n + 1 it agrees with m, which vanishes there",
								By(
									given,
									bounded.At(next, m),
									bounded.At(next, b.TermAs[Fun[Nat, Nat]]("«lowered»(suc(n), m)")),
									nat_order.LessThanIrrefl)),
							Case(
								"its exponents sum to those of m less one",
								ByArith(given, lastTerm.At(n, m), replaced.At(n, b.TermAs[Nat]("m(suc(n)) - 1"), m))),
							Case(
								"raising the lowered exponent restores m, the exponent at n + 1 being positive",
								Funext(),
								Derive(func(c *Argument) {
									c.FixAs[Nat]("y")
									c.Cases(c.Term("y = suc(n)"))
									c.When(
										"at n + 1 the exponent less one, plus one, is the exponent",
										func(e *Argument, at Fact) {
											e.Show(
												"m(n + 1) − 1 + 1 = m(n + 1), m(n + 1) being positive",
												ByArith(at, given))
										})
									c.Otherwise(
										"elsewhere neither move changes the exponent",
										func(e *Argument, off Fact) {
											e.Show(
												"y is not n + 1",
												By(off))
										})
								}))))
				}))
			lowerRaise := a.Have(
				"lowering an exponent just raised gives the monomial back",
				"∀j:num. ∀m:(num → num). «lowered»(j, «raised»(j, m)) = m",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("j")
					b.FixAs[Fun[Nat, Nat]]("m")
					b.Do(Funext())
					b.FixAs[Nat]("y")
					b.Cases(b.Term("y = j"))
					b.When(
						"at j the exponent plus one, less one, is the exponent",
						func(c *Argument, at Fact) {
							c.Show(
								"m(j) + 1 − 1 = m(j)",
								ByArith(at))
						})
					b.Otherwise(
						"elsewhere neither move changes the exponent",
						func(c *Argument, off Fact) {
							c.Show(
								"y is not j",
								By(off))
						})
				}))
			positivePart := a.Have(
				"the monomials of degree d + 1 up to n + 1 positive at n + 1 are as many as those of degree d",
				"∀n d b:num. has_size(«degree»(suc(n), d), b) ⇒ has_size(«positiveAtLast»(n, suc(d)), b)",
				Derive(func(c *Argument) {
					n := c.FixAs[Nat]("n")
					d := c.FixAs[Nat]("d")
					count := c.FixAs[Nat]("b")
					sized := c.Assume()
					up := c.Have(
						"raising the exponent at n + 1 lands among them, and lowering it again undoes the raising",
						Statement{
							Binders: "∀x:(num → num).",
							Hypotheses: []string{
								"x ∈ «degree»(suc(n), d)",
							},
							Conclusion: "«raised»(suc(n), x) ∈ «positiveAtLast»(n, suc(d)) ∧ " +
								"«lowered»(suc(n), «raised»(suc(n), x)) = x",
						},
						BySets(raising.At(n, d), lowerRaise.At(c.TermAs[Nat]("suc(n)"))))
					down := c.Have(
						"lowering the exponent at n + 1 of one of them lands one "+
							"degree down, and raising it again undoes the lowering",
						Statement{
							Binders: "∀y:(num → num).",
							Hypotheses: []string{
								"y ∈ «positiveAtLast»(n, suc(d))",
							},
							Conclusion: "«lowered»(suc(n), y) ∈ «degree»(suc(n), d) ∧ " +
								"«raised»(suc(n), «lowered»(suc(n), y)) = y",
						},
						BySets(lowering.At(n, d)))
					c.Show(
						"raising and lowering are inverse to each other between the two",
						By(
							up,
							down,
							sized,
							cardinality.MutualInversesHasSize.At(
								c.TermAs[Set[Fun[Nat, Nat]]]("«degree»(suc(n), d)"),
								c.TermAs[Set[Fun[Nat, Nat]]]("«positiveAtLast»(n, suc(d))"),
								c.TermAs[Fun[Fun[Nat, Nat], Fun[Nat, Nat]]]("«raised»(suc(n))"),
								c.TermAs[Fun[Fun[Nat, Nat], Fun[Nat, Nat]]]("«lowered»(suc(n))"),
								count)))
				}))
			split := a.Have(
				"the monomials of degree d + 1 up to n + 1 are those up to "+
					"n, with exponent zero at n + 1, and those positive there",
				"∀n d:num. "+
					"    «degree»(suc(n), suc(d)) = «degree»(n, suc(d)) ∪ «positiveAtLast»(n, suc(d)) ∧ "+
					"    disjoint(«degree»(n, suc(d)), «positiveAtLast»(n, suc(d)))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.FixAs[Nat]("d")
					b.Show(
						"a monomial up to n + 1 has exponent zero at n + 1 exactly when it is one up to n",
						BySets(lastZero.At(n, b.TermAs[Nat]("suc(d)"))))
				}))
			a.Induct("n")
			a.Base(
				"in the one variable 0, X₀^d is the only monomial of degree d",
				func(b *Argument) {
					d := b.FixAs[Nat]("d")
					b.Show(
						"one monomial, and binomial(d, 0) = 1",
						By(
							oneVariable.At(d),
							cardinality.HasSizeDef,
							cardinality.CardSing,
							finite_set.FiniteSing,
							binomial.Clauses,
							nat_arith.AddZero))
				})
			a.Step(
				"one variable more, by induction on the degree",
				func(b *Argument, fewer Fact) {
					b.Induct("d")
					b.Base(
						"in degree zero the constant monomial is the only one, and binomial(n + 1, n + 1) = 1",
						By(
							constantOnly.At(b.TermAs[Nat]("suc(n)")),
							cardinality.HasSizeDef,
							cardinality.CardSing,
							finite_set.FiniteSing,
							binomial.Diagonal,
							nat_arith.AddLeftZeroClause))
					b.Step(
						"degree d + 1 splits by the exponent at n + 1, and Pascal's rule adds the two counts",
						func(c *Argument, lower Fact) {
							n := c.TermAs[Nat]("n")
							d := c.TermAs[Nat]("d")
							pascal := c.Have(
								"Pascal's rule at the two counts",
								"binomial(suc(d) + suc(n), suc(n)) = binomial(suc(d) + n, n) + binomial(d + suc(n), suc(n))",
								Simp(Fwd(nat_arith.AddSuc), Fwd(nat_arith.AddLeftSucClause), Fwd(binomial.Clauses)),
								Refl())
							parts := c.Conjuncts(
								split.At(n, d),
								"the monomials of degree d + 1 up to n + 1 are those zero at n + 1 and those positive there",
								"and the two kinds do not meet")
							c.Show(
								"the two kinds number binomial(d + 1 + n, n) and binomial(d + n + 1, n + 1)",
								By(
									fewer.At(c.TermAs[Nat]("suc(d)")),
									lower,
									pascal,
									parts[0],
									parts[1],
									positivePart.At(n, d, c.TermAs[Nat]("binomial(d + suc(n), suc(n))")),
									cardinality.HasSizeUnion.At(
										c.TermAs[Set[Fun[Nat, Nat]]]("«degree»(n, suc(d))"),
										c.TermAs[Set[Fun[Nat, Nat]]]("«positiveAtLast»(n, suc(d))"),
										c.TermAs[Nat]("binomial(suc(d) + n, n)"),
										c.TermAs[Nat]("binomial(d + suc(n), suc(n))"))))
						})
				})
		}),
})}
