package boolean_degree

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// SignIndicatorIdentity expresses a signed indicator using agreement with the sign test.
// In the positive class the agreement test reads p. In the negative class it reads its complement.
var SignIndicatorIdentity = signIndicatorIdentityThm{family.Add(registry.ProofEntry{
	Name: "SignIndicatorIdentity",
	Key:  "prop_b990c20d6a9fc0de",
	Build: family.Theorem("∀p q:bool. "+
		"    COND(q, COND(p, &1, &0), -COND(p, &1, &0)) = COND((p ⇔ q), &1, &0) + COND(q, &1, &0) - &1",
		func(a *Argument, p, q *Expr[Bool]) {
			a.Show(
				"evaluate the indicators at each value of p and q",
				ByArith())
		}),
})}

// SignedIndicatorSum counts the signed contributions of P using its agreements with Q.
var SignedIndicatorSum = signedIndicatorSumThm{family.Add(registry.ProofEntry{
	Name: "SignedIndicatorSum",
	Key:  "prop_cf820e62cb54fda1",
	Build: family.Theorem(Statement{
		Binders:    "∀T:set(A). ∀P Q:(A → bool).",
		Hypotheses: []string{"finite(T)"},
		Conclusion: "sum(T, λx:A. COND(Q(x), COND(P(x), &1, &0), -COND(P(x), &1, &0))) = " +
			"&card({x:A | x ∈ T ∧ (P(x) ⇔ Q(x))}) + &card({x:A | x ∈ T ∧ Q(x)}) - &card(T)",
		Abbrev: Abbrev{
			{Name: "Agreement", Text: "λx:A. P(x) ⇔ Q(x)"},
			{Name: "MatchIndicator", Text: "λx:A. COND(«Agreement»(x), &1, &0)"},
			{Name: "PositiveIndicator", Text: "λx:A. COND(Q(x), &1, &0)"},
		},
	}, func(a *Argument, T *Expr[Set[A]], P, Q *Arrow[A, Bool], finite Fact) {
		a.Do(Simp(Fwd(SignIndicatorIdentity)))
		a.Show(
			"sum the two indicators and subtract one for every point",
			By(
				finite,
				real_sum.Sub.At(
					T,
					a.TermAs[Fun[A, Real]]("λx:A. «MatchIndicator»(x) + «PositiveIndicator»(x)"),
					a.TermAs[Fun[A, Real]]("λx:A. &1")),
				real_sum.Add.At(
					a.TermAs[Fun[A, Real]]("«MatchIndicator»"), a.TermAs[Fun[A, Real]]("«PositiveIndicator»"), T),
				real_sum.IndicatorSum.At(T, a.TermAs[Set[A]]("«Agreement»")),
				real_sum.IndicatorSum.At(T, Q),
				real_sum.CardAsSum.At(T)))
	}),
})}

// CountDichotomy compares two complementary counts with an exact half of their total.
var CountDichotomy = countDichotomyThm{family.Add(registry.ProofEntry{
	Name: "CountDichotomy",
	Key:  "prop_a375676d5e625932",
	Build: family.Theorem(Statement{
		Binders: "∀m n e t:num.",
		Hypotheses: []string{
			"m + n = t",
			"e + e = t",
			"m ≠ e",
		},
		Conclusion: "t < 2 * m ∨ t < 2 * n",
	}, func(a *Argument, m, n, e, t *Expr[Nat], total, half, off Fact) {
		a.Show(
			"one part must exceed half",
			ByArith(off, half, total))
	}),
})}

// SignedMajority detects a strict majority from a nonzero signed sum when the signs balance.
var SignedMajority = signedMajorityThm{family.Add(registry.ProofEntry{
	Name: "SignedMajority",
	Key:  "prop_afe5a8793a4bd3d8",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(A). ∀P Q:(A → bool).",
		Hypotheses: []string{
			"finite(T)",
			"card(«Positive») = card(«Negative»)",
			"sum(T, λx:A. COND(Q(x), COND(P(x), &1, &0), -COND(P(x), &1, &0))) ≠ &0",
		},
		Conclusion: "card(T) < 2 * card(«Agree») ∨ card(T) < 2 * card(«Disagree»)",
		Abbrev: Abbrev{
			{Name: "Positive", Text: "{x:A | x ∈ T ∧ Q(x)}"},
			{Name: "Negative", Text: "{x:A | x ∈ T ∧ ¬Q(x)}"},
			{Name: "Match", Text: "λx:A. P(x) ⇔ Q(x)"},
			{Name: "Agree", Text: "{x:A | x ∈ T ∧ «Match»(x)}"},
			{Name: "Disagree", Text: "{x:A | x ∈ T ∧ ¬«Match»(x)}"},
		},
	}, func(a *Argument, T *Expr[Set[A]], P, Q *Arrow[A, Bool], finite, balanced, nonzero Fact) {
		positive := a.TermAs[Nat]("card(«Positive»)")
		half := a.Have(
			"positive signs account for half the set",
			"card(«Positive») + card(«Positive») = card(T)",
			By(finite, balanced, cardinality.CardOfPredicateParts.At(T, Q)))
		unequal := a.Have(
			"the signed sum measures the excess of agreements",
			"&card(«Agree») + &card(«Positive») - &card(T) ≠ &0",
			By(finite, nonzero, SignedIndicatorSum.At(T, P, Q)))
		off := a.Have(
			"the agreements differ from half the set",
			"card(«Agree») ≠ card(«Positive»)",
			ByArith(half, unequal, real_construction.OfNumAdd.At(positive, positive)))
		a.Show(
			"one of agreement and disagreement has a majority",
			By(
				finite,
				off,
				half,
				cardinality.CardOfPredicateParts.At(T, a.TermAs[Set[A]]("«Match»")),
				CountDichotomy.At(a.TermAs[Nat]("card(«Agree»)"),
					a.TermAs[Nat]("card(«Disagree»)"),
					positive,
					a.TermAs[Nat]("card(T)"))))
	}),
})}
