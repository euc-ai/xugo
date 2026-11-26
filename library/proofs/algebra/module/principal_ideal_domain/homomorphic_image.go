// homomorphic_image.go — principal ideals carried along a ring
// homomorphism onto its target.

package principal_ideal_domain

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// SurjectiveImageIdealsPrincipal — a ring homomorphism φ from a principal
// ideal domain R onto a ring S leaves every ideal I of S principal. The
// preimage of I is an ideal of R, the multiples of some d, and φ(d)
// generates I: a member of I is φ(m) for an m of R, a multiple d n, so it
// is φ(d) φ(n); and φ(d) y, with y = φ(n), is φ(d n), which φ sends into I.
var SurjectiveImageIdealsPrincipal = surjectiveImageIdealsPrincipalThm{family.Add(registry.ProofEntry{
	Name: "SurjectiveImageIdealsPrincipal",
	Key:  "prop_2ffb8358d9ab8c69",
	Build: family.Theorem(Statement{
		Binders: "∀φ:ring_homomorphism(A, B). ∀I:set(B).",
		Hypotheses: []string{
			"principal_ideal_domain(R)",
			"image(φ, R.carrier) = S.carrier",
			"ring_ideal(S, I)",
		},
		Conclusion: "∃d:B. d ∈ S.carrier ∧ I = image(S.mul(d), S.carrier)",
	}, func(
		a *Argument,
		φ ring_homomorphism.RingHomomorphismFact[on.R, on.S],
		principal, onto Fact,
		I *Expr[Set[B]],
		ideal Fact,
	) {
		principalIdeals := a.Conjuncts(
			a.Unfolded(principal, PrincipalIdealDomainDef),
			"R is an integral domain",
			"whose every ideal is the multiples of one of its members")
		d, generated := a.ObtainAs[A](
			"the preimage of I, an ideal of R, is the multiples of some d in R",
			"∃d:A. d ∈ R.carrier ∧ preimage_on(R.carrier, φ, I) = image(R.mul(d), R.carrier)",
			By(ring_homomorphism.PreimageIdeal.Read(φ).At(I), ideal, principalIdeals[1]))
		generator := a.Conjuncts(
			generated,
			"d lies in R",
			"its multiples are the preimage of I")
		dm := a.MemberOf[on.R](d, generator[0])
		multiplesIn := a.Have(
			"φ sends every multiple of d into I",
			"∀n:A. n ∈ R.carrier ⇒ φ(d * n) ∈ I",
			BySets(generator[1]))
		inMultiples := a.Have(
			"a member of R that φ sends into I is a multiple of d",
			"∀m:A. m ∈ R.carrier ∧ φ(m) ∈ I ⇒ ∃n:A. n ∈ R.carrier ∧ m = d * n",
			BySets(generator[1]))
		a.Take(a.TermAs[B]("φ(d)"))
		a.Show(
			"φ(d) lies in S, and its multiples are I",
			SplitConj(
				Case(
					"φ carries d into S",
					By(ring_homomorphism.MapIn.Read(φ), dm)),
				Case(
					"the multiples of φ(d) are I",
					Derive(func(b *Argument) {
						b.Do(Simp(Fwd(set_basic.Extension)))
						b.FixAs[B]("x")
						b.Iff()
						b.Forward(
							"a member of I is φ(d) times a member of S",
							func(c *Argument, inIdeal Fact) {
								m, preimageOf := c.ObtainAs[A](
									"x lies in S, onto which φ carries R, so x is φ(m) for an m in R",
									"∃m:A. m ∈ R.carrier ∧ x = φ(m)",
									BySets(inIdeal, ideal, ring_ideal.IdealSubset, onto))
								n, factor := c.ObtainAs[A](
									"φ sends m into I, so m is d times some n in R",
									"∃n:A. n ∈ R.carrier ∧ m = d * n",
									BySets(inMultiples.At(m), preimageOf, inIdeal))
								multiple := c.Conjuncts(
									factor,
									"n lies in R",
									"m is d times n")
								nm := c.MemberOf[on.R](n, multiple[0])
								value := c.Have(
									"so x is φ(d) times φ(n)",
									"x = φ(d) * φ(n)",
									By(Normalized, preimageOf, multiple[1], ring_homomorphism.MapMul.Read(φ).At(dm, nm)))
								c.Show(
									"φ(n) lies in S, so x is a multiple of φ(d)",
									BySets(value, ring_homomorphism.MapIn.Read(φ), nm))
							})
						b.Backward(
							"φ(d) times a member of S lies in I",
							func(c *Argument, inImage Fact) {
								_, product := c.ObtainAs[B](
									"x is φ(d) times some y in S",
									"∃y:B. y ∈ S.carrier ∧ x = φ(d) * y",
									BySets(inImage))
								n, preimageOf := c.ObtainAs[A](
									"φ carries R onto S, so y is φ(n) for an n in R",
									"∃n:A. n ∈ R.carrier ∧ y = φ(n)",
									BySets(product, onto))
								lift := c.Conjuncts(
									preimageOf,
									"n lies in R",
									"y is φ(n)")
								nm := c.MemberOf[on.R](n, lift[0])
								value := c.Have(
									"so x is φ(d * n)",
									"x = φ(d * n)",
									By(Normalized, product, lift[1], ring_homomorphism.MapMul.Read(φ).At(dm, nm)))
								c.Show(
									"which φ sends into I",
									BySets(value, lift[0], multiplesIn.At(n)))
							})
					})),
			))
	}),
})}
