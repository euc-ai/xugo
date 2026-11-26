// factoring.go — a homomorphism on R that kills what a surjection u of R kills
// factors through u.

package ring_homomorphism

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// FactorsThroughOnto — a ring homomorphism v on R that vanishes wherever a
// surjective homomorphism u of R vanishes descends along u: two points with one
// image under u differ by a point of the kernel, so v takes one value on each
// fibre, and the map reading v at a chosen preimage keeps the ring laws.
var FactorsThroughOnto = factorsThroughOntoThm{family.Add(registry.ProofEntry{
	Name: "FactorsThroughOnto",
	Key:  "prop_5112a39490eb434e",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀u:(A → B). ∀v:(A → C).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, u)",
			"ring_homomorphism(R, T, v)",
			"image(u, R.carrier) = S.carrier",
			"∀x:A. x ∈ R.carrier ∧ u(x) = S.zero ⇒ v(x) = T.zero",
		},
		Conclusion: "∃h:(B → C). ring_homomorphism(S, T, h) ∧ (∀x:A. x ∈ R.carrier ⇒ h(u(x)) = v(x))",
	}, func(
		a *Argument,
		R *Expr[comm_ring.RingOps[A]],
		S *Expr[comm_ring.RingOps[B]],
		T *Expr[comm_ring.RingOps[C]],
		u *Arrow[A, B],
		v *Arrow[A, C],
		uHom, vHom, onto, kernel Fact,
	) {
		sourceRing, imageRing, targetRing := Source.Read(uHom), Target.Read(uHom), Target.Read(vHom)
		fibers := a.Have(
			"v takes one value on each fibre of u",
			"∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ∧ u(x) = u(y) ⇒ v(x) = v(y)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				parts := b.Conjuncts(
					b.Assume(),
					"x lies in R",
					"y lies in R",
					"x and y have one image")
				difference := b.Have(
					"x - y is in R",
					"x - y ∈ R.carrier",
					By(parts[0], parts[1], comm_ring.SubIn.Read(sourceRing).AsFact().At(x, y)))
				killed := b.Have(
					"u kills x - y",
					"u(x - y) = S.zero",
					GroupPremises(parts[0], parts[1], MapSub.Read(uHom).AsFact().At(x, y)).Rw(),
					parts[2].Rw(),
					ByArith(imageRing, MapIn.Read(uHom).AsFact().At(y), parts[1]))
				vanishes := b.Have(
					"so v does",
					"v(x - y) = T.zero",
					By(difference, killed, kernel.At(b.TermAs[A]("x - y"))))
				spread := b.Have(
					"v(x) - v(y) vanishes",
					"v(x) - v(y) = T.zero",
					GroupPremises(parts[0], parts[1], MapSub.Read(vHom).AsFact().At(x, y)).RwRev(),
					By(vanishes))
				b.Show(
					"so v(x) = v(y)",
					ByArith(
						targetRing,
						spread,
						MapIn.Read(vHom).AsFact().At(x),
						MapIn.Read(vHom).AsFact().At(y),
						parts[0],
						parts[1]))
			}))
		w, wDef := a.LetAs[Fun[B, C]]("w", "λy:B. v(inverse_on(R.carrier, u, y))")
		preimages := a.Have(
			"every target point has a chosen source preimage",
			Statement{
				Binders: "∀y:B.",
				Hypotheses: []string{
					"y ∈ S.carrier",
				},
				Conclusion: "inverse_on(R.carrier, u, y) ∈ R.carrier ∧ u(inverse_on(R.carrier, u, y)) = y",
			},
			By(
				Normalized,
				onto,
				At(functions.InverseOnIn, a.TermAs[Set[A]]("R.carrier"), u),
				At(functions.InverseOnRight, a.TermAs[Set[A]]("R.carrier"), u)))
		factorValues := a.Have(
			"the factor has the prescribed values on the image",
			"∀x:A. x ∈ R.carrier ⇒ w(u(x)) = v(x)",
			By(Normalized, MapIn.Read(uHom), wDef, preimages, fibers))
		factorCarrier := a.Have(
			"the factor maps into the target carrier",
			"∀y:B. y ∈ S.carrier ⇒ w(y) ∈ T.carrier",
			By(Normalized, MapIn.Read(vHom), wDef, preimages))
		sumOnImages := a.Have(
			"the factor preserves sums of images",
			"∀x z:A. x ∈ R.carrier ∧ z ∈ R.carrier ⇒ w(S.add(u(x), u(z))) = T.add(v(x), v(z))",
			Derive(func(c *Argument) {
				x := c.FixAs[A]("x")
				z := c.FixAs[A]("z")
				inSource := c.Assume()
				c.Show(
					"evaluate the factor on the image of the source sum",
					By(
						Normalized,
						inSource,
						At(factorValues, c.TermAs[A]("R.add(x, z)")),
						At(MapAdd.Read(uHom), x, z),
						At(MapAdd.Read(vHom), x, z),
						At(comm_ring.AddIn.Read(sourceRing), x, z)))
			}))
		factorAdditive := a.Have(
			"the factor preserves all sums in its carrier",
			"∀y z:B. y ∈ S.carrier ∧ z ∈ S.carrier ⇒ w(S.add(y, z)) = T.add(w(y), w(z))",
			By(Normalized, sumOnImages, factorValues, preimages))
		productOnImages := a.Have(
			"the factor preserves products of images",
			"∀x z:A. x ∈ R.carrier ∧ z ∈ R.carrier ⇒ w(S.mul(u(x), u(z))) = T.mul(v(x), v(z))",
			Derive(func(c *Argument) {
				x := c.FixAs[A]("x")
				z := c.FixAs[A]("z")
				inSource := c.Assume()
				c.Do(By(
					Normalized,
					inSource,
					At(factorValues, c.TermAs[A]("R.mul(x, z)")),
					At(MapMul.Read(uHom), x, z),
					At(MapMul.Read(vHom), x, z),
					At(comm_ring.MulIn.Read(sourceRing), x, z)))
			}))
		factorMultiplicative := a.Have(
			"the factor preserves all products in its carrier",
			"∀y z:B. y ∈ S.carrier ∧ z ∈ S.carrier ⇒ w(S.mul(y, z)) = T.mul(w(y), w(z))",
			Derive(func(c *Argument) {
				y := c.FixAs[B]("y")
				z := c.FixAs[B]("z")
				inTarget := c.Assume()
				c.Do(By(
					inTarget,
					At(preimages, y),
					At(preimages, z),
					At(
						productOnImages,
						c.TermAs[A]("inverse_on(R.carrier, u, y)"),
						c.TermAs[A]("inverse_on(R.carrier, u, z)")),
					At(factorValues, c.TermAs[A]("inverse_on(R.carrier, u, y)")),
					At(factorValues, c.TermAs[A]("inverse_on(R.carrier, u, z)"))))
			}))
		factorOne := a.Have(
			"the factor preserves one",
			"w(S.one) = T.one",
			By(
				Normalized,
				comm_ring.OneIn.Read(sourceRing),
				MapOne.Read(uHom),
				MapOne.Read(vHom),
				At(factorValues, a.TermAs[A]("R.one"))))
		factorHom := a.Have(
			"the factor is a ring homomorphism",
			"ring_homomorphism(S, T, w)",
			By(
				Target.Read(uHom),
				Target.Read(vHom),
				factorAdditive,
				factorMultiplicative,
				factorOne,
				factorCarrier,
				RingHomomorphism.At(S, T, w)))
		a.Take(w)
		a.Show(
			"w is a ring homomorphism with w(u(x)) = v(x) on R",
			By(factorValues, factorHom))
	}),
})}
