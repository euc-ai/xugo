// quotients.go — simple ideal layers, residue lines, the dimension and
// cardinality of quotients after multiplication by an invertible ideal,
// the colengths of the powers of a rational ideal, and the finite quotients
// of an invertible ideal's meet with S.

package ideal_colength

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/flat_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/invertible_fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// Simple layers and finite quotients
// ---------------------------------------------------------------------------

// ScaleQuotientHom — multiplication by a field element descends between
// quotient modules when it carries both numerators and denominators into
// their respective targets.
var ScaleQuotientHom = scaleQuotientHomThm{family.Add(registry.ProofEntry{
	Name: "ScaleQuotientHom",
	Key:  "prop_d89c9ea7e69d13b7",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S X Y K H:set(A). ∀c:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"submodule(«R», «V», X)",
			"submodule(«R», «V», Y)",
			"submodule(«R», «V», K)",
			"submodule(«R», «V», H)",
			"K ⊆ X",
			"H ⊆ Y",
			"c ∈ L.carrier",
			"image(L.mul(c), X) ⊆ Y",
			"image(L.mul(c), K) ⊆ H",
		},
		Conclusion: "∃q:(set(A) → set(A)). " +
			"    module_homomorphism(«R», «XQ», «YQ», q) ∧ " +
			"    (∀u:A. u ∈ X ⇒ q(left_coset(L.add, u, K)) = left_coset(L.add, c * u, H))",
		Abbrev: Abbrev{
			{Name: "XQ", Text: "quotient_module(restrict_module(«V», X), K)"},
			{Name: "YQ", Text: "quotient_module(restrict_module(«V», Y), H)"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], S, X, Y, K, H *Expr[Set[A]], c *Expr[A], h Fact) {
		p := a.Conjuncts(
			h,
			"S is a subring of L",
			"X is a submodule",
			"Y is a submodule",
			"K is a submodule",
			"H is a submodule",
			"K lies in X",
			"H lies in Y",
			"c lies in L",
			"c carries X into Y",
			"c carries K into H")
		subring, fracX, fracY, fracK, fracH := p[0], p[1], p[2], p[3], p[4]
		kInX, hInY, cInL, imageX, imageK := p[5], p[6], p[7], p[8], p[9]
		R := a.TermAs[module_record.RingOps[A]]("«R»")
		V := a.TermAs[module_record.ModuleOps[A, A]]("«V»")
		VX := a.TermAs[module_record.ModuleOps[A, A]]("restrict_module(«V», X)")
		VY := a.TermAs[module_record.ModuleOps[A, A]]("restrict_module(«V», Y)")
		YQ := a.TermAs[module_record.ModuleOps[A, Set[A]]]("«YQ»")
		fieldModule := a.Have(
			"L is an S-module",
			"module_on(«R», «V»)",
			By(subring, fractional_ideal.FieldModuleOn.Read(L).At(S)))
		moduleY := a.Have(
			"Y inherits its module structure",
			"module_on(«R», restrict_module(«V», Y))",
			By(fracY, submodule.SubmoduleModuleOn.Read(fieldModule).At(Y)))
		denomX := a.Have(
			"K is a submodule of X",
			"submodule(«R», restrict_module(«V», X), K)",
			By(fracK, kInX, submodule.SubmoduleRestrict.At(R, V, X, K)))
		denomY := a.Have(
			"H is a submodule of Y",
			"submodule(«R», restrict_module(«V», Y), H)",
			By(fracH, hInY, submodule.SubmoduleRestrict.At(R, V, Y, H)))
		multiply := a.TermAs[Fun[A, A]]("L.mul(c)")
		scalarHom := a.Have(
			"multiplication by c is S-linear on L",
			"module_homomorphism(«R», «V», «V», L.mul(c))",
			By(subring, cInL, field_extension.ScaleLinear.Read(L).AsFact().At(S, c)))
		points := a.Have(
			"it carries every member of X into Y",
			"∀u:A. u ∈ X ⇒ c * u ∈ Y",
			BySets(imageX))
		restricted := a.Have(
			"so its restriction is linear from X to Y",
			"module_homomorphism(«R», restrict_module(«V», X), restrict_module(«V», Y), L.mul(c))",
			By(scalarHom, fracX, fracY, points, module_homomorphism.HomRestrict.At(R, V, V, multiply, X, Y)))
		projection := a.TermAs[Fun[A, Set[A]]]("λw:A. left_coset(L.add, w, H)")
		projectionHom := a.Unfolded(a.Have(
			"projection onto Y/H is linear",
			"module_homomorphism(«R», restrict_module(«V», Y), «YQ», coset_map(L.add, H))",
			By(moduleY, denomY, module_homomorphism.ProjectionHom.At(R, VY, H))), group.CosetMapDef)
		pre, definedPre := a.LetAs[Fun[A, Set[A]]]("pre", "(λw:A. left_coset(L.add, w, H)) ∘ L.mul(c)")
		preHom := a.Have(
			"compose multiplication with projection",
			"module_homomorphism(«R», restrict_module(«V», X), «YQ», pre)",
			definedPre.Rw(),
			By(
				restricted,
				projectionHom,
				module_homomorphism.HomCompose.At(R, VX, VY, YQ, multiply, projection)))
		preFormula := a.Have(
			"the composite sends u to the coset of c*u",
			"∀u:A. pre(u) = left_coset(L.add, c * u, H)",
			definedPre.Rw(),
			Simp(Fwd(functions.ComposeApply)),
			Basic())
		killsK := a.Have(
			"every member of K maps to the zero coset",
			"∀u:A. u ∈ K ⇒ pre(u) = H",
			Derive(func(b *Argument) {
				u := b.FixAs[A]("u")
				uInK := b.Assume()
				cuH := b.Have(
					"c*u lies in H",
					"c * u ∈ H",
					BySets(uInK, imageK))
				cuY := b.Have(
					"and hence in Y",
					"c * u ∈ Y",
					BySets(cuH, hInY))
				zeroCoset := b.Have(
					"its coset is H",
					"left_coset(L.add, c * u, H) = H",
					By(
						cuY,
						cuH,
						submodule.SubmoduleSubgroup.Read(denomY),
						quotient_group.LeftCosetIsSubgroupIffIn.Read(module.AddGroupOn.Read(moduleY)).AsFact().At(
							b.TermAs[A]("c * u"), H)))
				b.Show(
					"the composite vanishes on u",
					By(Normalized, preFormula.At(u), zeroCoset))
			}))
		kernel := a.Have(
			"K lies in the kernel",
			"K ⊆ group_kernel(H, X, pre)",
			Unfold(group_homomorphism.GroupKernelDef),
			BySets(kInX, killsK))
		descended := a.Have(
			"the composite descends to X/K and keeps its formula",
			"module_homomorphism(«R», «XQ», «YQ», induced_map(pre)) ∧ "+
				"(∀u:A. u ∈ X ⇒ induced_map(pre, left_coset(L.add, u, K)) = pre(u))",
			By(denomX, preHom, kernel, module_homomorphism.InducedMapHom.At(R, VX, YQ, K, pre)))
		d := a.Conjuncts(
			descended,
			"the induced map is linear",
			"and agrees with pre on representatives")
		a.Take(a.TermAs[Fun[Set[A], Set[A]]]("induced_map(pre)"))
		a.Show(
			"this is the required scalar map on quotient modules",
			SplitConj(
				Case(
					"linearity",
					By(d[0])),
				Case(
					"formula on representatives",
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						uInX := b.Assume()
						b.Show(
							"first descend, then evaluate the scalar map",
							CalcEq(
								Leg(
									b.TermAs[Set[A]]("pre(u)"),
									"the induced map agrees with pre",
									By(d[1].At(u), uInX)),
								FinalLeg(
									"evaluate pre",
									By(preFormula.At(u)))))
					}))))
	}),
})}

// InvertibleSimpleLayer — a nonzero simple quotient I/J is unchanged,
// up to S-linear isomorphism, by multiplication by an invertible ideal.
// Pick u in I outside J. Its annihilator ann = {r ∈ S | r * u ∈ J}, the
// colon (J : {u}) cut down to S, is a fractional ideal killing I/J, and
// every member of S outside it is invertible modulo ann. Since
// M · (S : M) = S and one ∉ ann, some x ∈ M and f ∈ (S : M) have
// x * f ∉ ann; with v inverting x * f modulo ann, multiplication by x and
// by v * f descend to mutually inverse maps I/J ⇄ IM/JM.
var InvertibleSimpleLayer = invertibleSimpleLayerThm{family.Add(registry.ProofEntry{
	Name: "InvertibleSimpleLayer",
	Key:  "prop_33e73c9ac4fb840f",
	Reading: "Simplicity is the hypothesis that I covers J. The isomorphism depends " +
		"on a choice of x in M and f in its inverse; no natural isomorphism of arbitrary " +
		"quotients is asserted. There is no subfield or finite-quotient hypothesis.",
	Build: family.Theorem(
		Statement{
			Binders: "∀L:field_on(A). ∀S M I J:set(A).",
			Hypotheses: []string{
				"subring(field_ring(L), S)",
				"invertible_fractional(field_ring(L), S, M)",
				"ideal_cover(«layerRing», J, I)",
			},
			Conclusion: "module_isomorphic(«layerRing», «sourceLayer», «productLayer»)",
			Abbrev: Abbrev{
				{Name: "layerRing", Text: "restrict_ring(field_ring(L), S)"},
				{Name: "layerField", Text: "regular_module(field_ring(L))"},
				{Name: "sourceLayer", Text: "quotient_module(restrict_module(«layerField», I), J)"},
				{Name: "productLayer", Text: "quotient_module( " +
					"    restrict_module(«layerField», fractional_mul(field_ring(L), S, I, M)), " +
					"    fractional_mul(field_ring(L), S, J, M))"},
			},
		},
		func(a *Argument, L field.FieldFact[on.L], S, M, I, J *Expr[Set[A]], h Fact) {
			p := a.Conjuncts(
				h,
				"S is a subring of L",
				"M is invertible",
				"I covers J")
			subring, invertible := p[0], p[1]
			cover := a.Conjuncts(
				a.Unfolded(p[2], ring_ideal.IdealCoverDef),
				"J is an ideal",
				"I is an ideal",
				"J lies in I",
				"the inclusion is strict",
				"there is no ideal between J and I")
			idealJ, idealI, jInI, strict, interval := cover[0], cover[1], cover[2], cover[3], cover[4]
			R := a.TermAs[module_record.RingOps[A]]("«layerRing»")
			fieldRing := field.RingOn.Read(L)
			ring := a.Have(
				"S is a ring under L's operations",
				"comm_ring_on(«layerRing»)",
				By(subring, comm_ring.SubringRingOn.Read(fieldRing).At(S)))
			inField := a.Have(
				"S lies in L",
				"S ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(subring)))
			iInS := a.Have(
				"I lies in S",
				"I ⊆ S",
				By(ring_ideal.IdealSubset.Read(idealI)))
			jInS := a.Have(
				"J lies in S",
				"J ⊆ S",
				By(ring_ideal.IdealSubset.Read(idealJ)))

			cyclic := a.Have(
				"every nonzero coset generates the simple layer",
				"∀w z:A. w ∈ I ∧ w ∉ J ∧ z ∈ I ⇒ ∃s t:A. s ∈ S ∧ t ∈ J ∧ z = s * w + t",
				Derive(func(b *Argument) {
					w := b.FixAs[A]("w")
					b.FixAs[A]("z")
					members := b.Assume()
					insert := b.TermAs[Set[A]]("insert(w, J)")
					span := b.TermAs[Set[A]]("ideal_span(«layerRing», insert(w, J))")
					wInS := b.Have(
						"w lies in S",
						"w ∈ S",
						BySets(members, iInS))
					adjoined := b.Conjuncts(
						GroupPremises(jInS, ring_ideal.SpanInsertAbove.Read(ring).At(J, proof.MemberOf(w, wInS))),
						"the span of J with w is an ideal",
						"holding J",
						"and w",
						"and not J when w lies outside J")
					spanIdeal, jInSpan, distinctOutside := adjoined[0], adjoined[1], adjoined[3]
					insertI := b.Have(
						"adjoining w to J stays in I",
						"insert(w, J) ⊆ I",
						BySets(members, jInI))
					spanI := b.Have(
						"the span stays in I",
						"ideal_span(«layerRing», insert(w, J)) ⊆ I",
						By(idealI, insertI, ring_ideal.SpanLeast.At(R, insert, I)))
					spanNotJ := b.Have(
						"w lies outside J, so its span is larger",
						"ideal_span(«layerRing», insert(w, J)) ≠ J",
						By(distinctOutside, members))
					spanIeq := b.Have(
						"the interval forces that span to be I",
						"ideal_span(«layerRing», insert(w, J)) = I",
						By(interval.At(span), spanIdeal, jInSpan, spanI, spanNotJ))
					b.Show(
						"the span of J and w gives the coefficient and remainder",
						BySets(members, spanIeq, idealJ, wInS, ring_ideal.SpanInsertIdeal.Read(ring).AsFact().At(J, w)))
				}))
			u, chosenU := a.ObtainAs[A](
				"choose a nonzero coset",
				"∃u:A. u ∈ I ∧ u ∉ J",
				BySets(jInI, strict),
				Named("u"))
			ann, definedAnn := a.LetAs[Set[A]]("ann", "{r:A | r ∈ S ∧ r * u ∈ J}")
			uInL := a.Have(
				"u lies in the field",
				"u ∈ L.carrier",
				BySets(chosenU, iInS, inField))
			annInS := a.Have(
				"the annihilator lies in S",
				"ann ⊆ S",
				BySets(definedAnn))
			oneS := a.Have(
				"one lies in S",
				"L.one ∈ S",
				By(comm_ring.OneIn.Read(ring)))
			oneProduct := a.Have(
				"one fixes u",
				"L.one * u = u",
				ByArith(fieldRing, uInL))
			oneNotAnn := a.Have(
				"the annihilator is proper",
				"L.one ∉ ann",
				BySets(definedAnn, chosenU, oneProduct))

			unitOutside := a.Have(
				"every scalar outside ann has an inverse modulo ann",
				"∀r:A. r ∈ S ∧ r ∉ ann ⇒ ∃v:A. v ∈ S ∧ v * r - L.one ∈ ann",
				Derive(func(b *Argument) {
					r := b.FixAs[A]("r")
					outside := b.Assume()
					ruI := b.Have(
						"r*u lies in I",
						"r * u ∈ I",
						By(outside, chosenU, ring_ideal.IdealMul.Read(idealI).AsFact().At(r, u)))
					ruNotJ := b.Have(
						"r*u lies outside J",
						"r * u ∉ J",
						BySets(definedAnn, outside))
					s, t, data := b.Obtain2As[A, A](
						"r*u generates the coset of u",
						"∃s t:A. s ∈ S ∧ t ∈ J ∧ u = s * (r * u) + t",
						By(cyclic.At(b.TermAs[A]("r * u"), u), ruI, ruNotJ, chosenU),
						Named("s", "t"))
					fields := b.Have(
						"the coefficient and remainder lie in the field",
						"r ∈ L.carrier ∧ s ∈ L.carrier ∧ u ∈ L.carrier ∧ t ∈ L.carrier",
						BySets(outside, data, uInL, jInS, inField))
					nearInverse := b.Have(
						"the coefficient inverts r modulo the annihilator",
						"(s * r - L.one) * u = -t",
						ByArith(fieldRing, fields, data))
					negT := b.Have(
						"the remainder's negative lies in J",
						"-t ∈ J",
						By(data, idealJ, ring_ideal.IdealNeg.Read(ring).AsFact().At(J, t)))
					srS := b.Have(
						"s*r lies in S",
						"s * r ∈ S",
						By(outside, data, comm_ring.MulIn.Read(ring).AsFact().At(s, r)))
					differenceS := b.Have(
						"s*r-one lies in S",
						"s * r - L.one ∈ S",
						By(srS, oneS, comm_ring.SubIn.Read(ring).AsFact().At(b.TermAs[A]("s * r"), b.TermAs[A]("L.one"))))
					differenceAnn := b.Have(
						"that difference belongs to ann",
						"s * r - L.one ∈ ann",
						BySets(definedAnn, differenceS, nearInverse, negT))
					b.Take(s)
					b.Show(
						"s is the inverse modulo ann",
						By(data, differenceAnn))
				}))
			annKills := a.Have(
				"ann annihilates every coset of I/J",
				"∀r z:A. r ∈ ann ∧ z ∈ I ⇒ r * z ∈ J",
				Derive(func(b *Argument) {
					r, z := b.FixAs[A]("r"), b.FixAs[A]("z")
					members := b.Assume()
					rData := b.Have(
						"r lies in S and kills u modulo J",
						"r ∈ S ∧ r * u ∈ J",
						BySets(definedAnn, members))
					s, t, data := b.Obtain2As[A, A](
						"write z as a multiple of u modulo J",
						"∃s t:A. s ∈ S ∧ t ∈ J ∧ z = s * u + t",
						By(cyclic.At(u, z), chosenU, members),
						Named("s", "t"))
					fields := b.Have(
						"all factors lie in the field",
						"r ∈ L.carrier ∧ z ∈ L.carrier ∧ s ∈ L.carrier ∧ u ∈ L.carrier ∧ t ∈ L.carrier",
						BySets(members, rData, data, uInL, iInS, jInS, inField))
					coefficients := b.Conjuncts(
						data,
						"s lies in S",
						"t lies in J",
						"z = s*u+t")
					regroup := b.Have(
						"multiply this expression by r",
						"r * z = s * (r * u) + r * t",
						coefficients[2].Rw(),
						ByArith(fieldRing, fields))
					first := b.Have(
						"the multiple of r*u lies in J",
						"s * (r * u) ∈ J",
						By(data, rData, ring_ideal.IdealMul.Read(idealJ).AsFact().At(s, b.TermAs[A]("r * u"))))
					second := b.Have(
						"the multiple of t lies in J",
						"r * t ∈ J",
						By(data, rData, ring_ideal.IdealMul.Read(idealJ).AsFact().At(r, t)))
					sum := b.Have(
						"their sum lies in J",
						"s * (r * u) + r * t ∈ J",
						By(
							first,
							second,
							ring_ideal.IdealAdd.Read(idealJ).AsFact().At(b.TermAs[A]("s * (r * u)"), b.TermAs[A]("r * t"))))
					b.Show(
						"r kills the coset of z",
						regroup.Rw(),
						By(sum))
				}))

			fieldModule := a.Have(
				"L is an S-module",
				"module_on(«layerRing», «layerField»)",
				By(subring, fractional_ideal.FieldModuleOn.Read(L).At(S)))
			fracI := a.Have(
				"I is a fractional ideal",
				"submodule(«layerRing», «layerField», I)",
				By(subring, idealI, fractional_ideal.IntegralIdealFractional.Read(L).At(S, I)))
			fracJ := a.Have(
				"J is a fractional ideal",
				"submodule(«layerRing», «layerField», J)",
				By(subring, idealJ, fractional_ideal.IntegralIdealFractional.Read(L).At(S, J)))
			colon := a.TermAs[Set[A]]("{y:A | y ∈ L.carrier ∧ (∀n:A. n ∈ {u} ⇒ y * n ∈ J)}")
			fracColon := a.Have(
				"the colon (J : {u}) is a fractional ideal",
				"submodule(«layerRing», «layerField», {y:A | y ∈ L.carrier ∧ (∀n:A. n ∈ {u} ⇒ y * n ∈ J)})",
				By(
					inField,
					fracJ,
					uInL,
					set_order.SingSubset.At(a.TermAs[Set[A]]("L.carrier"), u),
					fractional_ideal.ColonSubmodule.Read(L).At(S, J, a.TermAs[Set[A]]("{u}"))))
			annMeet := a.Have(
				"ann is the part of that colon in S",
				"ann = {y:A | y ∈ L.carrier ∧ (∀n:A. n ∈ {u} ⇒ y * n ∈ J)} ∩ S",
				BySets(definedAnn, inField))
			fracAnn := a.Have(
				"so ann is a fractional ideal, the meet of that colon and the fractional ideal S",
				"submodule(«layerRing», «layerField», ann)",
				annMeet.Rw(),
				By(
					fracColon,
					subring,
					fractional_ideal.SubringSubmodule.Read(L).At(S),
					submodule.SubmoduleInter.At(R, a.TermAs[module_record.ModuleOps[A, A]]("«layerField»"), colon, S)))
			mData := a.Conjuncts(
				a.Unfolded(invertible, fractional_ideal.InvertibleFractionalDef),
				"M is a fractional ideal",
				"its product with its inverse is S")
			fracM, inversePair := mData[0], mData[1]
			mInL := a.Have(
				"M lies in L",
				"M ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(fracM)))
			inverse := a.TermAs[Set[A]]("fractional_inverse(field_ring(L), S, M)")
			inverseInL := a.Have(
				"the inverse lies in L",
				"fractional_inverse(field_ring(L), S, M) ⊆ L.carrier",
				By(fractional_ideal.FractionalInverseSubset.Read(L).At(S, M)))
			x, f, chosenPair := a.Obtain2As[A, A](
				"some product x*f escapes ann: else ann would hold M · (S : M) = S, and one with it",
				"∃x f:A. x ∈ M ∧ f ∈ fractional_inverse(field_ring(L), S, M) ∧ x * f ∉ ann",
				BySets(
					fracAnn,
					inversePair,
					oneS,
					oneNotAnn,
					fractional_ideal.FractionalMulLeast.Read(L).At(S, M, inverse, ann)),
				Named("x", "f"))
			pairFields := a.Have(
				"x and f lie in L",
				"x ∈ L.carrier ∧ f ∈ L.carrier",
				BySets(chosenPair, mInL, inverseInL))
			xInL := a.Have(
				"x lies in L",
				"x ∈ L.carrier",
				By(pairFields))
			fxS := a.Have(
				"an inverse multiplier carries x into S",
				"f * x ∈ S",
				BySets(
					chosenPair,
					fractional_ideal.FractionalInverseDef.At(
						a.TermAs[module_record.RingOps[A]]("field_ring(L)"), S, M)))
			commutePair := a.Have(
				"commute the two factors",
				"x * f = f * x",
				ByArith(fieldRing, pairFields))
			xfS := a.Have(
				"x*f lies in S",
				"x * f ∈ S",
				commutePair.Rw(),
				By(fxS))
			v, chosenV := a.ObtainAs[A](
				"invert x*f modulo ann",
				"∃v:A. v ∈ S ∧ v * (x * f) - L.one ∈ ann",
				By(unitOutside.At(a.TermAs[A]("x * f")), xfS, chosenPair),
				Named("v"))
			vInL := a.Have(
				"v lies in L",
				"v ∈ L.carrier",
				BySets(chosenV, inField))
			back, definedBack := a.LetAs[A]("back", "v * f")
			defect, definedDefect := a.LetAs[A]("defect", "back * x - L.one")
			backInL := a.Have(
				"the inverse scalar lies in L",
				"back ∈ L.carrier",
				definedBack.Rw(),
				By(vInL, pairFields, comm_ring.MulIn.Read(fieldRing).AsFact().At(v, f)))
			defectEq := a.Have(
				"the inverse defect is the chosen annihilator element",
				"defect = v * (x * f) - L.one",
				definedDefect.Rw(),
				definedBack.Rw(),
				ByArith(fieldRing, vInL, pairFields))
			defectAnn := a.Have(
				"the defect belongs to ann",
				"defect ∈ ann",
				defectEq.Rw(),
				By(chosenV))
			defectInL := a.Have(
				"the defect lies in L",
				"defect ∈ L.carrier",
				BySets(defectAnn, annInS, inField))

			cancel := a.Have(
				"multiplication by the inverse cancels M on every fractional ideal",
				Statement{
					Binders: "∀K:set(A).",
					Hypotheses: []string{
						"submodule(«layerRing», «layerField», K)",
					},
					Conclusion: "fractional_mul(field_ring(L), " +
						"    S, " +
						"    fractional_mul(field_ring(L), S, K, M), " +
						"    fractional_inverse(field_ring(L), S, M)) = " +
						"K",
				},
				Derive(func(b *Argument) {
					K := b.FixAs[Set[A]]("K")
					fracK := b.Assume()
					kInL := b.Have(
						"K lies in L",
						"K ⊆ L.carrier",
						By(submodule.SubmoduleSubset.Read(fracK)))
					b.Show(
						"associate, cancel M, and use S as the product unit",
						CalcEq(
							Leg(
								b.TermAs[Set[A]](
									"fractional_mul(field_ring(L), "+
										"    S, "+
										"    K, "+
										"    fractional_mul(field_ring(L), S, M, fractional_inverse(field_ring(L), S, M)))"),
								"associate the factors",
								By(
									subring,
									kInL,
									mInL,
									inverseInL,
									fractional_ideal.FractionalMulAssoc.Read(L).At(S, K, M, inverse))),
							Leg(
								b.TermAs[Set[A]]("fractional_mul(field_ring(L), S, K, S)"),
								"M times its inverse is S",
								inversePair.Rw(),
								Basic()),
							Leg(
								b.TermAs[Set[A]]("fractional_mul(field_ring(L), S, S, K)"),
								"commute S to the left",
								By(kInL, inField, fractional_ideal.FractionalMulComm.Read(L).At(S, K, S))),
							FinalLeg(
								"S is the product unit",
								By(subring, fracK, fractional_ideal.FractionalMulOne.Read(L).At(S, K)))))
				}))
			forward := a.Have(
				"multiplication by x carries each fractional ideal K into K*M",
				Statement{
					Binders: "∀K:set(A).",
					Hypotheses: []string{
						"submodule(«layerRing», «layerField», K)",
					},
					Conclusion: "image(L.mul(x), K) ⊆ fractional_mul(field_ring(L), S, K, M)",
				},
				Derive(func(b *Argument) {
					K := b.FixAs[Set[A]]("K")
					fracK := b.Assume()
					points := b.Have(
						"x times every member of K lies in K*M",
						"∀z:A. z ∈ K ⇒ x * z ∈ fractional_mul(field_ring(L), S, K, M)",
						Derive(func(c *Argument) {
							z := c.FixAs[A]("z")
							member := c.Assume()
							zInL := c.Have(
								"z lies in L",
								"z ∈ L.carrier",
								BySets(member, submodule.SubmoduleSubset.Read(fracK)))
							commute := c.Have(
								"commute z and x",
								"x * z = z * x",
								ByArith(fieldRing, zInL, pairFields))
							generator := c.Have(
								"z*x is a product generator",
								"z * x ∈ fractional_mul(field_ring(L), S, K, M)",
								By(member, chosenPair, fractional_ideal.FractionalMulHolds.Read(L).At(S, K, M, z, x)))
							c.Show(
								"x*z is the same generator",
								commute.Rw(),
								By(generator))
						}))
					b.Show(
						"the scalar image lies in K*M",
						BySets(points))
				}))
			backward := a.Have(
				"multiplication by back carries K*M back into K",
				Statement{
					Binders: "∀K:set(A).",
					Hypotheses: []string{
						"submodule(«layerRing», «layerField», K)",
					},
					Conclusion: "image(L.mul(back), fractional_mul(field_ring(L), S, K, M)) ⊆ K",
				},
				Derive(func(b *Argument) {
					K := b.FixAs[Set[A]]("K")
					fracK := b.Assume()
					KM := b.TermAs[Set[A]]("fractional_mul(field_ring(L), S, K, M)")
					fracKM := b.Have(
						"K*M is a fractional ideal",
						"submodule(«layerRing», «layerField», fractional_mul(field_ring(L), S, K, M))",
						By(
							subring,
							submodule.SubmoduleSubset.Read(fracK),
							mInL,
							fractional_ideal.FractionalMulSubmodule.Read(L).At(S, K, M)))
					points := b.Have(
						"back times every member of K*M lies in K",
						"∀z:A. z ∈ fractional_mul(field_ring(L), S, K, M) ⇒ back * z ∈ K",
						Derive(func(c *Argument) {
							z := c.FixAs[A]("z")
							member := c.Assume()
							product := c.Have(
								"z*f lies in the product with the inverse",
								"z * f ∈ "+
									"fractional_mul(field_ring(L), "+
									"    S, "+
									"    fractional_mul(field_ring(L), S, K, M), "+
									"    fractional_inverse(field_ring(L), S, M))",
								By(member, chosenPair, fractional_ideal.FractionalMulHolds.Read(L).At(S, KM, inverse, z, f)))
							zfK := c.Have(
								"cancellation puts z*f in K",
								"z * f ∈ K",
								BySets(product, cancel.At(K), fracK))
							vzfK := c.Have(
								"v multiplies it within K",
								"v * (z * f) ∈ K",
								By(chosenV, zfK, submodule.SubmoduleSmul.Read(fracK).AsFact().At(v, c.TermAs[A]("z * f"))))
							zInL := c.Have(
								"z lies in L",
								"z ∈ L.carrier",
								BySets(member, submodule.SubmoduleSubset.Read(fracKM)))
							regroup := c.Have(
								"back*z is the same scalar multiple",
								"back * z = v * (z * f)",
								definedBack.Rw(),
								ByArith(fieldRing, vInL, pairFields, zInL))
							c.Show(
								"back*z lies in K",
								regroup.Rw(),
								By(vzfK))
						}))
					b.Show(
						"the scalar image lies in K",
						BySets(points))
				}))

			IM, definedIM := a.LetAs[Set[A]]("IM", "fractional_mul(field_ring(L), S, I, M)")
			JM, definedJM := a.LetAs[Set[A]]("JM", "fractional_mul(field_ring(L), S, J, M)")
			iInL := a.Have(
				"I lies in L",
				"I ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(fracI)))
			fracIM := a.Have(
				"IM is a fractional ideal",
				"submodule(«layerRing», «layerField», IM)",
				definedIM.Rw(),
				By(subring, iInL, mInL, fractional_ideal.FractionalMulSubmodule.Read(L).At(S, I, M)))
			fracJM := a.Have(
				"JM is a fractional ideal",
				"submodule(«layerRing», «layerField», JM)",
				definedJM.Rw(),
				By(
					subring,
					submodule.SubmoduleSubset.Read(fracJ),
					mInL,
					fractional_ideal.FractionalMulSubmodule.Read(L).At(S, J, M)))
			xI := a.Have(
				"x carries I into IM",
				"image(L.mul(x), I) ⊆ IM",
				definedIM.Rw(),
				By(forward.At(I), fracI))
			xJ := a.Have(
				"x carries J into JM",
				"image(L.mul(x), J) ⊆ JM",
				definedJM.Rw(),
				By(forward.At(J), fracJ))
			backIM := a.Have(
				"back carries IM into I",
				"image(L.mul(back), IM) ⊆ I",
				definedIM.Rw(),
				By(backward.At(I), fracI))
			backJM := a.Have(
				"back carries JM into J",
				"image(L.mul(back), JM) ⊆ J",
				definedJM.Rw(),
				By(backward.At(J), fracJ))
			jmInIM := a.Have(
				"JM lies in IM",
				"JM ⊆ IM",
				definedJM.Rw(),
				definedIM.Rw(),
				By(jInI, set_order.SubsetRefl.At(M), fractional_ideal.FractionalMulMono.Read(L).At(S, J, I, M, M)))
			defectI := a.Have(
				"the defect carries I into J",
				"image(L.mul(defect), I) ⊆ J",
				BySets(defectAnn, annKills))
			scaledDefect := a.Have(
				"scaling commutes with multiplication by M",
				"fractional_mul(field_ring(L), S, image(L.mul(defect), I), M) = image(L.mul(defect), IM)",
				definedIM.Rw(),
				By(
					subring,
					defectInL,
					iInL,
					mInL,
					fractional_ideal.FractionalMulScale.Read(L).AsFact().At(S, I, M, defect)))
			smallProduct := a.Have(
				"multiplying the defect image by M stays in JM",
				"fractional_mul(field_ring(L), S, image(L.mul(defect), I), M) ⊆ JM",
				definedJM.Rw(),
				By(
					defectI,
					set_order.SubsetRefl.At(M),
					fractional_ideal.FractionalMulMono.Read(L).At(
						S, a.TermAs[Set[A]]("image(L.mul(defect), I)"), J, M, M)))
			defectIM := a.Have(
				"the defect carries IM into JM",
				"image(L.mul(defect), IM) ⊆ JM",
				scaledDefect.RwRev(),
				By(smallProduct))
			F, forwardMap := a.ObtainAs[Fun[Set[A], Set[A]]](
				"multiplication by x descends to the quotient layers",
				"∃F:(set(A) → set(A)). "+
					"    module_homomorphism(«layerRing», "+
					"        «sourceLayer», "+
					"        quotient_module(restrict_module(«layerField», IM), JM), "+
					"        F) ∧ "+
					"    (∀u:A. u ∈ I ⇒ F(left_coset(L.add, u, J)) = left_coset(L.add, x * u, JM))",
				By(
					subring,
					fracI,
					fracIM,
					fracJ,
					fracJM,
					jInI,
					jmInIM,
					xI,
					xJ,
					ScaleQuotientHom.Read(L).At(S, I, IM, J, JM, a.MemberOf[on.L](x, xInL))),
				Named("F"))
			fParts := a.Conjuncts(
				forwardMap,
				"F is linear",
				"F multiplies representatives by x")
			fHom, fFormula := fParts[0], fParts[1]
			_, backwardMap := a.ObtainAs[Fun[Set[A], Set[A]]](
				"multiplication by back descends in the other direction",
				"∃G:(set(A) → set(A)). "+
					"    module_homomorphism(«layerRing», "+
					"        quotient_module(restrict_module(«layerField», IM), JM), "+
					"        «sourceLayer», "+
					"        G) ∧ "+
					"    (∀u:A. u ∈ IM ⇒ G(left_coset(L.add, u, JM)) = left_coset(L.add, back * u, J))",
				By(
					subring,
					fracIM,
					fracI,
					fracJM,
					fracJ,
					jmInIM,
					jInI,
					backIM,
					backJM,
					ScaleQuotientHom.Read(L).At(S, IM, I, JM, J, a.MemberOf[on.L](back, backInL))),
				Named("G"))
			gParts := a.Conjuncts(
				backwardMap,
				"G is linear",
				"G multiplies representatives by back")
			gHom, gFormula := gParts[0], gParts[1]

			cosetInverse := a.Have(
				"a defect in the denominator makes both scalar composites the identity on cosets",
				"∀K:set(A). "+
					"    subgroup(module_additive_group(«layerField»), K) ⇒ "+
					"    ∀z:A. "+
					"        z ∈ L.carrier ∧ defect * z ∈ K ⇒ "+
					"        left_coset(L.add, back * (x * z), K) = left_coset(L.add, z, K) ∧ "+
					"        left_coset(L.add, x * (back * z), K) = left_coset(L.add, z, K)",
				Derive(func(b *Argument) {
					K := b.FixAs[Set[A]]("K")
					subgroup := b.Assume()
					z := b.FixAs[A]("z")
					members := b.Assume()
					difference := b.Have(
						"the composite differs from z by defect*z",
						"-z + back * (x * z) = defect * z",
						definedDefect.Rw(),
						ByArith(fieldRing, backInL, pairFields, members))
					inK := b.Have(
						"that difference lies in K",
						"-z + back * (x * z) ∈ K",
						difference.Rw(),
						By(members))
					productL := b.Have(
						"the composite lies in L",
						"back * (x * z) ∈ L.carrier",
						By(
							backInL,
							pairFields,
							members,
							comm_ring.MulIn.Read(fieldRing).AsFact().At(x, z),
							comm_ring.MulIn.Read(fieldRing).AsFact().At(back, b.TermAs[A]("x * z"))))
					first := b.Have(
						"the first composite has the same coset as z",
						"left_coset(L.add, back * (x * z), K) = left_coset(L.add, z, K)",
						By(
							members,
							productL,
							subgroup,
							inK,
							group.LeftCosetEqOn.Read(module.AddGroupOn.Read(fieldModule)).AsFact().At(
								z, b.TermAs[A]("back * (x * z)"), K)))
					commute := b.Have(
						"the other scalar composite is equal",
						"x * (back * z) = back * (x * z)",
						ByArith(fieldRing, backInL, pairFields, members))
					b.Show(
						"both composites fix this coset",
						SplitConj(Case(
							"back after x",
							By(first)), Case(
							"x after back",
							commute.Rw(),
							By(first))))
				}))
			gfRepresentatives := a.Have(
				"G after F fixes every representative in I",
				"∀z:A. z ∈ I ⇒ G(F(left_coset(L.add, z, J))) = left_coset(L.add, z, J)",
				Derive(func(b *Argument) {
					z := b.FixAs[A]("z")
					member := b.Assume()
					xzIM := b.Have(
						"x*z lies in IM",
						"x * z ∈ IM",
						BySets(member, xI))
					zInL := b.Have(
						"z lies in L",
						"z ∈ L.carrier",
						BySets(member, iInL))
					defectZJ := b.Have(
						"defect*z lies in J",
						"defect * z ∈ J",
						BySets(member, defectI))
					coset := b.Have(
						"the scalar round trip fixes the source coset",
						"left_coset(L.add, back * (x * z), J) = left_coset(L.add, z, J)",
						By(cosetInverse.At(J, z), submodule.SubmoduleSubgroup.Read(fracJ), zInL, defectZJ))
					fAt := b.Have(
						"evaluate F on this representative",
						"F(left_coset(L.add, z, J)) = left_coset(L.add, x * z, JM)",
						By(fFormula.At(z), member))
					gAt := b.Have(
						"evaluate G on its image",
						"G(left_coset(L.add, x * z, JM)) = left_coset(L.add, back * (x * z), J)",
						By(gFormula.At(b.TermAs[A]("x * z")), xzIM))
					b.Show(
						"the two evaluations return the original coset",
						fAt.Rw(),
						gAt.Rw(),
						By(coset))
				}))
			fgRepresentatives := a.Have(
				"F after G fixes every representative in IM",
				"∀z:A. z ∈ IM ⇒ F(G(left_coset(L.add, z, JM))) = left_coset(L.add, z, JM)",
				Derive(func(b *Argument) {
					z := b.FixAs[A]("z")
					member := b.Assume()
					backZI := b.Have(
						"back*z lies in I",
						"back * z ∈ I",
						BySets(member, backIM))
					zInL := b.Have(
						"z lies in L",
						"z ∈ L.carrier",
						BySets(member, submodule.SubmoduleSubset.Read(fracIM)))
					defectZJM := b.Have(
						"defect*z lies in JM",
						"defect * z ∈ JM",
						BySets(member, defectIM))
					coset := b.Have(
						"the scalar round trip fixes the target coset",
						"left_coset(L.add, x * (back * z), JM) = left_coset(L.add, z, JM)",
						By(cosetInverse.At(JM, z), submodule.SubmoduleSubgroup.Read(fracJM), zInL, defectZJM))
					gAt := b.Have(
						"evaluate G on this representative",
						"G(left_coset(L.add, z, JM)) = left_coset(L.add, back * z, J)",
						By(gFormula.At(z), member))
					fAt := b.Have(
						"evaluate F on its image",
						"F(left_coset(L.add, back * z, J)) = left_coset(L.add, x * (back * z), JM)",
						By(fFormula.At(b.TermAs[A]("back * z")), backZI))
					b.Show(
						"the two evaluations return the original coset",
						gAt.Rw(),
						fAt.Rw(),
						By(coset))
				}))
			moduleI := a.Have(
				"I inherits its module structure",
				"module_on(«layerRing», restrict_module(«layerField», I))",
				By(fracI, submodule.SubmoduleModuleOn.Read(fieldModule).At(I)))
			gf := a.Have(
				"G after F is the identity on I/J",
				"∀C:set(A). C ∈ left_cosets(L.add, I, J) ⇒ G(F(C)) = C",
				By(
					jInI,
					gfRepresentatives,
					quotient_group.ForallInLeftCosets.Read(module.AddGroupOn.Read(moduleI)).AsFact().At(
						J, a.TermAs[Fun[Set[A], Bool]]("λC:set(A). G(F(C)) = C"))))
			moduleIM := a.Have(
				"IM inherits its module structure",
				"module_on(«layerRing», restrict_module(«layerField», IM))",
				By(fracIM, submodule.SubmoduleModuleOn.Read(fieldModule).At(IM)))
			fg := a.Have(
				"F after G is the identity on IM/JM",
				"∀C:set(A). C ∈ left_cosets(L.add, IM, JM) ⇒ F(G(C)) = C",
				By(
					jmInIM,
					fgRepresentatives,
					quotient_group.ForallInLeftCosets.Read(module.AddGroupOn.Read(moduleIM)).AsFact().At(
						JM, a.TermAs[Fun[Set[A], Bool]]("λC:set(A). F(G(C)) = C"))))
			injective := a.Have(
				"the left inverse makes F injective",
				"injective_on(left_cosets(L.add, I, J), F)",
				Unfold(functions.InjectiveOnDef),
				By(gf))
			onto := a.Have(
				"the right inverse makes F onto",
				"image(F, left_cosets(L.add, I, J)) = left_cosets(L.add, IM, JM)",
				BySets(fg, module_homomorphism.HomIn.Read(fHom), module_homomorphism.HomIn.Read(gHom)))
			QI := a.TermAs[module_record.ModuleOps[A, Set[A]]]("«sourceLayer»")
			QT := a.TermAs[module_record.ModuleOps[A, Set[A]]](
				"quotient_module(restrict_module(«layerField», IM), JM)")
			isomorphism := a.Have(
				"F is an S-linear isomorphism between the layers",
				"module_isomorphism(«layerRing», "+
					"    «sourceLayer», "+
					"    quotient_module(restrict_module(«layerField», IM), JM), "+
					"    F)",
				By(fHom, injective, onto, module_homomorphism.ModuleIsomorphismDef.At(R, QI, QT, F)))
			a.Show(
				"the simple layer is preserved by multiplication by M",
				By(isomorphism, module_homomorphism.IsomorphicOfIsomorphism.At(R, QI, QT, F)))
		}),
})}

// InvertibleIdealResidueLine — for an invertible M, M/mM is one-dimensional
// over the actual residue field S/m, whether or not that field embeds back into
// S. Since S · M = M and m is maximal, InvertibleSimpleLayer at S and m gives an
// S-linear isomorphism f of S/m onto M/mM. M/mM is ideal_quotient_module: its
// denominator, the span of the products i * x, is the product mM, and S/m acts
// on its cosets by multiplication on representatives,
// (s + m)(x + mM) = s * x + mM, the cross terms lying in mM, so the same f is
// S/m-linear. The regular module S/m has a singleton basis, and f transfers its
// dimension to M/mM.
var InvertibleIdealResidueLine = invertibleIdealResidueLineThm{family.Add(registry.ProofEntry{
	Name: "InvertibleIdealResidueLine",
	Key:  "prop_df22e23cb7f5b435",
	Reading: "The scalar and vector types are both set(A), with carriers consisting " +
		"only of cosets. Maximality makes S/m a field, and invertibility makes M/mM a " +
		"line; m itself need not be invertible, so m={zero} when S is a field is included.",
	Build: family.Sections(
		Statement{
			Binders: "∀L:field_on(A). ∀S M m:set(A).",
			Hypotheses: []string{
				"subring(field_ring(L), S)",
				"«wfInvertible»(M)",
				"maximal_ideal(«wfScalars», m)",
			},
			Conclusion: "module_on(«residueScalars», «residueVectors») ∧ " +
				"finite_dimensional(«residueScalars», «residueVectors») ∧ " +
				"module_dim(«residueScalars», «residueVectors») = 1",
			Abbrev: Abbrev{
				{Name: "residueScalars", Text: "ideal_quotient_ring(«wfScalars», m)"},
				{Name: "residueVectors", Text: "ideal_quotient_module(«wfScalars», " +
					"    m, " +
					"    restrict_module(«wfField», M))"},
				{Name: "residueRecord", Text: "mk_module(set_mul(L.add), " +
					"    «wfMul»(m, M), " +
					"    set_inv(L.neg), " +
					"    quotient_mul(«wfMul»(m, M)), " +
					"    left_cosets(L.add, M, «wfMul»(m, M)))"},
				{Name: "regularResidue", Text: "regular_module(«residueScalars»)"},
				{Name: "residueProducts", Text: "{i * x | i:A, x:A | i ∈ m ∧ x ∈ M}"},
			},
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// M/mM is the record of the cosets of mM: the denominator of the ideal
			// quotient module is the span of the products i * x, which is mM.
			residueBridge := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀S M m:set(A).",
				Hypotheses: []string{
					"subring(field_ring(L), S)",
					"«wfFractional»(M)",
					"«wfIdeal»(m)",
				},
				Conclusion: "«residueVectors» = «residueRecord»",
			}, func(a *Argument, L field.FieldFact[on.L], S, M, m *Expr[Set[A]], given Fact) {
				p := a.Conjuncts(
					given,
					"S is a subring",
					"M is an S-submodule",
					"m is an ideal")
				subring, fractionalM, ideal := p[0], p[1], p[2]
				scalars := a.TermAs[module_record.RingOps[A]]("«wfScalars»")
				vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wfField»")
				VM := a.TermAs[module_record.ModuleOps[A, A]]("restrict_module(«wfField», M)")
				generatorsInM := a.Have(
					"the product generators lie in M",
					"«residueProducts» ⊆ M",
					BySets(ring_ideal.IdealSubset.Read(ideal), submodule.SubmoduleSmul.Read(fractionalM)))
				spannedProducts := a.Have(
					"spanning those products inside M gives mM",
					"module_span(«wfScalars», restrict_module(«wfField», M), «residueProducts») = «wfMul»(m, M)",
					By(
						subring,
						fractional_ideal.FieldModuleOn.Read(L).At(S),
						fractionalM,
						generatorsInM,
						linear_independence.SpanRestrict.At(scalars, vectors, M, a.TermAs[Set[A]]("«residueProducts»")),
						fractional_ideal.FractionalMulDef.At(a.TermAs[module_record.RingOps[A]]("field_ring(L)"), S, m, M)))
				a.Show(
					"the ideal quotient module of M is the module of cosets of mM, mM being the span of the products",
					By(
						spannedProducts,
						flat_module.IdealQuotientModuleDef.At(scalars, m, VM),
						quotient_ring.QuotientMulDef,
						quotient_group.SetMulDef))
			})

			mixedAction := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀S M m:set(A). ∀s x:A.",
				Hypotheses: []string{
					"subring(field_ring(L), S)",
					"«wfFractional»(M)",
					"«wfIdeal»(m)",
					"s ∈ S",
					"x ∈ M",
				},
				Conclusion: "quotient_mul(«wfMul»(m, M), " +
					"    left_coset(L.add, s, m), " +
					"    left_coset(L.add, x, «wfMul»(m, M))) = " +
					"left_coset(L.add, s * x, «wfMul»(m, M))",
			}, func(a *Argument, L field.FieldFact[on.L], S, M, m *Expr[Set[A]], s, x *Expr[A], given Fact) {
				p := a.Conjuncts(
					given,
					"S is a subring",
					"M is an S-submodule",
					"m is an ideal",
					"s lies in S",
					"x lies in M")
				subring, fractionalM, ideal, sInS, xInM := p[0], p[1], p[2], p[3], p[4]
				ambient := a.Have(
					"L is an S-module",
					"module_on(«wfScalars», «wfField»)",
					By(subring, fractional_ideal.FieldModuleOn.Read(L).At(S)))
				sInL := a.Have(
					"S lies in L",
					"S ⊆ L.carrier",
					By(comm_ring.SubringSubset.Read(subring)))
				mInL := a.Have(
					"M lies in L",
					"M ⊆ L.carrier",
					By(submodule.SubmoduleSubset.Read(fractionalM)))
				idealInS := a.Have(
					"m lies in S",
					"m ⊆ S",
					By(ring_ideal.IdealSubset.Read(ideal)))
				idealInL := a.Have(
					"so m lies in L",
					"m ⊆ L.carrier",
					BySets(idealInS, sInL))
				fractionalIdeal := a.Have(
					"m is an S-submodule of L",
					"«wfFractional»(m)",
					By(subring, ideal, fractional_ideal.IntegralIdealFractional.Read(L).At(S, m)))
				fractionalMM := a.Have(
					"mM is an S-submodule",
					"«wfFractional»(«wfMul»(m, M))",
					By(subring, idealInL, mInL, fractional_ideal.FractionalMulSubmodule.Read(L).At(S, m, M)))
				inL := a.Have(
					"the representatives lie in L",
					"s ∈ L.carrier ∧ x ∈ L.carrier",
					BySets(sInS, xInM, sInL, mInL))
				own := a.Have(
					"each representative belongs to its own coset",
					"s ∈ left_coset(L.add, s, m) ∧ x ∈ left_coset(L.add, x, «wfMul»(m, M))",
					By(
						inL,
						submodule.SubmoduleSubgroup.Read(fractionalIdeal),
						submodule.SubmoduleSubgroup.Read(fractionalMM),
						group.InOwnLeftCosetOn.Read(module.AddGroupOn.Read(ambient))))
				points := a.Have(
					"the mixed product and the product coset have the same points",
					"∀z:A. "+
						"    z ∈ "+
						"    quotient_mul(«wfMul»(m, M), left_coset(L.add, s, m), left_coset(L.add, x, «wfMul»(m, M))) ⇔ "+
						"    z ∈ left_coset(L.add, s * x, «wfMul»(m, M))",
					Derive(func(b *Argument) {
						b.FixAs[A]("z")
						b.Iff()
						b.Forward(
							"expand a point of the mixed product",
							func(c *Argument, member Fact) {
								_, _, _, point := c.Obtain3As[A, A, A](
									"take its three denominator terms",
									"∃i u e:A. i ∈ m ∧ u ∈ «wfMul»(m, M) ∧ e ∈ «wfMul»(m, M) ∧ z = (s + i) * (x + u) + e",
									member.Simp(
										Fwd(quotient_ring.QuotientMulDef),
										Fwd(quotient_group.InSetMul),
										Fwd(group.LeftCosetDef),
										Fwd(set_basic.InImage)),
									By(member))
								terms := c.Have(
									"the three terms lie in L",
									"i ∈ L.carrier ∧ u ∈ L.carrier ∧ e ∈ L.carrier",
									BySets(point, idealInL, submodule.SubmoduleSubset.Read(fractionalMM)))
								errorIn := c.Have(
									"every cross term lies in mM, so the remaining sum does",
									"s * u + i * x + i * u + e ∈ «wfMul»(m, M)",
									BySets(
										point,
										sInS,
										xInM,
										idealInS,
										submodule.SubmoduleSmul.Read(fractionalMM),
										submodule.SubmoduleAdd.Read(fractionalMM),
										fractional_ideal.FractionalMulHolds.Read(L).AsFact().At(S, m, M)))
								expansion := c.Have(
									"expand the product of representatives with denominator terms",
									"(s + i) * (x + u) + e = s * x + (s * u + i * x + i * u + e)",
									ByArith(field.RingOn.Read(L), inL, terms))
								c.Show(
									"so the point belongs to the product coset",
									Simp(Fwd(group.LeftCosetDef), Fwd(set_basic.InImage)),
									Witness(c.TermAs[A]("s * u + i * x + i * u + e")),
									By(errorIn, point, expansion))
							})
						b.Backward(
							"use the two representatives and the remaining denominator term",
							func(c *Argument, member Fact) {
								e, point := c.UnpackAs[A](c.Simplified(
									member,
									Fwd(group.LeftCosetDef),
									Fwd(set_basic.InImage)), "e")
								c.Show(
									"their product reconstructs the original point",
									Simp(Fwd(quotient_ring.QuotientMulDef), Fwd(quotient_group.InSetMul)),
									Witness(c.TermAs[A]("s * x")),
									Witness(e),
									SplitConjAll(
										Case(
											"the point is the product plus e",
											By(point)),
										Case(
											"s times x belongs to the product of the two cosets",
											Witness(s),
											Witness(x),
											By(own)),
										Case(
											"e lies in mM",
											By(point))))
							})
					}))
				a.Show(
					"therefore the two cosets are equal",
					By(points, set_basic.Extension))
			})

			// S/m is a field, and M/mM is isomorphic to it as a module over it.
			residueIsomorphism := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀S M m:set(A).",
				Hypotheses: []string{
					"subring(field_ring(L), S)",
					"«wfInvertible»(M)",
					"maximal_ideal(«wfScalars», m)",
				},
				Conclusion: "field_on(ideal_quotient_field(«wfScalars», m)) ∧ " +
					"comm_ring_on(«residueScalars») ∧ " +
					"module_on(«residueScalars», «residueVectors») ∧ " +
					"module_isomorphic(«residueScalars», «regularResidue», «residueVectors»)",
			}, func(a *Argument, L field.FieldFact[on.L], S, M, m *Expr[Set[A]], given Fact) {
				p := a.Conjuncts(
					given,
					"S is a subring",
					"M is invertible",
					"m is maximal")
				subring, invertible, maximal := p[0], p[1], p[2]
				fieldOps := a.TermAs[field.FieldOps[A]]("L")
				scalars := a.TermAs[module_record.RingOps[A]]("«wfScalars»")
				vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wfField»")
				VM := a.TermAs[module_record.ModuleOps[A, A]]("restrict_module(«wfField», M)")
				VS := a.TermAs[module_record.ModuleOps[A, A]]("restrict_module(«wfField», S)")
				mM := a.TermAs[Set[A]]("«wfMul»(m, M)")
				residueScalars := a.TermAs[module_record.RingOps[Set[A]]]("«residueScalars»")
				residueRecord := a.TermAs[module_record.ModuleOps[Set[A], Set[A]]]("«residueRecord»")
				regularResidue := a.TermAs[module_record.ModuleOps[Set[A], Set[A]]]("«regularResidue»")
				ringS := a.Have(
					"S is a commutative ring",
					"comm_ring_on(«wfScalars»)",
					By(subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
				ambient := a.Have(
					"L is an S-module",
					"module_on(«wfScalars», «wfField»)",
					By(subring, fractional_ideal.FieldModuleOn.Read(L).At(S)))
				fractionalM := a.Have(
					"M is an S-submodule",
					"«wfFractional»(M)",
					By(invertible, fractional_ideal.InvertibleFractionalDef))
				ideal := a.Have(
					"m is an ideal",
					"«wfIdeal»(m)",
					By(maximal, ring_ideal.MaximalIdealIdeal))
				idealInS := a.Have(
					"m lies in S",
					"m ⊆ S",
					By(ring_ideal.IdealSubset.Read(ideal)))
				fractionalIdeal := a.Have(
					"m is an S-submodule of L",
					"«wfFractional»(m)",
					By(subring, ideal, fractional_ideal.IntegralIdealFractional.Read(L).At(S, m)))
				fractionalMM := a.Have(
					"mM is an S-submodule",
					"«wfFractional»(«wfMul»(m, M))",
					By(
						subring,
						submodule.SubmoduleSubset.Read(fractionalIdeal),
						submodule.SubmoduleSubset.Read(fractionalM),
						fractional_ideal.FractionalMulSubmodule.Read(L).At(S, m, M)))
				moduleM := a.Have(
					"M inherits its S-module structure",
					"module_on(«wfScalars», restrict_module(«wfField», M))",
					By(fractionalM, submodule.SubmoduleModuleOn.Read(ambient).At(M)))
				productsInM := a.Have(
					"multiples by m stay in M",
					"∀i x:A. i ∈ m ∧ x ∈ M ⇒ i * x ∈ M",
					BySets(idealInS, submodule.SubmoduleSmul.Read(fractionalM)))
				mMInM := a.Have(
					"the product mM lies in M",
					"«wfMul»(m, M) ⊆ M",
					By(fractionalM, productsInM, fractional_ideal.FractionalMulLeast.Read(L).At(S, m, M, M)))
				unitProduct := a.Have(
					"multiplication by S fixes M",
					"«wfMul»(S, M) = M",
					By(subring, fractionalM, fractional_ideal.FractionalMulOne.Read(L).At(S, M)))
				linearLayers := a.Have(
					"multiplication by M preserves that simple layer",
					"module_isomorphic(«wfScalars», «quotient»(S, m), «quotient»(M, «wfMul»(m, M)))",
					By(
						Normalized,
						subring,
						invertible,
						maximal,
						ring_ideal.MaximalIdealCover.Read(ringS),
						unitProduct,
						InvertibleSimpleLayer.Read(L).At(S, M, S, m)))
				f, isoS := a.UnpackAs[Fun[Set[A], Set[A]]](
					a.Unfolded(linearLayers, module_homomorphism.ModuleIsomorphicDef), "f")
				isoParts := a.Conjuncts(
					a.Unfolded(isoS, module_homomorphism.ModuleIsomorphismDef),
					"f is S-linear",
					"f is injective",
					"f is onto")
				homS, injective, onto := isoParts[0], isoParts[1], isoParts[2]
				moduleS := a.Have(
					"S inherits its S-module structure",
					"module_on(«wfScalars», restrict_module(«wfField», S))",
					By(
						subring,
						fractional_ideal.SubringSubmodule.Read(L).At(S),
						submodule.SubmoduleModuleOn.Read(ambient).At(S)))
				denomS := a.Have(
					"m is a submodule of S",
					"submodule(«wfScalars», restrict_module(«wfField», S), m)",
					By(fractionalIdeal, idealInS, submodule.SubmoduleRestrict.At(scalars, vectors, S, m)))
				denomM := a.Have(
					"mM is a submodule of M",
					"submodule(«wfScalars», restrict_module(«wfField», M), «wfMul»(m, M))",
					By(fractionalMM, mMInM, submodule.SubmoduleRestrict.At(scalars, vectors, M, mM)))
				residueRing := a.Have(
					"S/m is a commutative ring",
					"comm_ring_on(«residueScalars»)",
					By(ideal, quotient_ring.QuotientRingOn.Read(ringS).At(m)))
				bridge := a.Have(
					"M/mM is the module of cosets of mM",
					"«residueVectors» = «residueRecord»",
					By(L, subring, fractionalM, ideal, At(residueBridge, fieldOps, S, M, m)))
				residueModule := a.Have(
					"M/mM is a module over S/m",
					"module_on(«residueScalars», «residueRecord»)",
					By(moduleM, ideal, bridge, flat_module.IdealQuotientModuleOn.At(scalars, VM, m)))
				linearRepresentatives := a.Have(
					"f respects residue scalars on representatives",
					Statement{
						Binders: "∀s t:A.",
						Hypotheses: []string{
							"s ∈ S",
							"t ∈ S",
						},
						Conclusion: "f(quotient_mul(m, left_coset(L.add, s, m), left_coset(L.add, t, m))) = " +
							"quotient_mul(«wfMul»(m, M), left_coset(L.add, s, m), f(left_coset(L.add, t, m)))",
					},
					Derive(func(b *Argument) {
						s := b.FixAs[A]("s")
						t := b.FixAs[A]("t")
						members := b.Assume()
						tCoset := b.TermAs[Set[A]]("left_coset(L.add, t, m)")
						cosetIn := b.Have(
							"the source representative defines a residue coset",
							"left_coset(L.add, t, m) ∈ left_cosets(L.add, S, m)",
							By(
								idealInS,
								members,
								quotient_group.LeftCosetInLeftCosets.Read(module.AddGroupOn.Read(moduleS)).AsFact().At(m, t)))
						x, representative := b.ObtainAs[A](
							"choose a representative in M of the image of that coset",
							"∃x:A. f(left_coset(L.add, t, m)) = left_coset(L.add, x, «wfMul»(m, M)) ∧ x ∈ M",
							By(
								mMInM,
								cosetIn,
								module_homomorphism.HomIn.Read(homS).AsFact().At(tCoset),
								quotient_group.InLeftCosets.Read(module.AddGroupOn.Read(moduleM)).AsFact().At(
									mM, b.TermAs[Set[A]]("f(left_coset(L.add, t, m))"))))
						b.Show(
							"the two scalar actions agree through f",
							CalcEq(
								Leg(
									b.TermAs[Set[A]]("f(quotient_smul(L.add, L.mul, m, s, left_coset(L.add, t, m)))"),
									"the product of two classes is s acting on the second: both are the class of s * t",
									By(
										ideal,
										moduleS,
										denomS,
										members,
										quotient_ring.QuotientMulCoset.Read(ringS).AsFact().At(m, s, t),
										submodule.QuotientSmulCoset.At(scalars, VS, m, s, t))),
								Leg(
									b.TermAs[Set[A]]("quotient_smul(L.add, L.mul, «wfMul»(m, M), s, f(left_coset(L.add, t, m)))"),
									"f is S-linear",
									By(members, cosetIn, module_homomorphism.HomSmul.Read(homS).AsFact().At(s, tCoset))),
								Leg(
									b.TermAs[Set[A]]("left_coset(L.add, s * x, «wfMul»(m, M))"),
									"f takes the class of t to the class of x, on which s acts through its representative",
									By(
										moduleM,
										denomM,
										members,
										representative,
										submodule.QuotientSmulCoset.At(scalars, VM, mM, s, x))),
								FinalLeg(
									"and the class of s acts on the class of x the same way",
									By(
										L,
										subring,
										fractionalM,
										ideal,
										members,
										representative,
										At(mixedAction, fieldOps, S, M, m, s, x)))))
					}))
				residueLinear := a.Have(
					"hence f respects every residue scalar",
					Statement{
						Binders: "∀C U:set(A).",
						Hypotheses: []string{
							"C ∈ «residueScalars».carrier",
							"U ∈ «residueScalars».carrier",
						},
						Conclusion: "f(«residueScalars».mul(C, U)) = «residueRecord».smul(C, f(U))",
					},
					By(
						idealInS,
						linearRepresentatives,
						quotient_group.ForallInLeftCosetsPair.Read(module.AddGroupOn.Read(moduleS)).AsFact().At(m,
							a.TermAs[Fun2[Set[A], Set[A], Bool]](
								"λC:set(A). λU:set(A). f(«residueScalars».mul(C, U)) = «residueRecord».smul(C, f(U))"))))
				image := a.Have(
					"f still maps into the target carrier",
					"∀U:set(A). U ∈ «regularResidue».carrier ⇒ f(U) ∈ «residueRecord».carrier",
					By(module_homomorphism.HomIn.Read(homS)))
				fAdditive := a.Have(
					"f still preserves addition",
					Statement{
						Binders: "∀U V:set(A).",
						Hypotheses: []string{
							"U ∈ «regularResidue».carrier",
							"V ∈ «regularResidue».carrier",
						},
						Conclusion: "f(«regularResidue».add(U, V)) = «residueRecord».add(f(U), f(V))",
					},
					By(module_homomorphism.HomAdd.Read(homS)))
				homResidue := a.Have(
					"f is linear over the residue field",
					"module_homomorphism(«residueScalars», «regularResidue», «residueRecord», f)",
					By(
						module.RegularModuleOn.Read(residueRing),
						residueModule,
						image,
						fAdditive,
						residueLinear,
						module_homomorphism.ModuleHomomorphismDef.At(residueScalars, regularResidue, residueRecord, f)))
				isoResidue := a.Have(
					"the unchanged bijection is a residue-linear isomorphism",
					"module_isomorphism(«residueScalars», «regularResidue», «residueRecord», f)",
					By(
						homResidue,
						injective,
						onto,
						module_homomorphism.ModuleIsomorphismDef.At(residueScalars, regularResidue, residueRecord, f)))
				a.Show(
					"S/m is a field, and M/mM, a module over it, is isomorphic to its regular module",
					bridge.Rw(),
					By(
						maximal,
						residueRing,
						residueModule,
						isoResidue,
						quotient_ring.QuotientFieldOn.Read(ringS).At(m),
						module_homomorphism.IsomorphicOfIsomorphism.At(residueScalars, regularResidue, residueRecord, f)))
			})

			return ctx.Theorem(headline, func(
				a *Argument,
				L field.FieldFact[on.L],
				S, M, m *Expr[Set[A]],
				given Fact,
			) {
				residueScalars := a.TermAs[module_record.RingOps[Set[A]]]("«residueScalars»")
				residueVectors := a.TermAs[module_record.ModuleOps[Set[A], Set[A]]]("«residueVectors»")
				regularResidue := a.TermAs[module_record.ModuleOps[Set[A], Set[A]]]("«regularResidue»")
				residueInv := a.TermAs[Fun[Set[A], Set[A]]]("ideal_quotient_field(«wfScalars», m).inv")
				residueCarrier := a.TermAs[Set[Set[A]]]("ideal_quotient_field(«wfScalars», m).carrier")
				p := a.Conjuncts(
					GroupPremises(L, given, At(residueIsomorphism, a.TermAs[field.FieldOps[A]]("L"), S, M, m)),
					"S/m is a field",
					"S/m is a commutative ring",
					"M/mM is a module over S/m",
					"M/mM is isomorphic to the regular residue module")
				residueField, residueRing, residueModule, isomorphic := p[0], p[1], p[2], p[3]
				fieldScalars := a.Have(
					"S/m is a field under its own operations, with the quotient field's inverse",
					"ring_subfield(«residueScalars», "+
						"    ideal_quotient_field(«wfScalars», m).inv, "+
						"    «residueScalars».carrier)",
					Simp(Rev(quotient_ring.IdealQuotientFieldRing)),
					By(
						field.CarrierSubfield.Read(residueField),
						field.SubfieldRingSubfield.Read(residueField).At(residueCarrier, residueCarrier),
						field.RingSubfieldRestrict.At(
							a.TermAs[module_record.RingOps[Set[A]]]("field_ring(ideal_quotient_field(«wfScalars», m))"),
							residueCarrier,
							residueInv,
							residueCarrier)))
				regularModule := a.Have(
					"S/m is a module over itself",
					"module_on(«residueScalars», «regularResidue»)",
					By(module.RegularModuleOn.Read(residueRing)))
				basisSet := a.TermAs[Set[Set[A]]]("{«residueScalars».one}")
				regularDimension := a.Have(
					"the regular residue module has the dimension of its singleton basis",
					"finite_dimensional(«residueScalars», «regularResidue») ∧ "+
						"module_dim(«residueScalars», «regularResidue») = card({«residueScalars».one})",
					By(
						regularModule,
						fieldScalars,
						linear_independence.RegularModuleBasis.Read(residueRing),
						finite_set.FiniteSing,
						module_dimension.FiniteBasisDim.At(residueScalars, regularResidue, residueInv, basisSet)))
				transfer := a.Have(
					"the residue-linear isomorphism transfers finite dimension",
					"finite_dimensional(«residueScalars», «residueVectors») ∧ "+
						"module_dim(«residueScalars», «residueVectors») = module_dim(«residueScalars», «regularResidue»)",
					By(
						regularModule,
						fieldScalars,
						residueModule,
						isomorphic,
						regularDimension,
						module_dimension.IsomorphicDim.At(residueScalars, regularResidue, residueInv, residueVectors)))
				a.Show(
					"M/mM is a one-dimensional vector space over S/m",
					By(residueModule, transfer, regularDimension, cardinality.CardSing))
			})
		}),
})}

// InvertibleQuotientCardinality — multiplication by an invertible ideal
// preserves a finite quotient cardinality: strong induction on the size
// of I/J splits off a simple layer, and index multiplicativity combines
// the transferred layer sizes.
var InvertibleQuotientCardinality = invertibleQuotientCardinalityThm{family.Add(registry.ProofEntry{
	Name: "InvertibleQuotientCardinality",
	Key:  "prop_874bcec43ddb9fe9",
	Reading: "The finiteness premise concerns the set I/J, not the ring, " +
		"the ideals, or a scalar field. The case I=J gives singleton coset sets " +
		"on both sides. No isomorphism between the whole quotients is claimed.",
	Build: family.Theorem(
		Statement{
			Binders: "∀L:field_on(A). ∀S M I J:set(A).",
			Hypotheses: []string{
				"subring(field_ring(L), S)",
				"invertible_fractional(field_ring(L), S, M)",
				"«ideal»(I)",
				"«ideal»(J)",
				"J ⊆ I",
				"finite(left_cosets(L.add, I, J))",
			},
			Conclusion: "finite(left_cosets(L.add, «mul»(I, M), «mul»(J, M))) ∧ " +
				"card(left_cosets(L.add, «mul»(I, M), «mul»(J, M))) = card(left_cosets(L.add, I, J))",
			Abbrev: Abbrev{
				{Name: "ideal", Text: "ring_ideal(«R»)"},
				{Name: "fractional", Text: "submodule(«R», «V»)"},
				{Name: "keptByM", Text: "λU:set(A). λW:set(A). " +
					"    finite(left_cosets(L.add, «mul»(U, M), «mul»(W, M))) ∧ " +
					"    card(left_cosets(L.add, «mul»(U, M), «mul»(W, M))) = card(left_cosets(L.add, U, W))"},
			},
		},
		func(a *Argument, L field.FieldFact[on.L], S, M, I, J *Expr[Set[A]], h Fact) {
			p := a.Conjuncts(
				h,
				"S is a subring of L",
				"M is invertible",
				"I is an ideal",
				"J is an ideal",
				"J lies in I",
				"I/J is finite")
			subring, invertible, idealI, idealJ, jInI, finiteI := p[0], p[1], p[2], p[3], p[4], p[5]
			R := a.TermAs[module_record.RingOps[A]]("«R»")
			V := a.TermAs[module_record.ModuleOps[A, A]]("«V»")
			ring := a.Have(
				"S is a ring under L's operations",
				"comm_ring_on(«R»)",
				By(subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
			fieldModule := a.Have(
				"L is an S-module",
				"module_on(«R», «V»)",
				By(subring, fractional_ideal.FieldModuleOn.Read(L).At(S)))
			mData := a.Conjuncts(
				a.Unfolded(invertible, fractional_ideal.InvertibleFractionalDef),
				"M is a fractional ideal",
				"M times its inverse is S")
			productsFractional := a.Have(
				"multiplication by M produces a fractional ideal",
				"∀K:set(A). «ideal»(K) ⇒ «fractional»(«mul»(K, M))",
				Derive(func(b *Argument) {
					K := b.FixAs[Set[A]]("K")
					idealK := b.Assume()
					kInL := b.Have(
						"K lies in S and hence in L",
						"K ⊆ L.carrier",
						BySets(ring_ideal.IdealSubset.Read(idealK), comm_ring.SubringSubset.Read(subring)))
					b.Show(
						"the product is a fractional ideal",
						By(
							subring,
							kInL,
							submodule.SubmoduleSubset.Read(mData[0]),
							fractional_ideal.FractionalMulSubmodule.Read(L).At(S, K, M)))
				}))
			productMono := a.Have(
				"multiplication by M preserves inclusions",
				"∀K H:set(A). K ⊆ H ⇒ «mul»(K, M) ⊆ «mul»(H, M)",
				Derive(func(b *Argument) {
					K, H := b.FixAs[Set[A]]("K"), b.FixAs[Set[A]]("H")
					included := b.Assume()
					b.Show(
						"apply product monotonicity with the second factor fixed",
						By(
							included,
							set_order.SubsetRefl.At(M),
							fractional_ideal.FractionalMulMono.Read(L).At(S, K, H, M, M)))
				}))
			subgroupWithin := a.Have(
				"nested fractional ideals are additive subgroups of the larger one",
				Statement{
					Binders: "∀X Y:set(A).",
					Hypotheses: []string{
						"«fractional»(X)",
						"«fractional»(Y)",
						"Y ⊆ X",
					},
					Conclusion: "subgroup(module_additive_group(restrict_module(«V», X)), Y)",
				},
				Derive(func(b *Argument) {
					X, Y := b.FixAs[Set[A]]("X"), b.FixAs[Set[A]]("Y")
					guard := b.Assume()
					b.Show(
						"Y is a submodule of X, so an additive subgroup of X",
						By(
							guard,
							submodule.SubmoduleRestrict.At(R, V, X, Y),
							submodule.SubmoduleSubgroup.At(
								R, b.TermAs[module_record.ModuleOps[A, A]]("restrict_module(«V», X)"), Y)))
				}))
			selfQuotient := a.Have(
				"a fractional ideal modulo itself has only its zero coset",
				"∀K:set(A). «fractional»(K) ⇒ left_cosets(L.add, K, K) = {K}",
				Derive(func(b *Argument) {
					K := b.FixAs[Set[A]]("K")
					fracK := b.Assume()
					moduleK := b.Have(
						"K inherits its module structure",
						"module_on(«R», restrict_module(«V», K))",
						By(fracK, submodule.SubmoduleModuleOn.Read(fieldModule).At(K)))
					groupK := b.Have(
						"its addition is a group",
						"group_on(module_additive_group(restrict_module(«V», K)))",
						By(module.AddGroupOn.Read(moduleK)))
					b.Show(
						"the quotient by the whole group is trivial",
						By(group.CarrierSubgroupOn.Read(groupK), quotient_group.QuotientTrivialIff.Read(groupK).At(K)))
				}))
			preserved := a.TermAs[Fun[Nat, Bool]](
				"λn:num. ∀X Y:set(A). " +
					"    «ideal»(X) ∧ " +
					"    «ideal»(Y) ∧ " +
					"    Y ⊆ X ∧ " +
					"    finite(left_cosets(L.add, X, Y)) ∧ " +
					"    card(left_cosets(L.add, X, Y)) = n ⇒ " +
					"    «keptByM»(X, Y)")
			a.Show(
				"strong induction on the quotient cardinality compares "+
					"every pair of nested ideals, I and J among them",
				ByInduction(At(
					nat_order.StrongInduction,
					preserved,
					a.TermAs[Nat]("card(left_cosets(L.add, I, J))")), idealI, idealJ, jInI, finiteI,
					Case(
						"the induction step for every numerator and denominator",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							ih := b.Assume()
							X, Y := b.FixAs[Set[A]]("X"), b.FixAs[Set[A]]("Y")
							guards := b.Conjuncts(
								b.Assume(),
								"X is an ideal",
								"Y is an ideal",
								"Y lies in X",
								"X/Y is finite",
								"its cardinality is n")
							idealX, idealY, yInX, finiteXY, countXY := guards[0], guards[1], guards[2], guards[3], guards[4]
							fracX := b.Have(
								"X is a fractional ideal",
								"«fractional»(X)",
								By(subring, idealX, fractional_ideal.IntegralIdealFractional.Read(L).At(S, X)))
							fracXM := b.Have(
								"X*M is a fractional ideal",
								"«fractional»(«mul»(X, M))",
								By(productsFractional.At(X), idealX))
							fracY := b.Have(
								"Y is a fractional ideal",
								"«fractional»(Y)",
								By(subring, idealY, fractional_ideal.IntegralIdealFractional.Read(L).At(S, Y)))
							fracYM := b.Have(
								"Y*M is a fractional ideal",
								"«fractional»(«mul»(Y, M))",
								By(productsFractional.At(Y), idealY))
							b.Cases(b.TermAs[Bool]("X = Y"))
							b.When(
								"equal ideals give singleton quotient carriers",
								func(c *Argument, equal Fact) {
									c.Do(equal.Rw())
									source := c.Have(
										"Y/Y is the singleton zero coset",
										"left_cosets(L.add, Y, Y) = {Y}",
										By(selfQuotient.At(Y), fracY))
									productY := c.TermAs[Set[A]]("«mul»(Y, M)")
									target := c.Have(
										"the product modulo itself is also a singleton",
										"left_cosets(L.add, «mul»(Y, M), «mul»(Y, M)) = {«mul»(Y, M)}",
										By(selfQuotient.At(productY), fracYM))
									c.Show(
										"both quotients are finite and have cardinality one",
										source.Rw(),
										target.Rw(),
										By(
											finite_set.FiniteSing.At(productY),
											cardinality.CardSing.At(productY),
											cardinality.CardSing.At(Y)))
								})
							b.Otherwise(
								"a simple layer reduces the quotient cardinality",
								func(c *Argument, different Fact) {
									H, layer := c.ObtainAs[Set[A]](
										"choose a nonzero simple ideal layer above Y",
										"∃H:set(A). ideal_cover(«R», Y, H) ∧ H ⊆ X",
										By(
											idealX,
											idealY,
											yInX,
											different,
											finiteXY,
											quotient_ring.FiniteQuotientHasSimpleLayer.Read(ring).At(X, Y)),
										Named("H"))
									layerParts := c.Conjuncts(
										layer,
										"the layer H/Y is simple",
										"H lies in X")
									simple, hInX := layerParts[0], layerParts[1]
									aboveParts := c.Conjuncts(
										c.Have(
											"H is an ideal strictly above Y",
											"«ideal»(H) ∧ Y ⊆ H ∧ Y ≠ H",
											By(c.Unfolded(simple, ring_ideal.IdealCoverDef))),
										"H is an ideal",
										"Y lies in H",
										"Y differs from H")
									idealH, yInH, strictLayer := aboveParts[0], aboveParts[1], aboveParts[2]
									fracH := c.Have(
										"H is a fractional ideal",
										"«fractional»(H)",
										By(subring, idealH, fractional_ideal.IntegralIdealFractional.Read(L).At(S, H)))
									fracHM := c.Have(
										"H*M is a fractional ideal",
										"«fractional»(«mul»(H, M))",
										By(productsFractional.At(H), idealH))
									XM, definedXM := c.LetAs[Set[A]]("XM", "«mul»(X, M)")
									YM, definedYM := c.LetAs[Set[A]]("YM", "«mul»(Y, M)")
									HM, definedHM := c.LetAs[Set[A]]("HM", "«mul»(H, M)")
									ymInHM := c.Have(
										"YM lies in HM",
										"YM ⊆ HM",
										definedYM.Rw(),
										definedHM.Rw(),
										By(productMono.At(Y, H), yInH))
									hmInXM := c.Have(
										"HM lies in XM",
										"HM ⊆ XM",
										definedHM.Rw(),
										definedXM.Rw(),
										By(productMono.At(H, X), hInX))
									moduleX := c.Have(
										"X inherits its module structure",
										"module_on(«R», restrict_module(«V», X))",
										By(fracX, submodule.SubmoduleModuleOn.Read(fieldModule).At(X)))
									groupX := c.Have(
										"addition on X is a group",
										"group_on(module_additive_group(restrict_module(«V», X)))",
										By(module.AddGroupOn.Read(moduleX)))
									moduleXM := c.Have(
										"XM inherits its module structure",
										"module_on(«R», restrict_module(«V», XM))",
										By(fracXM, submodule.SubmoduleModuleOn.Read(fieldModule).At(XM)))
									groupXM := c.Have(
										"addition on XM is a group",
										"group_on(module_additive_group(restrict_module(«V», XM)))",
										By(module.AddGroupOn.Read(moduleXM)))
									subH := c.Have(
										"H is an additive subgroup of X",
										"subgroup(module_additive_group(restrict_module(«V», X)), H)",
										By(subgroupWithin.At(X, H), fracX, fracH, hInX))
									subY := c.Have(
										"Y is an additive subgroup of X",
										"subgroup(module_additive_group(restrict_module(«V», X)), Y)",
										By(subgroupWithin.At(X, Y), fracX, fracY, yInX))
									subHM := c.Have(
										"HM is an additive subgroup of XM",
										"subgroup(module_additive_group(restrict_module(«V», XM)), HM)",
										By(subgroupWithin.At(XM, HM), fracXM, fracHM, hmInXM))
									ymInXM := c.Have(
										"YM lies in XM",
										"YM ⊆ XM",
										BySets(ymInHM, hmInXM))
									subYM := c.Have(
										"YM is an additive subgroup of XM",
										"subgroup(module_additive_group(restrict_module(«V», XM)), YM)",
										By(subgroupWithin.At(XM, YM), fracXM, fracYM, ymInXM))
									sourceIndex := c.Have(
										"the source quotient splits into the indices of its two layers",
										"(finite(left_cosets(L.add, X, Y)) ⇔ "+
											"    finite(left_cosets(L.add, X, H)) ∧ finite(left_cosets(L.add, H, Y))) ∧ "+
											"(finite(left_cosets(L.add, X, Y)) ⇒ "+
											"    card(left_cosets(L.add, X, Y)) = "+
											"    card(left_cosets(L.add, X, H)) * card(left_cosets(L.add, H, Y)))",
										By(
											subH,
											yInH,
											group.SubgroupOne.Read(subY),
											quotient_group.IndexMultiplicative.Read(groupX).At(Y, H)))
									finiteXH := c.Have(
										"the upper source quotient X/H is finite",
										"finite(left_cosets(L.add, X, H))",
										By(sourceIndex, finiteXY))
									finiteHY := c.Have(
										"the simple source layer H/Y is finite",
										"finite(left_cosets(L.add, H, Y))",
										By(sourceIndex, finiteXY))
									sourceProduct := c.Have(
										"the two source layer sizes multiply to card(X/Y)",
										"card(left_cosets(L.add, X, Y)) = card(left_cosets(L.add, X, H)) * card(left_cosets(L.add, H, Y))",
										By(sourceIndex, finiteXY))
									decrease := c.Have(
										"the strict lower layer makes the upper source quotient smaller",
										"card(left_cosets(L.add, X, H)) < card(left_cosets(L.add, X, Y))",
										By(
											subY,
											subH,
											yInH,
											strictLayer,
											finiteXY,
											quotient_group.StrictInclusionLowersIndex.Read(groupX).At(Y, H)))
									belowN := c.Have(
										"the upper source quotient has cardinality below n",
										"card(left_cosets(L.add, X, H)) < n",
										By(Normalized, decrease, countXY))
									upper := c.Have(
										"strong induction transfers the upper quotient X/H",
										"finite(left_cosets(L.add, XM, HM)) ∧ "+
											"card(left_cosets(L.add, XM, HM)) = card(left_cosets(L.add, X, H))",
										definedXM.Rw(),
										definedHM.Rw(),
										By(
											ih.At(c.TermAs[Nat]("card(left_cosets(L.add, X, H))"), X, H),
											belowN,
											idealX,
											idealH,
											hInX,
											finiteXH))
									upperParts := c.Conjuncts(
										upper,
										"XM/HM is finite",
										"its cardinality equals that of X/H")
									finiteUpper, countUpper := upperParts[0], upperParts[1]
									layerIso := c.Have(
										"multiplication by M preserves the simple layer up to S-linear isomorphism",
										"module_isomorphic(«R», "+
											"    quotient_module(restrict_module(«V», H), Y), "+
											"    quotient_module(restrict_module(«V», HM), YM))",
										definedHM.Rw(),
										definedYM.Rw(),
										By(subring, invertible, simple, InvertibleSimpleLayer.Read(L).At(S, M, H, Y)))
									f, isomorphism := c.UnpackAs[Fun[Set[A], Set[A]]](
										c.Unfolded(layerIso, module_homomorphism.ModuleIsomorphicDef), "f")
									mapParts := c.Conjuncts(
										c.Unfolded(isomorphism, module_homomorphism.ModuleIsomorphismDef),
										"the map is linear",
										"it is injective on H/Y",
										"its image is HM/YM")
									injective, onto := mapParts[1], mapParts[2]
									sourceLayer := c.TermAs[Set[Set[A]]]("left_cosets(L.add, H, Y)")
									finiteLayer := c.Have(
										"the product layer HM/YM is finite",
										"finite(left_cosets(L.add, HM, YM))",
										onto.RwRev(),
										By(finiteHY, finite_set.FiniteImage.At(f, sourceLayer)))
									countLayer := c.Have(
										"the product layer has the same cardinality as H/Y",
										"card(left_cosets(L.add, HM, YM)) = card(left_cosets(L.add, H, Y))",
										onto.RwRev(),
										By(injective, finiteHY, cardinality.CardImageInj.At(f, sourceLayer)))
									targetIndex := c.Have(
										"the product quotient splits into the same two layers",
										"(finite(left_cosets(L.add, XM, YM)) ⇔ "+
											"    finite(left_cosets(L.add, XM, HM)) ∧ finite(left_cosets(L.add, HM, YM))) ∧ "+
											"(finite(left_cosets(L.add, XM, YM)) ⇒ "+
											"    card(left_cosets(L.add, XM, YM)) = "+
											"    card(left_cosets(L.add, XM, HM)) * card(left_cosets(L.add, HM, YM)))",
										By(
											subHM,
											ymInHM,
											group.SubgroupOne.Read(subYM),
											quotient_group.IndexMultiplicative.Read(groupXM).At(YM, HM)))
									finiteTarget := c.Have(
										"both finite product layers make XM/YM finite",
										"finite(left_cosets(L.add, XM, YM))",
										By(targetIndex, finiteUpper, finiteLayer))
									targetProduct := c.Have(
										"the two product layer sizes multiply to card(XM/YM)",
										"card(left_cosets(L.add, XM, YM)) = "+
											"card(left_cosets(L.add, XM, HM)) * card(left_cosets(L.add, HM, YM))",
										By(targetIndex, finiteTarget))
									countTarget := c.Have(
										"the two layer comparisons preserve the full quotient cardinality",
										"card(left_cosets(L.add, XM, YM)) = card(left_cosets(L.add, X, Y))",
										targetProduct.Rw(),
										countUpper.Rw(),
										countLayer.Rw(),
										By(sourceProduct))
									c.Show(
										"the product quotient is finite with the source cardinality",
										By(finiteTarget, countTarget))
								})
						}))))
		}),
})}

// IdealIndexMultiplicative — the index of a product of two ideals of finite
// index, the second invertible, is the product of their indices: IJ ⊆ J ⊆
// S, so the index of IJ in S is the index of J times the index of IJ in J,
// and multiplying the pair I ⊆ S by J, with S · J = J, gives J/IJ the
// cardinality of S/I.
var IdealIndexMultiplicative = idealIndexMultiplicativeThm{family.Add(registry.ProofEntry{
	Name: "IdealIndexMultiplicative",
	Key:  "prop_2b1b3e236e9972d3",
	Build: family.Theorem(
		Statement{
			Binders: "∀L:field_on(A). ∀S I J:set(A).",
			Hypotheses: []string{
				"subring(field_ring(L), S)",
				"ring_ideal(«R», I)",
				"ring_ideal(«R», J)",
				"invertible_fractional(field_ring(L), S, J)",
				"finite(left_cosets(L.add, S, I))",
				"finite(left_cosets(L.add, S, J))",
			},
			Conclusion: "finite(left_cosets(L.add, S, «mul»(I, J))) ∧ " +
				"ideal_index(«R», «mul»(I, J)) = ideal_index(«R», I) * ideal_index(«R», J)",
		},
		func(a *Argument, L field.FieldFact[on.L], S, I, J *Expr[Set[A]], h Fact) {
			p := a.Conjuncts(
				h,
				"S is a subring of L",
				"I is an ideal",
				"J is an ideal",
				"J is invertible",
				"S/I is finite",
				"S/J is finite")
			subring, idealI, idealJ, invertible, finiteI, finiteJ := p[0], p[1], p[2], p[3], p[4], p[5]
			ring := a.Have(
				"S is a ring under L's operations",
				"comm_ring_on(«R»)",
				By(subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
			product := a.TermAs[Set[A]]("«mul»(I, J)")
			countI := a.TermAs[Nat]("card(left_cosets(L.add, S, I))")
			countJ := a.TermAs[Nat]("card(left_cosets(L.add, S, J))")
			iInS := a.Have(
				"I lies in S",
				"I ⊆ S",
				By(ring_ideal.IdealSubset.Read(idealI)))
			jInS := a.Have(
				"J lies in S",
				"J ⊆ S",
				By(ring_ideal.IdealSubset.Read(idealJ)))
			inL := a.Have(
				"and both lie in L",
				"I ⊆ L.carrier ∧ J ⊆ L.carrier",
				BySets(iInS, jInS, comm_ring.SubringSubset.Read(subring)))
			fractionalJ := a.Have(
				"J is an S-submodule of L",
				"submodule(«R», regular_module(field_ring(L)), J)",
				By(subring, idealJ, fractional_ideal.IntegralIdealFractional.Read(L).At(S, J)))
			unit := a.Have(
				"multiplication by S fixes J",
				"«mul»(S, J) = J",
				By(subring, fractionalJ, fractional_ideal.FractionalMulOne.Read(L).At(S, J)))
			multiplied := a.Have(
				"multiplying the pair I ⊆ S by J gives J/IJ the cardinality of S/I",
				"finite(left_cosets(L.add, J, «mul»(I, J))) ∧ "+
					"card(left_cosets(L.add, J, «mul»(I, J))) = card(left_cosets(L.add, S, I))",
				By(
					subring,
					invertible,
					idealI,
					iInS,
					finiteI,
					unit,
					ring_ideal.CarrierIdeal.Read(ring),
					InvertibleQuotientCardinality.Read(L).At(S, J, S, I)))
			productInJ := a.Have(
				"S containing I makes IJ lie in S · J = J",
				"«mul»(I, J) ⊆ J",
				By(
					Normalized,
					iInS,
					unit,
					set_order.SubsetRefl.At(J),
					fractional_ideal.FractionalMulMono.Read(L).At(S, I, S, J, J)))
			productInS := a.Have(
				"so IJ lies in S",
				"«mul»(I, J) ⊆ S",
				BySets(productInJ, jInS))
			productFractional := a.Have(
				"IJ is an S-submodule of L",
				"submodule(«R», regular_module(field_ring(L)), «mul»(I, J))",
				By(subring, inL, fractional_ideal.FractionalMulSubmodule.Read(L).At(S, I, J)))
			productIdeal := a.Have(
				"an S-submodule inside S is an ideal of S",
				"ring_ideal(«R», «mul»(I, J))",
				By(
					subring,
					productFractional,
					productInS,
					fractional_ideal.IntegralIdealFractional.Read(L).At(S, product)))
			subgroups := a.Conjuncts(
				a.Have(
					"J and IJ are additive subgroups of S",
					"subgroup(additive_group(«R»), J) ∧ subgroup(additive_group(«R»), «mul»(I, J))",
					By(
						idealJ,
						productIdeal,
						quotient_ring.IdealSubgroup.Read(ring).At(J),
						quotient_ring.IdealSubgroup.Read(ring).At(product))),
				"J is an additive subgroup of S",
				"so is IJ")
			indices := a.Have(
				"the index of IJ in S is the index of J times the index of IJ in J",
				"finite(left_cosets(L.add, S, «mul»(I, J))) ∧ "+
					"card(left_cosets(L.add, S, «mul»(I, J))) = "+
					"card(left_cosets(L.add, S, J)) * card(left_cosets(L.add, J, «mul»(I, J)))",
				By(
					productInJ,
					multiplied,
					finiteJ,
					subgroups[0],
					group.SubgroupOne.Read(subgroups[1]),
					quotient_group.IndexMultiplicative.Read(
						abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))).At(
						product, J)))
			a.Show(
				"the index of IJ is therefore the product of the indices of I and J",
				Simp(Fwd(quotient_ring.IdealIndexDef)),
				By(multiplied, indices, nat_arith.MulSym.At(countI, countJ)))
		}),
})}

// ---------------------------------------------------------------------------
// Colengths: quotients of products over a subfield k
// ---------------------------------------------------------------------------

// ScaleQuotientDim — multiplying by a nonzero member of the field keeps
// the dimension of a quotient of fractional ideals: dim(aM/aN) =
// dim(M/N). Multiplication by a is k-linear on L, and L.inv(a) undoes it,
// so it is a k-linear isomorphism of M onto aM. That isomorphism carries N
// to aN, so it descends to one of M/N onto aM/aN, and isomorphic spaces over
// k have one dimension.
var ScaleQuotientDim = scaleQuotientDimThm{family.Add(registry.ProofEntry{
	Name: "ScaleQuotientDim",
	Key:  "prop_e6b0713a8c694c20",
	Reading: "a ≠ zero is load-bearing: multiplication by zero " +
		"sends M/N to the zero space. M and N need not be invertible.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k S M N:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"k ⊆ S",
			"«wfFractional»(M)",
			"«wfFractional»(N)",
			"N ⊆ M",
			"a ∈ L.carrier",
			"a ≠ L.zero",
			"finite_dimensional(«wfOverK», «scaleSourceQuotient»)",
		},
		Conclusion: "finite_dimensional(«wfOverK», «scaleTargetQuotient») ∧ " +
			"module_dim(«wfOverK», «scaleTargetQuotient») = module_dim(«wfOverK», «scaleSourceQuotient»)",
		Abbrev: Abbrev{
			{Name: "scaleSourceModule", Text: "restrict_module(«wfField», M)"},
			{Name: "scaleTargetModule", Text: "restrict_module(«wfField», image(L.mul(a), M))"},
			{Name: "scaleSourceQuotient", Text: "quotient_module(«scaleSourceModule», N)"},
			{Name: "scaleTargetQuotient", Text: "quotient_module(«scaleTargetModule», image(L.mul(a), N))"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], k, S, M, N *Expr[Set[A]], a *Expr[A], given Fact) {
			parts := arg.Conjuncts(
				given,
				"k is a subfield of L",
				"k lies in S",
				"M is fractional",
				"N is fractional",
				"N lies in M",
				"a lies in L",
				"a is nonzero",
				"M/N is finite-dimensional")
			subfield, kInS := parts[0], parts[1]
			fractionalM, fractionalN, nInM := parts[2], parts[3], parts[4]
			aInField, nonzero, finite := parts[5], parts[6], parts[7]
			am := arg.MemberOf[on.L](a, aInField)
			overK := arg.TermAs[module_record.RingOps[A]]("«wfOverK»")
			scalars := arg.TermAs[module_record.RingOps[A]]("«wfScalars»")
			vectors := arg.TermAs[module_record.ModuleOps[A, A]]("«wfField»")
			VM := arg.TermAs[module_record.ModuleOps[A, A]]("«scaleSourceModule»")
			VT := arg.TermAs[module_record.ModuleOps[A, A]]("«scaleTargetModule»")
			QM := arg.TermAs[module_record.ModuleOps[A, Set[A]]]("«scaleSourceQuotient»")
			QT := arg.TermAs[module_record.ModuleOps[A, Set[A]]]("«scaleTargetQuotient»")
			multiply := arg.TermAs[Fun[A, A]]("L.mul(a)")
			imageM := arg.TermAs[Set[A]]("image(L.mul(a), M)")
			quotientMap := arg.TermAs[Fun[Set[A], Set[A]]]("λX:set(A). image(L.mul(a), X)")
			kRing := arg.Have(
				"k is a subring of L",
				"subring(field_ring(L), k)",
				By(subfield, field.SubfieldSubring.Read(L).At(k)))
			mOverK := arg.Have(
				"restrict the scalars of M from S to k",
				"submodule(«wfOverK», «wfField», M)",
				By(fractionalM, kInS, submodule.SubmoduleRestrictScalars.At(scalars, vectors, M, overK)))
			nOverK := arg.Have(
				"restrict the scalars of N from S to k",
				"submodule(«wfOverK», «wfField», N)",
				By(fractionalN, kInS, submodule.SubmoduleRestrictScalars.At(scalars, vectors, N, overK)))
			scaledModule := arg.Have(
				"the image aM is a k-submodule",
				"submodule(«wfOverK», «wfField», image(L.mul(a), M))",
				By(kRing, mOverK, fractional_ideal.ScaleSubmodule.Read(L).At(k, M, am)))
			intoImage := arg.Have(
				"a carries each point of M into aM",
				"∀u:A. u ∈ M ⇒ a * u ∈ image(L.mul(a), M)",
				BySets())
			restricted := arg.Have(
				"multiplication by a, k-linear on L, restricts to M and its image",
				"module_homomorphism(«wfOverK», «scaleSourceModule», «scaleTargetModule», L.mul(a))",
				By(
					kRing,
					field_extension.ScaleLinear.Read(L).At(k, am),
					mOverK,
					scaledModule,
					intoImage,
					module_homomorphism.HomRestrict.At(overK, vectors, vectors, multiply, M, imageM)))
			leftInverse := arg.Have(
				"multiplication by the inverse of a undoes multiplication by a",
				"∀u:A. u ∈ L.carrier ⇒ L.inv(a) * (a * u) = u",
				Derive(func(b *Argument) {
					u := b.FixAs[A]("u")
					um := b.MemberOf[on.L](u, b.Assume())
					b.Show(
						"inv(a) times a*u is u",
						ByArith(
							field.RingOn.Read(L),
							am,
							nonzero,
							um,
							field.InvIn.Read(L).At(am),
							Scaled(u, field.MulLeftInverseOn.Read(L).AsFact().At(am))))
				}))
			injective := arg.Have(
				"the left inverse makes multiplication injective on M",
				"injective_on(M, L.mul(a))",
				Unfold(functions.InjectiveOnDef),
				BySets(leftInverse, submodule.SubmoduleSubset.Read(fractionalM)))
			scalarIso := arg.Have(
				"multiplication is a k-linear isomorphism from M onto aM",
				"module_isomorphism(«wfOverK», «scaleSourceModule», «scaleTargetModule», L.mul(a))",
				By(restricted, injective, module_homomorphism.ModuleIsomorphismDef.At(overK, VM, VT, multiply)))
			denominator := arg.Have(
				"N is a k-submodule of M",
				"submodule(«wfOverK», «scaleSourceModule», N)",
				By(nInM, nOverK, submodule.SubmoduleRestrict.At(overK, vectors, M, N)))
			quotientIso := arg.Have(
				"the scalar isomorphism induces an isomorphism of the quotients",
				"module_isomorphism(«wfOverK», "+
					"    «scaleSourceQuotient», "+
					"    «scaleTargetQuotient», "+
					"    λX:set(A). image(L.mul(a), X))",
				By(scalarIso, denominator, module_homomorphism.QuotientIsomorphism.At(overK, VM, VT, multiply, N)))
			arg.Show(
				"the quotient isomorphism preserves finiteness and dimension",
				By(
					finite,
					quotientIso,
					subfield,
					field.SubfieldRingSubfield.Read(L).At(k, k),
					module_dimension.IsomorphismDim.At(overK, QM, arg.TermAs[Fun[A, A]]("L.inv"), QT, quotientMap)))
		}),
})}

// InvertibleQuotientDim — multiplying by an invertible fractional ideal
// keeps the dimension of a quotient of ideals: dim(IM/JM) = dim(I/J)
// for ideals J ⊆ I of S with I/J finite-dimensional over k. The proof is a
// strong induction on dim(I/J). When I ≠ J, an ideal H above J with H/J of
// least positive dimension makes H/J simple, InvertibleSimpleLayer
// identifies it S-linearly, hence k-linearly, with HM/JM, and the induction
// hypothesis handles the smaller I/H. The dimension formula of a chain of
// quotients adds the two layers on each side; I = J is the zero quotient.
var InvertibleQuotientDim = invertibleQuotientDimThm{family.Add(registry.ProofEntry{
	Name: "InvertibleQuotientDim",
	Key:  "prop_ccf3f9083dde3684",
	Reading: "k ⊆ S makes every S-module here a k-space, and asks nothing more of k: a simple " +
		"layer may have a residue field larger than k, its isomorphism being S-linear and so k-linear " +
		"whatever that field is. Invertibility is load-bearing: at M = {L.zero} both products are " +
		"{L.zero}. Only dimensions are compared; IM/JM and I/J are not claimed naturally isomorphic.",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀k S M I J:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subfield(L, k)",
			"k ⊆ S",
			"«wfInvertible»(M)",
			"«wfIdeal»(I)",
			"«wfIdeal»(J)",
			"J ⊆ I",
			"«finiteQuotient»(I, J)",
		},
		Conclusion: "«keptByM»(I, J)",
		Abbrev: Abbrev{
			{Name: "timesM", Text: "λU:set(A). «wfMul»(U, M)"},
			{Name: "keptByM", Text: "λU:set(A). λW:set(A). " +
				"    «finiteQuotient»(«timesM»(U), «timesM»(W)) ∧ " +
				"    «colength»(«timesM»(U), «timesM»(W)) = «colength»(U, W)"},
			{Name: "kSubspace", Text: "submodule(«wfOverK», «wfField»)"},
			{Name: "layerAt", Text: "λH:set(A). λd:num. " +
				"    «wfIdeal»(H) ∧ J ⊆ H ∧ H ⊆ I ∧ J ≠ H ∧ «colength»(H, J) = d"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			idealSpace := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀k S Z:set(A).",
				Hypotheses: []string{
					"subring(field_ring(L), S)",
					"k ⊆ S",
					"«wfIdeal»(Z)",
				},
				Conclusion: "«kSubspace»(Z)",
			}, func(a *Argument, L field.FieldFact[on.L], k, S, Z *Expr[Set[A]], given Fact) {
				p := a.Conjuncts(
					given,
					"S is a subring of L",
					"k lies in S",
					"Z is an ideal")
				subring, kInS, ideal := p[0], p[1], p[2]
				a.Show(
					"an ideal of S is fractional, and restricting its scalars from S to k keeps it a submodule",
					By(
						subring,
						kInS,
						ideal,
						fractional_ideal.IntegralIdealFractional.Read(L).At(S, Z),
						submodule.SubmoduleRestrictScalars.At(
							a.TermAs[module_record.RingOps[A]]("«wfScalars»"),
							a.TermAs[module_record.ModuleOps[A, A]]("«wfField»"),
							Z,
							a.TermAs[module_record.RingOps[A]]("«wfOverK»"))))
			})

			simpleLayer := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀k S I J:set(A).",
				Hypotheses: []string{
					"subring(field_ring(L), S)",
					"subfield(L, k)",
					"k ⊆ S",
					"«wfIdeal»(I)",
					"«wfIdeal»(J)",
					"J ⊆ I",
					"J ≠ I",
					"«finiteQuotient»(I, J)",
				},
				Conclusion: "∃H:set(A). ideal_cover(«wfScalars», J, H) ∧ H ⊆ I",
			}, func(a *Argument, L field.FieldFact[on.L], k, S, I, J *Expr[Set[A]], given Fact) {
				p := a.Conjuncts(
					given,
					"S is a subring of L",
					"k is a subfield",
					"k lies in S",
					"I is an ideal",
					"J is an ideal",
					"J lies in I",
					"J differs from I",
					"I/J is finite-dimensional")
				subring, subfield, kInS, idealI, idealJ, jInI, strict := p[0], p[1], p[2], p[3], p[4], p[5], p[6]
				inv := a.TermAs[Fun[A, A]]("L.inv")
				moduleK := a.Have(
					"L is a k-module",
					"module_on(«wfOverK», «wfField»)",
					By(subfield, field.SubfieldSubring.Read(L).At(k), fractional_ideal.FieldModuleOn.Read(L).At(k)))
				kField := a.Have(
					"the scalar ring on k is a field",
					"ring_subfield(«wfOverK», L.inv, k)",
					By(subfield, field.SubfieldRingSubfield.Read(L).At(k, k)))
				spaces := a.Have(
					"every ideal of S is a k-subspace of L",
					"∀Z:set(A). «wfIdeal»(Z) ⇒ «kSubspace»(Z)",
					By(L, subring, kInS, At(idealSpace, a.TermAs[field.FieldOps[A]]("L"), k, S)))
				chain := a.Have(
					"nested ideal quotients have additive dimensions",
					Statement{
						Binders: "∀U W Z:set(A).",
						Hypotheses: []string{
							"«wfIdeal»(U)",
							"«wfIdeal»(W)",
							"«wfIdeal»(Z)",
							"Z ⊆ W",
							"W ⊆ U",
							"«finiteQuotient»(U, Z)",
						},
						Conclusion: "«finiteQuotient»(U, W) ∧ " +
							"«finiteQuotient»(W, Z) ∧ " +
							"«colength»(U, Z) = «colength»(U, W) + «colength»(W, Z)",
					},
					Derive(func(b *Argument) {
						U, W, Z := b.FixAs[Set[A]]("U"), b.FixAs[Set[A]]("W"), b.FixAs[Set[A]]("Z")
						guard := b.Assume()
						b.Show(
							"apply the quotient chain dimension formula over k",
							By(
								guard,
								spaces.At(U),
								spaces.At(W),
								spaces.At(Z),
								kField,
								module_dimension.QuotientChainDim.Read(moduleK).At(inv, U, W, Z)))
					}))
				zero := a.Have(
					"an ideal quotient is a finite zero space exactly when the ideals agree",
					Statement{
						Binders: "∀U W:set(A).",
						Hypotheses: []string{
							"«wfIdeal»(U)",
							"«wfIdeal»(W)",
							"W ⊆ U",
						},
						Conclusion: "(«finiteQuotient»(U, W) ∧ «colength»(U, W) = 0) ⇔ U = W",
					},
					Derive(func(b *Argument) {
						U, W := b.FixAs[Set[A]]("U"), b.FixAs[Set[A]]("W")
						guard := b.Assume()
						b.Show(
							"use the dimension-zero quotient criterion",
							By(
								guard,
								spaces.At(U),
								spaces.At(W),
								kField,
								module_dimension.QuotientDimZeroIff.Read(moduleK).At(inv, U, W)))
					}))
				candidates := a.TermAs[Fun[Nat, Bool]]("λn:num. ∃H:set(A). «layerAt»(H, n)")
				attained := a.Have(
					"I supplies a nonzero layer above J",
					"∃n:num. ∃H:set(A). «layerAt»(H, n)",
					Derive(func(b *Argument) {
						b.Take(b.TermAs[Nat]("«colength»(I, J)"))
						b.Take(I)
						b.Show(
							"I is one of the candidate ideals",
							By(idealI, jInI, strict, set_order.SubsetRefl.At(I)))
					}))
				_, leastData := a.ObtainAs[Nat](
					"choose the least dimension of a nonzero ideal layer",
					"∃n:num. (∃H:set(A). «layerAt»(H, n)) ∧ (∀m:num. m < n ⇒ ¬(∃K:set(A). «layerAt»(K, m)))",
					By(attained, nat_order.WellOrdering.At(candidates)),
					Named("n"))
				leastParts := a.Conjuncts(
					leastData,
					"some ideal attains n",
					"no smaller dimension is attained")
				reachedN, noneBelow := leastParts[0], leastParts[1]
				H, chosenH := a.UnpackAs[Set[A]](reachedN, "H")
				hp := a.Conjuncts(
					chosenH,
					"H is an ideal",
					"J lies in H",
					"H lies in I",
					"J differs from H",
					"H/J has dimension n")
				idealH, hInI, dimensionN := hp[0], hp[2], hp[4]
				finiteHJ := a.Have(
					"the chosen layer is finite-dimensional",
					"«finiteQuotient»(H, J)",
					By(given, chosenH, chain.At(I, H, J)))
				noIntermediate := a.Have(
					"a strict intermediate ideal would have a smaller nonzero layer",
					"∀K:set(A). «wfIdeal»(K) ∧ J ⊆ K ∧ K ⊆ H ∧ K ≠ J ∧ K ≠ H ⇒ ⊥",
					Derive(func(b *Argument) {
						K := b.FixAs[Set[A]]("K")
						guard := b.Assume()
						layers := b.Have(
							"H/J splits through K",
							"«finiteQuotient»(H, K) ∧ "+
								"«finiteQuotient»(K, J) ∧ "+
								"«colength»(H, J) = «colength»(H, K) + «colength»(K, J)",
							By(idealH, idealJ, guard, finiteHJ, chain.At(H, K, J)))
						positive := b.Have(
							"the strict quotient H/K has nonzero dimension",
							"«colength»(H, K) ≠ 0",
							By(layers, idealH, guard, zero.At(H, K)))
						below := b.Have(
							"so K/J has dimension below the chosen minimum",
							"«colength»(K, J) < n",
							ByArith(layers, positive, dimensionN))
						candidateK := b.Have(
							"K attains that smaller dimension",
							"∃W:set(A). «layerAt»(W, «colength»(K, J))",
							Derive(func(c *Argument) {
								c.Take(K)
								c.Show(
									"K is a strict candidate above J",
									By(Normalized, guard, hInI, set_order.SubsetTrans.At(K, H, I)))
							}))
						b.Show(
							"minimality rules out this intermediate ideal",
							By(noneBelow.At(b.TermAs[Nat]("«colength»(K, J)")), below, candidateK))
					}))
				a.Take(H)
				a.Show(
					"H/J is a nonzero simple ideal layer",
					Simp(Fwd(ring_ideal.IdealCoverDef)),
					By(Normalized, idealJ, chosenH, noIntermediate))
			})

			preserveSimpleLayer := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀k S M H J:set(A).",
				Hypotheses: []string{
					"subring(field_ring(L), S)",
					"subfield(L, k)",
					"k ⊆ S",
					"«wfInvertible»(M)",
					"ideal_cover(«wfScalars», J, H)",
					"«finiteQuotient»(H, J)",
				},
				Conclusion: "«keptByM»(H, J)",
			}, func(a *Argument, L field.FieldFact[on.L], k, S, M, H, J *Expr[Set[A]], given Fact) {
				p := a.Conjuncts(
					given,
					"S is a subring",
					"k is a subfield",
					"k lies in S",
					"M is invertible",
					"H/J is simple",
					"H/J is finite-dimensional")
				subfield, kInS, finite := p[1], p[2], p[5]
				overK := a.TermAs[module_record.RingOps[A]]("«wfOverK»")
				QH := a.TermAs[module_record.ModuleOps[A, Set[A]]]("«quotient»(H, J)")
				QT := a.TermAs[module_record.ModuleOps[A, Set[A]]]("«quotient»(«wfMul»(H, M), «wfMul»(J, M))")
				inv := a.TermAs[Fun[A, A]]("L.inv")
				layer := a.Have(
					"multiplication by M preserves the simple layer over S",
					"module_isomorphic(«wfScalars», «quotient»(H, J), «quotient»(«wfMul»(H, M), «wfMul»(J, M)))",
					By(given, InvertibleSimpleLayer.Read(L).At(S, M, H, J)))
				f, iso := a.UnpackAs[Fun[Set[A], Set[A]]](
					a.Unfolded(layer, module_homomorphism.ModuleIsomorphicDef), "f")
				mp := a.Conjuncts(
					a.Unfolded(iso, module_homomorphism.ModuleIsomorphismDef),
					"f is S-linear",
					"f is injective",
					"f is onto")
				homS, injective, onto := mp[0], mp[1], mp[2]
				linearK := a.Have(
					"restrict the linear map from S-scalars to k-scalars",
					"module_homomorphism(«wfOverK», «quotient»(H, J), «quotient»(«wfMul»(H, M), «wfMul»(J, M)), f)",
					By(
						homS,
						kInS,
						subfield,
						field.SubfieldSubring.Read(L).At(k),
						module_homomorphism.HomRestrictSubring.At(
							a.TermAs[module_record.RingOps[A]]("field_ring(L)"), QH, QT, f, S, k)))
				isoK := a.Have(
					"the same bijection is a k-linear isomorphism",
					"module_isomorphism(«wfOverK», «quotient»(H, J), «quotient»(«wfMul»(H, M), «wfMul»(J, M)), f)",
					By(linearK, injective, onto, module_homomorphism.ModuleIsomorphismDef.At(overK, QH, QT, f)))
				a.Show(
					"the simple layer remains finite-dimensional of the same dimension",
					By(
						isoK,
						subfield,
						field.SubfieldRingSubfield.Read(L).At(k, k),
						finite,
						module_dimension.IsomorphismDim.At(overK, QH, inv, QT, f)))
			})

			return ctx.Theorem(headline, func(
				a *Argument,
				L field.FieldFact[on.L],
				k, S, M, I, J *Expr[Set[A]],
				given Fact,
			) {
				p := a.Conjuncts(
					given,
					"S is a subring",
					"k is a subfield",
					"k lies in S",
					"M is invertible",
					"I is an ideal",
					"J is an ideal",
					"J lies in I",
					"I/J is finite-dimensional")
				subring, subfield, kInS, invertible, idealI, idealJ, jInI, finite :=
					p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7]
				overK := a.TermAs[module_record.RingOps[A]]("«wfOverK»")
				scalars := a.TermAs[module_record.RingOps[A]]("«wfScalars»")
				vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wfField»")
				inv := a.TermAs[Fun[A, A]]("L.inv")
				fieldOps := a.TermAs[field.FieldOps[A]]("L")
				moduleK := a.Have(
					"L is a k-module",
					"module_on(«wfOverK», «wfField»)",
					By(subfield, field.SubfieldSubring.Read(L).At(k), fractional_ideal.FieldModuleOn.Read(L).At(k)))
				kField := a.Have(
					"the scalar ring on k is a field",
					"ring_subfield(«wfOverK», L.inv, k)",
					By(subfield, field.SubfieldRingSubfield.Read(L).At(k, k)))
				fractionalM := a.Have(
					"M is fractional",
					"«wfFractional»(M)",
					By(
						invertible,
						fractional_ideal.InvertibleFractionalDef.At(
							a.TermAs[module_record.RingOps[A]]("field_ring(L)"), S, M)))
				spaces := a.Have(
					"ideals and their products with M are k-subspaces",
					"∀Z:set(A). «wfIdeal»(Z) ⇒ «kSubspace»(Z) ∧ «kSubspace»(«timesM»(Z))",
					Derive(func(b *Argument) {
						Z := b.FixAs[Set[A]]("Z")
						idealZ := b.Assume()
						zInL := b.Have(
							"Z lies in L",
							"Z ⊆ L.carrier",
							BySets(idealZ, comm_ring.SubringSubset.Read(subring), ring_ideal.IdealSubset.Read(idealZ)))
						productZ := b.Have(
							"multiplying Z by M gives a fractional ideal",
							"«wfFractional»(«timesM»(Z))",
							By(
								subring,
								zInL,
								submodule.SubmoduleSubset.Read(fractionalM),
								fractional_ideal.FractionalMulSubmodule.Read(L).At(S, Z, M)))
						b.Show(
							"restrict the product from S-scalars to k-scalars, as for the ideal itself",
							By(
								L,
								subring,
								kInS,
								idealZ,
								productZ,
								At(idealSpace, fieldOps, k, S, Z),
								submodule.SubmoduleRestrictScalars.At(scalars, vectors, b.TermAs[Set[A]]("«timesM»(Z)"), overK)))
					}))
				preserved := a.TermAs[Fun[Nat, Bool]](
					"λn:num. ∀X Y:set(A). " +
						"    «wfIdeal»(X) ∧ «wfIdeal»(Y) ∧ Y ⊆ X ∧ «finiteQuotient»(X, Y) ∧ «colength»(X, Y) = n ⇒ " +
						"    «keptByM»(X, Y)")
				a.Show(
					"strong induction compares every nested pair of ideals, including I and J",
					ByInduction(At(
						nat_order.StrongInduction,
						preserved,
						a.TermAs[Nat]("«colength»(I, J)")), idealI, idealJ, jInI, finite,
						Case(
							"split a finite-dimensional quotient into a simple layer and a smaller quotient",
							Derive(func(b *Argument) {
								b.FixAs[Nat]("n")
								ih := b.Assume()
								X, Y := b.FixAs[Set[A]]("X"), b.FixAs[Set[A]]("Y")
								guards := b.Conjuncts(
									b.Assume(),
									"X is an ideal",
									"Y is an ideal",
									"Y lies in X",
									"X/Y is finite-dimensional",
									"X/Y has dimension n")
								idealX, idealY, yInX, finiteXY, countXY := guards[0], guards[1], guards[2], guards[3], guards[4]
								spacesX := b.Have(
									"X and XM are k-subspaces",
									"«kSubspace»(X) ∧ «kSubspace»(«timesM»(X))",
									By(idealX, spaces.At(X)))
								spacesY := b.Have(
									"Y and YM are k-subspaces",
									"«kSubspace»(Y) ∧ «kSubspace»(«timesM»(Y))",
									By(idealY, spaces.At(Y)))
								different := b.Unless(
									b.TermAs[Bool]("X = Y"),
									"equal ideals give zero quotients before and after multiplication",
									Given(func(c *Argument, equal Fact) {
										sourceZero := c.Have(
											"Y/Y is finite-dimensional of dimension zero",
											"«finiteQuotient»(Y, Y) ∧ «colength»(Y, Y) = 0",
											By(
												spacesY,
												kField,
												set_order.SubsetRefl.At(Y),
												module_dimension.QuotientDimZeroIff.Read(moduleK).At(inv, Y, Y)))
										YM := c.TermAs[Set[A]]("«timesM»(Y)")
										targetZero := c.Have(
											"YM/YM is finite-dimensional of dimension zero",
											"«finiteQuotient»(«timesM»(Y), «timesM»(Y)) ∧ «colength»(«timesM»(Y), «timesM»(Y)) = 0",
											By(
												spacesY,
												kField,
												set_order.SubsetRefl.At(YM),
												module_dimension.QuotientDimZeroIff.Read(moduleK).At(inv, YM, YM)))
										c.Show(
											"the two zero quotients have equal dimensions",
											Simp(Fwd(equal)),
											By(sourceZero, targetZero))
									}))
								H, layer := b.ObtainAs[Set[A]](
									"choose a nonzero simple ideal layer above Y",
									"∃H:set(A). ideal_cover(«wfScalars», Y, H) ∧ H ⊆ X",
									By(
										L,
										subring,
										subfield,
										kInS,
										idealX,
										idealY,
										yInX,
										different,
										finiteXY,
										At(simpleLayer, fieldOps, k, S, X, Y)),
									Named("H"))
								hp := b.Conjuncts(
									layer,
									"H/Y is simple",
									"H lies in X")
								simple, hInX := hp[0], hp[1]
								above := b.Conjuncts(
									b.Have(
										"H is an ideal strictly above Y",
										"«wfIdeal»(H) ∧ Y ⊆ H ∧ Y ≠ H",
										By(b.Unfolded(simple, ring_ideal.IdealCoverDef))),
									"H is an ideal",
									"Y lies in H",
									"Y differs from H")
								idealH, yInH, strict := above[0], above[1], above[2]
								spacesH := b.Have(
									"H and HM are k-subspaces",
									"«kSubspace»(H) ∧ «kSubspace»(«timesM»(H))",
									By(idealH, spaces.At(H)))
								sourceChain := b.Have(
									"X/Y splits into X/H and H/Y",
									"«finiteQuotient»(X, H) ∧ "+
										"«finiteQuotient»(H, Y) ∧ "+
										"«colength»(X, Y) = «colength»(X, H) + «colength»(H, Y)",
									By(
										kField,
										spacesX,
										spacesY,
										spacesH,
										yInH,
										hInX,
										finiteXY,
										module_dimension.QuotientChainDim.Read(moduleK).At(inv, X, H, Y)))
								positive := b.Have(
									"the nonzero layer H/Y has nonzero dimension",
									"«colength»(H, Y) ≠ 0",
									By(
										kField,
										spacesY,
										spacesH,
										yInH,
										strict,
										sourceChain,
										module_dimension.QuotientDimZeroIff.Read(moduleK).At(inv, H, Y)))
								decrease := b.Have(
									"the upper quotient X/H has dimension below n",
									"«colength»(X, H) < n",
									ByArith(sourceChain, positive, countXY))
								upper := b.Have(
									"induction preserves the upper quotient dimension",
									"«keptByM»(X, H)",
									By(ih.At(b.TermAs[Nat]("«colength»(X, H)"), X, H), decrease, idealX, idealH, hInX, sourceChain))
								lower := b.Have(
									"multiplication preserves the simple layer dimension",
									"«keptByM»(H, Y)",
									By(
										L,
										subring,
										subfield,
										kInS,
										invertible,
										simple,
										sourceChain,
										At(preserveSimpleLayer, fieldOps, k, S, M, H, Y)))
								productInclusions := b.Have(
									"the product ideals form the same nested chain",
									"«timesM»(Y) ⊆ «timesM»(H) ∧ «timesM»(H) ⊆ «timesM»(X)",
									By(
										yInH,
										hInX,
										set_order.SubsetRefl.At(M),
										fractional_ideal.FractionalMulMono.Read(L).At(S, Y, H, M, M),
										fractional_ideal.FractionalMulMono.Read(L).At(S, H, X, M, M)))
								XM, HM, YM :=
									b.TermAs[Set[A]]("«timesM»(X)"), b.TermAs[Set[A]]("«timesM»(H)"), b.TermAs[Set[A]]("«timesM»(Y)")
								targetChain := b.Have(
									"the finite product layers assemble into XM/YM",
									"«finiteQuotient»(«timesM»(X), «timesM»(Y)) ∧ "+
										"«colength»(«timesM»(X), «timesM»(Y)) = "+
										"«colength»(«timesM»(X), «timesM»(H)) + «colength»(«timesM»(H), «timesM»(Y))",
									By(
										kField,
										spacesX,
										spacesY,
										spacesH,
										productInclusions,
										upper,
										lower,
										module_dimension.QuotientChainExtend.Read(moduleK).At(inv, XM, HM, YM)))
								b.Show(
									"both layer comparisons preserve the full quotient dimension",
									By(sourceChain, upper, lower, targetChain))
							}))))
			})
		}),
})}

// InvertibleResidueLineOverSubfield — at the ideal m of a k-rational point
// of S, the quotient M/mM of an invertible fractional ideal is
// one-dimensional over k: S/m is a line over k (FieldResiduesColength),
// multiplying by M keeps its dimension in SM/mM, and SM is M.
var InvertibleResidueLineOverSubfield = invertibleResidueLineOverSubfieldThm{family.Add(registry.ProofEntry{
	Name: "InvertibleResidueLineOverSubfield",
	Key:  "prop_e555e3eb9eae96c0",
	Reading: "That a rational ideal misses L.one is load-bearing: at m = S, m · M = M and the " +
		"quotient is zero. Invertibility is load-bearing: at M = {L.zero} the quotient is zero.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k S M m:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subfield(L, k)",
			"k ⊆ S",
			"rational_ideal(field_ring(L), k, S, m)",
			"«wfInvertible»(M)",
		},
		Conclusion: "finite_dimensional(«wfOverK», «invertibleClasses») ∧ " +
			"module_dim(«wfOverK», «invertibleClasses») = 1",
		Abbrev: Abbrev{
			{Name: "invertibleClasses", Text: "«quotient»(M, «wfMul»(m, M))"},
			{Name: "residueClasses", Text: "«quotient»(S, m)"},
			{Name: "productClasses", Text: "«quotient»(«wfMul»(S, M), «wfMul»(m, M))"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k, S, M, m *Expr[Set[A]], given Fact) {
			p := a.Conjuncts(
				given,
				"S is a subring of L",
				"k is a subfield",
				"k lies in S",
				"m is the ideal of a k-rational point of S",
				"M is invertible")
			subring, subfield, kInS, point, invertible := p[0], p[1], p[2], p[3], p[4]
			pointParts := a.Conjuncts(
				a.Unfolded(point, quotient_ring.RationalIdealDef),
				"m is an ideal",
				"m misses one",
				"every class has a representative in k")
			ideal, oneOutside, residue := pointParts[0], pointParts[1], pointParts[2]
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			ringS := a.Have(
				"S is a commutative ring",
				"comm_ring_on(«wfScalars»)",
				By(subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
			rational := a.Have(
				"read inside S, m is the ideal of the same point",
				"rational_ideal(«wfScalars», k, S, m)",
				Simp(Fwd(quotient_ring.RationalIdealDef), Fwd(module_record.RestrictRingTwice)),
				By(ideal, oneOutside, residue))
			line := a.Have(
				"S/m is a line over k: the residues of a rational ideal "+
					"have colength one, and m is not S, which holds one",
				"finite_dimensional(«wfOverK», «residueClasses») ∧ module_dim(«wfOverK», «residueClasses») = 1",
				By(
					ringS,
					subfield,
					kInS,
					ideal,
					oneOutside,
					rational,
					field.SubfieldRingSubfield.Read(L).At(k, S),
					comm_ring.SubringOne.Read(subring),
					module_record.RegularModuleRestrict.At(fieldRing, S),
					module_record.RestrictRingTwice.At(fieldRing, S, k),
					module_dimension.FieldResiduesColength.At(
						a.TermAs[module_record.RingOps[A]]("«wfScalars»"), k, a.TermAs[Fun[A, A]]("L.inv"), m)))
			carried := a.Have(
				"multiplying by M keeps the dimension of S/m",
				"finite_dimensional(«wfOverK», «productClasses») ∧ "+
					"module_dim(«wfOverK», «productClasses») = module_dim(«wfOverK», «residueClasses»)",
				By(
					subring,
					subfield,
					kInS,
					invertible,
					ideal,
					line,
					ring_ideal.CarrierIdeal.Read(ringS),
					ring_ideal.IdealSubset.Read(ideal),
					InvertibleQuotientDim.Read(L).At(k, S, M, S, m)))
			a.Show(
				"and multiplying S by M gives M",
				By(
					subring,
					invertible,
					fractional_ideal.InvertibleFractionalDef.At(
						a.TermAs[module_record.RingOps[A]]("field_ring(L)"), S, M),
					fractional_ideal.FractionalMulOne.Read(L).At(S, M),
					carried,
					line))
		}),
})}

// RationalPowerColength — the n-th power of the ideal p of a k-rational point
// has colength n in S: each step pⁿ ⊇ p·pⁿ is a k-line
// (InvertibleResidueLineOverSubfield), and colengths add along S ⊇ pⁿ ⊇ p·pⁿ.
// So a member x of pⁿ, whose principal ideal xS lies in pⁿ, generates an ideal
// of colength at least n.
var RationalPowerColength = rationalPowerColengthThm{family.Add(registry.ProofEntry{
	Name: "RationalPowerColength",
	Key:  "prop_cf74845226a36571",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k S p:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subfield(L, k)",
			"k ⊆ S",
			"rational_ideal(field_ring(L), k, S, p)",
			"«wfInvertible»(p)",
		},
		Conclusion: "(∀n:num. «finiteQuotient»(S, «power»(n)) ∧ «colength»(S, «power»(n)) = n) ∧ " +
			"(∀x:A. ∀n:num. " +
			"    x ∈ «power»(n) ∧ «finiteQuotient»(S, image(L.mul(x), S)) ⇒ " +
			"    n ≤ «colength»(S, image(L.mul(x), S)))",
		Abbrev: Abbrev{
			{Name: "power", Text: "λn:num. " +
				"    monoid_pow(λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y), S, p, n)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k, S, p *Expr[Set[A]], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"k is a subfield",
				"k lies in S",
				"p is the ideal of a k-rational point",
				"p is invertible")
			subring, subfield, kInS, rational, invertible := given[0], given[1], given[2], given[3], given[4]
			scalars := a.TermAs[module_record.RingOps[A]]("«wfScalars»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wfField»")
			overK := a.TermAs[module_record.RingOps[A]]("«wfOverK»")
			inv := a.TermAs[Fun[A, A]]("L.inv")
			pointParts := a.Conjuncts(
				a.Unfolded(rational, quotient_ring.RationalIdealDef),
				"p is an ideal",
				"p misses one",
				"every class has a representative in k")
			ideal := pointParts[0]
			pInS := a.Have(
				"p lies in S",
				"p ⊆ S",
				By(ideal, ring_ideal.IdealSubset.At(scalars, p)))
			sInL := a.Have(
				"S lies in L",
				"S ⊆ L.carrier",
				By(subring, comm_ring.SubringSubset.At(a.TermAs[module_record.RingOps[A]]("field_ring(L)"), S)))
			vectorSpace := a.Have(
				"L is a vector space over k",
				"module_on(«wfOverK», «wfField»)",
				By(subfield, field.SubfieldSubring.Read(L).At(k), fractional_ideal.FieldModuleOn.Read(L).At(k)))
			scalarField := a.Have(
				"k is a field of scalars",
				"ring_subfield(«wfOverK», L.inv, k)",
				By(subfield, field.SubfieldRingSubfield.Read(L).At(k, k)))
			subspace := a.Have(
				"a fractional ideal of S is a k-subspace of L",
				"∀X:set(A). «wfFractional»(X) ⇒ submodule(«wfOverK», «wfField», X)",
				Derive(func(b *Argument) {
					X := b.FixAs[Set[A]]("X")
					fractional := b.Assume()
					b.Show(
						"restrict the scalars from S to k",
						By(fractional, kInS, submodule.SubmoduleRestrictScalars.At(scalars, vectors, X, overK)))
				}))
			sFractional := a.Have(
				"S is a fractional ideal of itself",
				"«wfFractional»(S)",
				By(subring, fractional_ideal.SubringSubmodule.Read(L).At(S)))
			absorbs := a.Have(
				"p multiplies a fractional ideal X into itself, p · X ⊆ S · X = X",
				"∀X:set(A). «wfFractional»(X) ⇒ «wfMul»(p, X) ⊆ X",
				Derive(func(b *Argument) {
					X := b.FixAs[Set[A]]("X")
					fractional := b.Assume()
					b.Show(
						"p lies in S, and S · X is X",
						By(
							Normalized,
							subring,
							pInS,
							fractional,
							set_order.SubsetRefl,
							fractional_ideal.FractionalMulMono.Read(L).At(S, p, S, X, X),
							fractional_ideal.FractionalMulOne.Read(L).At(S, X)))
				}))
			powers := a.Have(
				"every power of p is an invertible fractional ideal inside S",
				"∀n:num. «wfInvertible»(«power»(n)) ∧ «wfFractional»(«power»(n)) ∧ «power»(n) ⊆ S",
				a.ForEach(func(n *Expr[Nat]) Action {
					return By(
						subring,
						invertible,
						pInS,
						fractional_ideal.InvertibleIdealPowers.Read(L).At(S, p, n),
						fractional_ideal.InvertibleFractionalDef)
				}))
			colengths := a.Have(
				"the n-th power of p has colength n",
				"∀n:num. «finiteQuotient»(S, «power»(n)) ∧ «colength»(S, «power»(n)) = n",
				Derive(func(b *Argument) {
					b.Induct("n")
					b.Base(
						"the zeroth power is S, of colength zero",
						Simp(Fwd(comm_monoid.MonoidPowDef.Inst[Set[A]]())),
						By(
							vectorSpace,
							scalarField,
							sFractional,
							subspace.At(S),
							set_order.SubsetRefl.At(S),
							module_dimension.QuotientDimZeroIff.Read(vectorSpace).At(inv, S, S)))
					b.Step(
						"the next power adds a k-line below the last",
						func(c *Argument, ih Fact) {
							n := c.TermAs[Nat]("n")
							last := c.TermAs[Set[A]]("«power»(n)")
							next := c.TermAs[Set[A]]("«wfMul»(p, «power»(n))")
							previous := c.Conjuncts(
								powers.At(n),
								"the last power is invertible",
								"a fractional ideal",
								"inside S")
							nextFractional := c.Have(
								"p times it is the next power, a fractional ideal too",
								"«wfFractional»(«wfMul»(p, «power»(n)))",
								By(powers.At(c.TermAs[Nat]("suc(n)")), comm_monoid.MonoidPowDef))
							line := c.Have(
								"the step is a k-line",
								"«finiteQuotient»(«power»(n), «wfMul»(p, «power»(n))) ∧ "+
									"«colength»(«power»(n), «wfMul»(p, «power»(n))) = 1",
								By(
									subring,
									subfield,
									kInS,
									rational,
									previous[0],
									InvertibleResidueLineOverSubfield.Read(L).At(k, S, last, p)))
							chain := c.Have(
								"colengths add along S ⊇ pⁿ ⊇ p · pⁿ",
								"«finiteQuotient»(S, «wfMul»(p, «power»(n))) ∧ "+
									"«colength»(S, «wfMul»(p, «power»(n))) = "+
									"«colength»(S, «power»(n)) + «colength»(«power»(n), «wfMul»(p, «power»(n)))",
								By(
									vectorSpace,
									scalarField,
									subspace.At(S),
									subspace.At(last),
									subspace.At(next),
									sFractional,
									previous[1],
									nextFractional,
									absorbs.At(last),
									previous[2],
									ih,
									line,
									module_dimension.QuotientChainExtend.Read(vectorSpace).At(inv, S, last, next)))
							c.Do(Simp(Fwd(comm_monoid.MonoidPowDef.Inst[Set[A]]())))
							c.Show(
								"so the colength grows by one",
								ByArith(chain, line, ih))
						})
				}))
			bound := a.Have(
				"a member of pⁿ generates an ideal of colength at least n",
				Statement{
					Binders:    "∀x:A. ∀n:num.",
					Hypotheses: []string{"x ∈ «power»(n)", "«finiteQuotient»(S, image(L.mul(x), S))"},
					Conclusion: "n ≤ «colength»(S, image(L.mul(x), S))",
				},
				Derive(func(b *Argument) {
					x, n := b.FixAs[A]("x"), b.FixAs[Nat]("n")
					parts := b.Conjuncts(
						b.Assume(),
						"x lies in pⁿ",
						"S/xS is finite-dimensional")
					power := b.TermAs[Set[A]]("«power»(n)")
					principal := b.TermAs[Set[A]]("image(L.mul(x), S)")
					previous := b.Conjuncts(
						powers.At(n),
						"pⁿ is invertible",
						"a fractional ideal",
						"inside S")
					xInL := b.Have(
						"x lies in L",
						"x ∈ L.carrier",
						BySets(parts[0], previous[2], sInL))
					xm := b.MemberOf[on.L](x, xInL)
					multiples := b.Have(
						"xS lies in pⁿ, pⁿ being an S-module",
						"∀s:A. s ∈ S ⇒ x * s ∈ «power»(n)",
						Derive(func(c *Argument) {
							s := c.FixAs[A]("s")
							sIn := c.Assume()
							sm := c.MemberOf[on.L](s, c.Have(
								"s lies in L",
								"s ∈ L.carrier",
								BySets(sIn, sInL)))
							commuted := c.Have(
								"x · s = s · x",
								"x * s = s * x",
								ByArith(L, xm, sm))
							c.Show(
								"s · x is an S-multiple in pⁿ",
								By(commuted, sIn, parts[0], previous[1], submodule.SubmoduleSmul.At(scalars, vectors, power, s, x)))
						}))
					inside := b.Have(
						"so xS lies in pⁿ",
						"image(L.mul(x), S) ⊆ «power»(n)",
						By(multiples, set_image.ImageSubsetIff.At(b.TermAs[Fun[A, A]]("L.mul(x)"), S, power)))
					principalFractional := b.Have(
						"xS is a fractional ideal",
						"«wfFractional»(image(L.mul(x), S))",
						By(subring, sFractional, fractional_ideal.ScaleSubmodule.Read(L).At(S, S, xm)))
					chain := b.Have(
						"colengths add along S ⊇ pⁿ ⊇ xS",
						"«colength»(S, image(L.mul(x), S)) = "+
							"«colength»(S, «power»(n)) + «colength»(«power»(n), image(L.mul(x), S))",
						By(
							vectorSpace,
							scalarField,
							subspace.At(S),
							subspace.At(power),
							subspace.At(principal),
							sFractional,
							previous[1],
							principalFractional,
							inside,
							previous[2],
							parts[1],
							module_dimension.QuotientChainDim.Read(vectorSpace).At(inv, S, power, principal)))
					b.Show(
						"and pⁿ has colength n",
						ByArith(chain, colengths.At(n)))
				}))
			a.Show(
				"the colengths of the powers, and the bound they give",
				By(colengths, bound))
		}),
})}

// InvertibleFractionalQuotientDim — multiplying by an invertible fractional
// ideal keeps the dimension of a quotient of fractional ideals under an
// invertible one: a common denominator makes both integral, where
// InvertibleQuotientDim applies, and scaling back keeps the dimension.
var InvertibleFractionalQuotientDim = invertibleFractionalQuotientDimThm{family.Add(registry.ProofEntry{
	Name: "InvertibleFractionalQuotientDim",
	Key:  "prop_9f8574cf3d7cee2e",
	Reading: "fraction_field_carrier and the invertibility of I serve only for " +
		"a common denominator of I: J need only be fractional. The invertibility " +
		"of M is load-bearing: at M = {L.zero} both products are {L.zero}.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k S I J M:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subfield(L, k)",
			"k ⊆ S",
			"fraction_field_carrier(field_ring(L), S)",
			"«wfInvertible»(I)",
			"«wfFractional»(J)",
			"J ⊆ I",
			"«wfInvertible»(M)",
			"«finiteQuotient»(I, J)",
		},
		Conclusion: "«finiteQuotient»(«wfMul»(I, M), «wfMul»(J, M)) ∧ " +
			"«colength»(«wfMul»(I, M), «wfMul»(J, M)) = «colength»(I, J)",
	},
		func(a *Argument, L field.FieldFact[on.L], k, S, I, J, M *Expr[Set[A]], given Fact) {
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			ringS := a.TermAs[module_record.RingOps[A]]("«wfScalars»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wfField»")
			IM := a.TermAs[Set[A]]("«wfMul»(I, M)")
			JM := a.TermAs[Set[A]]("«wfMul»(J, M)")
			originalModules := a.Have(
				"the invertible numerator and factor are fractional modules",
				"«wfFractional»(I) ∧ «wfFractional»(M)",
				By(
					given,
					fractional_ideal.InvertibleFractionalDef.At(fieldRing, S, I),
					fractional_ideal.InvertibleFractionalDef.At(fieldRing, S, M)))
			originalCarriers := a.Have(
				"all three fractional modules lie in L",
				"I ⊆ L.carrier ∧ J ⊆ L.carrier ∧ M ⊆ L.carrier",
				By(
					given,
					originalModules,
					submodule.SubmoduleSubset.At(ringS, vectors, I),
					submodule.SubmoduleSubset.At(ringS, vectors, J),
					submodule.SubmoduleSubset.At(ringS, vectors, M)))
			c, denominator := a.ObtainAs[A](
				"choose a nonzero common denominator for I",
				"∃c:A. c ∈ S ∧ c ≠ L.zero ∧ image(L.mul(c), I) ⊆ S",
				By(given, invertible_fractional_ideal.InvertibleCommonDenominator.Read(L).At(S, I)))
			cInField := a.Have(
				"the common denominator lies in L",
				"c ∈ L.carrier",
				BySets(denominator, given, comm_ring.SubringSubset.At(fieldRing, S)))
			cm := a.MemberOf[on.L](c, cInField)
			scale := a.TermAs[Fun[A, A]]("L.mul(c)")
			cI := a.TermAs[Set[A]]("image(L.mul(c), I)")
			cJ := a.TermAs[Set[A]]("image(L.mul(c), J)")
			cIM := a.TermAs[Set[A]]("image(L.mul(c), «wfMul»(I, M))")
			cJM := a.TermAs[Set[A]]("image(L.mul(c), «wfMul»(J, M))")
			clearedInclusion := a.Have(
				"clearing denominators preserves inclusion and puts J inside S",
				"image(L.mul(c), J) ⊆ image(L.mul(c), I) ∧ image(L.mul(c), J) ⊆ S",
				By(denominator, given, set_image.ImageSubset.At(scale, J, I), set_order.SubsetTrans.At(cJ, cI, S)))
			clearedModules := a.Have(
				"the cleared modules remain S-submodules of L",
				"«wfFractional»(image(L.mul(c), I)) ∧ «wfFractional»(image(L.mul(c), J))",
				By(
					given,
					originalModules,
					fractional_ideal.ScaleSubmodule.Read(L).At(S, I, cm),
					fractional_ideal.ScaleSubmodule.Read(L).At(S, J, cm)))
			clearedIdeals := a.Have(
				"the cleared modules are integral ideals",
				"«wfIdeal»(image(L.mul(c), I)) ∧ «wfIdeal»(image(L.mul(c), J))",
				By(
					given,
					denominator,
					clearedInclusion,
					clearedModules,
					fractional_ideal.IntegralIdealFractional.Read(L).At(S, cI),
					fractional_ideal.IntegralIdealFractional.Read(L).At(S, cJ)))
			_, clearQuotientDef := a.LetAs[module_record.ModuleOps[A, Set[A]]](
				"Qclear", "«quotient»(image(L.mul(c), «wfMul»(I, M)), image(L.mul(c), «wfMul»(J, M)))")
			_, backQuotientDef := a.LetAs[module_record.ModuleOps[A, Set[A]]](
				"Qback",
				"«quotient»(image(L.mul(L.inv(c)), image(L.mul(c), «wfMul»(I, M))), "+
					"    image(L.mul(L.inv(c)), image(L.mul(c), «wfMul»(J, M))))")
			clearedQuotient := a.Have(
				"cI/cJ is finite-dimensional of the dimension of I/J",
				"«finiteQuotient»(image(L.mul(c), I), image(L.mul(c), J)) ∧ "+
					"«colength»(image(L.mul(c), I), image(L.mul(c), J)) = «colength»(I, J)",
				By(given, originalModules, denominator, ScaleQuotientDim.Read(L).At(k, S, I, J, cm)))
			productScaling := a.Have(
				"the denominator commutes with multiplication by M",
				"«wfMul»(image(L.mul(c), I), M) = image(L.mul(c), «wfMul»(I, M)) ∧ "+
					"«wfMul»(image(L.mul(c), J), M) = image(L.mul(c), «wfMul»(J, M))",
				By(
					given,
					originalCarriers,
					fractional_ideal.FractionalMulScale.Read(L).At(S, I, M, cm),
					fractional_ideal.FractionalMulScale.Read(L).At(S, J, M, cm)))
			multiplied := a.Have(
				"multiplying by M keeps the dimension of cI/cJ",
				"finite_dimensional(«wfOverK», Qclear) ∧ "+
					"module_dim(«wfOverK», Qclear) = «colength»(image(L.mul(c), I), image(L.mul(c), J))",
				Derive(func(e *Argument) {
					equations := e.Conjuncts(
						productScaling,
						"scaling the numerator product",
						"scaling the denominator product")
					e.Show(
						"apply preservation of ideal quotient dimensions to cI and cJ",
						Simp(Fwd(clearQuotientDef), Rev(equations[0]), Rev(equations[1])),
						By(
							given,
							clearedIdeals,
							clearedInclusion,
							clearedQuotient,
							InvertibleQuotientDim.Read(L).At(k, S, M, cI, cJ)))
				}))
			productModules := a.Have(
				"the products are fractional modules with JM contained in IM",
				"«wfFractional»(«wfMul»(I, M)) ∧ «wfFractional»(«wfMul»(J, M)) ∧ «wfMul»(J, M) ⊆ «wfMul»(I, M)",
				By(
					given,
					originalCarriers,
					fractional_ideal.FractionalMulSubmodule.Read(L).At(S, I, M),
					fractional_ideal.FractionalMulSubmodule.Read(L).At(S, J, M),
					fractional_ideal.FractionalMulMono.Read(L).At(S, J, I, M, M),
					set_order.SubsetRefl.At(M)))
			productCarriers := a.Have(
				"the products lie in L",
				"«wfMul»(I, M) ⊆ L.carrier ∧ «wfMul»(J, M) ⊆ L.carrier",
				By(
					productModules,
					submodule.SubmoduleSubset.At(ringS, vectors, IM),
					submodule.SubmoduleSubset.At(ringS, vectors, JM)))
			scaledProducts := a.Have(
				"the scaled products are fractional modules with the same inclusion",
				"«wfFractional»(image(L.mul(c), «wfMul»(I, M))) ∧ "+
					"«wfFractional»(image(L.mul(c), «wfMul»(J, M))) ∧ "+
					"image(L.mul(c), «wfMul»(J, M)) ⊆ image(L.mul(c), «wfMul»(I, M))",
				By(
					given,
					productModules,
					fractional_ideal.ScaleSubmodule.Read(L).At(S, IM, cm),
					fractional_ideal.ScaleSubmodule.Read(L).At(S, JM, cm),
					set_image.ImageSubset.At(scale, JM, IM)))
			inverseDenominator := a.Conjuncts(
				a.Have(
					"the inverse denominator is a nonzero member of L",
					"L.inv(c) ∈ L.carrier ∧ L.inv(c) ≠ L.zero",
					By(denominator, field.InvIn.Read(L).At(cm), field.InvEqZeroOn.Read(L).At(cm))),
				"L.inv(c) lies in L",
				"L.inv(c) is nonzero")
			inverse := a.MemberOf[on.L](a.TermAs[A]("L.inv(c)"), inverseDenominator[0])
			cancellation := a.Have(
				"inverse scaling recovers both product modules",
				"image(L.mul(L.inv(c)), image(L.mul(c), «wfMul»(I, M))) = «wfMul»(I, M) ∧ "+
					"image(L.mul(L.inv(c)), image(L.mul(c), «wfMul»(J, M))) = «wfMul»(J, M)",
				By(
					denominator,
					productCarriers,
					fractional_ideal.ScaleCancel.Read(L).At(IM, cm),
					fractional_ideal.ScaleCancel.Read(L).At(JM, cm)))
			inverseScaling := a.Have(
				"scaling by the inverse of c keeps the dimension of the finite product quotient",
				"finite_dimensional(«wfOverK», Qback) ∧ "+
					"module_dim(«wfOverK», Qback) = module_dim(«wfOverK», Qclear)",
				By(
					Normalized,
					clearQuotientDef,
					backQuotientDef,
					given,
					inverseDenominator[1],
					scaledProducts,
					multiplied,
					ScaleQuotientDim.Read(L).At(k, S, cIM, cJM, inverse)))
			a.Show(
				"the three comparisons preserve finiteness and the original dimension",
				By(backQuotientDef, cancellation, clearedQuotient, multiplied, inverseScaling))
		}),
})}

// NonzeroIdealQuotientFinite — when k is a subfield of L inside the subring
// S and every nonzero principal quotient S/a · S is finite-dimensional over
// k, so is S/I for every nonzero ideal I of S: I holds a nonzero f, and the
// chain f · S ⊆ I ⊆ S of k-subspaces makes S/I a quotient of S/f · S.
var NonzeroIdealQuotientFinite = nonzeroIdealQuotientFiniteThm{family.Add(registry.ProofEntry{
	Name: "NonzeroIdealQuotientFinite",
	Key:  "prop_f6ea6e83d1726392",
	Reading: "I ≠ {zero} is load-bearing: S modulo {zero} is S, " +
		"which need not be finite-dimensional over k (k[t] inside k(t)).",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k S I:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subfield(L, k)",
			"k ⊆ S",
			"∀a:A. a ∈ S ∧ a ≠ L.zero ⇒ «finiteQuotient»(S, image(L.mul(a), S))",
			"«wfIdeal»(I)",
			"I ≠ {L.zero}",
		},
		Conclusion: "«finiteQuotient»(S, I)",
	},
		func(a *Argument, L field.FieldFact[on.L], k, S, I *Expr[Set[A]], h Fact) {
			fieldOps := a.TermAs[field.FieldOps[A]]("L")
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			scalars := a.TermAs[module_record.RingOps[A]]("«wfScalars»")
			overK := a.TermAs[module_record.RingOps[A]]("«wfOverK»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wfField»")
			data := a.Conjuncts(
				h,
				"S is a subring of L",
				"k is a subfield",
				"k lies in S",
				"nonzero principal quotients of S are finite",
				"I is an ideal of S",
				"I is not the zero ideal")
			subring, constants, constantsInS := data[0], data[1], data[2]
			principalFinite, ideal, nonzero := data[3], data[4], data[5]
			f, chosen := a.ObtainAs[A](
				"I holds zero and is not {zero}, so it holds a nonzero f",
				"∃f:A. f ∈ I ∧ f ≠ L.zero",
				BySets(nonzero, ring_ideal.IdealZero.Read(ideal)),
				Named("f"))
			inside := a.Have(
				"I lies in S, and with it f, and S lies in L",
				"I ⊆ S ∧ f ∈ S ∧ S ⊆ L.carrier",
				BySets(
					chosen,
					ring_ideal.IdealSubset.Read(ideal),
					comm_ring.SubringSubset.At(fieldRing, S),
					subring))
			fm := a.MemberOf[on.L](f, a.Have(
				"f lies in L",
				"f ∈ L.carrier",
				BySets(inside)))
			multiples := a.Have(
				"I absorbs the products by members of S, and S is commutative, so it holds f · S",
				"image(L.mul(f), S) ⊆ I",
				BySets(
					chosen,
					inside,
					ring_ideal.IdealMul.Read(ideal),
					comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(L)))))
			principalQuotient := a.Have(
				"S/f · S is finite-dimensional over k",
				"«finiteQuotient»(S, image(L.mul(f), S))",
				By(chosen, inside, principalFinite.At(f)))
			vectorSpace := a.Have(
				"L is a vector space over k",
				"module_on(«wfOverK», «wfField»)",
				By(constants, field.SubfieldSubring.At(fieldOps, k), fractional_ideal.FieldModuleOn.Read(L).At(k)))
			inverse := a.TermAs[Fun[A, A]]("L.inv")
			scalarField := a.Have(
				"k, a subfield, is a field under the restricted scalar ring's operations, with L's inverse",
				"ring_subfield(«wfOverK», L.inv, k)",
				By(constants, field.SubfieldRingSubfield.Read(L).At(k, k)))
			subspaces := a.Have(
				"S and its ideal I are S-submodules of L, so k-subspaces",
				"submodule(«wfOverK», «wfField», S) ∧ submodule(«wfOverK», «wfField», I)",
				By(
					subring,
					ideal,
					constantsInS,
					fractional_ideal.SubringSubmodule.Read(L).At(S),
					fractional_ideal.IntegralIdealFractional.Read(L).At(S, I),
					submodule.SubmoduleRestrictScalars.At(scalars, vectors, S, overK),
					submodule.SubmoduleRestrictScalars.At(scalars, vectors, I, overK)))
			scaledSubspace := a.Have(
				"f · S is a k-subspace too, a multiple of the k-subspace S",
				"submodule(«wfOverK», «wfField», image(L.mul(f), S))",
				By(
					constants,
					subspaces,
					field.SubfieldSubring.At(fieldOps, k),
					fractional_ideal.ScaleSubmodule.Read(L).At(k, S, fm)))
			a.Show(
				"the chain f · S ⊆ I ⊆ S makes S/I a quotient of S/f · S",
				By(
					scalarField,
					principalQuotient,
					multiples,
					inside,
					subspaces,
					scaledSubspace,
					module_dimension.QuotientChainDim.Read(vectorSpace).At(
						inverse, S, I, a.TermAs[Set[A]]("image(L.mul(f), S)"))))
		}),
})}

// InvertibleMeetQuotientsFinite — when L is the field of fractions of S,
// k is a subfield of L contained in S, every nonzero principal quotient
// S/a · S is finite-dimensional over k, and J is an invertible fractional
// ideal, the meet J ∩ S has finite-dimensional quotients over k in S and
// in J. A nonzero c with c · S ⊆ J makes S/(J ∩ S) a quotient of S/c · S;
// a nonzero common denominator d of J makes J/(J ∩ S) a quotient of
// J/d · J, which J's invertibility gives the dimension of S/d · S.
var InvertibleMeetQuotientsFinite = invertibleMeetQuotientsFiniteThm{family.Add(registry.ProofEntry{
	Name: "InvertibleMeetQuotientsFinite",
	Key:  "prop_19428f8165155477",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k S J:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subfield(L, k)",
			"k ⊆ S",
			"fraction_field_carrier(field_ring(L), S)",
			"«wfInvertible»(J)",
			"∀a:A. a ∈ S ∧ a ≠ L.zero ⇒ «finiteQuotient»(S, image(L.mul(a), S))",
		},
		Conclusion: "«finiteQuotient»(S, J ∩ S) ∧ «finiteQuotient»(J, J ∩ S)",
	},
		func(a *Argument, L field.FieldFact[on.L], k, S, J *Expr[Set[A]], h Fact) {
			fieldOps := a.TermAs[field.FieldOps[A]]("L")
			scalars := a.TermAs[module_record.RingOps[A]]("«wfScalars»")
			overK := a.TermAs[module_record.RingOps[A]]("«wfOverK»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wfField»")
			data := a.Conjuncts(
				h,
				"S is a subring of L",
				"k is a subfield",
				"k lies in S",
				"S has fraction field L",
				"J is an invertible fractional ideal",
				"nonzero principal quotients of S are finite")
			subring, constants, constantsInS := data[0], data[1], data[2]
			fractions, invertible, principalFinite := data[3], data[4], data[5]
			invertibleData := a.Have(
				"J is a fractional ideal whose product with its inverse is S",
				"«wfFractional»(J) ∧ «wfMul»(J, «wfInverse»(J)) = S",
				By(
					invertible,
					fractional_ideal.InvertibleFractionalDef.At(
						a.TermAs[module_record.RingOps[A]]("field_ring(L)"), S, J)))
			subringSubmodule := a.Have(
				"S is a module over itself",
				"«wfFractional»(S)",
				By(subring, fractional_ideal.SubringSubmodule.Read(L).At(S)))
			carriers := a.Have(
				"S and J lie in L",
				"S ⊆ L.carrier ∧ J ⊆ L.carrier",
				By(
					subring,
					invertibleData,
					comm_ring.SubringSubset.At(a.TermAs[module_record.RingOps[A]]("field_ring(L)"), S),
					submodule.SubmoduleSubset.At(scalars, vectors, J)))
			d, denominator := a.ObtainAs[A](
				"clear a common denominator of J",
				"∃d:A. d ∈ S ∧ d ≠ L.zero ∧ image(L.mul(d), J) ⊆ S",
				By(
					subring,
					fractions,
					invertible,
					invertible_fractional_ideal.InvertibleCommonDenominator.Read(L).At(S, J)))
			c, principal := a.ObtainAs[A](
				"J contains a nonzero principal ideal c · S",
				"∃c:A. c ∈ S ∧ c ≠ L.zero ∧ image(L.mul(c), S) ⊆ J",
				By(
					subring,
					fractions,
					invertible,
					invertible_fractional_ideal.InvertibleContainsPrincipal.Read(L).At(S, J)))
			denominatorsInField := a.Have(
				"both c and d lie in L",
				"c ∈ L.carrier ∧ d ∈ L.carrier",
				BySets(principal, denominator, carriers))
			scaledJInJ := a.Have(
				"multiplication by d preserves J",
				"image(L.mul(d), J) ⊆ J",
				BySets(denominator, invertibleData, At(submodule.SubmoduleSmul, scalars, vectors, J, d)))
			principalInS := a.Have(
				"the principal ideals c · S and d · S lie in S",
				"image(L.mul(c), S) ⊆ S ∧ image(L.mul(d), S) ⊆ S",
				BySets(
					principal,
					denominator,
					subring,
					At(comm_ring.SubringMul, a.TermAs[module_record.RingOps[A]]("field_ring(L)"), S)))
			insideMeet := a.Have(
				"c · S and d · J both lie in the meet",
				"image(L.mul(c), S) ⊆ J ∩ S ∧ image(L.mul(d), J) ⊆ J ∩ S",
				BySets(principalInS, principal, scaledJInJ, denominator))
			vectorSpace := a.Have(
				"L is a vector space over k",
				"module_on(«wfOverK», «wfField»)",
				By(constants, field.SubfieldSubring.At(fieldOps, k), fractional_ideal.FieldModuleOn.Read(L).At(k)))
			inverse := a.TermAs[Fun[A, A]]("L.inv")
			scalarField := a.Have(
				"k, a subfield, is a field under the restricted scalar ring's operations, with L's inverse",
				"ring_subfield(«wfOverK», L.inv, k)",
				By(constants, field.SubfieldRingSubfield.Read(L).At(k, k)))
			subspaces := a.Have(
				"S and J are k-subspaces of L",
				"submodule(«wfOverK», «wfField», S) ∧ submodule(«wfOverK», «wfField», J)",
				By(
					subringSubmodule,
					invertibleData,
					constantsInS,
					submodule.SubmoduleRestrictScalars.At(scalars, vectors, S, overK),
					submodule.SubmoduleRestrictScalars.At(scalars, vectors, J, overK)))
			meetSubspace := a.Have(
				"their meet is a k-subspace",
				"submodule(«wfOverK», «wfField», J ∩ S)",
				By(subspaces, submodule.SubmoduleInter.At(overK, vectors, J, S)))
			scaledSubspaces := a.Have(
				"c · S and d · J are k-subspaces",
				"submodule(«wfOverK», «wfField», image(L.mul(c), S)) ∧ "+
					"submodule(«wfOverK», «wfField», image(L.mul(d), J))",
				By(
					constants,
					denominatorsInField,
					subspaces,
					field.SubfieldSubring.At(fieldOps, k),
					fractional_ideal.ScaleSubmodule.Read(L).AsFact().At(k, S, c),
					fractional_ideal.ScaleSubmodule.Read(L).AsFact().At(k, J, d)))
			principalQuotients := a.Have(
				"the principal quotients S/c · S and S/d · S are finite",
				"«finiteQuotient»(S, image(L.mul(c), S)) ∧ «finiteQuotient»(S, image(L.mul(d), S))",
				By(principal, denominator, principalFinite.At(c), principalFinite.At(d)))
			meetSubsets := a.Have(
				"the meet lies in S and J",
				"J ∩ S ⊆ S ∧ J ∩ S ⊆ J",
				BySets())
			subringQuotient := a.Have(
				"S modulo the meet is a quotient of S modulo c · S",
				"«finiteQuotient»(S, J ∩ S)",
				By(
					scalarField,
					principalQuotients,
					insideMeet,
					meetSubsets,
					subspaces,
					scaledSubspaces,
					meetSubspace,
					module_dimension.QuotientChainDim.Read(vectorSpace).At(
						inverse, S, a.TermAs[Set[A]]("J ∩ S"), a.TermAs[Set[A]]("image(L.mul(c), S)"))))
			principalSubmodule := a.Have(
				"d · S is a submodule over S",
				"«wfFractional»(image(L.mul(d), S))",
				By(
					subring,
					denominatorsInField,
					subringSubmodule,
					fractional_ideal.ScaleSubmodule.Read(L).AsFact().At(S, S, d)))
			ideals := a.Have(
				"S and d · S are ideals of S",
				"«wfIdeal»(S) ∧ «wfIdeal»(image(L.mul(d), S))",
				By(
					subring,
					subringSubmodule,
					principalSubmodule,
					principalInS,
					fractional_ideal.IntegralIdealFractional.Read(L).AsFact().At(S, S),
					fractional_ideal.IntegralIdealFractional.Read(L).AsFact().At(
						S, a.TermAs[Set[A]]("image(L.mul(d), S)")),
					set_order.SubsetRefl.At(S)))
			products := a.Have(
				"multiplication by J identifies the two ideal products",
				"«wfMul»(S, J) = J ∧ «wfMul»(image(L.mul(d), S), J) = image(L.mul(d), J)",
				By(
					subring,
					invertibleData,
					carriers,
					denominatorsInField,
					fractional_ideal.FractionalMulOne.Read(L).AsFact().At(S, J),
					fractional_ideal.FractionalMulScale.Read(L).AsFact().At(S, S, J, d)))
			scaledQuotient := a.Have(
				"invertibility transfers finiteness from S/d · S to J/d · J",
				"«finiteQuotient»(J, image(L.mul(d), J))",
				By(
					subring,
					constants,
					constantsInS,
					invertible,
					ideals,
					principalInS,
					principalQuotients,
					products,
					InvertibleQuotientDim.Read(L).AsFact().At(k, S, J, S, a.TermAs[Set[A]]("image(L.mul(d), S)"))))
			fractionalQuotient := a.Have(
				"J modulo the meet is a quotient of J modulo d · J",
				"«finiteQuotient»(J, J ∩ S)",
				By(
					scalarField,
					scaledQuotient,
					insideMeet,
					meetSubsets,
					subspaces,
					scaledSubspaces,
					meetSubspace,
					module_dimension.QuotientChainDim.Read(vectorSpace).At(
						inverse, J, a.TermAs[Set[A]]("J ∩ S"), a.TermAs[Set[A]]("image(L.mul(d), J)"))))
			a.Show(
				"both quotients by the meet are finite",
				By(subringQuotient, fractionalQuotient))
		}),
})}

// InvertibleColengthQuotient — dividing an invertible fractional ideal N
// by an invertible ideal I of S enlarges it by the colength of I. The
// product P = (S : I) · N is invertible, with S · P = P and, I cancelling
// its inverse, I · P = N. So I ⊆ S gives N ⊆ P, and InvertibleQuotientDim at
// S and I, with factor P, gives P/N the dimension of S/I.
var InvertibleColengthQuotient = invertibleColengthQuotientThm{family.Add(registry.ProofEntry{
	Name: "InvertibleColengthQuotient",
	Key:  "prop_e4f9161a3c0339ee",
	Reading: "Twisting at a point is the case where I is the point's ideal in a chart: (S : I) " +
		"· N is N with a simple pole allowed there, and the gain is one at a rational point. The " +
		"invertibility of I is load-bearing: at S = k[t³, t⁴, t⁵] in k(t), N = S and I the ideal " +
		"of t³, t⁴, t⁵, (S : I) = k[t], so (S : I)/S has dimension two while S/I has dimension one.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k S N I:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subfield(L, k)",
			"k ⊆ S",
			"«wfIdeal»(I)",
			"«wfInvertible»(I)",
			"«wfInvertible»(N)",
			"«finiteQuotient»(S, I)",
		},
		Conclusion: "N ⊆ «wfMul»(«wfInverse»(I), N) ∧ " +
			"finite_dimensional(«wfOverK», «enlargedClasses») ∧ " +
			"module_dim(«wfOverK», «enlargedClasses») = «colength»(S, I)",
		Abbrev: Abbrev{
			{Name: "enlargedClasses", Text: "«quotient»(«wfMul»(«wfInverse»(I), N), N)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k, S, N, I *Expr[Set[A]], hypotheses Fact) {
			p := a.Conjuncts(
				hypotheses,
				"S is a subring of L",
				"k is a subfield",
				"k lies in S",
				"I is an ideal of S",
				"I is invertible",
				"N is invertible",
				"S modulo I has finite dimension over k")
			subring, subfield, kInS, idealI, invertibleI, invertibleN, finite :=
				p[0], p[1], p[2], p[3], p[4], p[5], p[6]
			P, pDef := a.LetAs[Set[A]]("P", "«wfMul»(«wfInverse»(I), N)")
			inverseI := a.TermAs[Set[A]]("«wfInverse»(I)")
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			scalars := a.TermAs[module_record.RingOps[A]]("«wfScalars»")
			inverseInvertible := a.Have(
				"the inverse of I is invertible",
				"«wfInvertible»(«wfInverse»(I))",
				By(subring, invertibleI, fractional_ideal.InvertibleInverse.Read(L).At(S, I)))
			pInvertible := a.Have(
				"its product with N is invertible",
				"«wfInvertible»(P)",
				By(
					Normalized,
					subring,
					inverseInvertible,
					invertibleN,
					pDef,
					fractional_ideal.InvertibleProduct.Read(L).At(S, inverseI, N)))
			iData := a.Conjuncts(
				a.Unfolded(invertibleI, fractional_ideal.InvertibleFractionalDef),
				"I is fractional",
				"I cancels its inverse")
			fractionalI, unitI := iData[0], iData[1]
			fractionalN := a.Have(
				"N is fractional",
				"«wfFractional»(N)",
				By(invertibleN, fractional_ideal.InvertibleFractionalDef.At(fieldRing, S, N)))
			inverseInL := fractional_ideal.FractionalInverseSubset.Read(L).At(S, I)
			ringS := a.Have(
				"S is a ring under the inherited operations",
				"comm_ring_on(«wfScalars»)",
				By(subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
			iInS := a.Have(
				"I lies in S",
				"I ⊆ S",
				By(idealI, ring_ideal.IdealSubset.At(scalars, I)))
			sProduct := a.Have(
				"S fixes the fractional ideal P",
				"«wfMul»(S, P) = P",
				By(
					subring,
					pInvertible,
					fractional_ideal.InvertibleFractionalDef.At(fieldRing, S, P),
					fractional_ideal.FractionalMulOne.Read(L).At(S, P)))
			iProduct := a.Have(
				"multiplication by I cancels the inverse in P",
				"«wfMul»(I, P) = N",
				pDef.Rw(),
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("«wfMul»(«wfMul»(I, «wfInverse»(I)), N)"),
						"associate I with its inverse",
						By(
							subring,
							submodule.SubmoduleSubset.Read(fractionalI),
							inverseInL,
							submodule.SubmoduleSubset.Read(fractionalN),
							fractional_ideal.FractionalMulAssoc.Read(L).At(S, I, inverseI, N))),
					FinalLeg(
						"cancel the inverse pair and use S as the product's unit",
						unitI.Rw(),
						By(subring, fractionalN, fractional_ideal.FractionalMulOne.Read(L).At(S, N)))))
			monotone := a.Have(
				"the inclusion I into S is preserved by multiplication by P",
				"«wfMul»(I, P) ⊆ «wfMul»(S, P)",
				By(iInS, set_order.SubsetRefl, fractional_ideal.FractionalMulMono.Read(L).At(S, I, S, P, P)))
			inclusion := a.Have(
				"therefore N lies in P",
				"N ⊆ P",
				By(Normalized, monotone, iProduct, sProduct))
			transported := a.Have(
				"multiplication by invertible P preserves the dimension of S modulo I",
				"«finiteQuotient»(«wfMul»(S, P), «wfMul»(I, P)) ∧ "+
					"«colength»(«wfMul»(S, P), «wfMul»(I, P)) = «colength»(S, I)",
				By(
					subring,
					subfield,
					kInS,
					pInvertible,
					ring_ideal.CarrierIdeal.Read(ringS),
					idealI,
					iInS,
					finite,
					InvertibleQuotientDim.Read(L).At(k, S, P, S, I)))
			a.Show(
				"the two product identities identify that quotient with P modulo N",
				transported.Simp(Fwd(sProduct), Fwd(iProduct)),
				By(inclusion, transported))
		}),
})}
