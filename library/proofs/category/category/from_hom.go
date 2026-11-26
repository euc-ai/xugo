// from_hom.go — a category from its hom data. A category is as often
// given by a set of objects O and, for each pair of objects, a set
// H(x, y) of morphism data with an identity datum at each object and a
// composition of data, as by two carrier sets with source and target
// maps. `category_from_hom(O, H, e, c)` assembles the record of the
// second kind from data of the first: its morphisms are the data framed
// by their ends, `mk_morphism(x, y, f)` with f in H(x, y), and its
// source and target read the frame. One theorem says when the result
// is a category — the identity data are in their hom sets, the
// composition lands in its hom set, and the unit and associativity
// laws hold on the data — so every category the corpus assembles this
// way states its hom data and cites the theorem, and the bookkeeping
// of ends is proved once. The hom sets, the isomorphisms and the
// functors out of such a category are read off the frame the same way,
// once each.

package category

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// CategoryFromHomDef — `category_from_hom(O, H, e, c)`: the category on
// the objects O whose morphisms are the triples `mk_morphism(x, y, f)`
// with x and y in O and f in H(x, y), with source and target the frame,
// identity at x the framed datum e(x), and the composite of f: x → y
// and g: y → z the framed datum c(x, y, z, g, f), g after f.
var CategoryFromHomDef = categoryFromHomDefThm{family.Define(registry.DefEntry{
	Name:  "CategoryFromHomDef",
	Key:   "prop_bae9a3fb08f79a5c",
	Const: "category_from_hom",
	Type: "set(A) → " +
		"(A → A → set(D)) → " +
		"(A → D) → " +
		"(A → A → A → D → D → D) → " +
		"category_ops(A, morphism_triple(A, D))",
	Equations: []string{
		"∀O:set(A). ∀H:(A → A → set(D)). ∀e:(A → D). ∀c:(A → A → A → D → D → D). " +
			"    category_from_hom(O, H, e, c) = " +
			"    mk_category(O, " +
			"        {t:morphism_triple(A, D) | " +
			"            t.source ∈ O ∧ t.target ∈ O ∧ t.map ∈ H(t.source, t.target)}, " +
			"        λt:morphism_triple(A, D). t.source, " +
			"        λt:morphism_triple(A, D). t.target, " +
			"        λx:A. mk_morphism(x, x, e(x)), " +
			"        λg:morphism_triple(A, D). λf:morphism_triple(A, D). " +
			"            mk_morphism(f.source, g.target, c(f.source, f.target, g.target, g.map, f.map)))",
	},
	Deps: []registry.EntryLike{TripleSourceDef, TripleTargetDef, TripleMapDef},
	Reading: "The composite reads its middle object off the target of f; " +
		"on a composable pair that is the source of g, and off the composable " +
		"pairs the value is unconstrained, as a category's composition is.",
})}

// CategoryFromHom — the assembled record is a category when the hom
// data satisfy the laws on the data: the identity datum at an object
// is in its hom set, the composite of data in consecutive hom sets is
// in the hom set of the ends, the identity data are units, and
// composition of data associates. The ends of every morphism are then
// bookkept by the frame.
var CategoryFromHom = categoryFromHomThm{family.Add(registry.ProofEntry{
	Name: "CategoryFromHom",
	Key:  "prop_bfec6e8d10a0e551",
	Build: family.Theorem(Statement{
		Binders: "∀O:set(A). ∀H:(A → A → set(D)). ∀e:(A → D). ∀c:(A → A → A → D → D → D).",
		Hypotheses: []string{
			"∀x:A. x ∈ O ⇒ e(x) ∈ H(x, x)",
			"∀x y z:A. ∀f g:D. x ∈ O ∧ y ∈ O ∧ z ∈ O ∧ f ∈ H(x, y) ∧ g ∈ H(y, z) ⇒ c(x, y, z, g, f) ∈ H(x, z)",
			"∀x y:A. ∀f:D. x ∈ O ∧ y ∈ O ∧ f ∈ H(x, y) ⇒ c(x, y, y, e(y), f) = f",
			"∀x y:A. ∀f:D. x ∈ O ∧ y ∈ O ∧ f ∈ H(x, y) ⇒ c(x, x, y, f, e(x)) = f",
			"∀x y z w:A. ∀f g h:D. " +
				"    x ∈ O ∧ y ∈ O ∧ z ∈ O ∧ w ∈ O ∧ f ∈ H(x, y) ∧ g ∈ H(y, z) ∧ h ∈ H(z, w) ⇒ " +
				"    c(x, z, w, h, c(x, y, z, g, f)) = c(x, y, w, c(y, z, w, h, g), f)",
		},
		Conclusion: "category(category_from_hom(O, H, e, c))",
	},
		func(
			a *Argument,
			O *Expr[Set[A]],
			H *Arrow2[A, A, Set[D]],
			e *Arrow[A, D],
			c *Expr[Fun3[A, A, A, Op[D]]],
			homLaws Fact,
		) {
			laws := a.Conjuncts(
				homLaws,
				"identity data belong to their hom sets",
				"composition data belong to the hom set of the ends",
				"identity data are left units",
				"identity data are right units",
				"composition of data associates")
			identityIn, compositionIn, leftUnit, rightUnit, associate :=
				laws[0], laws[1], laws[2], laws[3], laws[4]
			a.Do(Unfold(CategoryFromHomDef), Unfold(Category), SplitConjAll(
				Case(
					"a morphism's frame consists of objects",
					SetTacMembership()),
				Case(
					"the identity datum is framed by its object",
					BySets(identityIn, TripleSourceDef, TripleTargetDef, TripleMapDef)),
				Case(
					"composable morphisms have a common middle object",
					Derive(func(b *Argument) {
						b.FixAs[MorphismTriple[A, D]]("f")
						b.FixAs[MorphismTriple[A, D]]("g")
						composable := b.Assume()
						b.Show(
							"the composite datum lies in the hom set of the two outer ends",
							BySets(
								composable,
								compositionIn.At(
									b.TermAs[A]("f.source"),
									b.TermAs[A]("f.target"),
									b.TermAs[A]("g.target"),
									b.TermAs[D]("f.map"),
									b.TermAs[D]("g.map")),
								TripleSourceDef,
								TripleTargetDef,
								TripleMapDef))
					})),
				Case(
					"the identity at the target is a left unit",
					Derive(func(b *Argument) {
						b.FixAs[MorphismTriple[A, D]]("f")
						morphism := b.Assume()
						b.Show(
							"the frame is unchanged and the datum satisfies the left unit law",
							Simp(Fwd(MorphismTripleData.Ext), Fwd(TripleSourceDef), Fwd(TripleTargetDef), Fwd(TripleMapDef)),
							BySets(
								morphism,
								leftUnit.At(b.TermAs[A]("f.source"), b.TermAs[A]("f.target"), b.TermAs[D]("f.map"))))
					})),
				Case(
					"the identity at the source is a right unit",
					Derive(func(b *Argument) {
						b.FixAs[MorphismTriple[A, D]]("f")
						morphism := b.Assume()
						b.Show(
							"the frame is unchanged and the datum satisfies the right unit law",
							Simp(Fwd(MorphismTripleData.Ext), Fwd(TripleSourceDef), Fwd(TripleTargetDef), Fwd(TripleMapDef)),
							BySets(
								morphism,
								rightUnit.At(b.TermAs[A]("f.source"), b.TermAs[A]("f.target"), b.TermAs[D]("f.map"))))
					})),
				Case(
					"three composable morphisms inherit associativity from their data",
					Derive(func(b *Argument) {
						b.FixAs[MorphismTriple[A, D]]("f")
						b.FixAs[MorphismTriple[A, D]]("g")
						b.FixAs[MorphismTriple[A, D]]("h")
						composable := b.Assume()
						b.Show(
							"the frames agree and the common middle objects identify the datum composites",
							Congr(),
							BySets(
								composable,
								associate.At(
									b.TermAs[A]("f.source"),
									b.TermAs[A]("f.target"),
									b.TermAs[A]("g.target"),
									b.TermAs[A]("h.target"),
									b.TermAs[D]("f.map"),
									b.TermAs[D]("g.map"),
									b.TermAs[D]("h.map"))))
					})),
			))
		}),
	Reading: "The five hypotheses are stated on the data only; nothing is asked of e or c off " +
		"O or off the hom sets, as nothing is asked of a category's operations off its carriers.",
})}

// CategoryFromHomHomIff — a framed datum lies in the hom set between its
// ends precisely when the ends are objects and the datum belongs to their
// hom set: the hom set holds the morphisms with those ends, and the frame
// reads back the ends and the datum.
var CategoryFromHomHomIff = categoryFromHomHomIffThm{family.Add(registry.ProofEntry{
	Name: "CategoryFromHomHomIff",
	Key:  "prop_2fa3e90565dc5efb",
	Build: family.Theorem("∀O:set(A). "+
		"∀H:(A → A → set(D)). "+
		"∀e:(A → D). "+
		"∀c:(A → A → A → D → D → D). "+
		"∀x y:A. "+
		"∀f:D. "+
		"    mk_morphism(x, y, f) ∈ category_hom(category_from_hom(O, H, e, c), x, y) ⇔ "+
		"    x ∈ O ∧ y ∈ O ∧ f ∈ H(x, y)",
		func(
			a *Argument,
			O *Expr[Set[A]],
			H *Arrow2[A, A, Set[D]],
			e *Arrow[A, D],
			c *Expr[Fun3[A, A, A, Op[D]]],
			x, y *Expr[A],
			f *Expr[D],
		) {
			a.Show(
				"the frame reads back the ends and the datum of a framed morphism",
				Unfold(CategoryHomDef),
				BySets(TripleSourceDef, TripleTargetDef, TripleMapDef))
		}),
})}

// CategoryFromHomIsomorphismIff — a framed datum is an isomorphism
// precisely when its ends are objects, its datum belongs to their hom
// set, and it has a two-sided inverse datum in the reversed hom set.
// Reading an inverse triple's components
// gives the inverse datum; framing such a datum gives the inverse triple.
var CategoryFromHomIsomorphismIff = categoryFromHomIsomorphismIffThm{family.Add(registry.ProofEntry{
	Name: "CategoryFromHomIsomorphismIff",
	Key:  "prop_2d7f0699ef53bb91",
	Build: family.Theorem("∀O:set(A). "+
		"∀H:(A → A → set(D)). "+
		"∀e:(A → D). "+
		"∀c:(A → A → A → D → D → D). "+
		"∀x y:A. "+
		"∀f:D. "+
		"    category_isomorphism(category_from_hom(O, H, e, c), mk_morphism(x, y, f)) ⇔ "+
		"    x ∈ O ∧ "+
		"    y ∈ O ∧ "+
		"    f ∈ H(x, y) ∧ "+
		"    (∃g:D. g ∈ H(y, x) ∧ c(x, y, x, g, f) = e(x) ∧ c(y, x, y, f, g) = e(y))",
		func(
			a *Argument,
			O *Expr[Set[A]],
			H *Arrow2[A, A, Set[D]],
			e *Arrow[A, D],
			c *Expr[Fun3[A, A, A, Op[D]]],
			x, y *Expr[A],
			f *Expr[D],
		) {
			a.Iff()
			a.Forward(
				"an inverse triple supplies an inverse datum",
				func(b *Argument, isomorphism Fact) {
					parts := b.Conjuncts(
						b.Unfolded(isomorphism, CategoryIsomorphismDef),
						"the framed datum is a morphism",
						"the framed datum has an inverse triple")
					_, inverse := b.UnpackAs[MorphismTriple[A, D]](parts[1], "t")
					inverseData := b.Simplified(
						inverse,
						Fwd(MorphismTripleData.Ext),
						Fwd(TripleSourceDef),
						Fwd(TripleTargetDef),
						Fwd(TripleMapDef))
					b.Do(SplitConj(
						Case(
							"the frame and datum have their required memberships",
							BySets(parts[0], TripleSourceDef, TripleTargetDef, TripleMapDef)),
						Case(
							"the inverse triple's map is an inverse datum",
							Derive(func(d *Argument) {
								d.Take(d.TermAs[D]("t.map"))
								d.Show(
									"the reversed ends and the two composite data satisfy the inverse equations",
									BySets(inverseData))
							})),
					))
				})
			a.Backward(
				"an inverse datum supplies an inverse triple",
				func(b *Argument, data Fact) {
					parts := b.Conjuncts(
						data,
						"the source is an object",
						"the target is an object",
						"the datum belongs to its hom set",
						"an inverse datum exists")
					_, inverse := b.UnpackAs[D](parts[3], "g")
					inverseLaws := b.Conjuncts(
						inverse,
						"the inverse datum belongs to the reversed hom set",
						"the inverse after the datum gives the source identity",
						"the datum after the inverse gives the target identity")
					b.Do(Unfold(CategoryIsomorphismDef), SplitConj(
						Case(
							"the framed datum is a morphism",
							BySets(parts[0], parts[1], parts[2], TripleSourceDef, TripleTargetDef, TripleMapDef)),
						Case(
							"frame the inverse datum with the reversed ends",
							Derive(func(d *Argument) {
								d.Take(d.TermAs[MorphismTriple[A, D]]("mk_morphism(y, x, g)"))
								d.Show(
									"the reversed frame preserves both inverse equations",
									Simp(Fwd(MorphismTripleData.Ext), Fwd(TripleSourceDef), Fwd(TripleTargetDef), Fwd(TripleMapDef)),
									BySets(
										inverseLaws[1],
										inverseLaws[2],
										parts[0],
										parts[1],
										inverseLaws[0],
										TripleSourceDef,
										TripleTargetDef,
										TripleMapDef))
							})),
					))
				})
		}),
})}

// FunctorFromHomIff — a functor from a category assembled from hom data
// is exactly an object map and maps of the hom data preserving identities
// and composition. Frame data to read the functor laws; read the frame of
// an arbitrary source morphism to recover those laws from the data.
var FunctorFromHomIff = functorFromHomIffThm{family.Add(registry.ProofEntry{
	Name: "FunctorFromHomIff",
	Key:  "prop_c4c8f212915a3156",
	Build: family.Theorem(Statement{
		Binders: "∀O:set(A). " +
			"∀H:(A → A → set(D)). " +
			"∀e:(A → D). " +
			"∀c:(A → A → A → D → D → D). " +
			"∀C:category_ops(B, N). " +
			"∀F:(A → B). " +
			"∀p:(A → A → D → N).",
		Hypotheses: []string{
			"category(category_from_hom(O, H, e, c))",
			"category(C)",
		},
		Conclusion: "functor(category_from_hom(O, H, e, c), " +
			"    C, " +
			"    mk_functor(F, λt:morphism_triple(A, D). p(t.source, t.target, t.map))) ⇔ " +
			"(∀x:A. x ∈ O ⇒ F(x) ∈ C.objects) ∧ " +
			"(∀x y:A. ∀f:D. x ∈ O ∧ y ∈ O ∧ f ∈ H(x, y) ⇒ p(x, y, f) ∈ category_hom(C, F(x), F(y))) ∧ " +
			"(∀x:A. x ∈ O ⇒ p(x, x, e(x)) = C.identity(F(x))) ∧ " +
			"(∀x y z:A. ∀f g:D. " +
			"    x ∈ O ∧ y ∈ O ∧ z ∈ O ∧ f ∈ H(x, y) ∧ g ∈ H(y, z) ⇒ " +
			"    p(x, z, c(x, y, z, g, f)) = C.compose(p(y, z, g), p(x, y, f)))",
	},
		func(
			a *Argument,
			O *Expr[Set[A]],
			H *Arrow2[A, A, Set[D]],
			e *Arrow[A, D],
			c *Expr[Fun3[A, A, A, Op[D]]],
			C *Expr[CategoryOps[B, N]],
			F *Arrow[A, B],
			p *Expr[Fun3[A, A, D, N]],
			categories Fact,
		) {
			a.Iff()
			a.Forward(
				"the functor laws read on framed hom data",
				func(b *Argument, functor Fact) {
					b.Do(SplitConjAll(
						Case(
							"objects are carried to objects",
							By(FunctorObjectImage.Read(functor))),
						Case(
							"a framed hom datum has an image with the required ends",
							Derive(func(d *Argument) {
								arrows := d.Have(
									"the functor carries source morphisms with their ends",
									Statement{
										Binders: "∀t:morphism_triple(A, D).",
										Hypotheses: []string{
											"t ∈ {s:morphism_triple(A, D) | s.source ∈ O ∧ s.target ∈ O ∧ s.map ∈ H(s.source, s.target)}",
										},
										Conclusion: "p(t.source, t.target, t.map) ∈ C.morphisms ∧ " +
											"C.source(p(t.source, t.target, t.map)) = F(t.source) ∧ " +
											"C.target(p(t.source, t.target, t.map)) = F(t.target)",
									},
									By(FunctorMapEnds.Read(functor)))
								d.FixAs[A]("x")
								d.FixAs[A]("y")
								d.FixAs[D]("f")
								data := d.Assume()
								framed := d.Have(
									"the datum framed by its ends is a source morphism",
									"mk_morphism(x, y, f) ∈ "+
										"{s:morphism_triple(A, D) | s.source ∈ O ∧ s.target ∈ O ∧ s.map ∈ H(s.source, s.target)}",
									BySets(data))
								d.Show(
									"the image lies in the target hom set",
									Simp(Fwd(CategoryHomDef)),
									BySets(framed, arrows.At(d.TermAs[MorphismTriple[A, D]]("mk_morphism(x, y, f)"))))
							})),
						Case(
							"identity data are carried to identities",
							By(FunctorPreservesIdentity.Read(functor))),
						Case(
							"consecutive hom data are carried to their composite",
							Derive(func(d *Argument) {
								composites := d.Have(
									"the functor preserves composition of source morphisms",
									Statement{
										Binders: "∀t u:morphism_triple(A, D).",
										Hypotheses: []string{
											"t ∈ {s:morphism_triple(A, D) | s.source ∈ O ∧ s.target ∈ O ∧ s.map ∈ H(s.source, s.target)}",
											"u ∈ {s:morphism_triple(A, D) | s.source ∈ O ∧ s.target ∈ O ∧ s.map ∈ H(s.source, s.target)}",
											"t.target = u.source",
										},
										Conclusion: "p(t.source, u.target, c(t.source, t.target, u.target, u.map, t.map)) = " +
											"C.compose(p(u.source, u.target, u.map), p(t.source, t.target, t.map))",
									},
									By(FunctorPreservesComposite.Read(functor)))
								d.FixAs[A]("x")
								d.FixAs[A]("y")
								d.FixAs[A]("z")
								d.FixAs[D]("f")
								d.FixAs[D]("g")
								data := d.Assume()
								framed := d.Have(
									"the framed data are composable source morphisms",
									"mk_morphism(x, y, f) ∈ "+
										"{s:morphism_triple(A, D) | s.source ∈ O ∧ s.target ∈ O ∧ s.map ∈ H(s.source, s.target)} ∧ "+
										"mk_morphism(y, z, g) ∈ "+
										"{s:morphism_triple(A, D) | s.source ∈ O ∧ s.target ∈ O ∧ s.map ∈ H(s.source, s.target)} ∧ "+
										"mk_morphism(x, y, f).target = mk_morphism(y, z, g).source",
									BySets(data))
								d.Show(
									"composition of the framed morphisms reads composition of their data",
									By(
										framed,
										composites.At(
											d.TermAs[MorphismTriple[A, D]]("mk_morphism(x, y, f)"),
											d.TermAs[MorphismTriple[A, D]]("mk_morphism(y, z, g)"))))
							})),
					))
				})
			a.Backward(
				"the hom data laws give the functor laws on arbitrary morphisms",
				func(b *Argument, data Fact) {
					laws := b.Conjuncts(
						data,
						"objects are carried to objects",
						"hom data are carried to the target hom sets",
						"identity data are preserved",
						"composition data are preserved")
					cats := b.Conjuncts(
						categories,
						"the hom category is a category",
						"the target is a category")
					b.Do(Unfold(FunctorDef))
					homImages := b.Unfolded(laws[1], CategoryHomDef)
					b.Do(SplitConjAll(
						Case(
							"the hom category is a category",
							By(cats[0])),
						Case(
							"the target is a category",
							By(cats[1])),
						Case(
							"objects are carried to objects",
							By(laws[0])),
						Case(
							"an arbitrary morphism supplies its source, target and datum",
							Derive(func(d *Argument) {
								d.FixAs[MorphismTriple[A, D]]("f")
								morphism := d.Assume()
								d.Show(
									"the hom set of the image specifies its membership and ends",
									BySets(
										morphism,
										homImages.At(d.TermAs[A]("f.source"), d.TermAs[A]("f.target"), d.TermAs[D]("f.map"))))
							})),
						Case(
							"identity data are preserved",
							By(laws[2])),
						Case(
							"composable morphisms supply data with a shared middle object",
							Derive(func(d *Argument) {
								d.FixAs[MorphismTriple[A, D]]("f")
								d.FixAs[MorphismTriple[A, D]]("g")
								composable := d.Assume()
								d.Show(
									"the composition law on data applies at the three frame objects",
									BySets(
										composable,
										laws[3].At(
											d.TermAs[A]("f.source"),
											d.TermAs[A]("f.target"),
											d.TermAs[A]("g.target"),
											d.TermAs[D]("f.map"),
											d.TermAs[D]("g.map"))))
							})),
					))
				})
		}),
})}
