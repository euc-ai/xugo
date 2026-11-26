// trace.go — the chapter's trace statements.

package field_trace

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_pairing"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// FieldTraceFromBasis — a finite basis E of L over K computes the field
// trace: multiplication by z is linear over K, so the module trace is
// its diagonal coordinate sum in E. The finite basis is itself the
// finite extension.
var FieldTraceFromBasis = fieldTraceFromBasisThm{family.Add(registry.ProofEntry{
	Name: "FieldTraceFromBasis",
	Key:  "prop_59312733b31430e6",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K E:set(A). ∀z:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite(E)",
			"module_basis(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), E)",
			"z ∈ L.carrier",
		},
		Conclusion: "field_trace(L, K, z) = " +
			"module_basis_trace(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), E, L.mul(z))",
	},
		func(p *Argument, L field.FieldFact[on.L], K, E *Expr[Set[A]], z *Expr[A], hypotheses Fact) {
			given := p.Conjuncts(
				hypotheses,
				"K is a subfield of L",
				"E is finite",
				"E is a K-basis of L",
				"z lies in L")
			subK, finiteE, basisE, zInL := given[0], given[1], given[2], p.MemberOf[on.L](z, given[3])
			moduleK := p.Have(
				"the regular module of L restricts to the scalars K",
				"module_on(restrict_ring(field_ring(L), K), regular_module(field_ring(L)))",
				By(subK, field_extension.SubfieldScalars.Read(L).At(K)))
			multiplication := p.Have(
				"multiplication by z is an endomorphism over K",
				"module_homomorphism(restrict_ring(field_ring(L), K), "+
					"    regular_module(field_ring(L)), "+
					"    regular_module(field_ring(L)), "+
					"    L.mul(z))",
				By(subK, zInL, field_extension.MultiplicationLinear.Read(L).At(K, zInL)))
			p.Show(
				"the finite basis E computes the module trace defining the field trace",
				Simp(Fwd(FieldTraceDef)),
				By(
					finiteE,
					basisE,
					multiplication,
					module_dimension.TraceFromBasis.Read(moduleK).At(E,
						p.TermAs[Fun[A, A]]("L.mul(z)"))))
		}),
})}

// FieldTraceLinear — the field trace of a finite extension is a K-linear
// functional on L: multiplication maps are endomorphisms, their traces
// lie in K, and their pointwise addition and scaling give the two trace
// identities.
var FieldTraceLinear = fieldTraceLinearThm{family.Add(registry.ProofEntry{
	Name: "FieldTraceLinear",
	Key:  "prop_3b6ea67220240ccb",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite_extension(L, K, L.carrier)",
		},
		Conclusion: "module_homomorphism(restrict_ring(field_ring(L), K), " +
			"    regular_module(field_ring(L)), " +
			"    restrict_module(regular_module(field_ring(L)), K), " +
			"    λz:A. field_trace(L, K, z))",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			traceLaws := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀K:set(A).",
				Hypotheses: []string{
					"module_on(restrict_ring(field_ring(L), K), regular_module(field_ring(L)))",
					"K ⊆ L.carrier", "subfield(L, K)",
					"finite_extension(L, K, L.carrier)",
				},
				Conclusion: "(∀z:A. z ∈ L.carrier ⇒ field_trace(L, K, z) ∈ K) ∧ " +
					"(∀z w:A. " +
					"    z ∈ L.carrier ∧ w ∈ L.carrier ⇒ " +
					"    field_trace(L, K, z + w) = field_trace(L, K, z) + field_trace(L, K, w)) ∧ " +
					"(∀a z:A. a ∈ K ∧ z ∈ L.carrier ⇒ field_trace(L, K, a * z) = a * field_trace(L, K, z))",
			}, func(p *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], hypotheses Fact) {
				given := p.Conjuncts(
					hypotheses,
					"L is a module over K",
					"K lies in L",
					"K is a subfield",
					"L is a finite extension of K")
				moduleK, within, subK, finite := given[0], given[1], given[2], given[3]
				scalars := p.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), K)")
				ambient := p.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
				carrier := p.Have(
					"the vectors of the field's ring, as a module over itself, are L.carrier",
					"regular_module(field_ring(L)).carrier = L.carrier",
					Simp(Fwd(module_record.RegularModuleDef), Fwd(field.FieldRingDef)),
					Basic())
				// The finite extension is the module L restricted to L.carrier, its
				// own carrier, which is the module L: L is finite-dimensional over K.
				finiteDimensional := p.Simplified(
					finite,
					Fwd(field_extension.FiniteExtensionDef),
					Rev(carrier),
					Fwd(module_record.RestrictModuleCarrier))
				E, basis := p.ObtainAs[Set[A]](
					"choose a finite basis of L over K",
					"∃E:set(A). "+
						"    finite(E) ∧ module_basis(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), E)",
					By(finiteDimensional, module_dimension.FiniteDimensionalDef.At(scalars, ambient)))
				basisParts := p.Conjuncts(
					basis,
					"E is finite",
					"E is a K-basis of L")
				finiteE, basisE := basisParts[0], basisParts[1]
				endomorphisms := p.Have(
					"multiplication by a field element is an endomorphism over K",
					Statement{
						Binders: "∀z:A.",
						Hypotheses: []string{
							"z ∈ L.carrier",
						},
						Conclusion: "module_homomorphism(restrict_ring(field_ring(L), K), " +
							"    regular_module(field_ring(L)), " +
							"    regular_module(field_ring(L)), " +
							"    L.mul(z))",
					},
					p.ForEach(func(z *Expr[A]) Action {
						return By(subK, field_extension.MultiplicationLinear.Read(L).AsFact().At(K, z))
					}))
				p.Show(
					"compute the range and the two linearity identities",
					SplitConjAll(
						Case(
							"the field trace takes its values in K",
							Derive(func(b *Argument) {
								z := b.FixAs[A]("z")
								zInL := b.MemberOf[on.L](z, b.Assume())
								computed := b.Have(
									"E computes the field trace as the basis trace of multiplication",
									"field_trace(L, K, z) = "+
										"module_basis_trace(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), E, L.mul(z))",
									By(subK, finiteE, basisE, FieldTraceFromBasis.Read(L).At(K, E, zInL)))
								b.Show(
									"a basis trace belongs to the scalar carrier K",
									computed.Rw(),
									By(
										finiteE,
										basisE,
										zInL,
										endomorphisms.At(z),
										module_dimension.BasisTraceInCarrier.Read(moduleK).At(E,
											b.TermAs[Fun[A, A]]("L.mul(z)"))))
							})),
						Case(
							"the field trace preserves addition",
							Derive(func(b *Argument) {
								z, w := b.FixAs[A]("z"), b.FixAs[A]("w")
								members := b.Assume()
								distributes := b.Have(
									"on L multiplication by z + w is the sum of the multiplications by z and by w",
									"∀v:A. v ∈ regular_module(field_ring(L)).carrier ⇒ (z + w) * v = z * v + w * v",
									carrier.Rw(),
									Derive(func(c *Argument) {
										c.FixAs[A]("v")
										c.Show(
											"the field product distributes over the sum",
											ByArith(L, members, c.Assume()))
									}))
								b.Show(
									"the trace of a sum of multiplications is the sum of their traces",
									Simp(Fwd(FieldTraceDef)),
									CalcEq(
										Leg(
											b.TermAs[A](
												"module_trace(restrict_ring(field_ring(L), K), "+
													"    regular_module(field_ring(L)), "+
													"    λv:A. z * v + w * v)"),
											"multiplication by z + w agrees on L with the sum of the two multiplications",
											By(
												distributes,
												Where(module_dimension.TraceCongruence, "f", b.TermAs[Fun[A, A]]("L.mul(z + w)")).Where(
													"g", b.TermAs[Fun[A, A]]("λv:A. z * v + w * v")))),
										FinalLeg(
											"the trace of a sum of endomorphisms is the sum of their traces",
											By(
												finiteDimensional,
												members,
												endomorphisms.At(z),
												endomorphisms.At(w),
												module_dimension.TraceAdd.Read(moduleK).At(
													b.TermAs[Fun[A, A]]("L.mul(z)"), b.TermAs[Fun[A, A]]("L.mul(w)")))),
									))
							})),
						Case(
							"the field trace preserves scaling by K",
							Derive(func(b *Argument) {
								a, z := b.FixAs[A]("a"), b.FixAs[A]("z")
								members := b.Assume()
								eachInL := b.Unfolded(within, set_basic.SubsetDef)
								aInL := b.MemberOf[on.L](a, b.Have(
									"a scalar of K is an element of L",
									"a ∈ L.carrier",
									By(members, eachInL.At(a))))
								scalarParts := b.Conjuncts(
									members,
									"a is a scalar of K",
									"z lies in L")
								scalar := proof.MemberOf(a, scalarParts[0])
								associates := b.Have(
									"on L multiplication by a * z is a times multiplication by z",
									"∀v:A. v ∈ regular_module(field_ring(L)).carrier ⇒ a * z * v = a * (z * v)",
									carrier.Rw(),
									Derive(func(c *Argument) {
										c.FixAs[A]("v")
										c.Show(
											"the field product associates",
											ByArith(L, aInL, members, c.Assume()))
									}))
								b.Show(
									"the trace of a multiple of a multiplication is the multiple of its trace",
									Simp(Fwd(FieldTraceDef)),
									CalcEq(
										Leg(
											b.TermAs[A](
												"module_trace(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), λv:A. a * (z * v))"),
											"multiplication by a * z agrees on L with a times multiplication by z",
											By(
												associates,
												Where(module_dimension.TraceCongruence, "f", b.TermAs[Fun[A, A]]("L.mul(a * z)")).Where(
													"g", b.TermAs[Fun[A, A]]("λv:A. a * (z * v)")))),
										FinalLeg(
											"the trace of a scalar multiple of an endomorphism is the multiple of its trace",
											By(
												finiteDimensional,
												members,
												endomorphisms.At(z),
												module_dimension.TraceScale.Read(moduleK).At(scalar, b.TermAs[Fun[A, A]]("L.mul(z)")))),
									))
							})),
					))
			})

			return ctx.Theorem(headline, func(
				p *Argument,
				L field.FieldFact[on.L],
				K *Expr[Set[A]],
				hypotheses Fact,
			) {
				given := p.Conjuncts(
					hypotheses,
					"K is a subfield of L",
					"L is a finite extension of K")
				subK, finite := given[0], given[1]
				supplied := p.Conjuncts(
					p.Have(
						"the subfield K supplies scalars acting on L",
						"subring(field_ring(L), K) ∧ "+
							"module_on(restrict_ring(field_ring(L), K), regular_module(field_ring(L)))",
						By(subK, field_extension.SubfieldScalars.Read(L).At(K))),
					"K is a subring of L",
					"L is a module over the restricted scalar ring K")
				subringK, moduleK := supplied[0], supplied[1]
				ringK := p.Have(
					"the scalar ring on K is commutative",
					"comm_ring_on(restrict_ring(field_ring(L), K))",
					By(subringK, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(K)))
				within := p.Have(
					"K lies in L",
					"K ⊆ L.carrier",
					By(comm_ring.SubringSubset.Read(subringK)))
				codomain := p.Have(
					"K is a module over its own scalar ring, the codomain being the regular module of the ring on K",
					"module_on(restrict_ring(field_ring(L), K), restrict_module(regular_module(field_ring(L)), K))",
					Simp(Rev(module_record.RegularModuleRestrict)),
					By(module.RegularModuleOn.Read(ringK)))
				laws := p.Conjuncts(
					p.Have(
						"the field trace has its scalar-valued linearity laws",
						"(∀z:A. z ∈ L.carrier ⇒ field_trace(L, K, z) ∈ K) ∧ "+
							"(∀z w:A. "+
							"    z ∈ L.carrier ∧ w ∈ L.carrier ⇒ "+
							"    field_trace(L, K, z + w) = field_trace(L, K, z) + field_trace(L, K, w)) ∧ "+
							"(∀a z:A. a ∈ K ∧ z ∈ L.carrier ⇒ field_trace(L, K, a * z) = a * field_trace(L, K, z))",
						By(moduleK, within, subK, finite, Read(traceLaws, L).At(K))),
					"the trace takes its values in K",
					"the trace preserves addition",
					"the trace preserves scaling by K")
				scalars := p.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), K)")
				ambient := p.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
				baseSpace := p.TermAs[module_record.ModuleOps[A, A]](
					"restrict_module(regular_module(field_ring(L)), K)")
				p.Show(
					"the three laws make the trace a homomorphism from L to K",
					By(
						moduleK,
						codomain,
						laws[0],
						laws[1],
						laws[2],
						module_homomorphism.ModuleHomomorphismDef.At(
							scalars, ambient, baseSpace, p.TermAs[Fun[A, A]]("λz:A. field_trace(L, K, z)"))))
			})
		}),
})}

// TracePairingBilinear — the trace pairing (x, y) ↦ Tr(x * y) of a
// finite extension is a symmetric K-bilinear pairing on L. Pairing with x
// is the trace after multiplication by x, both K-linear, so the pairing is
// K-linear in its second argument; the product commutes, so the pairing
// is symmetric, and K-linear in its first argument as well.
var TracePairingBilinear = tracePairingBilinearThm{family.Add(registry.ProofEntry{
	Name: "TracePairingBilinear",
	Key:  "prop_4e56e819f777ec91",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite_extension(L, K, L.carrier)",
		},
		Conclusion: "bilinear_pairing(restrict_ring(field_ring(L), K), " +
			"    regular_module(field_ring(L)), " +
			"    λx:A. λy:A. field_trace(L, K, x * y)) ∧ " +
			"(∀x y:A. x ∈ L.carrier ∧ y ∈ L.carrier ⇒ field_trace(L, K, x * y) = field_trace(L, K, y * x))",
	},
		func(a *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], hypotheses Fact) {
			given := a.Conjuncts(
				hypotheses,
				"K is a subfield of L",
				"L is a finite extension of K")
			subK, finite := given[0], given[1]
			scalars := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), K)")
			ambient := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			base := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(restrict_ring(field_ring(L), K))")
			trace := a.TermAs[Fun[A, A]]("λz:A. field_trace(L, K, z)")
			traceLinear := a.Have(
				"the trace is a K-linear functional, the regular module of the ring on K being L's restricted to K",
				"module_homomorphism(restrict_ring(field_ring(L), K), "+
					"    regular_module(field_ring(L)), "+
					"    regular_module(restrict_ring(field_ring(L), K)), "+
					"    λz:A. field_trace(L, K, z))",
				Simp(Fwd(module_record.RegularModuleRestrict)),
				By(subK, finite, FieldTraceLinear.Read(L).At(K)))
			carrier := a.Have(
				"the vectors of the field's ring, as a module over itself, are L.carrier",
				"regular_module(field_ring(L)).carrier = L.carrier",
				Simp(Fwd(module_record.RegularModuleDef), Fwd(field.FieldRingDef)),
				Basic())
			columns := a.Have(
				"the trace pairing is K-linear in its second argument",
				Statement{
					Binders: "∀x:A.",
					Hypotheses: []string{
						"x ∈ L.carrier",
					},
					Conclusion: "module_homomorphism(restrict_ring(field_ring(L), K), " +
						"    regular_module(field_ring(L)), " +
						"    regular_module(restrict_ring(field_ring(L), K)), " +
						"    λy:A. field_trace(L, K, x * y))",
				},
				Derive(func(q *Argument) {
					x := q.FixAs[A]("x")
					xIn := q.MemberOf[on.L](x, q.Assume())
					multiplication := q.TermAs[Fun[A, A]]("L.mul(x)")
					linear := q.Have(
						"multiplication by x is K-linear",
						"module_homomorphism(restrict_ring(field_ring(L), K), "+
							"    regular_module(field_ring(L)), "+
							"    regular_module(field_ring(L)), "+
							"    L.mul(x))",
						By(subK, xIn, field_extension.MultiplicationLinear.Read(L).At(K, xIn)))
					composite := q.Have(
						"and so is the trace after it",
						"module_homomorphism(restrict_ring(field_ring(L), K), "+
							"    regular_module(field_ring(L)), "+
							"    regular_module(restrict_ring(field_ring(L), K)), "+
							"    (λz:A. field_trace(L, K, z)) ∘ L.mul(x))",
						By(
							linear,
							traceLinear,
							module_homomorphism.HomCompose.At(scalars, ambient, ambient, base, multiplication, trace)))
					q.Show(
						"the trace after multiplication by x is pairing with x",
						By(q.Simplified(composite, Fwd(functions.ComposeApply))))
				}))
			symmetry := a.Have(
				"the trace pairing is symmetric",
				"∀x y:A. x ∈ L.carrier ∧ y ∈ L.carrier ⇒ field_trace(L, K, x * y) = field_trace(L, K, y * x)",
				Derive(func(q *Argument) {
					q.FixAs[A]("x")
					q.FixAs[A]("y")
					both := q.Assume()
					commute := q.Have(
						"the field's product commutes",
						"x * y = y * x",
						ByArith(Normalized, L, both))
					q.Show(
						"so the trace reads equal products",
						commute.Rw(),
						Basic())
				}))
			rows := a.Have(
				"so it is K-linear in its first argument as well",
				Statement{
					Binders: "∀y:A.",
					Hypotheses: []string{
						"y ∈ L.carrier",
					},
					Conclusion: "module_homomorphism(restrict_ring(field_ring(L), K), " +
						"    regular_module(field_ring(L)), " +
						"    regular_module(restrict_ring(field_ring(L), K)), " +
						"    λx:A. field_trace(L, K, x * y))",
				},
				Derive(func(q *Argument) {
					y := q.FixAs[A]("y")
					yIn := q.Assume()
					agree := q.Have(
						"symmetry exchanges the two readings",
						Statement{
							Binders: "∀x:A.",
							Hypotheses: []string{
								"x ∈ regular_module(field_ring(L)).carrier",
							},
							Conclusion: "field_trace(L, K, x * y) = field_trace(L, K, y * x)",
						},
						carrier.Rw(),
						By(yIn, symmetry))
					q.Show(
						"agreeing with pairing with y, the row is K-linear",
						By(
							yIn,
							columns.At(y),
							agree,
							module_homomorphism.HomCongruence.At(
								scalars,
								ambient,
								base,
								q.TermAs[Fun[A, A]]("λx:A. field_trace(L, K, y * x)"),
								q.TermAs[Fun[A, A]]("λx:A. field_trace(L, K, x * y)"))))
				}))
			bilinear := a.Have(
				"so the trace pairing is K-bilinear",
				"bilinear_pairing(restrict_ring(field_ring(L), K), "+
					"    regular_module(field_ring(L)), "+
					"    λx:A. λy:A. field_trace(L, K, x * y))",
				Unfold(linear_pairing.BilinearPairingDef),
				By(columns, rows))
			a.Show(
				"the trace pairing is K-bilinear and symmetric",
				By(bilinear, symmetry))
		}),
})}

// FieldTraceOfScalar — a base scalar has trace equal to the extension
// degree times that scalar: the trace of one counts a finite basis,
// and K-linearity gives the trace of any scalar multiple of one.
var FieldTraceOfScalar = fieldTraceOfScalarThm{family.Add(registry.ProofEntry{
	Name: "FieldTraceOfScalar",
	Key:  "prop_c0fe9fce1263acb7",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A). ∀a:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite_extension(L, K, L.carrier)",
			"a ∈ K",
		},
		Conclusion: "field_trace(L, K, a) = " +
			"L.mul(monoid_pow(L.add, " +
			"        L.zero, " +
			"        L.one, " +
			"        module_dim(restrict_ring(field_ring(L), K), regular_module(field_ring(L)))), " +
			"    a)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			traceOne := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀K E:set(A).",
				Hypotheses: []string{
					"module_on(restrict_ring(field_ring(L), K), regular_module(field_ring(L)))",
					"subfield(L, K)",
					"finite(E)",
					"module_basis(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), E)",
				},
				Conclusion: "field_trace(L, K, L.one) = monoid_pow(L.add, L.zero, L.one, card(E))",
			}, func(p *Argument, L field.FieldFact[on.L], K, E *Expr[Set[A]], hypotheses Fact) {
				given := p.Conjuncts(
					hypotheses,
					"L is a module over K",
					"K is a subfield",
					"E is finite",
					"E is a K-basis of L")
				moduleK, subK, finiteE, basisE := given[0], given[1], given[2], given[3]
				one := p.TermAs[A]("L.one")
				oneInL := p.MemberOf[on.L](one, comm_ring.OneIn.Read(field.RingOn.Read(L)))
				computed := p.Have(
					"E computes the trace of multiplication by one",
					"field_trace(L, K, L.one) = "+
						"module_basis_trace(restrict_ring(field_ring(L), K), "+
						"    regular_module(field_ring(L)), "+
						"    E, "+
						"    L.mul(L.one))",
					By(subK, finiteE, basisE, FieldTraceFromBasis.Read(L).At(K, E, oneInL)))
				within := p.Have(
					"the basis E lies in L",
					"E ⊆ L.carrier",
					By(linear_independence.BasisInCarrier.Read(basisE)))
				eachInL := p.Unfolded(within, set_basic.SubsetDef)
				diagonal := p.Have(
					"every diagonal coordinate of multiplication by one is one",
					Statement{
						Binders: "∀e:A.",
						Hypotheses: []string{
							"e ∈ E",
						},
						Conclusion: "module_basis_coordinates(restrict_ring(field_ring(L), K), " +
							"    regular_module(field_ring(L)), " +
							"    E, " +
							"    L.one * e, " +
							"    e) = " +
							"L.one",
					},
					Derive(func(b *Argument) {
						e := b.FixAs[A]("e")
						eInE := b.Assume()
						eInL := b.MemberOf[on.L](e, b.Have(
							"a basis vector lies in L",
							"e ∈ L.carrier",
							By(eInE, eachInL.At(e))))
						fixed := b.Have(
							"multiplication by one fixes the basis vector",
							"L.one * e = e",
							ByArith(L, eInL))
						coordinates := b.Have(
							"a basis vector has its Kronecker coordinate function",
							"module_basis_coordinates(restrict_ring(field_ring(L), K), "+
								"    regular_module(field_ring(L)), "+
								"    E, "+
								"    e) = "+
								"λx:A. COND(x = e, restrict_ring(field_ring(L), K).one, restrict_ring(field_ring(L), K).zero)",
							By(finiteE, basisE, eInE, module_dimension.BasisCoordinateDelta.Read(moduleK).At(E, e)))
						b.Show(
							"its coordinate at itself is one",
							fixed.Rw(),
							coordinates.Rw(),
							Simp(Fwd(module_record.RestrictRingDef), Fwd(field.FieldRingDef)),
							Basic())
					}))
				p.Show(
					"sum those diagonal entries and count E",
					CalcEq(
						Leg(
							p.TermAs[A](
								"module_basis_trace(restrict_ring(field_ring(L), K), "+
									"    regular_module(field_ring(L)), "+
									"    E, "+
									"    L.mul(L.one))"),
							"compute the trace in E",
							By(computed)),
						Leg(
							p.TermAs[A](
								"module_sum(restrict_ring(field_ring(L), K).add, "+
									"    restrict_ring(field_ring(L), K).zero, "+
									"    E, "+
									"    λx:A. L.one)"),
							"replace each diagonal entry by one",
							Simp(Fwd(module_dimension.ModuleBasisTraceDef)),
							By(diagonal, module.ModuleSumCongruence)),
						FinalLeg(
							"the finite sum of ones counts E",
							Simp(Fwd(module_record.RestrictRingDef), Fwd(field.FieldRingDef)),
							By(
								finiteE,
								module.ModuleSumConstantMonoid.Read(comm_ring.AddMonoidOn.Read(field.RingOn.Read(L))).At(
									E, oneInL))),
					))
			})

			return ctx.Theorem(headline, func(
				p *Argument,
				L field.FieldFact[on.L],
				K *Expr[Set[A]],
				a *Expr[A],
				hypotheses Fact,
			) {
				given := p.Conjuncts(
					hypotheses,
					"K is a subfield of L",
					"L is a finite extension of K",
					"a is a scalar of K")
				subK, finite, aInK := given[0], given[1], proof.MemberOf(a, given[2])
				traceHom := p.Have(
					"the trace is a K-linear functional on L",
					"module_homomorphism(restrict_ring(field_ring(L), K), "+
						"    regular_module(field_ring(L)), "+
						"    restrict_module(regular_module(field_ring(L)), K), "+
						"    λz:A. field_trace(L, K, z))",
					By(subK, finite, FieldTraceLinear.Read(L).At(K)))
				supplied := p.Conjuncts(
					p.Have(
						"the subfield K supplies scalars acting on L",
						"subring(field_ring(L), K) ∧ "+
							"module_on(restrict_ring(field_ring(L), K), regular_module(field_ring(L)))",
						By(subK, field_extension.SubfieldScalars.Read(L).At(K))),
					"K is a subring of L",
					"L is a module over the scalar ring on K")
				subringK, moduleK := supplied[0], supplied[1]
				within := p.Have(
					"K lies in L",
					"K ⊆ L.carrier",
					By(comm_ring.SubringSubset.Read(subringK)))
				scalars := p.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), K)")
				ambient := p.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
				carrier := p.Have(
					"the vectors of the field's ring, as a module over itself, are L.carrier",
					"regular_module(field_ring(L)).carrier = L.carrier",
					Simp(Fwd(module_record.RegularModuleDef), Fwd(field.FieldRingDef)),
					Basic())
				// The finite extension is the module L restricted to L.carrier, its
				// own carrier, which is the module L: L is finite-dimensional over K.
				finiteDimensional := p.Simplified(
					finite,
					Fwd(field_extension.FiniteExtensionDef),
					Rev(carrier),
					Fwd(module_record.RestrictModuleCarrier))
				E, basis := p.ObtainAs[Set[A]](
					"choose a finite K-basis E of L",
					"∃E:set(A). "+
						"    finite(E) ∧ module_basis(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), E)",
					By(finiteDimensional, module_dimension.FiniteDimensionalDef.At(scalars, ambient)))
				basisParts := p.Conjuncts(
					basis,
					"E is finite",
					"E is a K-basis of L")
				finiteE, basisE := basisParts[0], basisParts[1]
				dimension := p.Have(
					"the dimension over K is the cardinality of E",
					"module_dim(restrict_ring(field_ring(L), K), regular_module(field_ring(L))) = card(E)",
					Derive(func(b *Argument) {
						inverse := b.TermAs[Fun[A, A]]("L.inv")
						packed := b.Have(
							"K, a subfield of L, is a field under the scalar ring's operations with L's inverse",
							"ring_subfield(restrict_ring(field_ring(L), K), L.inv, K)",
							By(subK, field.SubfieldRingSubfield.Read(L).At(K, K)))
						b.Show(
							"the finite basis computes the dimension",
							By(packed, finiteE, basisE, module_dimension.DimBasis.Read(moduleK).At(inverse, E)))
					}))
				oneTrace := p.Have(
					"the trace of one counts the basis E",
					"field_trace(L, K, L.one) = monoid_pow(L.add, L.zero, L.one, card(E))",
					By(moduleK, subK, finiteE, basisE, Read(traceOne, L).At(K, E)))
				eachInL := p.Unfolded(within, set_basic.SubsetDef)
				aInL := p.MemberOf[on.L](a, p.Have(
					"the scalar a lies in L",
					"a ∈ L.carrier",
					By(aInK, eachInL.At(a))))
				// One is held once, untyped: HomIn and HomSmul take a member of the
				// source module's carrier, regular_module(field_ring(L)).carrier, and a
				// member typed in L.carrier names another carrier.
				one := proof.MemberOf(p.TermAs[A]("L.one"), p.Have(
					"one lies in L",
					"L.one ∈ L.carrier",
					By(comm_ring.OneIn.Read(field.RingOn.Read(L)))))
				traceOfOne := p.TermAs[A]("field_trace(L, K, L.one)")
				traceInK := p.Have(
					"the trace of one belongs to K",
					"field_trace(L, K, L.one) ∈ K",
					By(module_homomorphism.HomIn.Read(traceHom).At(one)))
				traceInL := p.MemberOf[on.L](traceOfOne, p.Have(
					"the trace of one therefore lies in L",
					"field_trace(L, K, L.one) ∈ L.carrier",
					By(traceInK, eachInL.At(traceOfOne))))
				scaled := p.Have(
					"K-linearity evaluates the trace at a times one",
					"field_trace(L, K, a * L.one) = a * field_trace(L, K, L.one)",
					By(aInK, one, module_homomorphism.HomSmul.Read(traceHom).At(aInK, one)))
				timesOne := p.Have(
					"one is the identity of the field product",
					"a * L.one = a",
					ByArith(L, aInL))
				p.Show(
					"scale the trace of one and replace the basis size by the dimension",
					CalcEq(
						Leg(
							p.TermAs[A]("a * field_trace(L, K, L.one)"),
							"apply K-linearity at one",
							By(scaled, timesOne)),
						Leg(
							p.TermAs[A]("field_trace(L, K, L.one) * a"),
							"commute the two field elements",
							ByArith(L, aInL, traceInL)),
						FinalLeg(
							"substitute the trace of one and the dimension",
							Simp(Fwd(oneTrace), Fwd(dimension)),
							Basic()),
					))
			})
		}),
})}

// CharZeroTraceNondegenerate — a finite extension in characteristic zero
// has positive degree and a nondegenerate trace pairing: its dimension
// cannot vanish, and pairing a nonzero element with its inverse gives
// the trace of one, a positive number of copies of one.
var CharZeroTraceNondegenerate = charZeroTraceNondegenerateThm{family.Add(registry.ProofEntry{
	Name: "CharZeroTraceNondegenerate",
	Key:  "prop_1bc05d25ae569960",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K:set(A).",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
			"subfield(L, K)",
			"finite_extension(L, K, L.carrier)",
		},
		Conclusion: "0 < extension_degree(L, K, L.carrier) ∧ " +
			"(∀x:A. x ∈ L.carrier ∧ x ≠ L.zero ⇒ ∃y:A. y ∈ L.carrier ∧ field_trace(L, K, x * y) ≠ L.zero)",
	}, func(a *Argument, L field.FieldFact[on.L], K *Expr[Set[A]], h Fact) {
		given := a.Conjuncts(
			h,
			"L has characteristic zero",
			"K is a subfield of L",
			"L is finite over K")
		charZero, subK, finite := given[0], given[1], given[2]
		fieldL := a.TermAs[FieldOps[A]]("L")
		carrier := a.TermAs[Set[A]]("L.carrier")
		one, zero := a.TermAs[A]("L.one"), a.TermAs[A]("L.zero")
		ring := field.RingOn.Read(L)
		additive, multiplicative := comm_ring.AddMonoidOn.Read(ring), comm_ring.MulMonoidOn.Read(ring)
		fullModule := a.Have(
			"restricting the regular module to L's carrier leaves it unchanged",
			"restrict_module(regular_module(field_ring(L)), L.carrier) = regular_module(field_ring(L))",
			Simp(
				Fwd(module_record.RegularModuleDef),
				Fwd(field.FieldRingDef),
				Fwd(module_record.RestrictModuleDef)),
			Basic())

		positiveDimension := a.Have(
			"the K-dimension of L is positive",
			"0 < module_dim(restrict_ring(field_ring(L), K), regular_module(field_ring(L)))",
			Derive(func(b *Argument) {
				moduleK := b.Have(
					"K supplies scalars acting on L",
					"module_on(restrict_ring(field_ring(L), K), regular_module(field_ring(L)))",
					By(subK, field_extension.SubfieldScalars.Read(L).At(K)))
				finiteDim := b.Have(
					"the regular module is finite dimensional over K",
					"finite_dimensional(restrict_ring(field_ring(L), K), regular_module(field_ring(L)))",
					By(Normalized, fullModule, finite, field_extension.FiniteExtensionDef.At(fieldL, K, carrier)))
				inverse := b.TermAs[Fun[A, A]]("L.inv")
				scalarField := b.Have(
					"K, a subfield of L, is a field under the scalar ring's operations, with L's inverse",
					"ring_subfield(restrict_ring(field_ring(L), K), L.inv, K)",
					By(subK, field.SubfieldRingSubfield.Read(L).At(K, K)))
				zeroCriterion := b.Have(
					"dimension zero would make L the zero module",
					"module_dim(restrict_ring(field_ring(L), K), regular_module(field_ring(L))) = 0 ⇔ "+
						"regular_module(field_ring(L)).carrier = {regular_module(field_ring(L)).zero}",
					By(scalarField, finiteDim, module_dimension.DimZero.Read(moduleK).At(inverse)))
				carrierAndZero := b.Have(
					"the regular module has L's carrier and zero",
					"regular_module(field_ring(L)).carrier = L.carrier ∧ regular_module(field_ring(L)).zero = L.zero",
					Simp(Fwd(module_record.RegularModuleDef), Fwd(field.FieldRingDef)),
					Basic())
				nonzeroDimension := b.Have(
					"one in L is distinct from zero, so the dimension cannot vanish",
					"module_dim(restrict_ring(field_ring(L), K), regular_module(field_ring(L))) ≠ 0",
					By(
						field.OneNotZeroOn.Read(L),
						comm_ring.OneIn.Read(ring),
						zeroCriterion,
						carrierAndZero,
						set_basic.InSing.At(one, zero)))
				b.Show(
					"a nonzero natural dimension is positive",
					ByArith(nonzeroDimension))
			}))
		positiveDegree := a.Have(
			"the extension degree is the same positive dimension",
			"0 < extension_degree(L, K, L.carrier)",
			By(
				Normalized,
				positiveDimension,
				fullModule,
				field_extension.ExtensionDegreeDef.At(fieldL, K, carrier)))

		traceOne := a.Have(
			"the trace of one is nonzero",
			"field_trace(L, K, L.one) ≠ L.zero",
			Derive(func(b *Argument) {
				characteristic := b.Unfolded(charZero, comm_ring.CharacteristicZeroDef)
				copiesNonzero := b.Have(
					"a positive number of copies of one is nonzero",
					"monoid_pow(L.add, "+
						"    L.zero, "+
						"    L.one, "+
						"    module_dim(restrict_ring(field_ring(L), K), regular_module(field_ring(L)))) ≠ "+
						"L.zero",
					By(positiveDimension, characteristic))
				b.Have(
					"one is a scalar of K",
					"L.one ∈ K",
					By(subK, field.SubfieldOne.At(fieldL, K)))
				b.Show(
					"the scalar trace formula counts those copies of one",
					Simp(
						Fwd(FieldTraceOfScalar.Read(L)),
						Fwd(comm_monoid.RightIdentityOn.Read(multiplicative)),
						Fwd(comm_monoid.PowIn.Read(additive)),
						Fwd(comm_ring.OneIn.Read(ring))),
					By(copiesNonzero))
			}))
		pairing := a.Have(
			"each nonzero element pairs with its reciprocal",
			"∀x:A. x ∈ L.carrier ∧ x ≠ L.zero ⇒ ∃y:A. y ∈ L.carrier ∧ field_trace(L, K, x * y) ≠ L.zero",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				guard := b.Conjuncts(
					b.Assume(),
					"x lies in L",
					"x is nonzero")
				xm := b.MemberOf[on.L](x, guard[0])
				b.Take(b.TermAs[A]("L.inv(x)"))
				b.Show(
					"the reciprocal lies in L and the product has nonzero trace",
					By(
						Normalized,
						traceOne,
						guard[1],
						field.InvIn.Read(L).At(xm),
						field.MulRightInverseOn.Read(L).At(xm)))
			}))
		a.Show(
			"positive degree and the reciprocal witnesses give the conclusion",
			By(positiveDegree, pairing))
	}),
})}

// FieldTraceInSubring — A common integral and field basis puts the trace back in the coefficient subring.
var FieldTraceInSubring = fieldTraceInSubringThm{family.Add(registry.ProofEntry{
	Name: "FieldTraceInSubring",
	Key:  "prop_27552887b9bc29ea",
	Deps: []registry.EntryLike{
		FieldTraceFromBasis,
		module_dimension.BasisCoordinatesUnique,
		module_dimension.BasisCoordinatesSpec,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K S B E:set(A). ∀z:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite_dimensional(restrict_ring(field_ring(L), K), regular_module(field_ring(L)))",
			"subring(field_ring(L), S)",
			"S ⊆ K",
			"subring(field_ring(L), B)",
			"S ⊆ B",
			"finite(E)",
			"module_basis(restrict_ring(field_ring(L), S), " +
				"    restrict_module(regular_module(field_ring(L)), B), " +
				"    E)",
			"module_basis(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), E)",
			"z ∈ B",
		},
		Conclusion: "field_trace(L, K, z) ∈ S",
	},
		"The S-basis coordinates of each z·e belong to S. Their expansion "+
			"is also the K-expansion, so its diagonal sum is the field trace."),
})}
