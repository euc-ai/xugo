// structure_sheaf.go — the structure sheaf of the prime spectrum of a
// ring on a set, in two parts marked by banners: the definitions; and
// the sheaf of rings, its sections over each open set a ring and its
// restrictions ring homomorphisms.

package structure_sheaf

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/local_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/scheme/locally_ringed_space"
	"github.com/euc-ai/xugo/library/proofs/scheme/prime_spectrum"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/presheaf"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The definitions
// ---------------------------------------------------------------------------

// FractionSectionDef — `fraction_section(R, U, a, b)`: the fraction a / b
// as a section over U — its class at each prime of U, ∅ elsewhere.
var FractionSectionDef = fractionSectionDefThm{family.Define(registry.DefEntry{
	Name:     "FractionSectionDef",
	Key:      "prop_f625bcf5515218c2",
	Const:    "fraction_section",
	Type:     "ring_ops(A) → set(set(A)) → A → A → set(A) → set(prod(A, A))",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀U:set(set(A)). ∀a b:A. ∀q:set(A). " +
			"    fraction_section(R, U, a, b, q) = " +
			"    COND(q ∈ U, fraction_class(R.mul, R.carrier, R.carrier ∖ q, a, b), ∅)",
	},
})}

// LocallyFractionDef — `locally_fraction(R, U, p, s)`: s is locally a
// fraction at p within U — on an open neighborhood V ⊆ U of p it is
// a / b, with b outside every prime of V.
var LocallyFractionDef = locallyFractionDefThm{family.Define(registry.DefEntry{
	Name:     "LocallyFractionDef",
	Key:      "prop_c4cb9a0cebc0fb1b",
	Const:    "locally_fraction",
	Type:     "ring_ops(A) → set(set(A)) → set(A) → (set(A) → set(prod(A, A))) → bool",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀U:set(set(A)). ∀p:set(A). ∀s:(set(A) → set(prod(A, A))). " +
			"    locally_fraction(R, U, p, s) ⇔ " +
			"    ∃V:set(set(A)). ∃a b:A. " +
			"        V ∈ zariski_topology(R) ∧ " +
			"        p ∈ V ∧ " +
			"        V ⊆ U ∧ " +
			"        a ∈ R.carrier ∧ " +
			"        b ∈ R.carrier ∧ " +
			"        (∀q:set(A). q ∈ V ⇒ b ∉ q ∧ s(q) = fraction_class(R.mul, R.carrier, R.carrier ∖ q, a, b))",
	},
})}

// StructureSectionsDef — the sections over U are functions from primes
// to fractions, empty outside U and locally one fraction in R.
var StructureSectionsDef = structureSectionsDefThm{family.Define(registry.DefEntry{
	Name:     "StructureSectionsDef",
	Key:      "prop_9c447f7396c899e8",
	Const:    "structure_sections",
	Type:     "ring_ops(A) → set(set(A)) → (set(set(A) → set(prod(A, A))))",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀U:set(set(A)). " +
			"    structure_sections(R, U) = " +
			"    {s:(set(A) → set(prod(A, A))) | " +
			"        (∀p:set(A). p ∉ U ⇒ s(p) = ∅) ∧ (∀p:set(A). p ∈ U ⇒ locally_fraction(R, U, p, s))}",
	},
	Deps: []registry.EntryLike{LocallyFractionDef},
})}

// StructureRestrictDef — `structure_restrict(U, V, s, p)`: s at p if p
// ∈ V, ∅ otherwise — a section restricted to V.
var StructureRestrictDef = structureRestrictDefThm{family.Define(registry.DefEntry{
	Name:  "StructureRestrictDef",
	Key:   "prop_aca30ca28651de2b",
	Const: "structure_restrict",
	Type:  "set(set(A)) → set(set(A)) → (set(A) → set(prod(A, A))) → set(A) → set(prod(A, A))",
	Equations: []string{
		"∀U V:set(set(A)). ∀s:(set(A) → set(prod(A, A))). ∀p:set(A). " +
			"    structure_restrict(U, V, s, p) = COND(p ∈ V, s(p), ∅)",
	},
})}

// StructureAddDef — `structure_add(R, U, s, t, p)`: the sum
// of two sections over U, at each p ∈ U the sum of their fractions at p.
var StructureAddDef = structureAddDefThm{family.Define(registry.DefEntry{
	Name:  "StructureAddDef",
	Key:   "prop_9fbd604866d91cfe",
	Const: "structure_add",
	Type: "ring_ops(A) → " +
		"set(set(A)) → " +
		"(set(A) → set(prod(A, A))) → " +
		"(set(A) → set(prod(A, A))) → " +
		"set(A) → " +
		"set(prod(A, A))",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀U:set(set(A)). " +
			"∀s:(set(A) → set(prod(A, A))). " +
			"∀t:(set(A) → set(prod(A, A))). " +
			"∀p:set(A). " +
			"    structure_add(R, U, s, t, p) = " +
			"    COND(p ∈ U, fraction_add(R.add, R.mul, R.carrier, R.carrier ∖ p, s(p), t(p)), ∅)",
	},
})}

// StructureMulDef — `structure_mul(R, U, s, t, p)`: the product of
// two sections over U.
var StructureMulDef = structureMulDefThm{family.Define(registry.DefEntry{
	Name:  "StructureMulDef",
	Key:   "prop_7a39ee8b151ec7c5",
	Const: "structure_mul",
	Type: "ring_ops(A) → " +
		"set(set(A)) → " +
		"(set(A) → set(prod(A, A))) → " +
		"(set(A) → set(prod(A, A))) → " +
		"set(A) → " +
		"set(prod(A, A))",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀U:set(set(A)). " +
			"∀s:(set(A) → set(prod(A, A))). " +
			"∀t:(set(A) → set(prod(A, A))). " +
			"∀p:set(A). " +
			"    structure_mul(R, U, s, t, p) = " +
			"    COND(p ∈ U, fraction_mul(R.mul, R.carrier, R.carrier ∖ p, s(p), t(p)), ∅)",
	},
})}

// StructureNegDef — `structure_neg(R, U, s, p)`: the negation
// of a section over U.
var StructureNegDef = structureNegDefThm{family.Define(registry.DefEntry{
	Name:     "StructureNegDef",
	Key:      "prop_57ab19aed0449cc9",
	Const:    "structure_neg",
	Type:     "ring_ops(A) → set(set(A)) → (set(A) → set(prod(A, A))) → set(A) → set(prod(A, A))",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀U:set(set(A)). ∀s:(set(A) → set(prod(A, A))). ∀p:set(A). " +
			"    structure_neg(R, U, s, p) = " +
			"    COND(p ∈ U, fraction_neg(R.neg, R.mul, R.carrier, R.carrier ∖ p, s(p)), ∅)",
	},
})}

// StructureSubDef — `structure_sub(R, U, s, t, p)`: the
// difference of two sections over U.
var StructureSubDef = structureSubDefThm{family.Define(registry.DefEntry{
	Name:  "StructureSubDef",
	Key:   "prop_a0e4903f9af4f98f",
	Const: "structure_sub",
	Type: "ring_ops(A) → " +
		"set(set(A)) → " +
		"(set(A) → set(prod(A, A))) → " +
		"(set(A) → set(prod(A, A))) → " +
		"set(A) → " +
		"set(prod(A, A))",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀U:set(set(A)). " +
			"∀s:(set(A) → set(prod(A, A))). " +
			"∀t:(set(A) → set(prod(A, A))). " +
			"∀p:set(A). " +
			"    structure_sub(R, U, s, t, p) = " +
			"    COND(p ∈ U, fraction_sub(R.add, R.neg, R.mul, R.carrier, R.carrier ∖ p, s(p), t(p)), ∅)",
	},
})}

// StructureZeroDef — `structure_zero(R, U, p)`: the zero
// section over U, the zero fraction at each p ∈ U.
var StructureZeroDef = structureZeroDefThm{family.Define(registry.DefEntry{
	Name:     "StructureZeroDef",
	Key:      "prop_ff2047b62df364a6",
	Const:    "structure_zero",
	Type:     "ring_ops(A) → set(set(A)) → set(A) → set(prod(A, A))",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀U:set(set(A)). ∀p:set(A). " +
			"    structure_zero(R, U, p) = " +
			"    COND(p ∈ U, fraction_zero(R.zero, R.mul, R.one, R.carrier, R.carrier ∖ p), ∅)",
	},
})}

// StructureOneDef — `structure_one(R, U, p)`: the one section
// over U.
var StructureOneDef = structureOneDefThm{family.Define(registry.DefEntry{
	Name:     "StructureOneDef",
	Key:      "prop_d5d33e60151b5fca",
	Const:    "structure_one",
	Type:     "ring_ops(A) → set(set(A)) → set(A) → set(prod(A, A))",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀U:set(set(A)). ∀p:set(A). " +
			"    structure_one(R, U, p) = COND(p ∈ U, fraction_one(R.mul, R.one, R.carrier, R.carrier ∖ p), ∅)",
	},
})}

// SpecSectionOps — the ring record of sections over the open U.
var SpecSectionOps = specSectionOpsThm{family.Define(registry.DefEntry{
	Name: "SpecSectionOps",
	Key:  "prop_6d4d038ca198ac1", Const: "spec_section_ops",
	Type: "ring_ops(A) → set(set(A)) → ring_ops(set(A) → set(prod(A, A)))",
	Equations: []string{
		"∀R:ring_ops(A). ∀U:set(set(A)). " +
			"    spec_section_ops(R, U) = " +
			"    mk_ring(structure_add(R, U), " +
			"        structure_zero(R, U), " +
			"        structure_neg(R, U), " +
			"        structure_mul(R, U), " +
			"        structure_one(R, U), " +
			"        structure_sub(R, U), " +
			"        structure_sections(R, U))",
	},
	Deps: []registry.EntryLike{
		StructureAddDef,
		StructureZeroDef,
		StructureNegDef,
		StructureMulDef,
		StructureOneDef,
		StructureSubDef,
		StructureSectionsDef,
	},
})}

// SpecSheaf — the spectrum's topology, section-ring family and restriction.
var SpecSheaf = family.Tuple("spec_sheaf", []string{"R"},
	"zariski_topology(R)", "spec_section_ops(R)", "structure_restrict")

// SpecStalkOps — the ring record of germs at the prime p.
var SpecStalkOps = specStalkOpsThm{family.Define(registry.DefEntry{
	Name: "SpecStalkOps",
	Key:  "prop_b61d9ade7831dcfb", Const: "spec_stalk_ops",
	Type: "ring_ops(A) → set(A) → ring_ops(set(prod(set(set(A)), set(A) → set(prod(A, A)))))",
	Equations: []string{
		"∀R:ring_ops(A). ∀p:set(A). " +
			"    spec_stalk_ops(R, p) = " +
			"    stalk_ring(zariski_topology(R), spec_section_ops(R), structure_restrict, p)",
	},
	Deps: []registry.EntryLike{SpecSectionOps},
})}

// ---------------------------------------------------------------------------
// The sheaf of rings
// ---------------------------------------------------------------------------

// ZariskiPointPrime — a point of an open set of the spectrum is a prime
// ideal: an open set is the spectrum less a closed set.
var ZariskiPointPrime = zariskiPointPrimeThm{family.Add(registry.ProofEntry{
	Name: "ZariskiPointPrime",
	Key:  "prop_12c45120f0e62af0",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀U:set(set(A)). ∀p:set(A).",
		Hypotheses: []string{"U ∈ zariski_topology(R)", "p ∈ U"},
		Conclusion: "prime_ideal(R, p)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		U *Expr[Set[Set[A]]],
		open Fact,
		p *Expr[Set[A]],
		point Fact,
	) {
		_, complement := a.UnpackAs[Set[A]](a.Unfolded(open, prime_spectrum.ZariskiTopologyDef), "I")
		a.Show(
			"U is the spectrum less the closed set of I, so p lies in the spectrum",
			BySets(point, complement, prime_spectrum.PrimeSpectrumDef.At(R)))
	}),
})}

// StructureRestrictIn — restriction preserves local fractions: intersect a
// representation neighborhood with the smaller open set.
var StructureRestrictIn = structureRestrictInThm{family.Add(registry.ProofEntry{
	Name: "StructureRestrictIn",
	Key:  "prop_ce6b7b149fdcc950",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀U V:set(set(A)). ∀s:(set(A) → set(prod(A, A))).",
		Hypotheses: []string{
			"V ∈ zariski_topology(R)",
			"V ⊆ U",
			"s ∈ structure_sections(R, U)",
		},
		Conclusion: "structure_restrict(U, V, s) ∈ structure_sections(R, V)",
	}, func(
		a *Argument,
		ring comm_ring.CommRingFact[on.R],
		U, V *Expr[Set[Set[A]]],
		s *Arrow[Set[A], Set[Prod[A, A]]],
		h Fact,
	) {
		conditions := a.Conjuncts(
			h,
			"V is open",
			"V lies in U",
			"s is a section over U")
		section := a.Unfolded(a.Unfolded(conditions[2], StructureSectionsDef), LocallyFractionDef)
		a.Do(Unfold(StructureSectionsDef))
		localData := a.Conjuncts(
			section,
			"the section is empty outside U",
			"the section is locally a fraction")
		local := a.Have(
			"restriction inherits a local fraction on the intersection",
			"∀p:set(A). p ∈ V ⇒ locally_fraction(R, V, p, structure_restrict(U, V, s))",
			Derive(func(b *Argument) {
				p := b.FixAs[Set[A]]("p")
				inV := b.Assume()
				b.Do(Unfold(LocallyFractionDef))
				N, c, d, representation := b.Obtain3As[Set[Set[A]], A, A](
					"the source section has a fraction near p",
					"∃N:set(set(A)). ∃c d:A. "+
						"    N ∈ zariski_topology(R) ∧ "+
						"    p ∈ N ∧ "+
						"    N ⊆ U ∧ "+
						"    c ∈ R.carrier ∧ "+
						"    d ∈ R.carrier ∧ "+
						"    (∀q:set(A). q ∈ N ⇒ d ∉ q ∧ s(q) = fraction_class(R.carrier, R.carrier ∖ q, c, d))",
					BySets(localData[1].At(p), inV, conditions[1]))
				b.Take(b.TermAs[Set[Set[A]]]("N ∩ V"))
				b.Take(c)
				b.Take(d)
				b.Show(
					"the same numerator and denominator represent the restriction",
					BySets(
						ring,
						inV,
						conditions[0],
						representation,
						prime_spectrum.ZariskiIsTopology.Read(ring),
						topological_space.InterOpen.At(b.TermAs[Set[Set[Set[A]]]]("zariski_topology(R)"), N, V),
						StructureRestrictDef))
			}))
		empty := a.Have(
			"restriction is empty outside V",
			"∀p:set(A). p ∉ V ⇒ structure_restrict(U, V, s, p) = ∅",
			By(StructureRestrictDef.Inst[A]().At(U, V, s)))
		a.Show(
			"these are the defining conditions for a section over V",
			By(empty, local))
	}),
})}

// StructureSectionValue — evaluating a section at a point of its open set
// gives a fraction with denominator outside that point.
var StructureSectionValue = structureSectionValueThm{family.Add(registry.ProofEntry{
	Name: "StructureSectionValue",
	Key:  "prop_a30742b0f84f6516",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀U:set(set(A)). ∀s:(set(A) → set(prod(A, A))). ∀p:set(A).",
		Hypotheses: []string{"s ∈ structure_sections(R, U)", "p ∈ U"},
		Conclusion: "s(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		U *Expr[Set[Set[A]]],
		s *Arrow[Set[A], Set[Prod[A, A]]],
		p *Expr[Set[A]],
		h Fact,
	) {
		conditions := a.Conjuncts(
			a.Unfolded(a.Unfolded(h, StructureSectionsDef), LocallyFractionDef),
			"s is locally a fraction and empty outside U",
			"p lies in U")
		localData := a.Conjuncts(
			conditions[0],
			"the section is empty outside U",
			"the section is locally a fraction")
		_, _, _, representation := a.Obtain3(
			"choose a representation near p",
			"∃V:set(set(A)). ∃c d:A. "+
				"    V ∈ zariski_topology(R) ∧ "+
				"    p ∈ V ∧ "+
				"    V ⊆ U ∧ "+
				"    c ∈ R.carrier ∧ "+
				"    d ∈ R.carrier ∧ "+
				"    (∀q:set(A). q ∈ V ⇒ d ∉ q ∧ s(q) = fraction_class(R.carrier, R.carrier ∖ q, c, d))",
			By(localData[1].At(p), conditions[1]))
		a.Show(
			"its value at p is a class in the localization",
			BySets(
				representation,
				ring_localization.RingLocalizationMember.At(
					a.TermAs[Op[A]]("R.mul"),
					a.TermAs[Set[A]]("R.carrier"),
					a.TermAs[Set[A]]("R.carrier ∖ p"),
					a.TermAs[Set[Prod[A, A]]]("s(p)"))))
	}),
})}

// ConstantFractionSection — a fraction whose denominator avoids an open set
// defines a section there, using the whole open set as its neighborhood.
var ConstantFractionSection = constantFractionSectionThm{family.Add(registry.ProofEntry{
	Name: "ConstantFractionSection",
	Key:  "prop_429b0dfad2973965",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀U:set(set(A)). ∀a b:A.",
		Hypotheses: []string{
			"U ∈ zariski_topology(R)",
			"a ∈ R.carrier",
			"b ∈ R.carrier",
			"∀q:set(A). q ∈ U ⇒ b ∉ q",
		},
		Conclusion: "fraction_section(R, U, a, b) ∈ structure_sections(R, U)",
	}, func(arg *Argument, R *Expr[RingOps[A]], U *Expr[Set[Set[A]]], a, b *Expr[A], h Fact) {
		parts := arg.Conjuncts(
			h,
			"U is open",
			"the numerator lies in R",
			"the denominator lies in R",
			"the denominator avoids U")
		open, aIn, bIn, avoids := parts[0], parts[1], parts[2], parts[3]
		arg.Do(Unfold(StructureSectionsDef))
		local := arg.Have(
			"the fraction is represented on U itself",
			"∀p:set(A). p ∈ U ⇒ locally_fraction(R, U, p, fraction_section(R, U, a, b))",
			Derive(func(e *Argument) {
				e.FixAs[Set[A]]("p")
				inU := e.Assume()
				e.Do(Unfold(LocallyFractionDef))
				e.Take(U)
				e.Take(a)
				e.Take(b)
				e.Show(
					"the chosen fraction agrees at each point of U",
					Simp(Fwd(FractionSectionDef)),
					BySets(avoids, aIn, bIn, inU, open))
			}))
		empty := arg.Have(
			"the section is empty outside U",
			"∀p:set(A). p ∉ U ⇒ fraction_section(R, U, a, b, p) = ∅",
			Simp(Fwd(FractionSectionDef)),
			BySets())
		arg.Show(
			"the local fractions and empty values define a section",
			By(empty, local))
	}),
})}

// StructureSectionLocalFraction — near each point a section is one
// fraction a / b on an open neighborhood, and at every point q of it the
// complement of q is a multiplicative set holding b, where s(q) is the
// class of a / b: the points of an open set are primes.
var StructureSectionLocalFraction = structureSectionLocalFractionThm{family.Add(registry.ProofEntry{
	Name: "StructureSectionLocalFraction",
	Key:  "prop_2d88dc158d5ed7a",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀U:set(set(A)). ∀s:(set(A) → set(prod(A, A))). ∀p:set(A).",
		Hypotheses: []string{"s ∈ structure_sections(R, U)", "p ∈ U"},
		Conclusion: "∃V:set(set(A)). ∃a b:A. " +
			"    V ∈ zariski_topology(R) ∧ " +
			"    p ∈ V ∧ " +
			"    V ⊆ U ∧ " +
			"    a ∈ R.carrier ∧ " +
			"    b ∈ R.carrier ∧ " +
			"    (∀q:set(A). " +
			"        q ∈ V ⇒ " +
			"        multiplicative_set(R.carrier, R.carrier ∖ q) ∧ " +
			"        b ∈ R.carrier ∖ q ∧ " +
			"        s(q) = fraction_class(R.carrier, R.carrier ∖ q, a, b))",
	}, func(
		arg *Argument,
		ring comm_ring.CommRingFact[on.R],
		U *Expr[Set[Set[A]]],
		s *Arrow[Set[A], Set[Prod[A, A]]],
		p *Expr[Set[A]],
		h Fact,
	) {
		conditions := arg.Conjuncts(
			h,
			"s is a section over U",
			"p lies in U")
		localData := arg.Conjuncts(
			arg.Unfolded(arg.Unfolded(conditions[0], StructureSectionsDef), LocallyFractionDef),
			"s is empty outside U",
			"s is locally a fraction")
		V, a, b, representation := arg.Unpack3As[Set[Set[A]], A, A](
			GroupPremises(conditions[1], localData[1].At(p)),
			"V",
			"a",
			"b")
		parts := arg.Conjuncts(
			representation,
			"V is open",
			"V contains p",
			"V lies in U",
			"a lies in the ring",
			"b lies in the ring",
			"s is a over b on V")
		arg.Take(V)
		arg.Take(a)
		arg.Take(b)
		arg.Show(
			"the representation of the definition carries over",
			SplitConj(
				Case(
					"the neighborhood and the coefficients are those of the definition",
					By(parts[0], parts[1], parts[2], parts[3], parts[4])),
				Case(
					"at each point of V the denominator lies in the multiplicative prime complement",
					Derive(func(c *Argument) {
						q := c.FixAs[Set[A]]("q")
						inV := c.Assume()
						multiplicative := c.Have(
							"q is a prime, so its complement is multiplicative",
							"multiplicative_set(R.carrier, R.carrier ∖ q)",
							By(
								parts[0],
								inV,
								ZariskiPointPrime.At(c.TermAs[RingOps[A]]("R"), V, q),
								local_ring.PrimeComplementMultiplicative.Read(ring).At(q)))
						c.Show(
							"b avoids q and s(q) is the class of a / b",
							BySets(multiplicative, parts[4], inV, parts[5].At(q)))
					}))))
	}),
})}

// StructureSectionsCommonNeighborhood — near a common point two sections
// over U are fractions a / b and c / d on one open neighborhood V inside
// U, at every point q of which the complement of q is multiplicative and
// holds b and d, so that the common denominator b * d avoids q: intersect
// the neighborhoods on which each section is one fraction.
var StructureSectionsCommonNeighborhood = structureSectionsCommonNeighborhoodThm{family.Add(registry.ProofEntry{
	Name: "StructureSectionsCommonNeighborhood",
	Key:  "prop_80434e5eeb09b54c",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀U:set(set(A)). ∀s t:(set(A) → set(prod(A, A))). ∀p:set(A).",
		Hypotheses: []string{"s ∈ structure_sections(R, U)", "t ∈ structure_sections(R, U)", "p ∈ U"},
		Conclusion: "∃V:set(set(A)). ∃a b c d:A. " +
			"    V ∈ zariski_topology(R) ∧ " +
			"    p ∈ V ∧ " +
			"    V ⊆ U ∧ " +
			"    a ∈ R.carrier ∧ " +
			"    b ∈ R.carrier ∧ " +
			"    c ∈ R.carrier ∧ " +
			"    d ∈ R.carrier ∧ " +
			"    (∀q:set(A). " +
			"        q ∈ V ⇒ " +
			"        multiplicative_set(R.carrier, R.carrier ∖ q) ∧ " +
			"        b ∈ R.carrier ∖ q ∧ " +
			"        d ∈ R.carrier ∖ q ∧ " +
			"        b * d ∉ q ∧ " +
			"        s(q) = fraction_class(R.carrier, R.carrier ∖ q, a, b) ∧ " +
			"        t(q) = fraction_class(R.carrier, R.carrier ∖ q, c, d))",
	}, func(
		arg *Argument,
		ring comm_ring.CommRingFact[on.R],
		U *Expr[Set[Set[A]]],
		s, t *Arrow[Set[A], Set[Prod[A, A]]],
		p *Expr[Set[A]],
		h Fact,
	) {
		conditions := arg.Conjuncts(
			h,
			"s is a section over U",
			"t is a section over U",
			"p lies in U")
		N, a, b, sFraction := arg.Unpack3As[Set[Set[A]], A, A](
			GroupPremises(conditions[0], conditions[2], StructureSectionLocalFraction.Read(ring).At(U, s, p)),
			"N",
			"a",
			"b")
		M, c, d, tFraction := arg.Unpack3As[Set[Set[A]], A, A](
			GroupPremises(conditions[1], conditions[2], StructureSectionLocalFraction.Read(ring).At(U, t, p)),
			"M",
			"c",
			"d")
		sParts := arg.Conjuncts(
			sFraction,
			"N is open",
			"N contains p",
			"N lies in U",
			"a lies in the ring",
			"b lies in the ring",
			"s is a / b on N")
		tParts := arg.Conjuncts(
			tFraction,
			"M is open",
			"M contains p",
			"M lies in U",
			"c lies in the ring",
			"d lies in the ring",
			"t is c / d on M")
		arg.Take(arg.TermAs[Set[Set[A]]]("N ∩ M"))
		arg.Take(a)
		arg.Take(b)
		arg.Take(c)
		arg.Take(d)
		arg.Show(
			"both fractions hold on the intersection, over the common denominator b * d",
			SplitConj(
				Case(
					"the intersection is an open neighborhood of p inside U, and the four coefficients lie in the ring",
					BySets(
						prime_spectrum.ZariskiIsTopology.Read(ring),
						sFraction,
						tFraction,
						topological_space.InterOpen.At(arg.TermAs[Set[Set[Set[A]]]]("zariski_topology(R)"), N, M))),
				Case(
					"at a point of both neighborhoods both fractions "+
						"hold, and its complement, multiplicative, holds b * d",
					Derive(func(e *Argument) {
						q := e.FixAs[Set[A]]("q")
						inBoth := e.Assume()
						e.Show(
							"q lies in N and in M, and a multiplicative set holds the product of two of its elements",
							BySets(
								inBoth,
								sParts[5].At(q),
								tParts[5].At(q),
								ring_localization.MultiplicativeSetDef.At(
									e.TermAs[Op[A]]("R.mul"),
									e.TermAs[A]("R.one"),
									e.TermAs[Set[A]]("R.carrier"),
									e.TermAs[Set[A]]("R.carrier ∖ q"))))
					}))))
	}),
})}

// StructureSectionAddIn — the sum of two locally represented sections is
// locally represented by the sum of the two fractions over a common
// denominator.
var StructureSectionAddIn = structureSectionAddInThm{family.Add(registry.ProofEntry{
	Name: "StructureSectionAddIn",
	Key:  "prop_72286a8bb1b0b11c",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀U:set(set(A)). ∀s t:(set(A) → set(prod(A, A))).",
		Hypotheses: []string{"s ∈ structure_sections(R, U)", "t ∈ structure_sections(R, U)"},
		Conclusion: "«sum» ∈ structure_sections(R, U)",
		Abbrev:     Abbrev{{Name: "sum", Text: "structure_add(R, U, s, t)"}},
	}, func(
		arg *Argument,
		ring comm_ring.CommRingFact[on.R],
		U *Expr[Set[Set[A]]],
		s, t *Arrow[Set[A], Set[Prod[A, A]]],
		sections Fact,
	) {
		local := arg.Have(
			"the sum is locally a fraction",
			"∀p:set(A). p ∈ U ⇒ locally_fraction(R, U, p, «sum»)",
			Derive(func(e *Argument) {
				p := e.FixAs[Set[A]]("p")
				inU := e.Assume()
				V, a, b, c, d, common := e.Unpack5As[Set[Set[A]], A, A, A, A](
					GroupPremises(sections, inU, StructureSectionsCommonNeighborhood.Read(ring).At(U, s, t, p)),
					"V",
					"a",
					"b",
					"c",
					"d")
				parts := e.Conjuncts(
					common,
					"V is open",
					"V contains p",
					"V lies in U",
					"a lies in the ring",
					"b lies in the ring",
					"c lies in the ring",
					"d lies in the ring",
					"on V, s is a / b and t is c / d over the common denominator b * d")
				e.Do(Unfold(LocallyFractionDef))
				e.Take(V)
				e.Take(e.TermAs[A]("a * d + c * b"))
				e.Take(e.TermAs[A]("b * d"))
				e.Show(
					"the common denominator represents the sum",
					SplitConj(
						Case(
							"the neighborhood and coefficients satisfy the carrier conditions",
							By(
								comm_ring.MulIn.Read(ring),
								comm_ring.AddIn.Read(ring),
								parts[0],
								parts[1],
								parts[2],
								parts[3],
								parts[4],
								parts[5],
								parts[6])),
						Case(
							"the sum agrees with the fraction throughout V",
							Derive(func(f *Argument) {
								q := f.FixAs[Set[A]]("q")
								inV := f.Assume()
								at := f.Conjuncts(
									GroupPremises(inV, parts[7].At(q)),
									"the complement of q is multiplicative",
									"b lies in the complement of q",
									"d lies in the complement of q",
									"the common denominator avoids q",
									"s(q) is the class of a / b",
									"t(q) is the class of c / d")
								f.Show(
									"the common denominator avoids q and the fraction addition law applies",
									SplitConj(
										Case(
											"the common denominator avoids q",
											By(at[3])),
										Case(
											"the value is the sum of the fractions",
											Simp(Fwd(StructureAddDef)),
											at[4].Rw(),
											at[5].Rw(),
											CondRewrite(),
											BySets(
												parts[3],
												at[1],
												parts[5],
												at[2],
												inV,
												parts[2],
												at[0],
												ring_localization.FractionAddClass.Read(ring).AsFact().At(
													f.TermAs[Set[A]]("R.carrier ∖ q"), a, b, c, d)))))
							}))))
			}))
		empty := arg.Have(
			"the sum is empty outside U",
			"∀p:set(A). p ∉ U ⇒ «sum»(p) = ∅",
			By(StructureAddDef.Inst[A]().At(arg.TermAs[RingOps[A]]("R"), U, s, t)))
		arg.Show(
			"the sum satisfies both defining section conditions",
			Unfold(StructureSectionsDef),
			By(empty, local))
	}),
})}

// StructureSectionMulIn — the product of two locally represented sections is
// locally represented by the product of the two fractions over a common
// denominator.
var StructureSectionMulIn = structureSectionMulInThm{family.Add(registry.ProofEntry{
	Name: "StructureSectionMulIn",
	Key:  "prop_b7b844891ceb56b4",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀U:set(set(A)). ∀s t:(set(A) → set(prod(A, A))).",
		Hypotheses: []string{"s ∈ structure_sections(R, U)", "t ∈ structure_sections(R, U)"},
		Conclusion: "«product» ∈ structure_sections(R, U)",
		Abbrev:     Abbrev{{Name: "product", Text: "structure_mul(R, U, s, t)"}},
	}, func(
		arg *Argument,
		ring comm_ring.CommRingFact[on.R],
		U *Expr[Set[Set[A]]],
		s, t *Arrow[Set[A], Set[Prod[A, A]]],
		sections Fact,
	) {
		local := arg.Have(
			"the product is locally a fraction",
			"∀p:set(A). p ∈ U ⇒ locally_fraction(R, U, p, «product»)",
			Derive(func(e *Argument) {
				p := e.FixAs[Set[A]]("p")
				inU := e.Assume()
				V, a, b, c, d, common := e.Unpack5As[Set[Set[A]], A, A, A, A](
					GroupPremises(sections, inU, StructureSectionsCommonNeighborhood.Read(ring).At(U, s, t, p)),
					"V",
					"a",
					"b",
					"c",
					"d")
				parts := e.Conjuncts(
					common,
					"V is open",
					"V contains p",
					"V lies in U",
					"a lies in the ring",
					"b lies in the ring",
					"c lies in the ring",
					"d lies in the ring",
					"on V, s is a / b and t is c / d over the common denominator b * d")
				e.Do(Unfold(LocallyFractionDef))
				e.Take(V)
				e.Take(e.TermAs[A]("a * c"))
				e.Take(e.TermAs[A]("b * d"))
				e.Show(
					"the common denominator represents the product",
					SplitConj(
						Case(
							"the neighborhood and coefficients satisfy the carrier conditions",
							By(
								comm_ring.MulIn.Read(ring),
								parts[0],
								parts[1],
								parts[2],
								parts[3],
								parts[4],
								parts[5],
								parts[6])),
						Case(
							"the product agrees with the fraction throughout V",
							Derive(func(f *Argument) {
								q := f.FixAs[Set[A]]("q")
								inV := f.Assume()
								at := f.Conjuncts(
									GroupPremises(inV, parts[7].At(q)),
									"the complement of q is multiplicative",
									"b lies in the complement of q",
									"d lies in the complement of q",
									"the common denominator avoids q",
									"s(q) is the class of a / b",
									"t(q) is the class of c / d")
								f.Show(
									"the common denominator avoids q and the fraction multiplication law applies",
									SplitConj(
										Case(
											"the common denominator avoids q",
											By(at[3])),
										Case(
											"the value is the product of the fractions",
											Simp(Fwd(StructureMulDef)),
											at[4].Rw(),
											at[5].Rw(),
											CondRewrite(),
											BySets(
												parts[3],
												at[1],
												parts[5],
												at[2],
												inV,
												parts[2],
												at[0],
												ring_localization.FractionMulClass.Read(ring).AsFact().At(
													f.TermAs[Set[A]]("R.carrier ∖ q"), a, b, c, d)))))
							}))))
			}))
		empty := arg.Have(
			"the product is empty outside U",
			"∀p:set(A). p ∉ U ⇒ «product»(p) = ∅",
			By(StructureMulDef.Inst[A]().At(arg.TermAs[RingOps[A]]("R"), U, s, t)))
		arg.Show(
			"the product satisfies both defining section conditions",
			Unfold(StructureSectionsDef),
			By(empty, local))
	}),
})}

// StructureSectionNegIn — negating a local fraction negates its numerator
// and keeps its denominator and neighborhood.
var StructureSectionNegIn = structureSectionNegInThm{family.Add(registry.ProofEntry{
	Name: "StructureSectionNegIn",
	Key:  "prop_25acbe265c305bd1",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀U:set(set(A)). ∀s:(set(A) → set(prod(A, A))).",
		Hypotheses: []string{"s ∈ structure_sections(R, U)"},
		Conclusion: "structure_neg(R, U, s) ∈ structure_sections(R, U)",
	}, func(
		arg *Argument,
		ring comm_ring.CommRingFact[on.R],
		U *Expr[Set[Set[A]]],
		s *Arrow[Set[A], Set[Prod[A, A]]],
		section Fact,
	) {
		local := arg.Have(
			"a local representation negates on the same neighborhood",
			"∀p:set(A). p ∈ U ⇒ locally_fraction(R, U, p, structure_neg(R, U, s))",
			Derive(func(e *Argument) {
				p := e.FixAs[Set[A]]("p")
				inU := e.Assume()
				e.Do(Unfold(LocallyFractionDef))
				V, a, b, representation := e.Unpack3As[Set[Set[A]], A, A](
					GroupPremises(section, inU, StructureSectionLocalFraction.Read(ring).At(U, s, p)),
					"V",
					"a",
					"b")
				parts := e.Conjuncts(
					representation,
					"V is open",
					"V contains p",
					"V lies in U",
					"a lies in the ring",
					"b lies in the ring",
					"s is a over b on V")
				e.Take(V)
				e.Take(e.TermAs[A]("-a"))
				e.Take(b)
				e.Show(
					"the negated fraction represents the negated section",
					SplitConj(
						Case(
							"the neighborhood and coefficients remain valid",
							By(comm_ring.NegIn.Read(ring), representation)),
						Case(
							"the fraction law holds at every point",
							Derive(func(f *Argument) {
								q := f.FixAs[Set[A]]("q")
								inV := f.Assume()
								at := f.Conjuncts(
									GroupPremises(inV, parts[5].At(q)),
									"the complement of q is multiplicative",
									"b lies in the complement of q",
									"s(q) is the class of a / b")
								f.Show(
									"the denominator avoids q and the value negates",
									SplitConj(
										Case(
											"the denominator avoids q",
											BySets(at[1])),
										Case(
											"fraction negation negates the numerator",
											Simp(Fwd(StructureNegDef)),
											CondRewrite(),
											at[2].Rw(),
											BySets(
												parts[3],
												at[1],
												inV,
												parts[2],
												at[0],
												ring_localization.FractionNegClass.Read(ring).AsFact().At(
													f.TermAs[Set[A]]("R.carrier ∖ q"), a, b)))))
							}))))
			}))
		empty := arg.Have(
			"the negation is empty outside U",
			"∀p:set(A). p ∉ U ⇒ structure_neg(R, U, s, p) = ∅",
			By(StructureNegDef.Inst[A]().At(arg.TermAs[RingOps[A]]("R"), U, s)))
		arg.Show(
			"these are the defining section conditions",
			Unfold(StructureSectionsDef),
			By(empty, local))
	}),
})}

// SpectrumLocalizationRing — fractions with denominators outside a prime
// form a commutative ring.
var SpectrumLocalizationRing = spectrumLocalizationRingThm{family.Add(registry.ProofEntry{
	Name: "SpectrumLocalizationRing",
	Key:  "prop_39e22f756aa60699",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀p:set(A).",
		Hypotheses: []string{"p ∈ prime_spectrum(R)"},
		Conclusion: "comm_ring_on(localized_ring(R, R.carrier ∖ p))",
	}, func(a *Argument, ring comm_ring.CommRingFact[on.R], p *Expr[Set[A]], point Fact) {
		a.Show(
			"localize at the multiplicative prime complement",
			Simp(Fwd(ring_localization.LocalizedRingDef)),
			By(
				a.Unfolded(point, prime_spectrum.PrimeSpectrumDef),
				local_ring.PrimeComplementMultiplicative.Read(ring).At(p),
				ring_localization.LocalizationRing.Read(ring).AsFact().At(a.TermAs[Set[A]]("R.carrier ∖ p"))))
	}),
})}

// StructureSectionRing — local fraction closure and the ring identities
// in each prime localization make the sections over an open set a ring.
var StructureSectionRing = structureSectionRingThm{family.Add(registry.ProofEntry{
	Name: "StructureSectionRing",
	Key:  "prop_336059c59f029db5",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀U:set(set(A)).",
		Hypotheses: []string{"U ∈ zariski_topology(R)"},
		Conclusion: "comm_ring_on(spec_section_ops(R, U))",
		Abbrev: Abbrev{
			{Name: "sectionRingRecord", Text: "mk_ring(structure_add(R, U), " +
				"    structure_zero(R, U), " +
				"    structure_neg(R, U), " +
				"    structure_mul(R, U), " +
				"    structure_one(R, U), " +
				"    structure_sub(R, U), " +
				"    structure_sections(R, U))"},
			{Name: "sectionAddGroup", Text: "mk_group(structure_add(R, U), " +
				"    structure_zero(R, U), " +
				"    structure_neg(R, U), " +
				"    structure_sections(R, U))"},
		},
	}, func(a *Argument, ring comm_ring.CommRingFact[on.R], U *Expr[Set[Set[A]]], open Fact) {
		R := a.TermAs[RingOps[A]]("R")
		localRings := a.Have(
			"each value is read in its prime localization",
			"∀p:set(A). p ∈ U ⇒ comm_ring_on(localized_ring(R, R.carrier ∖ p))",
			Derive(func(b *Argument) {
				p := b.FixAs[Set[A]]("p")
				inU := b.Assume()
				b.Show(
					"fractions at a prime p form a ring",
					BySets(
						ring,
						inU,
						open,
						ZariskiPointPrime.At(R, U, p),
						prime_spectrum.PrimeSpectrumDef.At(R),
						At(SpectrumLocalizationRing, R, p)))
			}))
		avoidsOne := a.Have(
			"one avoids every prime in U",
			"∀p:set(A). p ∈ U ⇒ R.one ∉ p",
			By(open, ZariskiPointPrime.Inst[A]().At(R, U), ring_ideal.PrimeIdealProper))
		zero := a.Have(
			"the constant zero fraction is a section",
			"structure_zero(R, U) ∈ structure_sections(R, U)",
			Simp(Fwd(StructureZeroDef), Fwd(ring_localization.FractionZeroDef), Rev(FractionSectionDef)),
			By(
				open,
				comm_ring.ZeroIn.Read(ring),
				comm_ring.OneIn.Read(ring),
				avoidsOne,
				At(ConstantFractionSection, R, U, a.TermAs[A]("R.zero"), a.TermAs[A]("R.one"))))
		one := a.Have(
			"the constant unit fraction is a section",
			"structure_one(R, U) ∈ structure_sections(R, U)",
			Simp(Fwd(StructureOneDef), Fwd(ring_localization.FractionOneDef), Rev(FractionSectionDef)),
			By(
				open,
				comm_ring.OneIn.Read(ring),
				avoidsOne,
				At(ConstantFractionSection, R, U, a.TermAs[A]("R.one"), a.TermAs[A]("R.one"))))
		sumAssoc := a.Have(
			"addition associates",
			Statement{
				Binders: "∀x y z:(set(A) → set(prod(A, A))).",
				Hypotheses: []string{
					"x ∈ structure_sections(R, U)",
					"y ∈ structure_sections(R, U)",
					"z ∈ structure_sections(R, U)",
				},
				Conclusion: "structure_add(R, U, x, structure_add(R, U, y, z)) = " +
					"structure_add(R, U, structure_add(R, U, x, y), z)",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[_Section]("x")
				y := b.FixAs[_Section]("y")
				z := b.FixAs[_Section]("z")
				sections := b.Assume()
				pointwise := b.Have(
					"the identity holds at every point",
					"∀p:set(A). "+
						"    structure_add(R, U, x, structure_add(R, U, y, z), p) = "+
						"    structure_add(R, U, structure_add(R, U, x, y), z, p)",
					Derive(func(c *Argument) {
						p := c.FixAs[Set[A]]("p")
						inU := c.Assuming(
							c.TermAs[Bool]("p ∈ U"),
							"outside U both expressions are empty",
							Given(func(d *Argument, _ Fact) {
								d.Show(
									"both values are empty",
									Simp(Fwd(StructureAddDef)),
									Refl())
							}))
						localRing := c.Have(
							"the fractions at p form a ring",
							"comm_ring_on(localized_ring(R, R.carrier ∖ p))",
							By(inU, localRings.At(p)))
						values := c.Have(
							"the section values belong to that ring",
							"x(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p) ∧ "+
								"y(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p) ∧ "+
								"z(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p)",
							By(
								inU,
								sections,
								At(StructureSectionValue, R, U, x, p),
								At(StructureSectionValue, R, U, y, p),
								At(StructureSectionValue, R, U, z, p)))
						c.Show(
							"read the ring law at these values",
							Simp(Fwd(StructureAddDef)),
							By(
								values,
								comm_monoid.AssocOn.Read(comm_ring.AddMonoidOn.Read(localRing)).AsFact().At(
									c.TermAs[Set[Prod[A, A]]]("x(p)"),
									c.TermAs[Set[Prod[A, A]]]("y(p)"),
									c.TermAs[Set[Prod[A, A]]]("z(p)")),
								ring_localization.LocalizedRingDef.At(R, c.TermAs[Set[A]]("R.carrier ∖ p"))))
					}))
				b.Show(
					"the functions agree pointwise",
					By(pointwise))
			}))
		zeroAdds := a.Have(
			"zero is an additive identity",
			Statement{
				Binders:    "∀x:(set(A) → set(prod(A, A))).",
				Hypotheses: []string{"x ∈ structure_sections(R, U)"},
				Conclusion: "structure_add(R, U, structure_zero(R, U), x) = x",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[_Section]("x")
				sections := b.Assume()
				pointwise := b.Have(
					"the identity holds at every point",
					"∀p:set(A). structure_add(R, U, structure_zero(R, U), x, p) = x(p)",
					Derive(func(c *Argument) {
						p := c.FixAs[Set[A]]("p")
						inU := c.Assuming(
							c.TermAs[Bool]("p ∈ U"),
							"outside U the section is empty",
							Given(func(d *Argument, outside Fact) {
								parts := d.Conjuncts(
									d.Unfolded(sections, StructureSectionsDef),
									"x is empty outside U",
									"x is locally a fraction")
								d.Show(
									"both values are empty",
									Simp(Fwd(StructureAddDef), Fwd(StructureZeroDef)),
									By(outside, parts[0].At(p)))
							}))
						localRing := c.Have(
							"the fractions at p form a ring",
							"comm_ring_on(localized_ring(R, R.carrier ∖ p))",
							By(inU, localRings.At(p)))
						values := c.Have(
							"the section values belong to that ring",
							"x(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p)",
							By(inU, sections, At(StructureSectionValue, R, U, x, p)))
						c.Show(
							"read the ring law at these values",
							Simp(Fwd(StructureAddDef), Fwd(StructureZeroDef)),
							By(
								values,
								comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(localRing)).AsFact().At(
									c.TermAs[Set[Prod[A, A]]]("x(p)")),
								ring_localization.LocalizedRingDef.At(R, c.TermAs[Set[A]]("R.carrier ∖ p"))))
					}))
				// Normalized reads the equation of sections pointwise, the form
				// the identity above is stated in. This close and those of the two
				// commutativities and of the multiplicative identity need it; the
				// other four identities meet their goals as stated.
				b.Show(
					"the functions agree pointwise",
					By(Normalized, pointwise))
			}))
		negationAdds := a.Have(
			"negation gives an additive inverse",
			Statement{
				Binders:    "∀x:(set(A) → set(prod(A, A))).",
				Hypotheses: []string{"x ∈ structure_sections(R, U)"},
				Conclusion: "structure_add(R, U, structure_neg(R, U, x), x) = structure_zero(R, U)",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[_Section]("x")
				sections := b.Assume()
				pointwise := b.Have(
					"the identity holds at every point",
					"∀p:set(A). structure_add(R, U, structure_neg(R, U, x), x, p) = structure_zero(R, U, p)",
					Derive(func(c *Argument) {
						p := c.FixAs[Set[A]]("p")
						inU := c.Assuming(
							c.TermAs[Bool]("p ∈ U"),
							"outside U both expressions are empty",
							Given(func(d *Argument, _ Fact) {
								d.Show(
									"both values are empty",
									Simp(Fwd(StructureAddDef), Fwd(StructureNegDef), Fwd(StructureZeroDef)),
									Refl())
							}))
						localRing := c.Have(
							"the fractions at p form a ring",
							"comm_ring_on(localized_ring(R, R.carrier ∖ p))",
							By(inU, localRings.At(p)))
						values := c.Have(
							"the section values belong to that ring",
							"x(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p)",
							By(inU, sections, At(StructureSectionValue, R, U, x, p)))
						c.Show(
							"read the ring law at these values",
							Simp(Fwd(StructureAddDef), Fwd(StructureNegDef), Fwd(StructureZeroDef)),
							By(
								values,
								group.LeftInverseOn.Read(
									abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(localRing))).AsFact().At(
									c.TermAs[Set[Prod[A, A]]]("x(p)")),
								ring_localization.LocalizedRingDef.At(R, c.TermAs[Set[A]]("R.carrier ∖ p")),
								module_record.AdditiveGroupDef.At(
									c.TermAs[RingOps[Set[Prod[A, A]]]]("localized_ring(R, R.carrier ∖ p)"))))
					}))
				b.Show(
					"the functions agree pointwise",
					By(pointwise))
			}))
		sumCommutes := a.Have(
			"addition commutes",
			Statement{
				Binders:    "∀x y:(set(A) → set(prod(A, A))).",
				Hypotheses: []string{"x ∈ structure_sections(R, U)", "y ∈ structure_sections(R, U)"},
				Conclusion: "structure_add(R, U, x, y) = structure_add(R, U, y, x)",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[_Section]("x")
				y := b.FixAs[_Section]("y")
				sections := b.Assume()
				pointwise := b.Have(
					"the identity holds at every point",
					"∀p:set(A). structure_add(R, U, x, y, p) = structure_add(R, U, y, x, p)",
					Derive(func(c *Argument) {
						p := c.FixAs[Set[A]]("p")
						inU := c.Assuming(
							c.TermAs[Bool]("p ∈ U"),
							"outside U both expressions are empty",
							Given(func(d *Argument, _ Fact) {
								d.Show(
									"both values are empty",
									Simp(Fwd(StructureAddDef)),
									Refl())
							}))
						localRing := c.Have(
							"the fractions at p form a ring",
							"comm_ring_on(localized_ring(R, R.carrier ∖ p))",
							By(inU, localRings.At(p)))
						values := c.Have(
							"the section values belong to that ring",
							"x(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p) ∧ "+
								"y(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p)",
							By(inU, sections, At(StructureSectionValue, R, U, x, p), At(StructureSectionValue, R, U, y, p)))
						c.Show(
							"read the ring law at these values",
							Simp(Fwd(StructureAddDef)),
							By(
								values,
								comm_monoid.CommOn.Read(comm_ring.AddMonoidOn.Read(localRing)).AsFact().At(
									c.TermAs[Set[Prod[A, A]]]("x(p)"), c.TermAs[Set[Prod[A, A]]]("y(p)")),
								ring_localization.LocalizedRingDef.At(R, c.TermAs[Set[A]]("R.carrier ∖ p"))))
					}))
				b.Show(
					"the functions agree pointwise",
					By(Normalized, pointwise))
			}))
		productCommutes := a.Have(
			"multiplication commutes",
			Statement{
				Binders:    "∀x y:(set(A) → set(prod(A, A))).",
				Hypotheses: []string{"x ∈ structure_sections(R, U)", "y ∈ structure_sections(R, U)"},
				Conclusion: "structure_mul(R, U, x, y) = structure_mul(R, U, y, x)",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[_Section]("x")
				y := b.FixAs[_Section]("y")
				sections := b.Assume()
				pointwise := b.Have(
					"the identity holds at every point",
					"∀p:set(A). structure_mul(R, U, x, y, p) = structure_mul(R, U, y, x, p)",
					Derive(func(c *Argument) {
						p := c.FixAs[Set[A]]("p")
						inU := c.Assuming(
							c.TermAs[Bool]("p ∈ U"),
							"outside U both expressions are empty",
							Given(func(d *Argument, _ Fact) {
								d.Show(
									"both values are empty",
									Simp(Fwd(StructureMulDef)),
									Refl())
							}))
						localRing := c.Have(
							"the fractions at p form a ring",
							"comm_ring_on(localized_ring(R, R.carrier ∖ p))",
							By(inU, localRings.At(p)))
						values := c.Have(
							"the section values belong to that ring",
							"x(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p) ∧ "+
								"y(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p)",
							By(inU, sections, At(StructureSectionValue, R, U, x, p), At(StructureSectionValue, R, U, y, p)))
						c.Show(
							"read the ring law at these values",
							Simp(Fwd(StructureMulDef)),
							By(
								values,
								comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(localRing)).AsFact().At(
									c.TermAs[Set[Prod[A, A]]]("x(p)"), c.TermAs[Set[Prod[A, A]]]("y(p)")),
								ring_localization.LocalizedRingDef.At(R, c.TermAs[Set[A]]("R.carrier ∖ p"))))
					}))
				b.Show(
					"the functions agree pointwise",
					By(Normalized, pointwise))
			}))
		productAssoc := a.Have(
			"multiplication associates",
			Statement{
				Binders: "∀x y z:(set(A) → set(prod(A, A))).",
				Hypotheses: []string{
					"x ∈ structure_sections(R, U)",
					"y ∈ structure_sections(R, U)",
					"z ∈ structure_sections(R, U)",
				},
				Conclusion: "structure_mul(R, U, x, structure_mul(R, U, y, z)) = " +
					"structure_mul(R, U, structure_mul(R, U, x, y), z)",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[_Section]("x")
				y := b.FixAs[_Section]("y")
				z := b.FixAs[_Section]("z")
				sections := b.Assume()
				pointwise := b.Have(
					"the identity holds at every point",
					"∀p:set(A). "+
						"    structure_mul(R, U, x, structure_mul(R, U, y, z), p) = "+
						"    structure_mul(R, U, structure_mul(R, U, x, y), z, p)",
					Derive(func(c *Argument) {
						p := c.FixAs[Set[A]]("p")
						inU := c.Assuming(
							c.TermAs[Bool]("p ∈ U"),
							"outside U both expressions are empty",
							Given(func(d *Argument, _ Fact) {
								d.Show(
									"both values are empty",
									Simp(Fwd(StructureMulDef)),
									Refl())
							}))
						localRing := c.Have(
							"the fractions at p form a ring",
							"comm_ring_on(localized_ring(R, R.carrier ∖ p))",
							By(inU, localRings.At(p)))
						values := c.Have(
							"the section values belong to that ring",
							"x(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p) ∧ "+
								"y(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p) ∧ "+
								"z(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p)",
							By(
								inU,
								sections,
								At(StructureSectionValue, R, U, x, p),
								At(StructureSectionValue, R, U, y, p),
								At(StructureSectionValue, R, U, z, p)))
						c.Show(
							"read the ring law at these values",
							Simp(Fwd(StructureMulDef)),
							By(
								values,
								comm_monoid.AssocOn.Read(comm_ring.MulMonoidOn.Read(localRing)).AsFact().At(
									c.TermAs[Set[Prod[A, A]]]("x(p)"),
									c.TermAs[Set[Prod[A, A]]]("y(p)"),
									c.TermAs[Set[Prod[A, A]]]("z(p)")),
								ring_localization.LocalizedRingDef.At(R, c.TermAs[Set[A]]("R.carrier ∖ p"))))
					}))
				b.Show(
					"the functions agree pointwise",
					By(pointwise))
			}))
		oneMultiplies := a.Have(
			"one is a multiplicative identity",
			Statement{
				Binders:    "∀x:(set(A) → set(prod(A, A))).",
				Hypotheses: []string{"x ∈ structure_sections(R, U)"},
				Conclusion: "structure_mul(R, U, structure_one(R, U), x) = x",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[_Section]("x")
				sections := b.Assume()
				pointwise := b.Have(
					"the identity holds at every point",
					"∀p:set(A). structure_mul(R, U, structure_one(R, U), x, p) = x(p)",
					Derive(func(c *Argument) {
						p := c.FixAs[Set[A]]("p")
						inU := c.Assuming(
							c.TermAs[Bool]("p ∈ U"),
							"outside U the section is empty",
							Given(func(d *Argument, outside Fact) {
								parts := d.Conjuncts(
									d.Unfolded(sections, StructureSectionsDef),
									"x is empty outside U",
									"x is locally a fraction")
								d.Show(
									"both values are empty",
									Simp(Fwd(StructureMulDef), Fwd(StructureOneDef)),
									By(outside, parts[0].At(p)))
							}))
						localRing := c.Have(
							"the fractions at p form a ring",
							"comm_ring_on(localized_ring(R, R.carrier ∖ p))",
							By(inU, localRings.At(p)))
						values := c.Have(
							"the section values belong to that ring",
							"x(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p)",
							By(inU, sections, At(StructureSectionValue, R, U, x, p)))
						c.Show(
							"read the ring law at these values",
							Simp(Fwd(StructureMulDef), Fwd(StructureOneDef)),
							By(
								values,
								comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(localRing)).AsFact().At(
									c.TermAs[Set[Prod[A, A]]]("x(p)")),
								ring_localization.LocalizedRingDef.At(R, c.TermAs[Set[A]]("R.carrier ∖ p"))))
					}))
				b.Show(
					"the functions agree pointwise",
					By(Normalized, pointwise))
			}))
		distributes := a.Have(
			"multiplication distributes over addition",
			Statement{
				Binders: "∀x y z:(set(A) → set(prod(A, A))).",
				Hypotheses: []string{
					"x ∈ structure_sections(R, U)",
					"y ∈ structure_sections(R, U)",
					"z ∈ structure_sections(R, U)",
				},
				Conclusion: "structure_mul(R, U, x, structure_add(R, U, y, z)) = " +
					"structure_add(R, U, structure_mul(R, U, x, y), structure_mul(R, U, x, z))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[_Section]("x")
				y := b.FixAs[_Section]("y")
				z := b.FixAs[_Section]("z")
				sections := b.Assume()
				pointwise := b.Have(
					"the identity holds at every point",
					"∀p:set(A). "+
						"    structure_mul(R, U, x, structure_add(R, U, y, z), p) = "+
						"    structure_add(R, U, structure_mul(R, U, x, y), structure_mul(R, U, x, z), p)",
					Derive(func(c *Argument) {
						p := c.FixAs[Set[A]]("p")
						inU := c.Assuming(
							c.TermAs[Bool]("p ∈ U"),
							"outside U both expressions are empty",
							Given(func(d *Argument, _ Fact) {
								d.Show(
									"both values are empty",
									Simp(Fwd(StructureMulDef), Fwd(StructureAddDef)),
									Refl())
							}))
						localRing := c.Have(
							"the fractions at p form a ring",
							"comm_ring_on(localized_ring(R, R.carrier ∖ p))",
							By(inU, localRings.At(p)))
						values := c.Have(
							"the section values belong to that ring",
							"x(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p) ∧ "+
								"y(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p) ∧ "+
								"z(p) ∈ ring_localization(R.mul, R.carrier, R.carrier ∖ p)",
							By(
								inU,
								sections,
								At(StructureSectionValue, R, U, x, p),
								At(StructureSectionValue, R, U, y, p),
								At(StructureSectionValue, R, U, z, p)))
						c.Show(
							"read the ring law at these values",
							Simp(Fwd(StructureMulDef), Fwd(StructureAddDef)),
							By(
								values,
								comm_ring.LeftDistribOn.Read(localRing).AsFact().At(
									c.TermAs[Set[Prod[A, A]]]("x(p)"),
									c.TermAs[Set[Prod[A, A]]]("y(p)"),
									c.TermAs[Set[Prod[A, A]]]("z(p)")),
								ring_localization.LocalizedRingDef.At(R, c.TermAs[Set[A]]("R.carrier ∖ p"))))
					}))
				b.Show(
					"the functions agree pointwise",
					By(pointwise))
			}))
		difference := a.Have(
			"subtraction is addition with the negation",
			Statement{
				Binders:    "∀x y:(set(A) → set(prod(A, A))).",
				Hypotheses: []string{"x ∈ structure_sections(R, U)", "y ∈ structure_sections(R, U)"},
				Conclusion: "structure_sub(R, U, x, y) = structure_add(R, U, x, structure_neg(R, U, y))",
			},
			Simp(
				Fwd(StructureSubDef),
				Fwd(StructureAddDef),
				Fwd(StructureNegDef),
				Fwd(ring_localization.FractionSubDef)),
			BySets())
		additiveGroup := a.Have(
			"addition makes the section carrier a group",
			"group_on(«sectionAddGroup»)",
			By(
				group.GroupOn,
				zero,
				StructureSectionAddIn.Read(ring).AsFact().At(U),
				StructureSectionNegIn.Read(ring).AsFact().At(U),
				sumAssoc,
				zeroAdds,
				negationAdds))
		abelian := a.Have(
			"the additive group is abelian",
			"abelian_group_on(«sectionAddGroup»)",
			By(abelian_group.AbelianGroupOn, additiveGroup, sumCommutes))
		additive := a.Have(
			"this is the additive group of the section ring record",
			"abelian_group_on(additive_group(«sectionRingRecord»))",
			By(
				abelian,
				module_record.AdditiveGroupDef,
				module_record.RingAddDef,
				module_record.RingZeroDef,
				module_record.RingNegDef,
				module_record.RingCarrierDef))
		multiplicative := a.Have(
			"multiplication makes the section carrier a commutative monoid",
			"comm_monoid_on(structure_sections(R, U), structure_mul(R, U), structure_one(R, U))",
			By(
				comm_monoid.CommMonoidOn,
				one,
				StructureSectionMulIn.Read(ring).AsFact().At(U),
				productCommutes,
				productAssoc,
				oneMultiplies))
		a.Show(
			"the section ring record satisfies the ring axioms",
			Simp(Fwd(SpecSectionOps)),
			By(comm_ring.CommRingOn, additive, multiplicative, distributes, difference))
	}),
})}

// StructurePresheaf — restriction keeps local fractions and satisfies the
// identity and composition laws.
var StructurePresheaf = structurePresheafThm{family.Add(registry.ProofEntry{
	Name: "StructurePresheaf",
	Key:  "prop_e205930dca49f9c3",
	Build: comm_ring.CommRingOn.Law("presheaf(zariski_topology(R), "+
		"    structure_sections(R), "+
		"    structure_restrict)",
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			identity := a.Have(
				"restriction to the same open set is the identity",
				Statement{
					Binders:    "∀U:set(set(A)). ∀s:(set(A) → set(prod(A, A))).",
					Hypotheses: []string{"U ∈ zariski_topology(R)", "s ∈ structure_sections(R, U)"},
					Conclusion: "structure_restrict(U, U, s) = s",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[Set[A]]]("U")
					b.FixAs[_Section]("s")
					h := b.Conjuncts(
						b.Assume(),
						"U is open",
						"s is a section")
					data := b.Conjuncts(
						b.Unfolded(h[1], StructureSectionsDef),
						"s is empty outside U",
						"s is locally a fraction")
					b.Show(
						"restriction keeps all values in U and both functions are empty elsewhere",
						Simp(Fwd(StructureRestrictDef)),
						BySets(data[0]))
				}))
			composition := a.Have(
				"restriction composes along inclusions",
				Statement{
					Binders: "∀U V W:set(set(A)). ∀s:(set(A) → set(prod(A, A))).",
					Hypotheses: []string{
						"U ∈ zariski_topology(R)",
						"V ∈ zariski_topology(R)",
						"W ∈ zariski_topology(R)",
						"W ⊆ V",
						"V ⊆ U",
						"s ∈ structure_sections(R, U)",
					},
					Conclusion: "structure_restrict(V, W, structure_restrict(U, V, s)) = structure_restrict(U, W, s)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[Set[A]]]("U")
					b.FixAs[Set[Set[A]]]("V")
					b.FixAs[Set[Set[A]]]("W")
					b.FixAs[_Section]("s")
					h := b.Assume()
					b.Show(
						"a point of W is already a point of V",
						Simp(Fwd(StructureRestrictDef)),
						BySets(h))
				}))
			a.Show(
				"the topology, section preservation and restriction laws define a presheaf",
				By(
					presheaf.Presheaf,
					ring,
					prime_spectrum.ZariskiIsTopology.Read(ring),
					At(StructureRestrictIn, a.TermAs[RingOps[A]]("R")),
					identity,
					composition))
		}),
})}

// StructureSectionsLocality — agreement after restriction to a cover of U
// determines a section pointwise, with empty values outside the union.
var StructureSectionsLocality = structureSectionsLocalityThm{family.Add(registry.ProofEntry{
	Name: "StructureSectionsLocality",
	Key:  "prop_bc4292e0c7b062d4",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀U:set(set(A)). ∀V:set(set(set(A))). ∀s t:(set(A) → set(prod(A, A))).",
		Hypotheses: []string{
			"⋃V = U",
			"s ∈ structure_sections(R, U)",
			"t ∈ structure_sections(R, U)",
			"∀W:set(set(A)). W ∈ V ⇒ structure_restrict(U, W, s) = structure_restrict(U, W, t)",
		},
		Conclusion: "s = t",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		U *Expr[Set[Set[A]]],
		V *Expr[Set[Set[Set[A]]]],
		s, t *Arrow[Set[A], Set[Prod[A, A]]],
		h Fact,
	) {
		conditions := a.Conjuncts(
			h,
			"the cover has union U",
			"s is a section",
			"t is a section",
			"the restrictions agree on the cover")
		sData := a.Conjuncts(
			a.Unfolded(conditions[1], StructureSectionsDef),
			"s is empty outside U",
			"s is locally a fraction")
		tData := a.Conjuncts(
			a.Unfolded(conditions[2], StructureSectionsDef),
			"t is empty outside U",
			"t is locally a fraction")
		pointwise := a.Have(
			"the two sections agree at every point",
			"∀p:set(A). s(p) = t(p)",
			Derive(func(b *Argument) {
				p := b.FixAs[Set[A]]("p")
				b.Cases(b.TermAs[Bool]("p ∈ U"))
				b.When(
					"inside U choose a cover member containing the point",
					func(c *Argument, inU Fact) {
						W, contains := c.Obtain(
							"a cover member contains p",
							"∃W:set(set(A)). W ∈ V ∧ p ∈ W",
							BySets(inU, conditions[0]))
						c.Show(
							"agreement of the restrictions gives agreement at p",
							BySets(
								conditions[3].At(W),
								contains,
								StructureRestrictDef.Inst[A]().At(U, W, s, p),
								StructureRestrictDef.Inst[A]().At(U, W, t, p)))
					})
				b.Otherwise(
					"outside U both sections are empty",
					func(c *Argument, outside Fact) {
						c.Show(
							"the values are equal to the empty set",
							By(Normalized, outside, sData[0].At(p), tData[0].At(p)))
					})
			}))
		a.Show(
			"pointwise agreement is equality of sections",
			By(Normalized, pointwise))
	}),
})}

// StructureSectionsGluing — compatible sections on a cover of U glue:
// choose one value at each point, use agreement on overlaps, and inherit
// the chosen section's local fraction representation.
var StructureSectionsGluing = structureSectionsGluingThm{family.Add(registry.ProofEntry{
	Name: "StructureSectionsGluing",
	Key:  "prop_d577cc0ddb09dee4",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀U:set(set(A)). " +
			"∀C:set(set(set(A))). " +
			"∀g:(set(set(A)) → set(A) → set(prod(A, A))).",
		Hypotheses: []string{
			"⋃C = U",
			"∀W:set(set(A)). W ∈ C ⇒ g(W) ∈ structure_sections(R, W)",
			"∀W W₁:set(set(A)). " +
				"    W ∈ C ∧ W₁ ∈ C ⇒ structure_restrict(W, W ∩ W₁, g(W)) = structure_restrict(W₁, W ∩ W₁, g(W₁))",
		},
		Conclusion: "∃s:(set(A) → set(prod(A, A))). " +
			"    s ∈ structure_sections(R, U) ∧ (∀W:set(set(A)). W ∈ C ⇒ structure_restrict(U, W, s) = g(W))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		U *Expr[Set[Set[A]]],
		C *Expr[Set[Set[Set[A]]]],
		g *Arrow[Set[Set[A]], _Section],
		h Fact,
	) {
		parts := a.Conjuncts(
			h,
			"the cover has union U",
			"the prescribed functions are sections",
			"the prescribed sections agree on overlaps")
		cover, sections, compatible := parts[0], parts[1], parts[2]
		s, sDef := a.LetAs[_Section]("s", "λp:set(A). COND(p ∈ U, g(εW:set(set(A)). W ∈ C ∧ p ∈ W)(p), ∅)")
		agree := a.Have(
			"the chosen value agrees with every cover member through the point",
			"∀p:set(A). ∀W:set(set(A)). W ∈ C ∧ p ∈ W ⇒ s(p) = g(W)(p)",
			Derive(func(b *Argument) {
				p := b.FixAs[Set[A]]("p")
				W := b.FixAs[Set[Set[A]]]("W")
				onW := b.Assume()
				T, tDef := b.LetAs[Set[Set[A]]]("T", "εV:set(set(A)). V ∈ C ∧ p ∈ V")
				chosen := b.Have(
					"the selected cover member contains p",
					"T ∈ C ∧ p ∈ T",
					By(HilbertDenoted, tDef, onW))
				values := b.Have(
					"overlap compatibility identifies the two values at p",
					"g(T)(p) = g(W)(p)",
					Derive(func(c *Argument) {
						inOverlap := c.Have(
							"p belongs to the overlap",
							"p ∈ T ∩ W",
							BySets(chosen, onW))
						overlap := c.TermAs[Set[Set[A]]]("T ∩ W")
						c.Show(
							"evaluate the equal restrictions at p",
							By(
								chosen,
								onW,
								inOverlap,
								compatible.At(T, W),
								StructureRestrictDef.At(T, overlap, g.Apply(T), p),
								StructureRestrictDef.At(W, overlap, g.Apply(W), p)))
					}))
				inU := b.Have(
					"every point of a cover member lies in U",
					"p ∈ U",
					BySets(cover, onW))
				b.Show(
					"the glued value is the prescribed value",
					sDef.Rw(),
					tDef.RwRev(),
					By(Normalized, values, inU))
			}))
		a.Take(s)
		a.Do(SplitConj(
			Case(
				"the glued function is locally a fraction and empty outside U",
				Derive(func(b *Argument) {
					sectionData := b.Unfolded(b.Unfolded(sections, StructureSectionsDef), LocallyFractionDef)
					outside := b.Have(
						"the glued function is empty outside U",
						"∀p:set(A). p ∉ U ⇒ s(p) = ∅",
						Derive(func(c *Argument) {
							c.FixAs[Set[A]]("p")
							notInU := c.Assume()
							c.Show(
								"use the empty value",
								sDef.Rw(),
								By(notInU))
						}))
					local := b.Have(
						"a local fraction representation is inherited from a cover member",
						"∀p:set(A). p ∈ U ⇒ locally_fraction(R, U, p, s)",
						Derive(func(c *Argument) {
							p := c.FixAs[Set[A]]("p")
							inU := c.Assume()
							c.Do(Unfold(LocallyFractionDef))
							W, onW := c.ObtainAs[Set[Set[A]]](
								"choose a cover member through p",
								"∃W:set(set(A)). W ∈ C ∧ p ∈ W",
								By(Normalized, cover, inU, set_basic.InUnions.At(C, p)))
							V, numerator, denominator, fraction := c.Obtain3As[Set[Set[A]], A, A](
								"take a local fraction for the prescribed section",
								"∃V:set(set(A)). ∃a b:A. "+
									"    V ∈ zariski_topology(R) ∧ "+
									"    p ∈ V ∧ "+
									"    V ⊆ W ∧ "+
									"    a ∈ R.carrier ∧ "+
									"    b ∈ R.carrier ∧ "+
									"    (∀q:set(A). q ∈ V ⇒ b ∉ q ∧ g(W)(q) = fraction_class(R.carrier, R.carrier ∖ q, a, b))",
								By(onW, sectionData.At(W)))
							c.Take(V)
							c.Take(numerator)
							c.Take(denominator)
							c.Do(SplitConj(
								Case(
									"the same neighborhood lies in U and the fraction has coefficients in R",
									BySets(fraction, onW, cover)),
								Case(
									"the same fraction represents s throughout the neighborhood",
									Derive(func(d *Argument) {
										q := d.FixAs[Set[A]]("q")
										inV := d.Assume()
										d.Show(
											"agreement transfers the fraction representation",
											BySets(fraction, onW, inV, agree.At(q, W)))
									}))))
						}))
					b.Show(
						"these are the defining conditions for a section",
						Unfold(StructureSectionsDef),
						By(outside, local))
				})),
			Case(
				"the glued function restricts to every prescribed section",
				Derive(func(b *Argument) {
					W := b.FixAs[Set[Set[A]]]("W")
					inCover := b.Assume()
					pointwise := b.Have(
						"the restriction has the prescribed value at every point",
						"∀p:set(A). structure_restrict(U, W, s, p) = g(W)(p)",
						Derive(func(c *Argument) {
							p := c.FixAs[Set[A]]("p")
							c.Do(Unfold(StructureRestrictDef))
							c.Cases(c.TermAs[Bool]("p ∈ W"))
							c.When(
								"inside W, agreement gives the prescribed value",
								func(d *Argument, inW Fact) {
									d.Show(
										"use agreement on W",
										By(Normalized, inW, inCover, agree.At(p, W)))
								})
							c.Otherwise(
								"outside W, both functions are empty",
								func(d *Argument, notInW Fact) {
									sectionData := d.Unfolded(sections, StructureSectionsDef)
									d.Show(
										"a section on W is empty outside W",
										By(notInW, inCover, sectionData.At(W)))
								})
						}))
					b.Show(
						"pointwise equality gives equality of functions",
						By(Normalized, pointwise))
				}))))
	}),
})}

// StructureRestrictionHomomorphism — restriction preserves the pointwise
// ring operations and the unit section.
var StructureRestrictionHomomorphism = structureRestrictionHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "StructureRestrictionHomomorphism",
	Key:  "prop_d008c5657a2a5a5",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀U V:set(set(A)).",
		Hypotheses: []string{"U ∈ zariski_topology(R)", "V ∈ zariski_topology(R)", "V ⊆ U"},
		Conclusion: "ring_homomorphism(spec_section_ops(R, U), " +
			"    spec_section_ops(R, V), " +
			"    structure_restrict(U, V))",
	}, func(a *Argument, ring comm_ring.CommRingFact[on.R], U, V *Expr[Set[Set[A]]], h Fact) {
		conditions := a.Conjuncts(
			h,
			"U is open",
			"V is open",
			"V lies in U")
		addition := a.Have(
			"restriction preserves addition",
			Statement{
				Binders:    "∀s t:(set(A) → set(prod(A, A))).",
				Hypotheses: []string{"s ∈ structure_sections(R, U)", "t ∈ structure_sections(R, U)"},
				Conclusion: "structure_restrict(U, V, structure_add(R, U, s, t)) = " +
					"structure_add(R, V, structure_restrict(U, V, s), structure_restrict(U, V, t))",
			},
			Simp(Fwd(StructureRestrictDef), Fwd(StructureAddDef)),
			BySets(conditions[2]))
		multiplication := a.Have(
			"restriction preserves multiplication",
			Statement{
				Binders:    "∀s t:(set(A) → set(prod(A, A))).",
				Hypotheses: []string{"s ∈ structure_sections(R, U)", "t ∈ structure_sections(R, U)"},
				Conclusion: "structure_restrict(U, V, structure_mul(R, U, s, t)) = " +
					"structure_mul(R, V, structure_restrict(U, V, s), structure_restrict(U, V, t))",
			},
			Simp(Fwd(StructureRestrictDef), Fwd(StructureMulDef)),
			BySets(conditions[2]))
		unit := a.Have(
			"restriction preserves the unit section",
			"structure_restrict(U, V, structure_one(R, U)) = structure_one(R, V)",
			Simp(Fwd(StructureRestrictDef), Fwd(StructureOneDef)),
			BySets(conditions[2]))
		R := a.TermAs[RingOps[A]]("R")
		a.Show(
			"section preservation and the pointwise operation laws give a ring homomorphism",
			By(
				ring_homomorphism.RingHomomorphism,
				ring,
				conditions[0],
				conditions[1],
				conditions[2],
				SpecSectionOps.At(R, U),
				SpecSectionOps.At(R, V),
				At(StructureSectionRing, R, U),
				At(StructureSectionRing, R, V),
				At(StructureRestrictIn, R, U, V),
				addition,
				multiplication,
				unit))
	}),
})}

// StructureSheafOfRings — the sections form a sheaf of rings on the
// spectrum.
var StructureSheafOfRings = structureSheafOfRingsThm{family.Add(registry.ProofEntry{
	Name: "StructureSheafOfRings",
	Key:  "prop_9d291dc5d75b55b8",
	Build: comm_ring.CommRingOn.Law("sheaf_of_rings(spec_sheaf(R))",
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			R := a.TermAs[RingOps[A]]("R")
			a.Do(Unfold(locally_ringed_space.SheafOfRings), SplitConj(
				Case(
					"locality and compatible-cover gluing make the section presheaf a sheaf",
					By(
						ring,
						presheaf.Sheaf,
						At(StructurePresheaf, R),
						At(StructureSectionsLocality, R),
						At(StructureSectionsGluing, R))),
				Case(
					"restrictions are ring homomorphisms",
					By(ring, At(StructureRestrictionHomomorphism, R)))))
		}),
})}
