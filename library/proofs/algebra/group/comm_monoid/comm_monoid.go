// comm_monoid.go — a commutative monoid, the commutative monoid on a
// set, and the monoid's two readings; the power is power.go's.
//
// Four parts, marked by banners: the structures and their axioms; what
// the axioms give on the other side; the homomorphic image of a
// commutative monoid; the bridge to the fold mechanism's
// `monoidal_op`. Every law of the monoid is proved once, on a carrier set
// c, and stated beside it on the whole type as the view of that proof
// (CommMonoidAtUniverse; constitution §Structures, "One proof per law").
// The image along a map relates two monoids, each on its own set, and is
// stated on the sets alone. The bridge to the fold mechanism and the
// powers stay on the whole type: a fold and a choice-named identity read
// no carrier.

package comm_monoid

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structures and their axioms
// ---------------------------------------------------------------------------

// CommMonoid — a commutative monoid on a carrier A: an operation that
// commutes and associates, and an element that is its left identity.
// The operation and the identity are the structure's two components;
// an instance names both (`comm_monoid(real_add, &0)`), and every law
// below is stated for arbitrary ones.
var CommMonoid = commMonoidThm{family.DefineStructure(registry.DefEntry{
	Name:  "CommMonoid",
	Key:   "prop_390d0084e8da446d",
	Const: "comm_monoid",
	Type:  "(A → A → A) → A → bool",
	Equations: []string{
		"∀op:(A → A → A). ∀e:A. " +
			"    comm_monoid(op, e) ⇔ " +
			"    (∀x y:A. op(x, y) = op(y, x)) ∧ " +
			"    (∀x y z:A. op(x, op(y, z)) = op(op(x, y), z)) ∧ " +
			"    (∀x:A. op(e, x) = x)",
	},
})}

// CommMonoidOn — `comm_monoid_on(c, op, e)`: a commutative monoid whose
// carrier is the set c rather than the whole type. The set holds the
// identity and is closed under the operation, and the three axioms hold
// for its members. The whole-type monoid is the case c = 𝕌
// (CommMonoidOnUniverse). The carrier comes first, as on every structure
// on a set.
var CommMonoidOn = commMonoidOnThm{family.DefineStructure(registry.DefEntry{
	Name:    "CommMonoidOn",
	Key:     "prop_c15290e1e246963f",
	Const:   "comm_monoid_on",
	Subject: "c",
	Type:    "set(A) → (A → A → A) → A → bool",
	Equations: []string{
		"∀c:set(A). ∀op:(A → A → A). ∀e:A. " +
			"    comm_monoid_on(c, op, e) ⇔ " +
			"    e ∈ c ∧ " +
			"    (∀x y:A. x ∈ c ∧ y ∈ c ⇒ op(x, y) ∈ c) ∧ " +
			"    (∀x y:A. x ∈ c ∧ y ∈ c ⇒ op(x, y) = op(y, x)) ∧ " +
			"    (∀x y z:A. x ∈ c ∧ y ∈ c ∧ z ∈ c ⇒ op(x, op(y, z)) = op(op(x, y), z)) ∧ " +
			"    (∀x:A. x ∈ c ⇒ op(e, x) = x)",
	},
})}

// CommMonoidOnUniverse — a commutative monoid on the whole type is a
// commutative monoid: every membership in 𝕌 holds, so the closure
// conditions ask nothing and the guarded axioms are the axioms.
var CommMonoidOnUniverse = commMonoidOnUniverseThm{family.Add(registry.ProofEntry{
	Name: "CommMonoidOnUniverse",
	Key:  "prop_8ad751ea144b9068",
	Build: family.Theorem("∀op:(A → A → A). ∀e:A. comm_monoid(op, e) ⇔ comm_monoid_on(𝕌, op, e)",
		func(a *Argument, op *Arrow2[A, A, A], e *Expr[A]) {
			a.Show(
				"with every membership in 𝕌 true, the two predicates unfold to the same three axioms",
				Unfold(CommMonoid),
				Unfold(CommMonoidOn),
				Simp(Fwd(set_basic.InUniv)),
				Basic())
		}),
})}

// CommMonoidAtUniverse — the whole-type monoid is the monoid on 𝕌: a
// law of the monoid is proved once on the carrier set, and the
// whole-type member is its view through this door.
var CommMonoidAtUniverse = CommMonoid.AtUniverse(
	CommMonoidOn, CommMonoidOnUniverse, set_basic.InUniv)

// The axioms, each an axiom of the monoid on a set — what a proof cites
// at a comm_monoid_on hypothesis — and, through the view, a law of the
// whole-type monoid, cited at a monoid hypothesis or at an instance. The
// two closure axioms have no whole-type form: on 𝕌 they say nothing.

// IdentityIn — the identity lies in the carrier.
var IdentityIn = identityInThm{family.Add(registry.ProofEntry{
	Name:  "IdentityIn",
	Key:   "prop_5785050fda30ff3",
	Build: CommMonoidOn.Axiom("e ∈ c"),
})}

// OpIn — the carrier is closed under the operation.
var OpIn = opInThm{family.Add(registry.ProofEntry{
	Name: "OpIn",
	Key:  "prop_53a7a532f386c73d",
	Build: CommMonoidOn.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ c",
			"y ∈ c",
		},
		Conclusion: "op(x, y) ∈ c",
	}),
})}

// CommOn — the operation commutes.
var CommOn = commOnThm{family.Add(registry.ProofEntry{
	Name: "CommOn",
	Key:  "prop_c7692d1104742525",
	Build: CommMonoidOn.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ c",
			"y ∈ c",
		},
		Conclusion: "op(x, y) = op(y, x)",
	}),
})}

// Comm — CommOn on the whole type.
var Comm = commThm{family.Add(registry.ProofEntry{
	Name:  "Comm",
	Key:   "prop_819221e4409559e1",
	Build: CommMonoidAtUniverse.Law("∀x y:A. op(x, y) = op(y, x)", CommOn),
})}

// AssocOn — the operation associates.
var AssocOn = assocOnThm{family.Add(registry.ProofEntry{
	Name: "AssocOn",
	Key:  "prop_8cfc22be7295c30b",
	Build: CommMonoidOn.Axiom(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ c",
			"y ∈ c",
			"z ∈ c",
		},
		Conclusion: "op(x, op(y, z)) = op(op(x, y), z)",
	}),
})}

// Assoc — AssocOn on the whole type.
var Assoc = assocThm{family.Add(registry.ProofEntry{
	Name:  "Assoc",
	Key:   "prop_fb3ad5ba31fed2a7",
	Build: CommMonoidAtUniverse.Law("∀x y z:A. op(x, op(y, z)) = op(op(x, y), z)", AssocOn),
})}

// LeftIdentityOn — the identity, from the left.
var LeftIdentityOn = leftIdentityOnThm{family.Add(registry.ProofEntry{
	Name: "LeftIdentityOn",
	Key:  "prop_e9e90281bd9d83a6",
	Build: CommMonoidOn.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ c",
		},
		Conclusion: "op(e, x) = x",
	}),
})}

// LeftIdentity — LeftIdentityOn on the whole type.
var LeftIdentity = leftIdentityThm{family.Add(registry.ProofEntry{
	Name:  "LeftIdentity",
	Key:   "prop_9a6d0c1695ca549f",
	Build: CommMonoidAtUniverse.Law("∀x:A. op(e, x) = x", LeftIdentityOn),
})}

// ---------------------------------------------------------------------------
// What the axioms give
// ---------------------------------------------------------------------------

// RightIdentityOn — the identity from the right: commutativity mirrors
// the axiom.
var RightIdentityOn = rightIdentityOnThm{family.Add(registry.ProofEntry{
	Name: "RightIdentityOn",
	Key:  "prop_1a908a2d7403e455",
	Build: CommMonoidOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ c",
		},
		Conclusion: "op(x, e) = x",
	},
		func(a *Argument, monoid CommMonoidFact[on.C], x *Member[A, on.C]) {
			swap := a.Have(
				"x and e commute",
				"op(x, e) = op(e, x)",
				By(CommOn, monoid, x, IdentityIn))
			a.Show(
				"so it is the left identity",
				swap.Rw(),
				By(LeftIdentityOn, monoid, x))
		}),
})}

// RightIdentity — RightIdentityOn on the whole type.
var RightIdentity = rightIdentityThm{family.Add(registry.ProofEntry{
	Name:  "RightIdentity",
	Key:   "prop_cb6a713572ff823b",
	Build: CommMonoidAtUniverse.Law("∀x:A. op(x, e) = x", RightIdentityOn),
})}

// LeftCommOn — the rearrangement AC-normalization runs on: the outer
// operand may pass the inner one.
var LeftCommOn = leftCommOnThm{family.Add(registry.ProofEntry{
	Name: "LeftCommOn",
	Key:  "prop_d4d86e882c6faa90",
	Build: CommMonoidOn.Law(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ c",
			"y ∈ c",
			"z ∈ c",
		},
		Conclusion: "op(x, op(y, z)) = op(y, op(x, z))",
	},
		func(a *Argument, monoid CommMonoidFact[on.C], x, y, z *Member[A, on.C]) {
			swap := a.Have(
				"x and y commute",
				"op(x, y) = op(y, x)",
				By(CommOn, monoid, x, y, z))
			a.Show(
				"reassociate, commute the inner pair, reassociate back",
				CalcEq(
					Leg(
						a.TermAs[A]("op(op(x, y), z)"),
						"reassociate",
						By(AssocOn, monoid, x, y, z)),
					Leg(
						a.TermAs[A]("op(op(y, x), z)"),
						"commute the inner pair",
						swap.Rw(),
						Basic()),
					FinalLeg(
						"reassociate back",
						By(AssocOn, monoid, x, y, z)),
				))
		}),
})}

// LeftComm — LeftCommOn on the whole type.
var LeftComm = leftCommThm{family.Add(registry.ProofEntry{
	Name:  "LeftComm",
	Key:   "prop_3688aaea15c3747c",
	Build: CommMonoidAtUniverse.Law("∀x y z:A. op(x, op(y, z)) = op(y, op(x, z))", LeftCommOn),
})}

// ---------------------------------------------------------------------------
// The homomorphic image of a commutative monoid
// ---------------------------------------------------------------------------

// ImageCommMonoidOn — the homomorphic image of a commutative monoid is
// one: a map that carries the carrier c of a commutative monoid onto a
// set d, the operation to op₂ and the identity to e₂ makes d a
// commutative monoid under op₂ and e₂. The image holds e₂ as the value
// of the source's identity; each other condition quantifies over points
// of the image, and pulled back along the map it is a condition at the
// values of points of c, where the map's law turns it into the source's
// own.
var ImageCommMonoidOn = imageCommMonoidOnThm{family.Add(registry.ProofEntry{
	Name: "ImageCommMonoidOn",
	Key:  "prop_4c673c6714e8f851",
	Build: family.Theorem(Statement{
		Binders: "∀op:(A → A → A). ∀e:A. ∀c:set(A). ∀op₂:(B → B → B). ∀e₂:B. ∀d:set(B). ∀f:(A → B).",
		Hypotheses: []string{
			"comm_monoid_on(c, op, e)",
			"image(f, c) = d",
			"∀x y:A. x ∈ c ∧ y ∈ c ⇒ f(op(x, y)) = op₂(f(x), f(y))",
			"f(e) = e₂",
		},
		Conclusion: "comm_monoid_on(d, op₂, e₂)",
	},
		func(
			a *Argument,
			op *Arrow2[A, A, A],
			e *Expr[A],
			c *Expr[Set[A]],
			op2 *Arrow2[B, B, B],
			e2 *Expr[B],
			d *Expr[Set[B]],
			f *Arrow[A, B],
			monoid CommMonoidFact[on.C],
			onto, hom, one Fact,
		) {
			identityIn := a.Have(
				"e₂ is f(e), the image of the identity of c",
				"e₂ ∈ image(f, c)",
				one.RwRev(),
				By(set_image.FunInImage, IdentityIn.Read(monoid)))
			closed := a.Have(
				"the operation of two image points is an image point",
				"∀u v:B. u ∈ image(f, c) ∧ v ∈ image(f, c) ⇒ op₂(u, v) ∈ image(f, c)",
				Simp(Fwd(set_image.ForallInImagePair)),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					points := b.Assume()
					b.Show(
						"op₂(f(x), f(y)) is the image of op(x, y), a point of c",
						Simp(Rev(hom)),
						By(set_image.FunInImage, OpIn.Read(monoid), points))
				}))
			commutes := a.Have(
				"the operation commutes at image points",
				"∀u v:B. u ∈ image(f, c) ∧ v ∈ image(f, c) ⇒ op₂(u, v) = op₂(v, u)",
				Simp(Fwd(set_image.ForallInImagePair)),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					b.Assume()
					b.Show(
						"the two sides are the images of op(x, y) and op(y, x), which are equal as op commutes on c",
						Simp(Rev(hom), Fwd(CommOn.Read(monoid))),
						Basic())
				}))
			associates := a.Have(
				"the operation associates at image points",
				Statement{
					Binders: "∀u v w:B.",
					Hypotheses: []string{
						"u ∈ image(f, c)",
						"v ∈ image(f, c)",
						"w ∈ image(f, c)",
					},
					Conclusion: "op₂(u, op₂(v, w)) = op₂(op₂(u, v), w)",
				},
				Simp(Fwd(set_image.ForallInImageTriple)),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					b.FixAs[A]("z")
					b.Assume()
					b.Show(
						"the two sides are the images of op(x, op(y, z)) and "+
							"op(op(x, y), z), which are equal as op associates on c",
						Simp(Rev(hom), Fwd(OpIn.Read(monoid)), Fwd(AssocOn.Read(monoid))),
						Basic())
				}))
			identity := a.Have(
				"e₂ is a left identity at image points",
				"∀u:B. u ∈ image(f, c) ⇒ op₂(e₂, u) = u",
				Simp(Fwd(set_image.ForallInImage)),
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.Assume()
					b.Show(
						"op₂(e₂, f(x)) is op₂(f(e), f(x)), the image of op(e, x), that is of x",
						Simp(Rev(one), Rev(hom), Fwd(IdentityIn.Read(monoid)), Fwd(LeftIdentityOn.Read(monoid))),
						Basic())
				}))
			a.Show(
				"d is the image, and the image meets the five conditions of a commutative monoid",
				onto.RwRev(),
				By(CommMonoidOn, identityIn, closed, commutes, associates, identity))
		}),
})}

// ---------------------------------------------------------------------------
// The bridge to the fold mechanism
// ---------------------------------------------------------------------------
//
// `monoidal_op op` is the fold mechanism's commutative monoid: the same
// three axioms, with the identity named by Hilbert choice
// (`neutral_elem op`) instead of carried as a component. The two readings
// are the same structure, and the bridge runs both ways.

// Neutral — the choice-named identity IS the component. `neutral_elem op`
// is whatever element ε picks among the two-sided identities; e is one
// (LeftIdentity and RightIdentity), so the choice lands on some identity z, and
// op(e, z) is z by LeftIdentity and e by z's own identity law.
var Neutral = neutralThm{family.Add(registry.ProofEntry{
	Name: "Neutral",
	Key:  "prop_f8bb11b928991bf5",
	Build: CommMonoid.Law("neutral_elem(op) = e",
		func(a *Argument, monoid Fact) {
			// Unfolding leaves the ε-term as the goal's left side.
			a.Do(Unfold(monoidal.NeutralElemDef))
			a.Show(
				"an identity is unique",
				By(LeftIdentity, RightIdentity, monoid))
		}),
})}

// Monoidal — a commutative monoid folds: its three axioms are the
// mechanism's three, once the neutral element is known to be e.
var Monoidal = monoidalThm{family.Add(registry.ProofEntry{
	Name: "Monoidal",
	Key:  "prop_feba8b457f1c3d3",
	Build: CommMonoid.Law("monoidal_op(op)",
		func(a *Argument, monoid Fact) {
			a.Do(Unfold(monoidal.MonoidalOpDef))
			a.Show(
				"the three axioms, the neutral element read as e",
				By(Comm, Assoc, LeftIdentity, Neutral, monoid))
		}),
})}

// FromMonoidal — and back: an operation that folds is a commutative
// monoid at its neutral element. Its hypothesis is `monoidal_op`, not
// this chapter's predicate, so it is an ordinary theorem rather than
// a Law; the two readings unfold to the same three clauses, grouped
// differently, and the unfolds are the whole proof.
var FromMonoidal = fromMonoidalThm{family.Add(registry.ProofEntry{
	Name: "FromMonoidal",
	Key:  "prop_41a75033d5cfbc47",
	Build: family.Theorem(Statement{
		Binders: "∀op:(A → A → A).",
		Hypotheses: []string{
			"monoidal_op(op)",
		},
		Conclusion: "comm_monoid(op, neutral_elem(op))",
	},
		Chain(Unfold(CommMonoid), Unfold(monoidal.MonoidalOpDef))),
})}
