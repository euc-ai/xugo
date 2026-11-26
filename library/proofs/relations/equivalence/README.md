# relations/equivalence — equivalences on a type and on a set, their classes and quotients, and partitions

A binary relation is **reflexive** when every point stands in it to
itself, **symmetric** when it reads the same backwards, **transitive**
when two of its steps are one, and an **equivalence** when it is all
three. The equivalence is stated as a structure whose one component is
the relation: `equivalence(R)` is the predicate, and a law here is
`equivalence(R) ⇒ body` with the hypothesis handed to the proof. It is
the case c = 𝕌 of the equivalence on a set, below, and its three laws
`Reflexive`, `Symmetric`, `Transitive` are that structure's axioms read
on the whole type (constitution §Structures).

The chapter's subject is what an equivalence does to the set it lives
on. The **class** of a point, `equivalence_class(R, x)`, is the set of points x
is related to; under an equivalence a point lies in its own class, two
classes are equal exactly when their points are related, and two
classes are equal or disjoint. Those three facts are the partition
theorem in one direction: the classes, taken together, partition the
type.

A **partition**, `set_partition(P)`, is a family of sets with no empty
block, every point in some block, and two blocks that share a point
being one block. The constant carries the `set_` prefix because the
bare word belongs to more than one domain — a partition of an integer is
not this notion. It is stated as a structure too, over the family, with
those three clauses as its axioms. A partition induces a relation,
`same_block(P, x, y)`: some block holds both points. That it is an
equivalence is the partition theorem in the other direction.

The uniqueness clause of a partition is stated as "two blocks sharing a
point are one block", the pointwise form, rather than as a unique
existence; the two are the same axiom, and the pointwise one is the one
a proof reads.

An equivalence is usually met on a SET, not on a type: the cosets of a
subgroup are the classes of "differ by a member of the subgroup" on the
group's carrier, the fractions of a ring the classes of "equal cross
products" on its pairs, the homotopy classes of spheres those of
"homotopic" on the spheres. The relation is defined on the type and is an
equivalence only on the set. `equivalence_on(c, R)` asks the three axioms
of the points of c and of nothing else; the whole-type equivalence is the
case c = 𝕌, and every law of it is read off the law on the set
(constitution §Structures, "One proof per law").

The quotient of c is then taken of the relation RESTRICTED to c,
`relation_on(c, R)`: two points related when both lie in c and R relates
them. Its classes are the classes inside c, whatever R does outside, and
`quotient_on(c, R)` is the set of them, the image of c under the class
map — a set of subsets of c, which no type has to carry, since c and R are
variables. A quotient another chapter builds is this constant at its
relation. Where c is closed under R — a point related to a point of c
lies in c, as a coset of a subgroup lies in the group — the class inside c
is the class itself (`ClassOnClosed`), and the quotient is the image of c
under the unrestricted class map (`QuotientOnClosed`).

A map out of the quotient is a map out of c that RESPECTS the relation,
`respects_on(c, R, f)`, read at a chosen member of each class:
`induced_map(f, s)` is f at a member of s chosen by ε. Nothing is lost by
the choice — on a class f takes one value — and nothing about a quotient
needs it otherwise: its members are read through their representatives
(`InQuotientOn`, `ForallInQuotientOn`), and two of them are compared by
whether their representatives are related (`ClassOnEqIff`).

## The equivalence relation

| member | statement |
|---|---|
| `ReflexiveDef` | `reflexive(R) ⇔ ∀x. R(x, x)` |
| `SymmetricDef` | `symmetric(R) ⇔ ∀x y. R(x, y) ⇒ R(y, x)` |
| `TransitiveDef` | `transitive(R) ⇔ ∀x y z. R(x, y) ∧ R(y, z) ⇒ R(x, z)` |
| `Equivalence` | `equivalence(R) ⇔ reflexive(R) ∧ symmetric(R) ∧ transitive(R)` |
| `Reflexive` | `R(x, x)` |
| `Symmetric` | `R(x, y) ⇒ R(y, x)` |
| `Transitive` | `R(x, y) ∧ R(y, z) ⇒ R(x, z)` |

The three laws are views of the axioms of the equivalence on a set at
𝕌, below.

## The equivalence on a set

| member | statement |
|---|---|
| `EquivalenceOn` | `equivalence_on(c, R)` ⇔ R is reflexive, symmetric and transitive at the points of c |
| `ReflexiveOn` | `x ∈ c ⇒ R(x, x)` |
| `SymmetricOn` | `x ∈ c ∧ y ∈ c ⇒ R(x, y) ⇒ R(y, x)` |
| `TransitiveOn` | `x ∈ c ∧ y ∈ c ∧ z ∈ c ⇒ R(x, y) ∧ R(y, z) ⇒ R(x, z)` |
| `EquivalenceOnUniverse` | `equivalence(R) ⇔ equivalence_on(𝕌, R)` |
| `EquivalenceOnMono` | `equivalence_on(c, R) ⇒ (d ⊆ c ⇒ equivalence_on(d, R))` |
| `SymmetricOnDef` | `symmetric_on(c, R) ⇔ ∀x y. x ∈ c ∧ y ∈ c ∧ R(x, y) ⇒ R(y, x)`: symmetry at the points of c alone, the hypothesis a relation needs for its closure on c to be an equivalence there |

## The quotient of a set

| member | statement |
|---|---|
| `RelationOnDef` | `relation_on(c, R, x, y) ⇔ x ∈ c ∧ y ∈ c ∧ R(x, y)` |
| `QuotientOnDef` | `quotient_on(c, R) = image(equivalence_class(relation_on(c, R)), c)` |
| `InQuotientOn` | `s ∈ quotient_on(c, R) ⇔ ∃x. s = equivalence_class(relation_on(c, R), x) ∧ x ∈ c` |
| `ClassInQuotientOn` | `x ∈ c ⇒ equivalence_class(relation_on(c, R), x) ∈ quotient_on(c, R)` |
| `ForallInQuotientOn` | `(∀s. s ∈ quotient_on(c, R) ⇒ P(s)) ⇔ ∀x. x ∈ c ⇒ P(equivalence_class(relation_on(c, R), x))` |
| `ForallInQuotientOnPair` | the same for two members and two points |
| `ExistsInQuotientOn` | `(∃s. s ∈ quotient_on(c, R) ∧ P(s)) ⇔ ∃x. x ∈ c ∧ P(equivalence_class(relation_on(c, R), x))` |
| `QuotientOnFinite` | `finite(c) ⇒ finite(quotient_on(c, R))` |

These hold for any relation: the quotient is an image, and they are the
image laws at the class map.

## The class of a point

| member | statement |
|---|---|
| `EquivalenceClassDef` | `equivalence_class(R, x) = {y \| R(x, y)}` |
| `InClass` | `y ∈ equivalence_class(R, x) ⇔ R(x, y)` |
| `ChosenRepresentative` | `R(x, x) ⇒ R(x, εy. y ∈ equivalence_class(R, x))` |

`InClass` and `ChosenRepresentative` hold for any relation and are stated
without the structure: the first is the membership reading every later
member reads a class through, the second the point a choice of
representative picks, related to x as soon as x is related to itself.

## The class inside a set

| member | statement |
|---|---|
| `InClassOn` | `y ∈ equivalence_class(relation_on(c, R), x) ⇔ x ∈ c ∧ y ∈ c ∧ R(x, y)` |
| `ClassOnSubset` | `equivalence_class(relation_on(c, R), x) ⊆ c` |
| `ClassOnClosed` | `x ∈ c ∧ (∀y. R(x, y) ⇒ y ∈ c) ⇒ equivalence_class(relation_on(c, R), x) = equivalence_class(R, x)` |
| `ClassOnUniverse` | `equivalence_class(relation_on(𝕌, R), x) = equivalence_class(R, x)` |
| `QuotientOnClosed` | `(∀x y. x ∈ c ∧ R(x, y) ⇒ y ∈ c) ⇒ quotient_on(c, R) = image(equivalence_class(R), c)` |
| `ClassOwnOn` | `equivalence_on(c, R) ⇒ (x ∈ c ⇒ x ∈ equivalence_class(relation_on(c, R), x))` |
| `ClassOnEqIff` | `equivalence_on(c, R) ⇒ (x ∈ c ∧ y ∈ c ⇒ (equivalence_class(relation_on(c, R), x) = equivalence_class(relation_on(c, R), y) ⇔ R(x, y)))` |
| `ClassOnDisjointOrEqual` | under the same, the two classes are equal or disjoint |
| `QuotientOnCovers` | `equivalence_on(c, R) ⇒ ⋃quotient_on(c, R) = c` |
| `QuotientOnDisjointOrEqual` | `equivalence_on(c, R) ⇒ (s ∈ quotient_on(c, R) ∧ t ∈ quotient_on(c, R) ⇒ s = t ∨ disjoint(s, t))` |
| `InQuotientOnClosed` | c closed under R ⇒ (`s ∈ quotient_on(c, R)` ⇔ ∃x. `s = equivalence_class(R, x)` ∧ `x ∈ c`) |
| `ClassInQuotientOnClosed` | c closed under R ⇒ (`x ∈ c ⇒ equivalence_class(R, x) ∈ quotient_on(c, R)`) |
| `ClassEqIffClosed` | `equivalence_on(c, R)` ∧ c closed under R ⇒ (`x ∈ c ∧ y ∈ c ⇒ (equivalence_class(R, x) = equivalence_class(R, y) ⇔ R(x, y))`) |

The first five hold for any relation; the rest are laws of the
equivalence on c, and say that its quotient partitions c into the classes,
two points sharing one exactly when they are related. The last three are
the forms a chapter building a quotient reads: its relation keeps the
carrier closed, so its classes are the relation's own, and its membership
reading and its class law are each one cite.

On the whole type the same three laws are those at c = 𝕌, where the
class inside 𝕌 is the class (`ClassOnUniverse`):

| member | statement |
|---|---|
| `ClassOwn` | `x ∈ equivalence_class(R, x)` |
| `ClassEqIff` | `equivalence_class(R, x) = equivalence_class(R, y) ⇔ R(x, y)` |
| `ClassesDisjointOrEqual` | `equivalence_class(R, x) = equivalence_class(R, y) ∨ disjoint(equivalence_class(R, x), equivalence_class(R, y))` |

## Partitions

| member | statement |
|---|---|
| `SetPartition` | `set_partition(P)` ⇔ no block is empty, every point lies in a block, two blocks sharing a point are one block |
| `BlockNonempty` | `c ∈ P ⇒ c ≠ ∅` |
| `BlocksCover` | `∃c. c ∈ P ∧ x ∈ c` |
| `BlocksOverlapEqual` | `c ∈ P ∧ d ∈ P ∧ x ∈ c ∧ x ∈ d ⇒ c = d` |
| `SameBlockDef` | `same_block(P, x, y) ⇔ ∃c. c ∈ P ∧ x ∈ c ∧ y ∈ c` |

## The partition theorem

| member | statement |
|---|---|
| `ClassesPartition` | `equivalence(R) ⇒ set_partition(image(equivalence_class(R), 𝕌))` |
| `PartitionEquivalence` | `set_partition(P) ⇒ equivalence(same_block(P))` |

The family of classes is written as the range of the class map,
`image(equivalence_class(R), 𝕌)`, and needs no constant of its own.
`ClassesPartition` reads its three clauses off representatives: a
block is the class of a point that lies in it, every point lies in its
own class, and two classes sharing a point are equal because classes
are equal or disjoint.

## The two constructions are inverse

Going from a partition to its relation and back to the classes returns
the partition, and going from an equivalence to its classes and back to
the relation returns the equivalence — so the two theorems above are the
two halves of one correspondence. The first round trip stands on a
lemma worth its own name: under a partition's relation, the class of a
point is the block that holds it.

| member | statement |
|---|---|
| `BlockIsClass` | `set_partition(P) ⇒ (c ∈ P ∧ x ∈ c ⇒ equivalence_class(same_block(P), x) = c)` |
| `ClassesOfSameBlock` | `set_partition(P) ⇒ image(equivalence_class(same_block(P)), 𝕌) = P` |
| `SameBlockOfClasses` | `equivalence(R) ⇒ same_block(image(equivalence_class(R), 𝕌)) = R` |

## Counting by classes

The classes cut the set they live on into blocks; when the blocks all
have one size, counting the set is counting the blocks. On a set c with
an equivalence on it the count needs nothing more (`CountByClassesOn`).
The whole-type form counts a finite set s CLOSED under an equivalence on
the type — the classes of its points then lie inside it and cover it —
so that it reads at a finite part of an infinite type: a finite subgroup
of a group, cut into the cosets of a smaller one, is Lagrange's theorem
(`algebra/group/group`).

| member | statement |
|---|---|
| `CountByClassesOn` | `equivalence_on(c, R) ⇒ finite(c) ∧ (∀x. x ∈ c ⇒ has_size(equivalence_class(relation_on(c, R), x), m)) ⇒ card(c) = m * card(quotient_on(c, R))` |
| `CountByClasses` | `equivalence(R) ⇒ finite(s) ∧ (∀x y. x ∈ s ∧ R(x, y) ⇒ y ∈ s) ∧ (∀x. x ∈ s ⇒ has_size(equivalence_class(R, x), m)) ⇒ card(s) = m * card(image(equivalence_class(R), s))` |

The count is the cardinality chapter's `HasSizeUnions`, read at the
quotient. The whole-type form is the count on s: an equivalence is one on
every set, and s being closed under it, its quotient is the image of s
under the class map.

## The value of a map on a class

| member | statement |
|---|---|
| `RespectsOnDef` | `respects_on(c, R, f) ⇔ ∀x y. x ∈ c ∧ y ∈ c ∧ R(x, y) ⇒ f(x) = f(y)` |
| `InducedMapDef` | `induced_map(f, s) = f(εx. x ∈ s)` |
| `InducedMapClass` | `equivalence_on(c, R) ⇒ (respects_on(c, R, f) ⇒ (x ∈ c ⇒ induced_map(f, equivalence_class(relation_on(c, R), x)) = f(x)))` |

The induced map is the lift of f to the quotient: on the class of x it
is f(x), whichever member was chosen.

## Who reads them

`transitive` is read by `relations/closure`, which states that taking
the transitive closure changes nothing exactly when the relation was
already transitive. The equivalence on the whole type has instances in
the chapters that define their relations: congruence modulo m on ℤ
(`int_congruence.CongruenceEquivalence`, whose classes are the residue
classes), the equality of slopes that the construction of the
non-negative reals quotients by (`eudoxus_slope.NaddEqEquivalence`), and the
equality of pairs that the construction of the reals quotients by
(`nonneg_real_formal_diff.TrealEqEquivalence`).

The equivalence on a set has its instances where a quotient is taken of
a carrier, and each such quotient is `quotient_on` at its relation:
lying in a point's left coset of a subgroup (`group.CosetEquivalenceOn`;
the cosets `left_cosets(c, h)`, and through them the quotient rings,
the quotient modules and homology), equal cross products of fractions
(`ring_localization.FractionEquivalenceOn`; the ring of fractions),
homotopy of spheres and of edges (the homotopy groups of a Kan complex
and the morphisms of the homotopy category of a quasi-category), and
being a nonzero multiple of an invertible lattice pair (Pic⁰ of a
curve). Every law here applies to them.

The framework mechanics (typed cites, recorded deps, the shared family CNF blob,
replay) are the standard ones — see
`library/chapter_constitution.md` and `library/registry/`.
