# functions — maps, and what their properties amount to

This chapter speaks about a map `f : A → B` itself. What `f` does to
sets — what `image(f, ·)` preserves, and what images and preimages tell
you about `f` — is `set_image`'s, which stands on this chapter.

Three questions organize it. First, how are maps built from maps — the
identity and composition, and the laws that make the notation safe to
use. Second, what it means for a map to be injective, surjective or
bijective, where the answer is always the same shape: it means an
inverse exists. Third, when one map factors through another — the same
answer again, since a factor IS a one-sided inverse asked for by name.
Beside them the chapter names the sets a map determines that the corpus
spells everywhere: the preimage of a set and the support of a map.

Each property is stated twice: unrestricted, about a map on the whole of
its type, and relativized, about a map on part of it. They are not two
theorems — the unrestricted one is the relativized one at the
restriction that asks nothing — and keeping the pair adjacent is why the
chapter reads the way it does. That restriction is a SET for the
injectivity and inverse laws, where the guard is `𝕌`, and a bare
PREDICATE for the factoring laws, where it is `λx. ⊤` and no set
vocabulary enters at all.

## The combinators

    I = λx. x                    o = λf g x. f(g(x))

Both are defined outright, here: `IdentityApply` and `ComposeApply` ARE
the two definitions (their equations spell the stand-ins `id` and
`compose`, since the DSL reads `identity_map` and `∘` as notation), and their
pointwise readings are what the definitions' closures normalize to. So
the four laws here have no content beyond those two equations, and
each of the other two proofs is one or two unfoldings. What they say
together is that maps under `∘` form a monoid with `identity_map` as its unit:
composition is running one map after another (`ComposeApply`), the
nesting does not matter (`ComposeAssoc`), `identity_map` returns what it is given
(`IdentityApply`), and composing with `identity_map` changes nothing
(`ComposeIdentity`).

They are meant to be the notation the chapter is written in rather than
a hypothesis it argues from, and their readers are mostly elsewhere:
`set_image` states functoriality through `∘`, and eleven proofs about
lists and about iterated operations reach for the application law.

The two composition laws are stated point-free, as equations between
maps; the two application laws are pointwise, because what happens at a
point is their whole content. The point-free form is available because
normalization η-expands: `f ∘ I = f` and its pointwise reading are one
theorem rather than two.

`ComposeIdentity` is the chapter's first statement whose two occurrences
of one name sit at different types — composing on the left, `identity_map` is the
identity of the target; on the right, of the source. Its statement text
says so, and the entry's own comment explains how.

## Injectivity

A map separates the points of a set `s` when `f(x) = f(y)` holds at
points of `s` only where `x = y`. The chapter names that:

    injective_on(s, f) ⇔ ∀x y. x ∈ s ∧ y ∈ s ∧ f(x) = f(y) ⇒ x = y

(`InjectiveOnDef`), and a map injective outright is one injective on
`𝕌`. The corpus states injectivity through this name, on a set or on
`𝕌`. A fact `injective_on(s, f)` is one atom in a proof's context,
where the formula is a wide ∀ whose conclusion `x = y` matches every
equation a proof is after — the apply rung reaches for it and the
refuter drowns in it — so no closer sees through the name: a proof
that needs the points opens it.

Two things are said about injectivity, and each is said twice.

The first is that the implication may be read as a biconditional
(`InjectiveAlt`, and `InjectiveOnAlt` restricted to the points of a
set). The converse, `x = y ⇒ f(x) = f(y)`, is congruence
and holds of every map, so the biconditional adds nothing about `f`;
what it adds is a form a rewrite can use, which an implication is not.

The second is that injectivity IS a left inverse — a `g` with
`g(f(x)) = x`. One direction is immediate, since `x` is recoverable
from `f(x)`. The other is where the mathematics is, and it is CHOICE:
injectivity says of each point of the target separately that at most
one source lies above it, while a left inverse names all those sources
at once. `InjectiveOnLeftInverse` puts the fibre-by-fibre form on the
page as a section of its own, so the step across it is a named step of
the proof rather than something a refuter did in passing.

`InjectiveLeftInverse` is where the chapter's `_ON_`-pair reading first
does work rather than being observed: the unrestricted law is proved as
the relativized one at `𝕌`, citing its own sibling, and not proved a
second time.

## Surjectivity

A map is onto exactly when it has a right inverse: a `g` that picks, for
each target point, some source landing on it. `SurjectiveRightInverse`
says it for a map on the whole of its type, `SurjectiveOnRightInverse`
for a map from a set `s` to a set `t`. The content is Skolemization —
turning "for every `y` there is an `x`" into "there is a function
choosing the `x`" — which is why a refuter settles both without ever
building the `g`.

The same fact has a second face. A map is onto exactly when quantifying
over its values is the same as quantifying over the target: for `∀` that
is `SurjectiveForall`, for `∃` `SurjectiveExists`. Each has to be
a biconditional in `P`, not merely an implication — one direction says
`f` reaches everything, and it is the arbitrary `P` that forces it.

`SurjectiveOnRightInverse` is the chapter's only outside reader:
`set_image`'s `SubsetImageInj` needs to pick one source per point, and
this is where its choice comes from.

`Cantor` is the one theorem in the chapter saying that a map with a
given property does NOT exist: no map from `s` to the subsets of `s` is
onto them. It is stated the way the diagonal argument proves it — every such
`f` misses some subset of `s`, and the proof names one: the diagonal
set, the points of `s` that `f` sends to a set not containing them. It
is a subset of `s` by construction, and it cannot be `f(x)` for any
`x ∈ s`, since `x` would then lie in `f(x)` exactly when it does not.

## Choosing a value at every point of a set

`ChooseOn` trades a relation that holds for some value at each point of a set, `∀s ∈ S. ∃x. P(s, x)`, for one function meeting it, `∃f. ∀s ∈ S. P(s, f(s))`; `ChooseThreeOn` makes three such choices at once. It is the trade `SurjectiveOnRightInverse` makes, for any relation. The refuter closes it at a relation it cannot see into, so a proof making the trade at a λ of its own cites the law there.

| Member | Statement |
|---|---|
| `ChooseOn` | a relation met by some value at each point of a set is met by one function |
| `ChooseThreeOn` | three such choices at once |

## Bijectivity

Each half of bijectivity buys an inverse on its own side, and neither
buys it uniquely: surjectivity buys a section that is free to choose
among preimages, injectivity a retraction that is unconstrained off the
image. `BijectiveLeftRightInverse` says that holding both conditions at
once is exactly those two maps collapsing into one — a single `g` asked
to do both jobs, which is what removes the slack on either side.

`BijectiveOnLeftRightInverse` says it for a map from a set `s` to a set
`t`, and the relativized form is where the collapse becomes visible
rather than merely true. The statement carries `f` into `t` as a
standing condition, and that condition is what lets the section
surjectivity supplies serve as the retraction too: `g` is asked about
`f(x)` only for `x` in `s`, and `f(x)` lies in `t`, where `g` has an
answer — an answer injectivity on `s` leaves no room to be anything but
`x`. That is why one `g` meets a demand written as three.

## A named inverse on a carrier

`inverse_on(c, f, y)` chooses a point of `c` sent to `y`. Its carrier
comes first, just as in `injective_on(c, f)`. Outside `image(f, c)` the
definition imposes no useful condition; each law that reads a chosen
point therefore keeps the image guard visible.

| member | statement |
|---|---|
| `InverseOnDef` | `inverse_on(c, f, y) = εx. x ∈ c ∧ f(x) = y` |
| `InverseOnLeft` | `injective_on(c, f) ∧ x ∈ c ⇒ inverse_on(c, f, f(x)) = x` |
| `InverseOnRight` | `y ∈ image(f, c) ⇒ f(inverse_on(c, f, y)) = y` |
| `InverseOnIn` | `y ∈ image(f, c) ⇒ inverse_on(c, f, y) ∈ c` |
| `InverseOnInjective` | `injective_on(image(f, c), inverse_on(c, f))` |
| `InverseOnImage` | `injective_on(c, f) ⇒ image(inverse_on(c, f), image(f, c)) = c` |
| `InverseOnUnique` | `(∀x. x ∈ c ⇒ g(f(x)) = x) ∧ y ∈ image(f, c) ⇒ g(y) = inverse_on(c, f, y)` |
| `TwoSidedInverseBijection` | Carrier-preserving maps inverse on both carriers give `injective_on(c, f) ∧ image(f, c) = c'`. |

The right-inverse and membership laws come from the same nonempty
fibre. Injectivity of `f` then makes its chosen point the original
point, giving the left-inverse law. The inverse itself is injective
on the image even when `f` is not: applying `f` recovers its input.
Any left inverse agrees with this choice on the image, by evaluating
it at the chosen source. `TwoSidedInverseBijection` packages the
carrier-preserving inverse equations directly in the form that the
structure isomorphism predicates use.

## Injectivity as a predicate

A proof that keeps injectivity as a HYPOTHESIS holds the atom and asks
three more things of it: where it comes from when the map is the
identity, whether it survives restriction to a part of the set, and
whether it survives composition. Both are relativized,
and the whole-type reading is the one at `𝕌` — the permutations of a
type are the maps injective on `𝕌` and sending `𝕌` onto itself
(`algebra/group/symmetric_group`), which reads both members there.

| member | statement |
|---|---|
| `IdentityInjective` | `injective_on(s, identity_map)` |
| `InjectiveOnSubset` | `injective_on(t, f) ∧ s ⊆ t ⇒ injective_on(s, f)` |
| `InjectiveOnCompose` | `injective_on(t, f) ∧ injective_on(s, g) ∧ (∀x. x ∈ s ⇒ g(x) ∈ t) ⇒ injective_on(s, f ∘ g)` |

That the identity sends `s` onto itself is `set_image`'s
(`ImageI`), and so is the image of a composite (`ImageCompose`):
surjectivity onto a set is spelled `image(f, s) = t`, which needs no
name of its own.

## Factoring

Given `f` and a second map `g`, when does `f` run through `g`? There are
two questions, by the side the new factor is wanted on, and each answer
is a condition on `f` and `g` that never mentions the factor.

On the right, `f = g ∘ h` is solvable exactly when every value `f` takes
is already a value of `g` — nothing about HOW `f` takes them matters, so
the content is a trade of quantifiers. On the left, `f = h ∘ g` is
solvable exactly when `f` cannot tell apart two points `g` identifies;
here `h` must be built, one value per fibre of `g`, and building it
across all fibres at once is choice. `FactorsLeftGen` puts that fibre
form on the page as a section, the same way `InjectiveOnLeftInverse`
does — the two members share one architecture, and in both the choice
step is the only non-formal move.

Each question is asked twice, over the points a predicate admits and
over all of them. `FactorsLeft` is the unrestricted law read at the
guard that admits every point; that guard is a bare predicate rather
than a set, so what discharges it is β-reduction and no membership law
enters.

## Preimages

The chapter names the preimage, cut to a source set:

    preimage_on(s, f, t) = {x | x ∈ s ∧ f(x) ∈ t}

(`PreimageOnDef`); the whole preimage is `preimage_on(𝕌, f, t)`, and
statements spell every preimage through this name. It is in the set
driver's vocabulary, so `BySets` reads it as its membership condition.

What pulling back says about `f` is `set_image`'s: asked this chapter's
two questions, `t ↦ preimage_on(s, f, t)` is injective exactly when `f`
is surjective and surjective exactly when `f` is injective, and those
laws sit there beside the same questions asked of `image(f, ·)`.

| member | statement |
|---|---|
| `PreimageOnDef` | `preimage_on(s, f, t) = {x \| x ∈ s ∧ f(x) ∈ t}` |

## Supports

The support of a map `f` relative to a value `zero` is the set of
points where `f` is not `zero`:

    fun_support(zero, f) = {x | f(x) ≠ zero}

(`FunSupportDef`). The corpus spells every support through this name —
of a coefficient sequence, an exponent vector, a divisor, a finitely
supported function — and like `preimage_on` its definition declares
that the closers read membership in it as its condition
(`MembershipRead`): `x ∈ fun_support(zero, f)` is `f(x) ≠ zero` to the
set driver, the refuter and the arithmetic closer alike, so a proof
cites nothing to read it; `InFunSupport` states that reading for a
rewrite or an instance. The zero is always written: a support
relative to a value other than a record's own zero is as common as one
relative to it.

| member | statement |
|---|---|
| `FunSupportDef` | `fun_support(zero, f) = {x \| f(x) ≠ zero}` |
| `InFunSupport` | `x ∈ fun_support(zero, f) ⇔ f(x) ≠ zero` |

## Normalizing a map off a set

A map on a type carries values outside the set it is meant on, and two
maps meant on one set differ there without differing in substance.
`normalize_on(S, z, f)` pins a map to one default `z` off `S`, so that
the maps meant on `S`, normalized, are equal exactly when they agree
on `S`: the device by which a class of maps on a set becomes a set of
maps whose equality is extensional. The default is the caller's —
`junk`, minted here, or a zero. A composite of normalized maps is
normalized again, since `g ∘ f` off `S` is `g` at the default and not
the default; on `S` the inner normalization is invisible.

| member | statement |
|---|---|
| `JunkDef` | `junk = εx. ⊤` |
| `NormalizeOnDef` | `normalize_on(S, z, f) = λx. COND(x ∈ S, f(x), z)` |
| `NormalizeOnIn` | `x ∈ S ⇒ normalize_on(S, z, f, x) = f(x)` |
| `NormalizeOnOut` | `x ∉ S ⇒ normalize_on(S, z, f, x) = z` |
| `NormalizeOnEqIff` | `normalize_on(S, z, f) = normalize_on(S, z, g) ⇔ ∀x. x ∈ S ⇒ f(x) = g(x)` |
| `NormalizedEqIff` | `normalize_on(S, z, f) = f ∧ normalize_on(S, z, g) = g ⇒ (f = g ⇔ ∀x. x ∈ S ⇒ f(x) = g(x))` |
| `NormalizeOnIdempotent` | `normalize_on(S, z, normalize_on(S, z, f)) = normalize_on(S, z, f)` |
| `NormalizeOnComposeInner` | `normalize_on(S, w, g ∘ normalize_on(S, z, f)) = normalize_on(S, w, g ∘ f)` |

## Mechanics

`Unfold` of one of the two combinators is the only closer the
combinators file needs: each of its statements IS one of the two
defining equations, read in one direction or the other.

`BySets()` — the closer the sibling set chapters use — opens the set
constructors before refuting the resulting formula. Many statements
here need only that refutation, since they name no set constructor.
The named inverse laws also use `By` with explicit premises: the
choice step exhibits the fibre, and its membership and value are then
read from the chosen conjunction.

Where a statement mentions `∘`, the order matters — `Unfold(ComposeApply)`
first, whether or not a set constructor is present — and `vocab.go`
says why at the closer. `injective_on` is opened the same way, by
`Unfold(InjectiveOnDef)` ahead of the closer, since the set driver's
vocabulary is the set constructors and the predicate is not one;
`preimage_on` and `fun_support` are set constructors and need no opening. Where
a section keeps its premises named, the opening is narrower: one fact
by `a.Unfolded(h, InjectiveOnDef)`, the goal alone by
`Simp(Fwd(InjectiveOnDef))`.

The members that are more than one closer call fall into four shapes.

Some SPLIT their biconditional and close each arm separately, because
the closer that declines the whole statement takes each half without
complaint: `BijectiveOnLeftRightInverse`. Some pass through a STATED
INTERMEDIATE that deserves to be on the page: `InjectiveOnLeftInverse`
and `FactorsLeftGen` each state the fibre form as a section of its own.
Some are GROUND CITES of a sibling at the guard that asks nothing —
`InjectiveLeftInverse` and `FactorsLeft`; what each needs alongside the
cite varies with what its guards are made of, nothing at all for
`FactorsLeft` (β-reduction discharges a predicate) and one law about
`𝕌` for `InjectiveLeftInverse`. And two make ONE MOVE before they
close: `FactorsRight` unfolds, and `Cantor` names its witness.

`vocab.go` states the engine fact behind that last law beside the
closer: `BySets()` unfolds the set constructors, so a guard like
`x ∈ 𝕌` dissolves under it without a law being named, where a `By` —
which ends in a refutation — has to be handed one.

## Overriding a map on a set

`override_on(K, f, g)` takes f's values on K and g's off K
(`OverrideOnDef`); `normalize_on` is the case of a constant g. The
restriction of a map v to K with the other points pinned to defaults z
is `override_on(K, v, z)`, and it forgets exactly the values off K: two
maps restrict to the same map exactly when they agree on K
(`agree_on(K, v)`, `AgreeOnDef`). Two overrides compose to one on the
union, the outer one winning where they overlap.

| Member | Statement |
|---|---|
| `OverrideOnDef` | `override_on(K, f, g) = λx. COND(x ∈ K, f(x), g(x))` |
| `AgreeOnDef` | `agree_on(K, v) = {w \| ∀x. x ∈ K ⇒ w(x) = v(x)}` |
| `OverrideOnAgree` | `override_on(K, v, z) = override_on(K, w, z) ⇔ w ∈ agree_on(K, v)` — card |
| `OverrideOnOverride` | `override_on(K, f, override_on(L, g, h)) = override_on(K ∪ L, override_on(K, f, g), h)` — card |
