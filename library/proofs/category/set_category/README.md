# set_category — the category of the subsets of a type, with the maps between them

The objects of `set_category` are all the sets of one type `M`, and a
morphism from `S` to `T` is a map `M → M` carrying `S` into `T`,
normalized with `junk` off `S`: two maps agreeing on `S` are one
morphism, as a function between sets is determined by its values on
its domain. The identity at `S` is the identity map normalized, and
the composite of `f : S → T` and `g : T → V` is `g ∘ f` normalized
again, since off `S` the composite is `g` at `junk` rather than
`junk`. The category is assembled from this hom data
(`category.CategoryFromHom`). Identity and composite closure, the
unit laws, and associativity are checked on the source carrier using
normalization.

The category is one per type: a set of a type `M` is an object of
`set_category⟨M⟩`, and a set of another type belongs to another
category. This is where the corpus's types stand in for universes —
each type carries its own category of sets, and a statement about
"the category of sets" is a statement about every such category at
once, polymorphic in `M`. A limit whose index set lives in another type
is stated under a hypothesis that `M` has room for it.

## The category and its isomorphisms

| member | statement |
|---|---|
| `SetCategoryDef` | `set_category`: `category_from_hom` at every subset of `M`, the normalized maps from `S` into `T`, the normalized identity and the normalized composite |
| `SetCategory` | `category(set_category)` |
| `SetIsomorphismIff` | a morphism `mk_morphism(S, T, f)` is an isomorphism ⇔ `f` carries `S` into `T`, is normalized off `S`, is one-to-one on `S` and has image `T` |

## Elements: morphisms and functors evaluated

| member | statement |
|---|---|
| `SetMorphismMapsInto` | a morphism of sets from `S` to `T` carries each element of `S` into `T` |
| `SetIdentityValue`, `SetComposeValue` | the identity of sets at `S` fixes each element of `S`; the composite `g ∘ f` takes an element `t` of the source of `f` to `g(f(t))` |
| `SetFunctorMapsInto` | a functor into the sets carries an element of the image of the source of `f` into the image of its target |
| `SetFunctorIdentityValue`, `SetFunctorComposeValue` | a functor into the sets fixes the elements of `F(x)` under `F(1_x)`, and evaluates `F(g ∘ f)` as `F(g)` after `F(f)`; a presheaf reads them at `opposite_category(C)` |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
