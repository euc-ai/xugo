# yoneda — the Yoneda lemma in its element form

The Yoneda lemma is stated in its element form. For a presheaf `P` on
`C`, a functor from the opposite of `C` into the sets of a type `B`, a
natural family assigns to each morphism `g: x → c` an element
`α(x, g)` of `P(x)`, precomposition with `f: y → x` acting as `P(f)`.
Such a family is determined by `α(c, 1_c)`, and every element `u` of
`P(c)` arises, from the family `g ↦ P(g)(u)`. The type `B` is free:
the lemma compares the hom sets of `C` with the sets `P(x)` without
asking them to share a type. The standard simplex `Δⁿ`, whose simplices
are monotone maps, names the simplices of any simplicial set by the
same argument, unfolded there (`simplicial_operator.SimplexYoneda`).

## The lemma

| member | statement |
|---|---|
| `yonedaFamilyDef` | `yoneda_family(C, c, P, α)`: `α(x, g) ∈ P(x)` for `g: x → c`, and `α(y, g ∘ f) = P(f)(α(x, g))` |
| `yonedaFamilySetDef` | `yoneda_family_set(C, c, P)`: the natural families, normalized with `junk` off the objects and off each hom set |
| `yonedaElementDef`, `yonedaInverseDef` | `yoneda_element(C, c, α) = α(c, 1_c)`; `yoneda_inverse(C, c, P, u)`: `g ↦ P(g)(u)`, normalized |
| `YonedaFamilyFromElement` | a natural family is determined by its element: `α(x, g) = P(g)(α(c, 1_c))` |
| `YonedaLemma` | for a presheaf `P` and an object `c`, `yoneda_element` is a bijection from the natural families onto `P(c)`, inverted by `yoneda_inverse` |
| `YonedaNatural` | the correspondence is natural in `c`: a natural family read along `h: c → c'` has `P(h)` of its element for its element |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
