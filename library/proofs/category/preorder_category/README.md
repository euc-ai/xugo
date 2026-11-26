# preorder_category — the category of a preorder on a set, with at most one morphism between two objects

The category of a preorder `R` on a set `c` has the points of `c` for
objects and one morphism from `x` to `y` exactly when `R(x, y)`. It is
assembled from hom data in which each hom set holds at most the one
datum `⊤`, so its laws are `⊤ = ⊤` and its morphisms are determined by
their ends. The ordered set `[n]` of the simplex category is the
preorder `≤` on `0 .. n` (`simplex_category.ordinal_category`).

| member | statement |
|---|---|
| `PreorderCategoryDef` | `preorder_category(R, c)`: `category_from_hom` at `c`, the hom set from `x` to `y` holding `⊤` exactly when `R(x, y)` |
| `PreorderCategory` | a preorder gives a category |
| `PreorderCategoryThin` | two morphisms with the same ends are equal — card |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
