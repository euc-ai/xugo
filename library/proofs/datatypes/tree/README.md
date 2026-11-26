# tree — binary trees

A binary tree over `A` is either a `btree_leaf` or a `btree_node` carrying a left
subtree, a label and a right subtree. The chapter mints the type through
the datatype door, the same door `list` uses: `btree(A)` is carved out
of the recursive-type universe `recspace(A)`, and the four principles a
datatype comes with — induction, the recursion schema, the injectivity
of `btree_node` and the distinctness of the two constructors — are derived
there rather than written by hand.

Where `list` is the corpus's one-successor datatype, this is its
two-successor sibling, and that is the whole difference the proofs feel:
an induction step grants a hypothesis per subtree rather than one. In
three of the four proofs below both arrive ambient and a rewrite ladder
reaches its close without naming either; only `FlattenMirror` has to
take them in hand, and its comment says why.

## The operations

Three, by primitive recursion over the two constructors:

| constant | reading |
|---|---|
| `btree_size(t)` | the number of labels: `0` at a leaf, one more than the two subtrees carry between them |
| `btree_mirror(t)` | reflection: the two subtrees swapped, all the way down |
| `btree_flatten(t)` | the labels read out left to right, as a list |

`btree_flatten` is the one that leaves the chapter: it is defined by
`list_append(btree_flatten(l), cons(a, btree_flatten(r)))`, so the tree's theory and the
list's theory meet in it, and the two laws about it are where that
meeting is paid for.

## Reflection

| member | statement |
|---|---|
| `MirrorMirror` | `btree_mirror(btree_mirror(t)) = t` — the swap is its own inverse |
| `SizeMirror` | `btree_size(btree_mirror(t)) = btree_size(t)` — reflection moves labels, never their number |

## Flattening

| member | statement |
|---|---|
| `LengthFlatten` | `list_length(btree_flatten(t)) = btree_size(t)` — reading a tree out is a faithful count, so the chapter's own recursion and the list theory's agree |
| `FlattenMirror` | `btree_flatten(btree_mirror(t)) = list_reverse(btree_flatten(t))` — reflecting a tree reverses its reading |

The framework mechanics (typed cites, recorded deps, the shared family CNF blob,
replay) are the standard ones — see
`library/chapter_constitution.md` and `library/registry/`.
