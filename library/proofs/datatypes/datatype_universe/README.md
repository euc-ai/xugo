# datatype_universe — the recursive-type universe

Every type the datatype door (`family.DefineData`) introduces — lists, options, trees of any
shape — is carved out of one universe: `recspace(A)`. A tree is a node
`recspace_node(c, i, r)` with a numeric tag `c`,
a label `i` of the parameter type, and countably many children `r(n)`
(unused positions hold the empty tree `recspace_bottom`). The chapter is the
theory of that universe, in the order it is built:

Every constant named here is defined in the chapter itself
(`definitions.go`, and `family_cons` beside its consumers), in the order the
universe is built.

- **The injective encodings.** A tree is represented as a predicate on
  pairs `(num, A)`. Two pairing functions on ℕ — `num_pair(x, y) =
  2^x (2y + 1)` and `num_tag(b, x)` (double, plus one when `b`) — are
  injective, and so are the four injections that encode a number
  (`inject_num`), an atom (`inject_atom`), a countable family (`inject_family`) and a pair of
  encodings (`inject_pair`) as such predicates. Injectivity of the encodings is
  what makes the universe's constructors injective later. Each pairing
  function is undone by two projections, defined as the components of
  some pair encoding the number — `num_pair_fst`/`num_pair_snd` and
  `num_tag_bit`/`num_tag_value` — which injectivity makes unique, and that is
  what `NumPairProjections` and `NumTagProjections` say.
- **The universe.** `encoded_node(c, i, r)` encodes a node from its tag,
  label and children, `encoded_bottom` the empty tree, and they are distinct.
  `is_recspace` is the smallest predicate closed under `encoded_bottom` and
  `encoded_node`, defined by those two rules and coming with its theorems:
  `UniverseRules`, `UniverseInduct`, the strengthened `UniverseInductStrong`
  that tells a step its children are themselves well-formed, and
  `UniverseCases`. Nothing unfolds it. The type `recspace(A)` is the subset
  `is_recspace` picks out, with `mk_recspace` / `dest_recspace` the bijection —
  stamped against the empty tree, the inhabitant a type definition must
  be shown — and the two facts it comes with, the retraction and the
  membership criterion, are the definition's own. Both halves are
  injective where they are defined.
- **The constructors.** `recspace_bottom` and `recspace_node` are `encoded_bottom` and `encoded_node`
  read into the type. They are distinct, `recspace_node` is injective in all
  three arguments, and the universe's induction principle — a property
  holding at `recspace_bottom` and inherited by a node from its children holds
  everywhere — is the inductive predicate's own. `family_cons` is the
  countable-family constructor (`family_cons(a, f)` is the family starting
  with `a` and continuing as `f`), defined by its two recursion clauses
  against ℕ's recursion schema.
- **Recursion.** The universe's recursion theorem: for any `Fn`, some
  `f` satisfies `f(recspace_node(c, i, r)) = Fn(c, i, r, λn. f(r(n)))` — a
  function on trees is determined by how it combines a node's tag,
  label, children and the values at those children. This is the theorem
  every datatype's recursion schema is an instance of;
  `datatypes/list` and `datatypes/option` read theirs off it.

The framework mechanics (typed cites, recorded deps, the shared family CNF blob,
replay) are the standard ones — see
`library/chapter_constitution.md` and `library/registry/`.
