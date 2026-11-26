# tower — constructing the real numbers

This directory builds ℝ from ℕ and nothing else, then hands the rest of
XuGo a short list of laws to cite. The construction is split into
five family sub-packages.

The mathematical problem it solves: ℕ has addition, multiplication and
order, but no subtraction, no division, and no limits. Each layer below
adds exactly one of those, and each pays for it with a construction.

## The four steps

**1. `internal/eudoxus_slope` — approximate ℕ→ℕ arithmetic.**
A *slope* is a nearly-additive function `f:ℕ→ℕ`:
`|f(m+n) − f(m) − f(n)|` stays bounded. Read `f(n)` as "n times the
real number f approximates", so a slope is a real number given by its
integer multiples, to within a fixed error. This is the Eudoxus
construction, and it is the only layer doing hard analysis — the
estimate lemmas (`Lipschitz`, `ArchMult`, the `bound_*`/`recip_*`
files) are where the ε-management lives. Everything above it is
bookkeeping by comparison.

**2. `internal/nonneg_real` — the nonnegative reals.**
Slopes that approximate the same number are identified: `hreal` is the
quotient of slopes by `nadd_eq`. Nothing new is proved here about
arithmetic; the chapter is pure **transport** — each slope law proved
*up to equivalence* becomes an *identity* on the quotient type.

**3. `internal/nonneg_real_formal_diff` — signed numbers.**
Pairs `(a, b)` of nonnegative reals, read as the formal difference
`a − b`, with `treal_eq(x, y)` identifying pairs of equal difference.
This is what buys subtraction. Still a pre-quotient representation:
the laws hold up to `treal_eq`, not as identities.

**4. `real_construction` — the real numbers.**
`real` is `treal` quotiented by `treal_eq`, and the chapter transports
the formal-difference laws across that last quotient into the twenty statements
the rest of the library cites. This is the tower's **public face**.

Alongside them, **`real_completeness`** — the completeness spur:
the Archimedean property and least-upper-bound completeness, from
`Arch` up to `RealComplete`. It is the one part of the tower not
on the construction critical path, which is why it is a separate
family rather than a tier of `real_construction`.

## What is public and what retires

The three construction layers live under `internal/`, and that is the
compiler enforcing a mathematical intention: they exist to establish
the laws and then retire. **No theorem outside this tower should
build on slopes, `hreal` or `treal`** — downstream real analysis cites
`real_construction` and `real_completeness` and never learns how ℝ was built. Go's
`internal/` rule refuses those typed imports outright.

The same quotient construction runs twice — slopes→`hreal` and
`treal`→`real` — and both go through the quotient door: each family
declares its type with `family.DefineQuotient` (the class map, written
⁅x⁆, and the seven facts a quotient comes with), defines each operation
at the classes with the layer below's well-definedness law as its one
obligation, and proves each transported law by inducting to
representatives, computing at the classes, and citing the law below.

## Reading order

Bottom-up (`eudoxus_slope` → `nonneg_real` → `nonneg_real_formal_diff` →
`real_construction`) follows the
construction and is the right path if you want to know *why ℝ exists*.
Top-down (`real_construction` first) is the right path if you want to know *what
the tower delivers*, and is enough for anyone citing it.

Each family carries its own `README.md` with the chapter narrative.

## Files here

- `tower.go` — the aggregator package. Its blank imports pull every
  tower family into the build, which both compiles the typed-dep DAG
  (a cross-family cycle is an import cycle) and triggers registration
  into `library/registry`. The ℝ domain aggregator one level up
  (`proofs/real`) imports this one package rather than five, because
  it cannot reach the `internal/` families directly — the same rule
  that keeps a future ℝ theory chapter, a sibling of this directory,
  from citing the construction instead of `real_construction` / `real_completeness`.
