# real_construction — the real numbers, constructed, and their laws

The tower's public face. Every theorem below is a `real`-side statement
the rest of XuGo's real analysis will cite by name; the internal
families (eudoxus_slope / nonneg_real / nonneg_real_formal_diff) exist to prove these, and then
retire (`internal/` refuses typed imports from outside).

## The laws

The tower delivers the laws of the real numbers — the theorems
naming their ring, order, embedding, and inverse-at-zero facts,
expressed against the primitives `real_add / real_mul / real_neg /
real_inv / real_of_num / real_le`.

Those six primitives, and ℝ itself, are defined here
(`definitions.go`). A real is a `treal_eq`-class of pre-reals, carved
out of the predicates on `hreal × hreal` exactly as the layer below
carves the nonnegative reals out of the slopes, and each operation
names what its result's members are. So the laws below are theorems
about a construction this corpus owns end to end: no statement in the
tower rests on a definition taken on faith.

The members' names form a mirror ladder with eudoxus_slope/nonneg_real/nonneg_real_formal_diff.

**Additive group.**

| member | Statement (informal)               |
|-------------------|------------------------------------|
| `AddSym`          | `x + y = y + x`                    |
| `AddAssoc`        | `x + (y + z) = (x + y) + z`      |
| `AddLeftId`       | `0 + x = x`                        |
| `AddLeftInv`      | `(−x) + x = 0`                     |

**Multiplicative monoid + inverse (with `inv 0 = 0` convention).**

| member | Statement (informal)            |
|-------------------|---------------------------------|
| `MulSym`          | `x·y = y·x`                     |
| `MulAssoc`        | `x·(y·z) = (x·y)·z`             |
| `MulLeftId`       | `1·x = x`                       |
| `MulLeftInverse`  | `x ≠ 0 ⇒ inv(x)·x = 1`          |
| `InvZero`         | `inv(0) = 0`                    |
| `LeftDistrib`     | `x·(y + z) = x·y + x·z`       |

**Linear order + order/ring compatibility.**

| member | Statement (informal)                       |
|---------------------|--------------------------------------------|
| `LessEqAntisym`     | `x = y ⇔ x ≤ y ∧ y ≤ x`                    |
| `LessEqTrans`       | `x ≤ y ∧ y ≤ z ⇒ x ≤ z`                    |
| `LessEqTotal`       | `x ≤ y ∨ y ≤ x`                            |
| `LessEqAddLeftImp`  | `y ≤ z ⇒ x + y ≤ x + z`                    |
| `LessEqMul`         | `0 ≤ x ∧ 0 ≤ y ⇒ 0 ≤ x·y`                  |

**ℕ-embedding as an ordered semiring.**

| member | Statement (informal)             |
|-------------------|----------------------------------|
| `OfNumLessEq`     | `&m ≤ &n  ⇔  m ≤ n`              |
| `OfNumEq`         | `&m = &n  ⇔  m = n`              |
| `OfNumAdd`        | `&(m + n) = &m + &n`             |
| `OfNumMul`        | `&(m · n) = &m · &n`             |

`OfNumEq` is the one member here that never descends to the quotient:
every other computes the numerals at their classes and lands on the
`nonneg_real_formal_diff` law mirroring it, whereas injectivity is an argument about `≤`
that `OfNumLessEq` has already carried across. It is therefore also the only member reaching
outside the tower — to `nat_order.LessEqAntisym`, for ℕ's half.

Reflexivity of `≤` is not one of these
laws. It is a one-step theorem of them — totality read at `y := x` —
and reflexivity's siblings are the order theorems rather than the
field's presentation, so it lives in `real_order_ring` as `LessEqRefl`.
Cite it there.

That is the whole criterion, and it cuts finer than "derivable". `OfNumEq`
— the injectivity of ℕ's embedding — is one step from these laws too,
and IS a member, because a chapter above needs exactly it: `real_field`
rests on ℝ being nontrivial (`&1 ≠ &0`), which is this injectivity read
at `(1, 0)`. So derivability alone never excludes a statement. What
decides is whether the chapter's consumers want the statement in this
chapter's own vocabulary — and that is a question about the corpus as
it stands, which a new chapter can reopen.

## The quotient

`real` is the quotient of `treal = hreal × hreal` by `treal_eq`,
declared through the quotient door (`family.DefineQuotient`, `RealDef`)
on nonneg_real_formal_diff's `TrealEqEquivalence`: the class map `real_of_treal` —
written `⁅p⁆`, the class of the pair p — with `mk_real` / `dest_real`
the bijection underneath it. A real is the equivalence class of a
formal difference `(a, b)` of nonnegative reals, thought of as `a − b`.
The door derives the seven facts a quotient comes with
(`RealDef.Surjectivity`, `.Induct` — the induction principle
`real_induction` —, `.Sound`, `.Exact`, `.Eq`, `.ForallOnImage`,
`.ExistsOnImage`), and each operation is defined at the classes with
the nonneg_real_formal_diff well-definedness law as its one obligation (`RealAddDef`:
`⁅a⁆ + ⁅b⁆ = ⁅a + b⁆`; `RealLeDef`: `⁅a⁆ ≤ ⁅b⁆ ⇔ a ≤ b`). Every law
below reduces — induct each real binder to a pre-real, compute at the
classes, cite — to a `treal`-side statement proved in `nonneg_real_formal_diff`,
which itself reduces to `hreal`-side facts proved in `nonneg_real`.

## Where things live

- [family.go](family.go) — registry handle, `//go:embed real_construction.cnf.pb`,
  the `realVocab` statement bundle (both floors: the real primitives
  and the treal-side consts every proof reduces to).
- [definitions.go](definitions.go) — the quotient declaration and the
  six constants defined at its classes.
- **One part per table above**, named for the movement rather than for
  a member; each entry is a `var … = family.Add(registry.ProofEntry{…})`.

## Family posture

- **Transport before arithmetic.** No proof here rests on real
  arithmetic (which these axioms ground), and none needs to: a
  transported law computes at the classes before there is anything to
  arithmetize, and what is left is the nonneg_real_formal_diff law.
- **The nonneg_real precedent applies** with the substitution `hreal →
  real`, `eudoxus_slope → nonneg_real_formal_diff`: induct, compute at the classes, cite the
  corresponding nonneg_real_formal_diff law.
- **Orientation is the one thing to watch.** Class equality reads as
  `treal_eq(A, B)` in the order the statement has them, and `treal_eq`
  is a relation, not `=`: a member whose statement puts the operation on
  the right of what the nonneg_real_formal_diff law puts on the left (`OfNumAdd`,
  `OfNumMul`) cites `TrealEqSym` beside the law.
