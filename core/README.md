# core — the kernel

## Overview
Package `core` is the trusted base: the types, terms and theorems of higher-order logic, and the primitive inference rules every theorem is derived by. Everything above it — `ext`, `prover`, `engine`, the library — builds terms and derives theorems through it, and none of it can make a theorem the rules did not.

Code above the kernel seldom calls it directly: `ext` wraps its terms and `ext/prop` its propositions, with the rules as methods.

## Type System

### Key Abstractions
- `HolType`: Interface for all logical types with operations including:
  - Equality testing and alpha-equivalence
  - Type substitution
  - Free type variable calculation
  - Type comparison and matching

### Implementations
- `VarType`: Type variables (e.g., `A`, `B`) that can be instantiated to any concrete type
- `CompositeType`: Complex types formed by composition of simpler types
  - Function types (`A → B`): Representing mappings between types
  - Predefined base type: Bool
  - Operations: type decomposition, type pattern matching

### Type Operations
- Type substitution: Instantiating type variables with more concrete types

### Data Structure
```go
type HolType interface {
    Equals(HolType) bool
    Compare(HolType) int
    Key() TypeKey
    Substitute(...TypeSubst) HolType
    Matches(HolType, VarTypePredicate) ([]TypeSubst, bool)
 // ... other methods
}

// Implementations: each a handle, one word passed by value, over a node
// the package does not export (see "Handles" below).
type VarType struct{ *_VarTypeNode }             // name
type CompositeType struct{ *_CompositeTypeNode } // meta, subTypes
type MetaType struct{ *_MetaTypeNode }           // name, arity
```

### Predefined Type

| Type | Implementation | Description |
|------|----------------|-------------|
|`A`| `TypeA()` | the basic variable type that can be instantiated to any type |
|`bool`| `TypeBool()` | the boolean type |
|`fun`| `MetaTypeFun()` | the meta type to compose a function type |

## Term System
### Key Abstractions
- `Term`: Interface for logical expressions with operations including:
  - Substitution and instantiation
  - Free variable calculation
  - Alpha-equivalence checking
  - Type checking and type inference

### Implementations
- `VarTerm`: Variables in logical expressions
- `ConstTerm`: Constants with fixed interpretation
  - Predefined const terms: `=`, `ε`
  - `ConstTermMeta` that defines the abstract type of the term
- `AppliedTerm`: Function application (`f a`)
  - Type checking for function application
- `AbsTerm`: Lambda abstractions (`λx.t`) for variable binding
  - De Bruijn level representation for bound variables
  - Capture avoidance mechanisms

### Term Operations
- Alpha conversion: Renaming bound variables while preserving meaning
- Term substitution: Instantiating variables with terms
- Term type substitution: Instantiating the type variables in the term type
- Shared subterms: a term is a DAG, and every walk over one term is
  bounded by its nodes rather than by its tree; a walk over two terms
  stops at identical pointers.
- Keys: `AlphaKey` is a digest of a term, the same for two terms that
  differ in the names of their BOUND variables alone. A type variable is
  part of the key under its own name (`VarType.Key`), so one statement
  over `A` and over `B` has two keys. Whatever is read back against a
  recorded key — a certificate, a plan — therefore reproduces the recorded
  type assignment, never a renaming of it.

  Two terms that are not α-equal have one key in two ways only, and
  neither comes up in ordinary use: the 64-bit hash a key is cut from
  collides (among a million terms, three chances in a hundred million), or
  a name spells a piece of a key — the variable `p_type_boolvar_p`, a type
  constant `var_A` beside a type variable `A` — which no name of the
  library does (`TestLintNamesSpellNoKeyWord`). Either can be made on
  purpose by whoever picks the names. So a key indexes terms and files
  what is known of them, where a wrong answer is found by the rule that
  reads it; and wherever nothing checks afterwards, the terms are
  compared. `core` takes no equal key for an equal statement: an
  assumption is found by comparing statements (`assumed`), and a
  predicate handed to `ForceWithBoundary` owes the same.

### Data Structure
```go
type Term interface {
    Type() HolType
    Size() int
    Equals(Term) bool
    AlphaEquals(Term) bool
    Compare(Term) int
    AlphaKey() TermKey
 // ... many other methods
}

// Implementations: each a handle over a node the package does not export.
type VarTerm struct{ *_VarTermNode }             // name, type, de Bruijn level
type ConstTerm struct{ *_ConstTermNode }         // meta, type
type ConstTermMeta struct{ *_ConstTermMetaNode } // name, abstract type, definition
type AppliedTerm struct{ *_AppliedTermNode }     // fun, arg, type, size
type AbsTerm struct{ *_AbsTermNode }             // bound variable, body, type, size
```

### Predefined Const Term Meta

| Const Term Meta | Abstract Type | Implementation | Description |
|-----------------|---------------|----------------|-------------|
|`=`|`(A, A) → bool` | `MetaEq()` | Equality |
|`ε`|`(A → bool) → A` | `MetaHilbert()` | Select (Hilbert operator) |

## Theorem Representation
- `Prop`: sequent representation of a proposition (hypotheses + conclusion) —
  proven or not.
- `Thm`: the *proven-or-provable* interface — its kernel value is either a
  realized `ThmCert` or a deferred `ThmPromise` (see Theorem Promises below).
- `ThmCert`: the realized, kernel-derived certificate (the unforgeable primary).
- Primitive inference rules.

### Data Structure
```go
type Prop interface {
    Conclusion() Term
    Hyps() []Term
    HypIter() iter.Seq[Term]
 // ... other methods
    Proved() bool
    AsThmCert() ThmCert  // collapse to the concrete cert; panics if not proved
    AsProp() Prop
}

// A statement: a conclusion under hypotheses in a canonical order.
// Written once, where it is made, and never handed out.
type _Statement struct {
    conclusion Term
    hyps       []Term
}

// Thm is the proven-or-provable interface: the currency the proof graph
// traffics in. Its kernel value is a ThmCert or a ThmPromise, and Force
// (a function, below) is total over it — always yields a kernel certificate.
type Thm interface {
    Prop
    theorem()
}

type ThmCert struct{ *_Certificate }  // a realized kernel certificate

// The node a certificate is a handle over: its statement, and the
// statements it stands on that no rule derived.
type _Certificate struct {
    _Statement
    assumes *_Assumptions
}
```

Three kernel values stand behind a `Prop`, exactly: a bare proposition
(unproved — *not* a `Thm`; `MakeProp` makes one), a `ThmCert` (realized) and a
`ThmPromise` (deferred). The `Thm` interface admits the last two — "things
that are, or can be, proven". Two narrowing helpers sit at the boundary: the
**method** `p.AsThmCert()` collapses a Prop to the concrete `ThmCert` (forcing
nothing — it *panics* on an unforced promise), while the free **function**
`core.AsThm(p) Thm` re-types a Prop known to be a thm/promise into the `Thm`
interface *without* forcing (keeping a promise lazy).

### Handles

Every kernel object — the four kinds of term, a constant's meta, the three
kinds of type object, a certificate, a promise — is a **handle**: a struct of
one word, passed by value, whose only field is an embedded pointer to a node
the package does not export.

```go
type AppliedTerm struct{ *_AppliedTermNode }

type _AppliedTermNode struct {
    fun, arg Term
    holType  HolType
    size     int
}
```

Each handle is the one type over its node. A bare proposition is a handle over
a `_Statement` and a certificate over a `_Certificate`, a node only
`certify` makes: Go converts one struct type to another of the same underlying
type, so two handles over one node type would each be made from the other.

What a holder of a handle can do is copy it, compare it (`==` is identity of
the node) and call its methods. What it cannot do is write the node: no
exported function, method or field of the package has a pointer to a kernel
type, or an unexported type, anywhere in its signature, so there is no
expression outside the package whose value is a pointer to a node. Assigning
to a handle overwrites the holder's own copy and nothing else.

The zero value of a handle (`core.VarTerm{}`, `core.ThmCert{}`) stands for
nothing. `IsZero` reports it, the functions that return "no such object"
return it (`MatchesHilbert`, `ConstTermMeta.Term`, `DefThm`), and every door
of the kernel panics on one.

The package exports no variable. The predefined types and constants are
functions (`TypeBool()`, `TypeA()`, `MetaEq()`, `MetaHilbert()`, `IFF()`,
`MetaTypeBool()`, `MetaTypeFun()`): a package variable is assignable by any
importer, and the rules read these.

### Logical Consistency
The implementation of the theorem system in XuGo is carefully designed to ensure logical consistency by restricting how theorem objects can be created. This is achieved through Go's package visibility rules:

```go
// Inside thm.go
// Public constructor - only create general proposition
func MakeProp(concl Term, hyps ...Term) Prop

// Private constructor - only accessible within the core package
func makeThm(concl Term, hyps ...Term) ThmCert { return certify(makeStatement(concl, hyps), nil) }

// Public constructor - explicitly marked for testing only; the certificate
// assumes its own statement
func TestThm(concl Term, hyps ...Term) ThmCert
```

+ **Restricted Theorem Construction**: The `makeThm` function is private (unexported), meaning it can only be called from within the `core` package itself, and a `ThmCert` is a handle over a certificate node: a pointer no other package can produce, in a struct type that no value of another type converts to.

+ **An input is read through its kernel value**: `Prop` and `Term` each carry one unexported method, `kernel()`, and `HolType` one, `core()`, returning the kernel value a value stands on. Every constructor and every primitive collapses the interface-typed inputs it is handed through that method before reading anything, a kernel object holds kernel values only, and `deriveProp` stamps a certificate only over kernel values. A type outside `core` can satisfy one of these interfaces only by embedding a core value — an unexported method cannot be declared elsewhere — and Go's promotion makes the embedded value's `kernel()` the embedder's, so overriding `Conclusion`, `Proved`, `Core`, `Type`, `Equals` or `AlphaEquals` on an embedder changes nothing the kernel sees. Sealing alone would not give this: an embedder of the interface satisfies a sealed interface too, with its overrides intact. `Core()` is exported and is not consulted by the kernel. Forcing is held the same way: `Force`, `ForceWithBoundary` and `Forcer.Force` are functions of the package that read the kernel value, and `Thm` declares no exported method of its own, so there is no force an embedder could answer in the kernel's place — the certificate that comes back is the kernel's, of the embedded value's statement. What an embedder's overrides do change is what a *caller* of those methods is told: a caller that needs the kernel's answer reads the kernel value, which `AsThm` returns, or a `ThmCert`, a struct no other type can be. The replay harness reads the theorem a member's build hands back through `AsThm` before it asks it anything, and forces that. An input typed as a kind (`VarTerm`, `AppliedTerm`, `MetaType`, …) is a handle and needs no such reading. `core/kernel_trust_test.go` and `core/object_model_test.go`, compiled as the outside package `core_test`, feed such embedders to the doors.

+ **The kernel keeps lists of its own**: a list a caller passes in (`MakeCompositeType`'s argument types, `MakeProp`'s hypotheses, a substitution list) is copied before it is kept, and a list the kernel hands out (`Hyps`, `TypeSubsts`) is a copy. A substitution (`TermSubst`, `TypeSubst`) is a struct a caller may build as a literal, so its replacement is read through `kernel()` and checked against its variable's type where a substitution is read, not only where `MakeTermSubst` builds one.

+ **A proposition's hypotheses are a canonical list**: `MakeProp` sorts the hypotheses by `Term.Compare` and drops α-duplicates, in a list of the statement's own, so `Hyps()` returns them in that order and never in the order they were given. Code that wants a particular hypothesis finds it by content.

+ **Primitive Rules as Gatekeepers**: The primitive inference rules — those of `primitives.go`, and `ConstTermMeta.TypeDefExpand` in `const_term.go` — are the only functions that can create new `ThmCert` values, and they do so only when all logical prerequisites are satisfied.

+ **Proposition vs. Theorem**: The system distinguishes between mere propositions and proven theorems (`ThmCert`):
   - A `ThmCert` can only be created through primitive rules or from existing theorems
   - A proposition becomes a theorem only when a valid proof is constructed

+ **Validation in Rules**: Each primitive rule includes assertions that check the validity of its application before producing a new theorem.

+ **Testing Escape Hatch**: The only public constructor, `TestThm`, is explicitly named to indicate its use should be restricted to testing scenarios.

This design guarantees that outside the core package, it is impossible to create theorems except by applying primitive rules to existing theorems. This ensures that every theorem in the system is either an axiom or has been derived from axioms through sound logical inference.

+ **What Go leaves open.** The guarantee is about Go code that respects Go's visibility and has no data race, and what the language permits beyond that is named here with what holds for each.
   - A zero-valued certificate, `core.ThmCert{}`, is a composite literal Go allows anywhere, unexported fields or not. It holds no statement, so it proves nothing: it reports `Proved() == false`, and every rule, and every read of its statement, panics on it. `core/kernel_trust_test.go` feeds it to every door.
   - The `unsafe` package would let a program write a node. No hand-written file of the module imports it; the generated protobuf code does (`*.pb.go`, four files), and the audit below greps for the import.
   - `reflect` cannot set a node through a handle: the handle's one field is unexported, so every value reached through it is read-only to `Value.Set`. It can still write one with no `unsafe` import, through `reflect.NewAt` over the address `Value.UnsafePointer` gives. No file of the module calls either, and the audit below greps for both.
   - `reflect.Value.Clear` is the one write `reflect` makes through a read-only value: it zeroes the elements of a slice, or empties a map, without asking whether the value may be set. A kernel value reaches six slices and no map: a statement's hypotheses, a composite type's arguments, a constant's type instantiation, a derived promise's dependencies, a certificate's assumptions and, from the `Forcer` a builder is handed, a bounded force's record of what it settled from trust. The zero of each element type is no kernel value and a cleared slice keeps its length, so clearing drops no hypothesis, assumption or dependency: it leaves a node that the next rule or force to read it panics on, and a record that no longer reads beside a certificate that still says what it stands on. A cleared node proves nothing. `core/object_model_test.go` lists the six by type and clears each. No file of the module calls `Clear` on a `reflect.Value`, and the audit below greps for the call.
   - `reflect.Value.Convert` makes any conversion Go allows, between types its caller cannot name as between those it can, and Go allows one between two struct types of the same underlying type. The certificate's handle shares its underlying type with no other type, the bare proposition's included, so no value converts to a certificate; `reflect.StructOf` does not build that underlying type either, refusing an embedded field of an unexported type. `core/object_model_test.go` tries every kind of kernel value against every other, by value, behind a pointer and by node.
   - A data race is outside what Go promises of a program's memory, and the kernel's guarantee with it.
   - The order in which packages initialize builds no theorem differently: a theorem built at any moment is built by a rule, and of two definitions under one name, or of the definitions of a cycle, the kernel refuses whichever comes last.
   - `core/export_surface_test.go` reads the package's declarations and fails on an exported variable, on a pointer to a kernel type or an unexported type in an exported signature, on an exported struct that is neither a handle nor a struct of exported fields, and on a handle that converts to or from another declared type. It keeps this package's own edits to the shape above; it defends against nothing.

### Theorem Promises (deferred certificates)

A `ThmPromise` is an *honest IOU* for a theorem: a stateful proof handle over an
**immutable statement** whose certificate may arrive later. It is the deferred
flavor of the `Thm` interface (the realized flavor being `ThmCert`), and the
sound replacement for fabricating a stand-in with `TestThm` — the statement is
declared now and built upon eagerly, while the expensive proof is deferred and,
crucially, can only be realized by a genuine kernel `ThmCert`.

```go
// ThmPromise is a handle over its cell. The cell holds the immutable
// statement; only its certificate moves, unresolved → resolved-with-a-real-ThmCert.
type ThmPromise struct{ *_PromiseCell }

// Promise is the sole root constructor: a statement plus an on-demand builder.
func Promise(p Prop, builder func(Forcer) ThmCert) ThmPromise

// Force realizes a Thm to the ThmCert of its statement (or panics): the
// kernel value itself for a ThmCert, and for a ThmPromise the certificate
// its cell settles with, after running the builder / forcing the deps.
// Threaded through the primitive rules: EqMP/Deduct/TypeInst/
// TypeDefExpand/… over a promise yield a *derived* promise (deriveProp), so a
// whole derivation tree builds on statements and snaps to proved when its
// leaves realize. There is NO "force a Prop" function — forcing is a Thm
// operation; a Prop known to be forceable is narrowed first via AsThm.
func Force(ctx context.Context, t Thm) ThmCert
// ForceWithBoundary forces like Force, but settles any root promise whose
// statement is `trusted` directly from its statement (not built) — bounded / modular
// verification; `assumed` is what this call settled that way. See below.
func ForceWithBoundary(ctx context.Context, t Thm, trusted PropPredicate) (cert ThmCert, assumed []Prop)
func IsPromised(p Prop) bool   // "p's kernel value is a ThmPromise" (forced or not)

// A builder uses its supplied Forcer for every nested force.
func NewForcer(ctx context.Context) Forcer // independent top-level forcing
func (f Forcer) Force(t Thm) ThmCert
func (f Forcer) Context() context.Context
func (f Forcer) WithContext(ctx context.Context) Forcer
```

`Thm` (the interface above) is what the *define-then-run proof graph* traffics
in: a member's `Build` (`registry.ProofEntry.Build`) yields a proof whose
section roots are promises — each a `Thm`, unforced, no CNF replayed — and the
library theorems its environment hands it are `Thm`s too. Forcing the roots
(e.g. in the replay harness) drives the whole graph.
Because a leaf primitive that consumes a promise threads it (deriveProp), an
`EqMP` / `TypeInst` / `TypeDefExpand` over an unforced lemma produces another
unforced promise rather than forcing — laziness propagates through the build.

Design choices that keep it in the kernel's spirit:

+ **Two cell flavors.** *builder-root* (`Promise`, carries a builder) and
  *derived* (`deriveProp` inside the primitive rules, carries dependencies). No
  goroutine — realization is synchronous on the caller; the first caller to a
  builder-root runs it inline, concurrent callers wait on a channel.

+ **An explicit forcing scope.** A builder receives a `Forcer` carrying its
  promise's identity and the caller's trust boundary. Every nested force,
  including one reached through a helper, uses `f.Force(dep)`. A builder may
  share its `Forcer` with concurrent child calls, but must join all of those
  calls before returning. Returning with unfinished forces panics, and the
  supplied `Forcer` expires when the builder ends, whether by returning,
  panicking, or `runtime.Goexit`. The zero `Forcer` is invalid. A concurrent
  trust settle does not end the builder's scope.

  `Force(ctx, t)`, `ForceWithBoundary(ctx, t, trusted)`, and `NewForcer(ctx)`
  are independent top-level entries. Calling one inside a builder bypasses
  its supplied identity and is forbidden by the builder contract; the kernel
  cannot identify such a call as nested. `Forcer.Context` supplies context
  values for work other than forcing. `WithContext` changes those values
  while preserving the owner, trust boundary, and lifetime. Cancellation is
  not consulted: realization must finish or panic.

+ **A graph of active builder dependencies.** A nested force records an edge
  from the current builder's promise to a builder dependency in `_ForceDeps`.
  Derived promises are transparent: forcing their immutable dependency DAG
  retains the current builder as the owner. This lets concurrent realizations
  of the same derived promise proceed independently.

  Edges distinguish running a builder synchronously from waiting for its
  certificate. A synchronous edge lasts until the builder call ends, even if
  trust settles its promise first. A wait edge stops contributing to paths
  when its target settles or is poisoned, before the waiter wakes and removes
  it. Concurrent calls holding the same kind of edge are counted. Inserting
  an edge and checking for a cycle happen under one lock, so the edge that
  closes a cycle panics with its builder promises, even when several goroutines
  participate. The graph reads no goroutine identity or runtime stack text.
  Locks, `sync.Once`, and other waits outside the forcing API are outside this
  graph.

+ **A derived cell holds its dependencies as they were.** The dependencies of
  a derived promise are kernel values, each a handle copied into the cell when
  the rule ran. What a holder later does with its own copy of a promise does
  not reach the cell.

+ **No errors — Assert/panic, like the rest of the kernel.** `Force` returns a
  `ThmCert` and *panics* on anything unexpected (a builder failure, an
  unforceable dependency, a cycle). A formal-proof module has no useful error to
  hand a caller; failing fast forces a debug at the source. A builder that
  ends without a certificate poisons its unsettled cell and wakes its waiters;
  every later force panics with that failure instead of retrying or parking.

#### Soundness: construction confined to core

The soundness gate is one check in `settle`: a root promise can only settle via
a real `ThmCert` whose statement **α-equals** the promised statement (the
builder's output is checked the same way), and a derived promise stamps a
certificate over its statement only once every dependency is proved — and the
statement was computed by a primitive rule from input *statements*, so it is
byte-for-byte what the kernel would produce. Mismatch panics. **There is no
path that mints a `ThmCert` from a promise except behind this gate.**

This preserves the *grep-based audit* that the unforgeable-`ThmCert` design
above gives. A `ThmPromise` is a handle over a cell only `core` can make, so no
code outside `core` can fabricate a promise — exactly as no code outside `core`
can fabricate a `ThmCert`. The *only* way to mint a promise from an arbitrary
statement is `core.Promise`, which is therefore the promise analogue of
`TestThm`. So the complete soundness audit of the deferred-certificate layer is:

```
grep TestThm            # fabricated ThmCert  (the original escape hatch)
grep 'Promise('         # minted root promises (arbitrary statement)
grep ForceWithBoundary  # bounded forces — each trusts a frontier of statements
grep NewAxiom           # axioms: the library's postulate and its CARDS
grep '"unsafe"'         # the import that writes a node: the generated *.pb.go files, no other
grep 'reflect.NewAt'    # with the next, reflect's way to a node without that import: no file of the module
grep 'UnsafePointer('
grep '\.Clear()'        # reflect's write through a read-only value, zeroing a slice a kernel value reaches: on no reflect.Value of the module
```

`NewAxiom` has two production callers, the corpus seam (`library/serve`)
and the replay harness, and both mint an axiom for a library member with
no proof: a CARD — a member stated without a proof
(`registry.Family.Card`), `⊢ <statement>`, an axiom until its proof
lands — or the POSTULATE (`registry.Family.Postulate`), `⊢ <term>` at
the term its chapter builds. The registry admits one postulate. The
kernel itself states no axiom. The corpus is sound relative to its
postulate and its cards; `xugo query axioms` lists both.

Definitions are CONSERVATIVE, and the kernel holds that itself
(`definition_table.go`). A constant is identified by its name and a
type by its name and arity, and either is made by hand under any name
(`MakeConstMeta`, `MakeMetaType`), so a definition could be an axiom
two ways. Under a name in use: two constant definitions under one name
are two axioms whose consequence is `t₁ = t₂`, and a second type
definition is a second bijection for the one type. Through itself: the
term a definition is made from may mention the name it defines, as in
`c = ¬c`, or a name whose own definition leads back to it. `NewConstDef`
and `NewTypeDef` panic on both. The kernel keeps every name a
definition has introduced in the process — its own `=`, ε, `bool` and
`fun` are there from the start — and, for each, the constants and the
types its term mentions, and it searches that graph before it mints.

Two things are no second axiom, and are admitted. Defining a name again
from an α-equal term — for a type, from an α-equal source under the
same two constant names — returns what the first definition made. And a
name may be mentioned before it is defined, where no cycle closes: a
set of definitions is accepted or refused as a set, whatever order it
arrives in, and of a cycle the definition that closes it is the one
refused.

The library's checks come before the kernel's and answer with an error
an author reads: `registry.ConstMetaManager.ClaimName` refuses a
constant name that is taken before a door mints, and
`proof.MintTypeDefinition` refuses a type name any registered constant
mentions (`TypeNameInUseProbe`), a type made by hand among them. The
gate `TestEveryMintIsADoor` holds that every constant a chapter
registers is a door entry's. They keep the corpus's vocabulary in
order — one entry for a constant, no type given a meaning after
statements spell it — and the kernel's soundness rests on none of them.

`ForceWithBoundary(ctx, t, trusted)` is the third escape: it settles any root
promise — a cell with a builder — whose statement satisfies `trusted` directly
from that statement (a certificate stamped over it, bypassing the builder and
the α-gate), so the returned cert holds *given the trusted statements as
axioms*. A derived cell is never settled that way: it is derived from its
dependencies whatever its statement, so a derivation whose result happens to
be a trusted statement stands on what it was derived over. This is bounded / modular
verification — it trades a re-verification for a trust. The trust is not
scoped to the call: a cell settled this way stays settled for the rest of the
process, and a later `Force` of it returns the minted certificate without
running its builder. A build of the cell that was in flight when trust
settled it changes nothing by failing: the failure reaches the caller that
ran the build and no other. The `assumed []Prop` return lists the statements
this call settled from trust; a cell an earlier call settled is not among
them, so it is not the whole trusted base of the certificate it comes with.
That is read from the certificate: `ThmCert.Assumes`, below. A bounded force is sound
only relative to its frontier: inspect each call site's predicate, which
bounds what the call can settle.

#### What a certificate assumes

A certificate carries the statements it stands on that no rule derived, each
with the door it came in by, and `ThmCert.Assumes()` lists them:

| Door | What enters by it |
|---|---|
| `AxiomDoor` | `NewAxiom`: the library's postulate and its cards |
| `BoundaryDoor` | a root promise `ForceWithBoundary` settled from its statement |
| `TestDoor` | `TestThm` |

A rule's certificate assumes what its premises assume — `deriveProp`, the one
tail every rule ends in, takes the union — and a derived promise settles
with what its dependencies turn out to assume. So the list is the whole of
it, whichever force settled a cell and whenever, and a certificate that
assumes nothing was derived by the rules from the definitions alone. The
`#print axioms` of a certificate is this list. Two mints of α-equal
statements through one door are one entry of it, and the statements are
compared to say so: the list names the statement a certificate was minted
over, whatever else has that statement's key.

The replay harness reads it (`checkAssumptions`,
`library/integrity/gates/replay_test.go`): what a member's certificates
assume must lie among the member's recorded edges — its dependency cone and
the foundations of the capabilities recorded there — and is never the
member's own statement, nor a `TestThm`. The entry an assumption states is
found by comparing statements too (`registry.EntriesStating`), as is every
statement the harness trusts. The dependency graph the cycle scan
reads is thereby held to what the kernel saw each proof stand on.

`deriveProp`'s derived promises are **not** on the audit surface — their
statement comes from a kernel primitive (sound by construction). And unlike
`TestThm` (an un-verifiable fake), a root promise is *checkable by forcing*: it
reports `Proved()==false` until forced, so it can never masquerade as a realized
cert, and `settle`'s α-gate catches a lying builder the moment it is forced.
Forcing the graph (e.g. in CI) is the mechanical audit that every root's builder
really delivers a certificate matching its promised statement. Keep `Promise`
call sites few and each backed by a real producer; never add a path that settles
a cell bypassing the α-gate **except** the explicit `ForceWithBoundary` frontier
above — that gate, plus the statement being out of every other package's
reach, is the entire trusted base of this layer.

## The logic and what it assumes

Classical higher-order logic: Church's simple type theory with type
variables. The types are `bool`, the function type, the type
variables, and named composite types: those `NewTypeDef` carves out of
an existing one as the subset a predicate names (`TypeDefExpand` hands
over the two theorems that make the new type and that subset a
bijection), and any other the library introduces. A type is identified
by its name and arity, so introducing one asks nothing of the kernel.
The primitive constants are equality, at every type, and Hilbert's ε
(`MetaHilbert()`, of type `(A → bool) → A`); ⊤, ⊥, ¬, ∧, ∨, ⇒, ∀, ∃ and
∃! are defined from them in `ext/basic_defs.go`, as Henkin set them up.

Of the rules, two state assumptions rather than reasoning steps:

| Assumption | Where |
|---|---|
| η-conversion, `⊢ λx. t(x) = t` | the rule `Eta` |
| the axiom of choice, `P(x) ⊢ P(εP)` | the rule `Select` |

Function extensionality follows from η and abstraction (`PropAbs`).
Every axiom is the library's — its postulate and its cards — and the
`grep NewAxiom` line of the soundness audit above finds every caller.
A definition is no axiom: `NewConstDef` and `NewTypeDef` define a name
once and close no cycle of definitions, which the kernel holds, as that
audit says.

## Primitive Inference Rules

The rules, the only functions that produce a theorem: those of
`primitives.go`, and one method of `const_term.go`, the last row.

| Primitive | Description |
|---|---|
| `Refl(t)` | Reflexivity: `⊢ t = t` |
| `Assume(t)` | Assumption: `t ⊢ t` |
| `Beta(t)` | Beta reduction: `⊢ (λx.t)(x) = t` |
| `Eta(t)` | Eta reduction: `⊢ λx.(t(x)) = t` |
| `Select(t)` | Axiom of ε-calculus: `P(x) ⊢ P(εP)` |
| `PropApply(t0, t1)` | Function application to equalities:<br> `{h0} ⊢ f = g` <br> `{h1} ⊢ a = b` <br> →` {h0} + {h1} ⊢ f a = g b` |
| `PropLeftApply(f, t)` | `PropApply` at a fixed function: <br>`... ⊢ a = b` <br> →`... ⊢ f a = f b` |
| `PropRightApply(t, a)` | `PropApply` at a fixed argument: <br>`... ⊢ f = g` <br> →`... ⊢ f a = g a` |
| `PropAbs(v, t)` | Abstraction:<br>`... ⊢ l = r` <br> →`... ⊢ λx.l = λx.r` |
| `EqMP(t0, t1)` | Equality modus ponens: <br>`{h0} ⊢ l = r` <br> `{h1} ⊢ l` <br> →` {h0} + {h1} ⊢ r` |
| `Deduct(t0, t1)` | Deduction: <br>`{h0}, r ⊢ l` <br> `{h1}, l ⊢ r` <br> →` {h0} + {h1} ⊢ l = r` |
| `PropTypeInst(t, subst)` | Type instantiation: Instantiates type variables in a theorem |
| `PropTermInst(t, subst)` | Term instantiation: Instantiates term variables in a theorem |
| `NewAxiom(t)` | Axiom: Introduces a new axiom |
| `NewConstDef(t, name)` | Constant definition: `⊢ name = t`, the name defined once and through no cycle |
| `NewTypeDef(...)` | Type definition: a new type and its two constants, each name defined once and through no cycle |
| `DeriveTrans(t0, t1)` | Derivation transitivity: <br>`{h0} ⊢ l` <br> `{h1}, l ⊢ r` <br> →` {h0} + {h1} ⊢ r` |
| `EqTrans(t0, t1)` | Equality transitivity: <br>`{h0} ⊢ l = m` <br> `{h1} ⊢ m = r` <br> →` {h0} + {h1} ⊢ l = r` |
| `EqSym(t)` | Equality symmetry: <br>`... ⊢ l = r` <br> →`... ⊢ r = l` |
| `c.TypeDefExpand(t)` | Type definition, its two theorems: from `⊢ P(_)`, the statement `NewTypeDef` minted the type by, <br>→ `⊢ abs(rep a) = a` and `⊢ P(r) = (rep(abs r) = r)`, at `c` either of the pair's constants |
