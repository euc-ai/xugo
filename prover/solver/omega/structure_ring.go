package omega

// structure_ring.go — ring identities and integer linear combinations
// read at comm_ring(R), field(F), or their carrier forms.
//
// Whole-type facts are bridged to records with carrier 𝕌. Operations
// and the carrier are projections of the carrier fact's record,
// computed in the instance normal form. Every leaf instantiates a
// carrier law at its record, discharges the structure hypothesis from
// the resident fact or installed instance, and proves the membership
// guard. On 𝕌 every membership is InUniv; on another carrier every atom
// needs a resident membership. Formed terms use the closure laws,
// including inverse and division for a field. Missing atoms are named
// by StructureRingMissingMemberships; subset inclusions are not inferred.
//
// Canonical numerals are monoid_pow(add, zero, one, n). The monoid
// chapter retains its operation, identity and carrier parameters. A
// concrete instance on 𝕌 may supply a literal reader and a theorem
// bridging its spelling to that canonical numeral.
//
// Laws. StructureRingLaws holds the carrier laws the leaves read, in
// their stated form (the `⇒` is what DemoteHyp peels), the two bridges
// and InUniv; library/serve installs them from the algebra chapters.
// The carrier facts and derived monoids and additive group are cached
// per structure fact and provenance. Leaves are bound per decision to
// its memberships. The shared ring and signed normalizers compose the
// instantiated laws; order has no structure-ring reading.
//
// Facts. For a goal atom `l = r` at carrier τ the facts are the goal's
// hypotheses headed by comm_ring_on, comm_ring, field_on or field at τ
// (a chapter's structure Fact, assumed), then the installed instances
// at τ (SetStructureInstances). Among several whose operations head the
// atom's operators, those on 𝕌 are tried first, then each carrier whose
// memberships the context holds. An atom between two atoms, heading no
// operation, is tried at every fact at τ once the context holds an
// equation at τ to combine it with.
//
// What it decides: a ring identity, and an equation that is an integer
// linear combination of the context's equations over the monomial
// basis, by Gaussian elimination over ℚ, declined when a coefficient is
// not an integer. At a field the combination also reads the unit facts
// R·(inv(t)·t) = R of the sequent's inverse atoms, on the context's
// evidence that t is not zero, or ℝ's for a real an instance embeds
// (structure_unit_facts.go), and the cofactor of a nonzero factor in a
// product the context equates to zero. And an equation the context
// denies is decided ⊥: one that, joined to the context's equations,
// combines to an equation a resident disequality denies, or at a field
// to `one = zero` (structure_refute.go). The context's
// equations are the hypotheses and the conjuncts of hypotheses at τ
// (contextEquations); on a carrier set one over an atom without a
// resident membership is not read, and the decline names that atom as
// it names the goal's. A `Scaled(c, h)` premise supplies a polynomial
// coefficient as the hypothesis `c·l = c·r`.

import (
	"fmt"
	"math/big"
	"slices"
	"sort"
	"strings"
	"sync"
	"sync/atomic"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// Structure predicate names, as the algebra chapters mint them. omega
// identifies a structure fact by its head constant's NAME: the
// constants themselves are chapter mints this package cannot import.
const (
	commRingConstName   = "comm_ring"
	commRingOnConstName = "comm_ring_on"
	fieldConstName      = "field"
	fieldOnConstName    = "field_on"
)

// StructureRingLaws are the carrier laws as stated: a structure
// hypothesis followed by element binders and membership guards. The
// record normalizers compute the same form for the kernel derivations
// and the matchers. Installed by library/serve from the algebra chapters.
type StructureRingLaws struct {
	// ── comm_ring_on(R) ⇒ …
	MulMonoid *prop.PropWrapper // comm_monoid_on(c, mul, one)
	AddMonoid *prop.PropWrapper // comm_monoid_on(c, add, zero)
	AddGroup  *prop.PropWrapper // abelian_group_on(additive_group(R))
	// ── abelian_group_on(G) ⇒ …
	Group  *prop.PropWrapper // group_on(G)
	NegAdd *prop.PropWrapper // ∀x y. x ∈ c ∧ y ∈ c ⇒ neg(add(x, y)) = add(neg(x), neg(y))
	// ── comm_monoid_on(c, op, e) ⇒ …
	Comm          *prop.PropWrapper // ∀x y. x ∈ c ∧ y ∈ c ⇒ op(x, y) = op(y, x)
	Assoc         *prop.PropWrapper // ∀x y z. x ∈ c ∧ y ∈ c ∧ z ∈ c ⇒ op(x, op(y, z)) = op(op(x, y), z)
	LeftIdentity  *prop.PropWrapper // ∀x. x ∈ c ⇒ op(e, x) = x
	RightIdentity *prop.PropWrapper // ∀x. x ∈ c ⇒ op(x, e) = x
	PowOne        *prop.PropWrapper // ∀x. x ∈ c ⇒ monoid_pow(op, e, x, 1) = x
	PowAdd        *prop.PropWrapper // ∀x m n. x ∈ c ⇒ monoid_pow(op, e, x, m + n) = op(monoid_pow(op, e, x, m), monoid_pow(op, e, x, n))
	PowIn         *prop.PropWrapper // ∀x n. x ∈ c ⇒ monoid_pow(op, e, x, n) ∈ c
	// ── monoid_pow's definition clauses (no structure hypothesis)
	PowZeroClause *prop.PropWrapper // ∀op e x. monoid_pow(op, e, x, 0) = e
	PowSucClause  *prop.PropWrapper // ∀op e x n. monoid_pow(op, e, x, suc(n)) = op(x, monoid_pow(op, e, x, n))
	// ── group_on(G) ⇒ …
	InvInv      *prop.PropWrapper // ∀x. x ∈ c ⇒ inv(inv(x)) = x
	InvOne      *prop.PropWrapper // inv(e) = e
	LeftInverse *prop.PropWrapper // ∀x. x ∈ c ⇒ op(inv(x), x) = e
	RightCancel *prop.PropWrapper // ∀x y z. x ∈ c ∧ y ∈ c ∧ z ∈ c ⇒ (op(y, x) = op(z, x) ⇔ y = z)
	// ── comm_ring_on(R) ⇒ …
	LeftDistrib  *prop.PropWrapper // ∀x y z. x ∈ c ∧ y ∈ c ∧ z ∈ c ⇒ mul(x, add(y, z)) = add(mul(x, y), mul(x, z))
	RightDistrib *prop.PropWrapper // ∀x y z. x ∈ c ∧ y ∈ c ∧ z ∈ c ⇒ mul(add(x, y), z) = add(mul(x, z), mul(y, z))
	MulLeftZero  *prop.PropWrapper // ∀x. x ∈ c ⇒ mul(zero, x) = zero
	MulRightZero *prop.PropWrapper // ∀x. x ∈ c ⇒ mul(x, zero) = zero
	SubAddNeg    *prop.PropWrapper // ∀x y. x ∈ c ∧ y ∈ c ⇒ sub(x, y) = add(x, neg(y))
	MulRightNeg  *prop.PropWrapper // ∀x y. x ∈ c ∧ y ∈ c ⇒ mul(x, neg(y)) = neg(mul(x, y))
	AddPowMul    *prop.PropWrapper // ∀m n. monoid_pow(add, zero, one, m * n) = mul(monoid_pow(add, zero, one, m), monoid_pow(add, zero, one, n))
	// ── the carrier's closure laws: comm_ring_on(R) ⇒ …
	ZeroIn *prop.PropWrapper // zero ∈ c
	OneIn  *prop.PropWrapper // one ∈ c
	AddIn  *prop.PropWrapper // ∀x y. x ∈ c ∧ y ∈ c ⇒ add(x, y) ∈ c
	NegIn  *prop.PropWrapper // ∀x. x ∈ c ⇒ neg(x) ∈ c
	MulIn  *prop.PropWrapper // ∀x y. x ∈ c ∧ y ∈ c ⇒ mul(x, y) ∈ c
	SubIn  *prop.PropWrapper // ∀x y. x ∈ c ∧ y ∈ c ⇒ sub(x, y) ∈ c
	// ── whole-type structures read through their universal-carrier forms
	RingOnUniverse  *prop.PropWrapper // ∀R. comm_ring(R) ⇔ comm_ring_on(restrict_ring(R, 𝕌))
	FieldOnUniverse *prop.PropWrapper // ∀F. field(F) ⇔ field_on(restrict_field(F, 𝕌))
	InUniv          *prop.PropWrapper // ∀x. x ∈ 𝕌
	// ── field_on(F) ⇒ …
	FieldRing *prop.PropWrapper // comm_ring_on(field_ring(F))
	DivMulInv *prop.PropWrapper // ∀x y. x ∈ F.carrier ∧ y ∈ F.carrier ⇒ F.div(x, y) = F.mul(x, F.inv(y))
	InvMul    *prop.PropWrapper // ∀x y. x ∈ F.carrier ∧ y ∈ F.carrier ⇒ F.inv(F.mul(x, y)) = F.mul(F.inv(x), F.inv(y))
	InvIn     *prop.PropWrapper // ∀x. x ∈ F.carrier ⇒ F.inv(x) ∈ F.carrier
	DivIn     *prop.PropWrapper // ∀x y. x ∈ F.carrier ∧ y ∈ F.carrier ⇒ F.div(x, y) ∈ F.carrier
	// MulLeftInverse is the one law whose guard is not memberships
	// alone; the unit facts discharge it (structure_unit_facts.go).
	MulLeftInverse *prop.PropWrapper // ∀x. x ∈ F.carrier ∧ x ≠ F.zero ⇒ F.mul(F.inv(x), x) = F.one
	// OneNotZero is what a field denies whatever the context holds: the
	// refutation of an equation reads it (structure_refute.go).
	OneNotZero *prop.PropWrapper // F.one ≠ F.zero
	// PowEqZero: a power that is zero has a zero base — the evidence that
	// a power of a term that is not zero is not zero, and what a context
	// equation `xⁿ = zero` says of x (structure_refute.go).
	PowEqZero *prop.PropWrapper // ∀x n. x ∈ F.carrier ∧ monoid_pow(F.mul, F.one, x, n) = F.zero ⇒ x = F.zero

	// NormalizeWith computes the instance normal form with kernel
	// equations, each read through read — a proof's own read of the
	// equation's theorem (LibraryReader), nil for the fallback
	// library/serve installs; NormalizeTerm computes the same form for
	// matching without reading.
	NormalizeWith func(read LibraryRead) prop.Rewrite
	NormalizeTerm func(core.Term) core.Term

	// monoidPow is the `monoid_pow` constant, read off PowZeroClause at
	// install; member is the membership constant `∈`, read off InUniv
	// (SetStructureRingLaws).
	monoidPow Term
	member    core.ConstTermMeta
}

// StructureInstance is an installed ring or field theorem, in either form.
// A record with carrier 𝕌 may supply its carrier's own numeral spelling
// beyond zero and one (ℂ: complex_of_real(&n)). A proper carrier's
// literals are formed by the ring and placed there by its closure laws.
type StructureInstance struct {
	Fact *prop.PropWrapper
	// Literal reads a carrier literal as Domain.asLiteral does: (n,
	// shaped, ok), n the natural it spells, at any size. nil when the
	// carrier spells no numeral of its own.
	Literal func(Term) (n *big.Int, shaped, ok bool)
	// LiteralBridge proves `⊢ t = monoid_pow(add, zero, one, n)` for a
	// term Literal read as n. Required when Literal is set.
	LiteralBridge func(t Term, n *big.Int) *prop.PropWrapper
	// RealEmbedding is an injective map of ℝ into the carrier that sends
	// &0 to its zero (ℂ: complex_of_real); nil when the carrier has none.
	// With it an embedded real is not zero wherever ℝ's arithmetic shows
	// the real is not (structure_unit_facts.go), a literal among them.
	RealEmbedding *RealEmbedding
}

// RealEmbedding is a carrier's copy of ℝ: the map and its injectivity.
type RealEmbedding struct {
	// Map is the embedding, a term of type real → carrier whose value at
	// &0 is the carrier's zero as the ring reads it.
	Map Term
	// Injective is `⊢ ∀x y:real. Map(x) = Map(y) ⇔ x = y`.
	Injective *prop.PropWrapper
}

var (
	structureLaws      *StructureRingLaws
	structureInstances []StructureInstance
	// structureFoundationKeys is the laws' capability foundation closure
	// — every entry the carrier laws and InUniv rest on — and
	// structureInstanceFoundationKeys the installed instances', for the
	// scope-less circularity gate (circularity.go).
	structureFoundationKeys         map[core.PropKey]bool
	structureInstanceFoundationKeys map[core.PropKey]bool

	// structureGeneration counts the installs of the laws and the
	// instances; a reader's rings are dropped at a new one, as their
	// derived facts rest on the previous table.
	structureGeneration atomic.Uint64
)

// LibraryRead reads a record equation's theorem by its registered name:
// a proof's own read of a library theorem, the read prover/tactic takes
// (tactic.LibraryRead). nil reads through the fallback library/serve
// installs.
type LibraryRead func(entry string) *prop.PropWrapper

// LibraryReader is one proof's reading of the record equations: its
// read of an equation's theorem, the normal form computed through that
// read, and the structure rings built with it (ringFor), so every fact
// a ring derives rests on the proof's own cites and lands in its
// dependency record. A proof's steps share one reader (prover/proof's
// scope hands it to the arith step, the chase and the By executor's
// scaling). A nil reader reads through the installed fallback and keeps
// its rings for the process (fallbackReader).
type LibraryReader struct {
	Read LibraryRead

	mu sync.Mutex
	// generation is the install the rings were built at.
	generation uint64
	rings      map[string]*structureRing
	// normalize is the installed laws' NormalizeWith(Read), computed
	// once per install.
	normalize prop.Rewrite
}

// fallbackReader reads through the installed fallback: the reader of a
// caller that builds no proof, and of the content classifiers.
var fallbackReader = &LibraryReader{}

func readerOrFallback(r *LibraryReader) *LibraryReader {
	if r == nil {
		return fallbackReader
	}
	return r
}

// _ReadLaws is the carrier laws as one reader reads them: the table and
// the normal form computed through the reader's read, which every
// derived fact's conclusion is read in (at, normalFact).
type _ReadLaws struct {
	*StructureRingLaws
	normalize prop.Rewrite
}

// reading is the installed laws as this reader reads them, its rings
// dropped at a new install; ok is false with no laws installed.
func (r *LibraryReader) reading() (laws _ReadLaws, ok bool) {
	table := structureLaws
	if table == nil {
		return _ReadLaws{}, false
	}
	r.mu.Lock()
	defer r.mu.Unlock()
	if generation := structureGeneration.Load(); r.rings == nil || r.generation != generation {
		r.generation = generation
		r.rings = map[string]*structureRing{}
		r.normalize = nil
		if table.NormalizeWith != nil {
			r.normalize = table.NormalizeWith(r.Read)
		}
	}
	return _ReadLaws{StructureRingLaws: table, normalize: r.normalize}, true
}

// SetStructureRingLaws installs the carrier laws (nil uninstalls). The
// per-fact cache is dropped: its derived facts rest on the previous
// laws.
func SetStructureRingLaws(l *StructureRingLaws) {
	if l != nil {
		if l.PowZeroClause == nil {
			panic("omega.SetStructureRingLaws: PowZeroClause is required (it names the monoid_pow constant)")
		}
		body, _ := l.PowZeroClause.StripConclForAll()
		lhs, _, ok := prop.MatchesEQ(body.Conclusion())
		if !ok {
			panic("omega.SetStructureRingLaws: PowZeroClause is not an equation")
		}
		head, args := ext.MatchesApply(lhs)
		if _, isConst := head.AsConst(); !isConst || len(args) != 4 {
			panic("omega.SetStructureRingLaws: PowZeroClause's left side is not monoid_pow applied to four arguments")
		}
		l.monoidPow = head
		if l.InUniv == nil || l.RingOnUniverse == nil || l.FieldOnUniverse == nil {
			panic("omega.SetStructureRingLaws: InUniv, RingOnUniverse and FieldOnUniverse are required (a whole-type fact is read on the carrier 𝕌)")
		}
		inUniv, _ := l.InUniv.StripConclForAll()
		memberHead, memberArgs := ext.MatchesApply(inUniv.Conclusion())
		memberConst, isConst := memberHead.AsConst()
		if !isConst || len(memberArgs) != 2 {
			panic("omega.SetStructureRingLaws: InUniv's body is not a membership `x ∈ 𝕌`")
		}
		l.member = memberConst.Meta()
	}
	structureLaws = l
	resetStructureRings()
}

// SetStructureInstances installs the concrete-carrier facts (nil
// uninstalls).
func SetStructureInstances(instances []StructureInstance) {
	for i, inst := range instances {
		if inst.Fact == nil {
			panic(fmt.Sprintf("omega.SetStructureInstances: instance %d has no fact", i))
		}
		if (inst.Literal == nil) != (inst.LiteralBridge == nil) {
			panic(fmt.Sprintf("omega.SetStructureInstances: instance %d sets one of Literal / LiteralBridge without the other", i))
		}
		comps, ok := structureComponentsOf(inst.Fact.Conclusion(), structureLaws)
		if !ok {
			panic(fmt.Sprintf("omega.SetStructureInstances: instance %d is not a ring or field structure fact: %s",
				i, ext.PrintTerm(inst.Fact.Conclusion())))
		}
		laws, _ := fallbackReader.reading()
		if !structureSetIsUniverse(laws, comps.carrierSet, comps.zero) && inst.Literal != nil {
			// A literal the ring reads but does not form has no closure
			// law to place it in the set; the leaves would reach it
			// unchecked.
			panic(fmt.Sprintf("omega.SetStructureInstances: instance %d is a ring on a carrier set and spells a literal of its own: %s",
				i, ext.PrintTerm(inst.Fact.Conclusion())))
		}
		if e := inst.RealEmbedding; e != nil {
			checkRealEmbedding(i, e, comps)
		}
	}
	structureInstances = slices.Clone(instances)
	resetStructureRings()
}

// SetStructureBundleFoundation installs the laws' capability foundation
// closure for the scope-less gate (the twin of SetIntBundleFoundation).
func SetStructureBundleFoundation(keys map[core.PropKey]bool) { structureFoundationKeys = keys }

// SetStructureInstanceFoundation installs the installed instances'
// capability foundation closure for the scope-less gate.
func SetStructureInstanceFoundation(keys map[core.PropKey]bool) {
	structureInstanceFoundationKeys = keys
}

// StructureBundleAllowsTarget — the gate's twin for the structure ring's
// laws.
func StructureBundleAllowsTarget(target core.PropKey) bool {
	if target == "" {
		return true
	}
	return !structureFoundationKeys[target]
}

// StructureInstancesAllowTarget — the gate for the installed instances:
// a proof an instance rests on may not read its carrier through it.
func StructureInstancesAllowTarget(target core.PropKey) bool {
	if target == "" {
		return true
	}
	return !structureInstanceFoundationKeys[target]
}

// StructureRingEnabled reports whether the structure ring is live: its
// laws are installed.
func StructureRingEnabled() bool { return structureLaws != nil }

// InstalledStructureRingLaws is the installed table, for a test that
// observes what it holds; nil when none is installed.
func InstalledStructureRingLaws() *StructureRingLaws { return structureLaws }

func resetStructureRings() {
	structureGeneration.Add(1)
}

// structureComponents are the operations and carrier projected from the
// record of a carrier fact, with whole-type structures restricted to 𝕌.
type structureComponents struct {
	add, zero, neg, mul, one, sub Term
	carrierSet                    Term
	inv, div                      Term
	ringRecord, fieldRecord       Term
}

func (c structureComponents) carrier() core.HolType { return c.zero.Type() }

// lawBodyAt substitutes a record into a law's leading binder and reads
// its final body as a term. This is matching only: it reads no theorem.
func (l *StructureRingLaws) lawBodyAt(law *prop.PropWrapper, record Term) Term {
	abs := ext.MatchesFORALL(law.Conclusion())
	if abs.IsZero() {
		panic("omega: a record law has no leading binder")
	}
	var types []core.TypeSubst
	if !core.MatchTypeInto(abs.Var().Type(), record.Type(), func(core.VarType) bool { return true }, &types) {
		panic("omega: a record law's binder does not match its record")
	}
	types = slices.DeleteFunc(types, func(s core.TypeSubst) bool { return s.HolType.Equals(s.VarType) })
	abs = ext.MatchesFORALL(law.Conclusion().TypeSubstitute(types...))
	body := abs.Body().Substitute(core.MakeTermSubst(abs.Var(), record))
	for {
		if a := ext.MatchesFORALL(body); !a.IsZero() {
			body = a.Body()
		} else if _, b, ok := prop.MatchesIMPLY(body); ok {
			body = b
		} else {
			break
		}
	}
	return body
}

func (l *StructureRingLaws) normalTerm(t Term) Term {
	if l.NormalizeTerm != nil {
		return l.NormalizeTerm(t)
	}
	return t
}

// normalFact is w with its conclusion in the instance normal form —
// the form `at` gives every derived fact, and the one the ring's
// records and components are read in, so a law instantiated at a
// record discharges its structure hypothesis from the fact it is read
// from however the goal spelled the record.
func (l _ReadLaws) normalFact(w *prop.PropWrapper) *prop.PropWrapper {
	if l.normalize == nil {
		return w
	}
	return w.RewriteConcl(l.normalize)
}

// closureComponent reads an operation from its closure law's concluding
// membership, peeling its element arguments and normalizing its record
// projection.
func (l *StructureRingLaws) closureComponent(law *prop.PropWrapper, record Term, arity int) (Term, Term) {
	_, args := ext.MatchesApply(l.lawBodyAt(law, record))
	if len(args) != 2 {
		panic("omega: a closure law does not conclude a membership")
	}
	op := args[0]
	for range arity {
		app, ok := op.AsAppliedTerm()
		if !ok {
			panic("omega: a closure law's operation has too few arguments")
		}
		op = app.Fun()
	}
	return l.normalTerm(op), l.normalTerm(args[1])
}

// wholeBridge selects the chapter's whole-type equivalence. Carrier
// facts need no bridge; the returned record is the whole fact's subject.
func (l *StructureRingLaws) wholeBridge(fact Term) (*prop.PropWrapper, Term) {
	head, args := ext.MatchesApply(fact)
	predicate, ok := head.AsConst()
	if !ok || len(args) != 1 {
		return nil, nil
	}
	switch string(predicate.Name()) {
	case commRingConstName:
		return l.RingOnUniverse, args[0]
	case fieldConstName:
		return l.FieldOnUniverse, args[0]
	}
	return nil, nil
}

// carrierTerm reads the bridge's right side without deriving a theorem.
// Matching must use its universal carrier, never the whole record's field.
func (l *StructureRingLaws) carrierTerm(fact Term) Term {
	bridge, record := l.wholeBridge(fact)
	if bridge == nil {
		return fact
	}
	_, carrier, ok := prop.MatchesIFF(l.lawBodyAt(bridge, record))
	if !ok {
		panic("omega: a whole-type structure bridge is not an equivalence")
	}
	return carrier
}

// structureRecordOf reads the record a ring or field fact is stated
// at, as the fact spells it: ring for comm_ring_on, field for field_on
// (the other nil), through the whole-type bridge for a whole-type fact.
// The one head match the components and the carrier are read from.
func structureRecordOf(fact Term, laws *StructureRingLaws) (ring, field Term, ok bool) {
	if laws == nil {
		return nil, nil, false
	}
	head, args := ext.MatchesApply(laws.carrierTerm(fact))
	predicate, isConst := head.AsConst()
	if !isConst || len(args) != 1 {
		return nil, nil, false
	}
	switch string(predicate.Name()) {
	case commRingOnConstName:
		return args[0], nil, true
	case fieldOnConstName:
		return nil, args[0], true
	}
	return nil, nil, false
}

// fieldRingRecord is the ring record a field's record projects to,
// read from the FieldRing law without deriving it.
func (l *StructureRingLaws) fieldRingRecord(field Term) Term {
	_, projected := ext.MatchesApply(l.lawBodyAt(l.FieldRing, field))
	if len(projected) != 1 {
		panic("omega: the field's ring projection does not name one record")
	}
	return projected[0]
}

// structureCarrierOf is the carrier type of a ring or field fact: the
// type of its ring's zero, read from the ZeroIn law at the record as
// the fact spells it. The normal form is a kernel equation and keeps
// every term's type, so the carrier needs none of it — and the scans
// over a context (structureCarriers, structureFactsAt) ask only this
// of every hypothesis and installed instance, at every decision.
func structureCarrierOf(fact Term, laws *StructureRingLaws) (core.HolType, bool) {
	ring, field, ok := structureRecordOf(fact, laws)
	if !ok {
		return nil, false
	}
	if field != nil {
		ring = laws.fieldRingRecord(field)
	}
	_, member := ext.MatchesApply(laws.lawBodyAt(laws.ZeroIn, ring))
	if len(member) != 2 {
		panic("omega: a closure law does not conclude a membership")
	}
	return member[0].Type(), true
}

func structureComponentsOf(fact Term, laws *StructureRingLaws) (structureComponents, bool) {
	ring, field, ok := structureRecordOf(fact, laws)
	if !ok {
		return structureComponents{}, false
	}
	// The records in the normal form: the fact a ring is built at is
	// read in it (structureRingFor), and so is every derived fact's
	// conclusion (at), so a law instantiated at a record meets the
	// fact that discharges its hypothesis spelled the same way — a goal
	// may state `field_on(mk_field(field_ring(K).add, …))`, whose ring
	// `field_ring(mk_field(…))` normalizes inside.
	c := structureComponents{}
	if field != nil {
		c.fieldRecord = laws.normalTerm(field)
		c.ringRecord = laws.normalTerm(laws.fieldRingRecord(c.fieldRecord))
		c.inv, _ = laws.closureComponent(laws.InvIn, c.fieldRecord, 1)
		c.div, _ = laws.closureComponent(laws.DivIn, c.fieldRecord, 2)
	} else {
		c.ringRecord = laws.normalTerm(ring)
	}
	c.zero, c.carrierSet = laws.closureComponent(laws.ZeroIn, c.ringRecord, 0)
	c.one, _ = laws.closureComponent(laws.OneIn, c.ringRecord, 0)
	c.add, _ = laws.closureComponent(laws.AddIn, c.ringRecord, 2)
	c.neg, _ = laws.closureComponent(laws.NegIn, c.ringRecord, 1)
	c.mul, _ = laws.closureComponent(laws.MulIn, c.ringRecord, 2)
	c.sub, _ = laws.closureComponent(laws.SubIn, c.ringRecord, 2)
	return c, true
}

func structureSetIsUniverse(laws _ReadLaws, set, zero Term) bool {
	inUniv := laws.at(laws.InUniv, []Term{zero}, nil)
	_, args := ext.MatchesApply(inUniv.Conclusion())
	return set.AlphaEquals(args[1])
}

// structureRing is the ring machinery instantiated at one fact: the
// derived structure facts on the carrier set, and the matchers. The
// leaves themselves are wired per decision (bind), since a leaf on a
// carrier set discharges its guards from the goal's hypotheses.
type structureRing struct {
	// fact is the resident assumption or installed theorem. ringFact is
	// comm_ring_on(R): the fact itself, its whole-type bridge, or a
	// field's ring projection. fieldFact is the corresponding field_on.
	fact, ringFact, fieldFact *prop.PropWrapper
	comps                     structureComponents
	set                       Term               // the carrier set of ringFact
	universe                  bool               // set is 𝕌: every membership is InUniv
	instance                  *StructureInstance // the installed instance, nil for a resident fact
	laws                      _ReadLaws

	// dom holds the matchers and the literal readers, which read no
	// context: mentionsComponent and ScaleEquation use it. A decision
	// runs on a bound copy.
	dom *Domain

	// derived structure facts, Γ ⊢ … on set
	monoidMul, monoidAdd, addGroup, group *prop.PropWrapper

	// unguardedLaws holds, on the carrier 𝕌, each law read at this ring
	// with its membership guard discharged once (unguarded): the
	// whole-type shape `Γ ⊢ ∀xs. body`, which a leaf instantiates at its
	// terms with no guard left to pay for. Keyed by the law AND the
	// structure fact it is read at: one monoid law serves both monoids.
	// Unused on a carrier set.
	unguardedMu   sync.Mutex
	unguardedLaws map[unguardedKey]*prop.PropWrapper

	// oneNotZero is Γ ⊢ ¬(one = zero) at a field, read once
	// (structure_refute.go); nil at a ring that is no field.
	oneNotZeroOnce sync.Once
	oneNotZero     *prop.PropWrapper
}

type unguardedKey struct{ law, fact *prop.PropWrapper }

// ringFor returns the ring at either form of a ring or field fact, read
// through this reader and kept by the fact's statement and provenance.
// The ring holds the fact with its conclusion in the instance normal
// form, as it holds every derived fact and component; a resident fact
// is read as the goal spells it and keeps that hypothesis.
func (r *LibraryReader) ringFor(fact *prop.PropWrapper, instance *StructureInstance) *structureRing {
	laws, ok := r.reading()
	if !ok {
		return nil
	}
	key := string(fact.Conclusion().AlphaKey())
	if fact.NumHyps() > 0 {
		key = "assumed|" + key
	}
	r.mu.Lock()
	defer r.mu.Unlock()
	if sr, ok := r.rings[key]; ok {
		return sr
	}
	fact = laws.normalFact(fact)
	comps, ok := structureComponentsOf(fact.Conclusion(), laws.StructureRingLaws)
	if !ok {
		return nil
	}
	sr := &structureRing{fact: fact, comps: comps, instance: instance, laws: laws,
		unguardedLaws: map[unguardedKey]*prop.PropWrapper{}}
	sr.build()
	r.rings[key] = sr
	return sr
}

// lawAt instantiates a general law at lead (its record or a definition
// clause's parameters), discharges
// the structure hypothesis from fact when the law has one, and
// instantiates the body's own leading binders at args: Γ ⊢ body[args],
// its membership guard, when the law has one, still ahead of the body
// (memberCtx.discharge). The law's type variables are instantiated by
// matching its first binder's type against lead[0]'s.
func lawAt(law *prop.PropWrapper, lead []Term, fact *prop.PropWrapper, args ...Term) *prop.PropWrapper {
	if law == nil {
		panic("omega: a structure ring law the leaves read is not installed")
	}
	w := law
	if len(lead) > 0 {
		abs := ext.MatchesFORALL(w.Conclusion())
		if abs.IsZero() {
			panic(fmt.Sprintf("omega: structure ring law has no leading binder: %s", ext.PrintTerm(w.Conclusion())))
		}
		var env []core.TypeSubst
		if !core.MatchTypeInto(abs.Var().Type(), lead[0].Type(), func(core.VarType) bool { return true }, &env) {
			panic(fmt.Sprintf("omega: structure ring law's first binder %s does not type-match the component %s",
				ext.PrintTerm(abs.Var()), ext.PrintTerm(lead[0])))
		}
		env = slices.DeleteFunc(env, func(s core.TypeSubst) bool { return s.HolType.Equals(s.VarType) })
		if len(env) > 0 {
			w = w.TypeInst(env...)
		}
		w = w.ConclForAllInsts(lead...)
	}
	if fact != nil {
		w = w.DemoteHyp().DeriveHypFrom(fact)
	}
	if len(args) > 0 {
		w = w.ConclForAllInsts(args...)
	}
	return w
}

// at computes the projections of an instantiated carrier law.
func (l _ReadLaws) at(law *prop.PropWrapper, lead []Term, fact *prop.PropWrapper, args ...Term) *prop.PropWrapper {
	w := lawAt(law, lead, fact, args...)
	if l.normalize != nil {
		w = w.RewriteConcl(l.normalize)
	}
	return w
}

// build derives the structure facts on the carrier set and the
// context-free matchers.
func (sr *structureRing) build() {
	laws := sr.laws
	c := sr.comps
	carrierFact := sr.fact
	if bridge, record := laws.wholeBridge(sr.fact.Conclusion()); bridge != nil {
		carrierFact = laws.normalFact(lawAt(bridge, []Term{record}, nil).EqMP(sr.fact))
	}
	sr.ringFact, sr.set = carrierFact, c.carrierSet
	if c.fieldRecord != nil {
		sr.fieldFact = carrierFact
		sr.ringFact = laws.at(laws.FieldRing, []Term{c.fieldRecord}, sr.fieldFact)
	}
	sr.universe = structureSetIsUniverse(laws, sr.set, c.zero)
	ringOn := []Term{c.ringRecord}
	sr.monoidMul = laws.at(laws.MulMonoid, ringOn, sr.ringFact)
	sr.monoidAdd = laws.at(laws.AddMonoid, ringOn, sr.ringFact)
	sr.addGroup = laws.at(laws.AddGroup, ringOn, sr.ringFact)
	_, subjects := ext.MatchesApply(sr.addGroup.Conclusion())
	sr.group = laws.at(laws.Group, subjects, sr.addGroup)
	sr.dom = sr.bind(nil).dom
}

// ── memberships ─────────────────────────────────────────────────────────────

// memberCtx proves the memberships one decision needs: an atom's from
// the goal's hypotheses — a resident `t ∈ c`, or a conjunct of a
// resident conjunction — and a formed term's from the closure laws at
// its parts; on the carrier 𝕌 every membership is InUniv. What it
// cannot prove it records in missing, and the decision declines: the
// closer does not infer `t ∈ c` from `t ∈ s` and `s ⊆ c` (the manual's
// structure ring entry says why), it names the atom instead.
type memberCtx struct {
	sr      *structureRing
	hyps    []Term
	proofs  map[core.TermKey]*prop.PropWrapper
	missing []Term
}

func (sr *structureRing) members(hyps []Term) *memberCtx {
	return &memberCtx{sr: sr, hyps: hyps, proofs: map[core.TermKey]*prop.PropWrapper{}}
}

// membership is the term `t ∈ set`.
func (m *memberCtx) membership(t Term) Term {
	member := core.MakeConstTerm(m.sr.laws.member,
		core.MakeFun(t.Type(), core.MakeFun(m.sr.set.Type(), core.TypeBool())))
	return ext.Apply(member, t, m.sr.set)
}

// isMembership reports whether t is `u ∈ set` at this ring's set, and u.
func (m *memberCtx) isMembership(t Term) (Term, bool) {
	head, args := ext.MatchesApply(t)
	c, isConst := head.AsConst()
	if !isConst || c.Meta() != m.sr.laws.member || len(args) != 2 || !args[1].AlphaEquals(m.sr.set) {
		return nil, false
	}
	return args[0], true
}

// prove is Γ ⊢ t ∈ set, or false with t's unprovable atom recorded.
func (m *memberCtx) prove(t Term) (*prop.PropWrapper, bool) {
	if m.sr.universe {
		return m.sr.laws.at(m.sr.laws.InUniv, []Term{t}, nil), true
	}
	key := t.AlphaKey()
	if w, ok := m.proofs[key]; ok {
		return w, w != nil
	}
	before := len(m.missing)
	w := m.proveUncached(t)
	m.proofs[key] = w
	if w == nil {
		// A formed term fails through a part, already recorded; an
		// atom is recorded here.
		if len(m.missing) == before {
			m.missing = append(m.missing, t)
		}
		return nil, false
	}
	return w, true
}

func (m *memberCtx) proveUncached(t Term) *prop.PropWrapper {
	if w := m.resident(t); w != nil {
		return w
	}
	sr := m.sr
	c, laws, d := sr.comps, sr.laws, sr.dom
	ringOn := []Term{c.ringRecord}
	closure := func(law *prop.PropWrapper, lead []Term, fact *prop.PropWrapper, args ...Term) *prop.PropWrapper {
		w, _, ok := m.discharge(laws.at(law, lead, fact, args...))
		if !ok {
			return nil
		}
		return w
	}
	switch {
	case t.AlphaEquals(c.zero):
		return laws.at(laws.ZeroIn, ringOn, sr.ringFact)
	case t.AlphaEquals(c.one):
		return laws.at(laws.OneIn, ringOn, sr.ringFact)
	}
	if a, b, ok := d.matchPlus(t); ok {
		return closure(laws.AddIn, ringOn, sr.ringFact, a, b)
	}
	if a, b, ok := d.matchStar(t); ok {
		return closure(laws.MulIn, ringOn, sr.ringFact, a, b)
	}
	if a, b, ok := d.matchSub(t); ok {
		return closure(laws.SubIn, ringOn, sr.ringFact, a, b)
	}
	if a, ok := d.matchNeg(t); ok {
		return closure(laws.NegIn, ringOn, sr.ringFact, a)
	}
	if c.fieldRecord != nil {
		if a, ok := t.AsAppliedTerm(); ok && a.Fun().AlphaEquals(c.inv) {
			return closure(laws.InvIn, []Term{c.fieldRecord}, sr.fieldFact, a.Arg())
		}
		if a, b, ok := d.matchQuotient(t); ok {
			return closure(laws.DivIn, []Term{c.fieldRecord}, sr.fieldFact, a, b)
		}
	}
	// A power: the additive power of one (a numeral) at the additive
	// monoid, an element's multiplicative power at the multiplicative.
	if head, args := ext.MatchesApply(t); len(args) == 4 {
		if h, isConst := head.AsConst(); isConst {
			if pow, isPow := laws.monoidPow.AsConst(); isPow && h.Meta() == pow.Meta() {
				switch {
				case args[0].AlphaEquals(c.add) && args[1].AlphaEquals(c.zero):
					return closure(laws.PowIn, []Term{sr.set, c.add, c.zero}, sr.monoidAdd, args[2], args[3])
				case args[0].AlphaEquals(c.mul) && args[1].AlphaEquals(c.one):
					return closure(laws.PowIn, []Term{sr.set, c.mul, c.one}, sr.monoidMul, args[2], args[3])
				}
			}
		}
	}
	return nil
}

// resident finds `t ∈ set` among the hypotheses, as a hypothesis or as
// a conjunct of one.
func (m *memberCtx) resident(t Term) *prop.PropWrapper {
	target := m.membership(t)
	for _, h := range m.hyps {
		if h.AlphaEquals(target) {
			return prop.Assume(h)
		}
	}
	for _, h := range m.hyps {
		if w := conjunctProof(h, target); w != nil {
			return w
		}
	}
	return nil
}

// conjunctProof is {h} ⊢ target when target is a conjunct of the
// conjunction h, else nil.
func conjunctProof(h, target Term) *prop.PropWrapper {
	a, b, ok := prop.MatchesAND(h)
	if !ok {
		return nil
	}
	if a.AlphaEquals(target) {
		return prop.HypAND0(a, b)
	}
	if b.AlphaEquals(target) {
		return prop.HypAND1(a, b)
	}
	if w := conjunctProof(a, target); w != nil {
		return prop.HypAND0(a, b).DeriveTrans(w)
	}
	if w := conjunctProof(b, target); w != nil {
		return prop.HypAND1(a, b).DeriveTrans(w)
	}
	return nil
}

// discharge removes a membership guard ahead of w's conclusion —
// `u ∈ set ∧ … ⇒ body`, each conjunct a membership at this ring's set
// — proving every membership; a conclusion without such a guard is
// returned as it is. When a conjunct is no such membership or is
// unprovable, ok is false and failed names that conjunct.
func (m *memberCtx) discharge(w *prop.PropWrapper) (out *prop.PropWrapper, failed Term, ok bool) {
	guard, _, isGuarded := prop.MatchesIMPLY(w.Conclusion())
	if !isGuarded {
		return w, nil, true
	}
	proof, failed, ok := m.proveGuard(guard)
	if !ok {
		return nil, failed, false
	}
	return w.DemoteHyp().DeriveHypFrom(proof), nil, true
}

// proveGuard is Γ ⊢ guard for a conjunction of memberships at set;
// false, with the conjunct, when one is no such membership or is
// unprovable.
func (m *memberCtx) proveGuard(guard Term) (*prop.PropWrapper, Term, bool) {
	if a, b, ok := prop.MatchesAND(guard); ok {
		pa, failed, okA := m.proveGuard(a)
		if !okA {
			return nil, failed, false
		}
		pb, failed, okB := m.proveGuard(b)
		if !okB {
			return nil, failed, false
		}
		// The two conjuncts may be one membership (`u ∈ c ∧ u ∈ c` for
		// op(u, u)): the kernel keeps one hypothesis, discharged once.
		w := prop.ConclAND(a, b).DeriveHypFrom(pa)
		return prop.WrapProp(pb.MaybeDeriveTrans(w)), nil, true
	}
	u, ok := m.isMembership(guard)
	if !ok {
		return nil, guard, false
	}
	w, ok := m.prove(u)
	if !ok {
		return nil, guard, false
	}
	return w, nil, true
}

// must discharges a leaf law's guard whose memberships the decision
// checked ahead (proveAtoms): a failure here is the ring forming a term
// over an atom it never checked, or a law whose guard is not a
// membership at the set.
func (m *memberCtx) must(w *prop.PropWrapper) *prop.PropWrapper {
	out, failed, ok := m.discharge(w)
	if !ok {
		panic(fmt.Sprintf("omega: structure ring could not discharge the guard %s of %s",
			ext.PrintTerm(failed), ext.PrintTerm(w.Conclusion())))
	}
	return out
}

// unguarded is, on the carrier 𝕌, law read at this ring with its
// membership guard discharged once: `Γ ⊢ ∀xs. body`, the whole-type
// shape, memoized per law. The guard is discharged at the law's own
// binders (InUniv), which are then re-generalized.
func (sr *structureRing) unguarded(law *prop.PropWrapper, lead []Term, fact *prop.PropWrapper, m *memberCtx) *prop.PropWrapper {
	sr.unguardedMu.Lock()
	defer sr.unguardedMu.Unlock()
	key := unguardedKey{law, fact}
	if w, ok := sr.unguardedLaws[key]; ok {
		return w
	}
	w := sr.laws.at(law, lead, fact)
	body, vars := w.StripConclForAll()
	open, failed, ok := m.discharge(body)
	if !ok {
		panic(fmt.Sprintf("omega: structure ring on 𝕌 could not discharge the guard %s of %s",
			ext.PrintTerm(failed), ext.PrintTerm(body.Conclusion())))
	}
	w = open.ConclForAllList(vars...)
	sr.unguardedLaws[key] = w
	return w
}

// proveAtoms proves the membership of every atom of the terms — the
// leaves the ring's reading stops at — recording each it cannot (in
// missing); true when all are proved. On the carrier 𝕌 nothing is
// checked.
func (m *memberCtx) proveAtoms(terms ...Term) bool {
	if m.sr.universe {
		return true
	}
	ok := true
	for _, t := range terms {
		for _, a := range m.sr.atoms(t) {
			if _, proved := m.prove(a); !proved {
				ok = false
			}
		}
	}
	return ok
}

// atoms lists the leaves of t under the ring's reading: the elements
// of the carrier the reading does not decompose.
func (sr *structureRing) atoms(t Term) []Term {
	d := sr.dom
	var out []Term
	var walk func(Term)
	walk = func(t Term) {
		if _, shaped, _ := d.asLiteral(t); shaped {
			return
		}
		if l, r, ok := d.matchPlus(t); ok {
			walk(l)
			walk(r)
			return
		}
		if l, r, ok := d.matchStar(t); ok {
			walk(l)
			walk(r)
			return
		}
		if l, r, ok := d.matchSub(t); ok {
			walk(l)
			walk(r)
			return
		}
		if a, ok := d.matchNeg(t); ok {
			walk(a)
			return
		}
		if base, _, ok := d.powLiteral(t); ok {
			walk(base)
			return
		}
		if d.matchQuotient != nil {
			if numerator, denominator, ok := d.matchQuotient(t); ok {
				walk(numerator)
				walk(denominator)
				return
			}
		}
		if d.isElem(t) {
			out = append(out, t)
		}
	}
	walk(t)
	return out
}

// ── the leaves, bound to a decision ─────────────────────────────────────────

// boundRing is the ring's machinery wired to one decision's
// memberships.
type boundRing struct {
	sr      *structureRing
	members *memberCtx
	dom     *Domain
	ring    *ringVocab
	subneg  *subnegVocab
	// foldedLiterals is set once the ring has folded a pair of numeral
	// literals, which it does by nat's numeral arithmetic.
	foldedLiterals atomic.Bool
	// realEvidence admits ℝ's arithmetic as the evidence that an embedded
	// real is not zero (embeddedNonzero): the decision's policy admits the
	// real layer and its bundle is installed.
	realEvidence bool
}

// at instantiates a law's body binders at args through the ring's
// reading of the law: on the carrier 𝕌 the law unguarded once per ring
// (unguarded), on a carrier set its guard discharged from the
// decision's memberships at this instance.
func (b *boundRing) at(law *prop.PropWrapper, lead []Term, fact *prop.PropWrapper, args ...Term) *prop.PropWrapper {
	if b.sr.universe {
		return b.sr.unguarded(law, lead, fact, b.members).ConclForAllInsts(args...)
	}
	return b.members.must(b.sr.laws.at(law, lead, fact, args...))
}

// moveAcross is the move-across of an equation carrying sub/neg into the
// positive two-sided form, `⊢ t ⇔ positive`, nil where t carries none.
// At a ring on 𝕌 the laws it reads have no guard, so the result does not
// turn on the decision's memberships: a decision, the evidence searches
// under it and the next decision over the same hypotheses ask for the
// same equations, and the answer is kept for the arith step
// (structureMoveMemo).
func (b *boundRing) moveAcross(t Term) *prop.PropWrapper {
	if !b.sr.universe {
		return b.subneg.moveAcrossCmp(t)
	}
	key := structureMoveKey{ring: b.sr, term: t.AlphaKey()}
	if w, ok := structureMoveMemo.lookup(key, t); ok {
		return w
	}
	w := b.subneg.moveAcrossCmp(t)
	structureMoveMemo.store(key, t, w)
	return w
}

// structureMoveKey names a move-across: the ring and the equation.
type structureMoveKey struct {
	ring *structureRing
	term core.TermKey
}

// structureMoveCap bounds the move-acrosses kept for a step.
const structureMoveCap = 4096

// structureMoves is the step's memo of move-acrosses at rings on 𝕌.
type structureMoves struct {
	mu      sync.Mutex
	entries map[structureMoveKey]structureMove
}

type structureMove struct {
	term  Term
	proof *prop.PropWrapper // nil: the equation carries nothing to move
}

var structureMoveMemo structureMoves

func (m *structureMoves) lookup(key structureMoveKey, t Term) (*prop.PropWrapper, bool) {
	m.mu.Lock()
	defer m.mu.Unlock()
	e, ok := m.entries[key]
	if !ok || !e.term.Equals(t) {
		return nil, false
	}
	return e.proof, true
}

func (m *structureMoves) store(key structureMoveKey, t Term, w *prop.PropWrapper) {
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.entries == nil || len(m.entries) >= structureMoveCap {
		m.entries = make(map[structureMoveKey]structureMove)
	}
	m.entries[key] = structureMove{term: t, proof: w}
}

func (m *structureMoves) reset() {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.entries = nil
}

// bind wires the Domain, the ringVocab and the subnegVocab at the fact
// for a decision under hyps: every leaf law on a carrier set discharges
// its guard through the decision's memberships (at).
func (sr *structureRing) bind(hyps []Term) *boundRing {
	laws := sr.laws
	c := sr.comps
	members := sr.members(hyps)
	bound := &boundRing{sr: sr, members: members}
	ringOn := []Term{c.ringRecord}
	mulMonoid := []Term{sr.set, c.mul, c.one}
	addMonoid := []Term{sr.set, c.add, c.zero}
	_, addGroupComps := ext.MatchesApply(sr.addGroup.Conclusion())
	atRing := func(law *prop.PropWrapper, args ...Term) *prop.PropWrapper {
		return bound.at(law, ringOn, sr.ringFact, args...)
	}

	carrier := c.carrier()
	never := func(Term) (Term, Term, bool) { return nil, nil, false }
	matchBin := func(op Term) func(Term) (Term, Term, bool) {
		return func(t Term) (Term, Term, bool) {
			app, ok := t.AsAppliedTerm()
			if !ok {
				return nil, nil, false
			}
			inner, ok := app.Fun().AsAppliedTerm()
			if !ok || !inner.Fun().AlphaEquals(op) {
				return nil, nil, false
			}
			return inner.Arg(), app.Arg(), true
		}
	}
	matchUn := func(op Term) func(Term) (Term, bool) {
		return func(t Term) (Term, bool) {
			app, ok := t.AsAppliedTerm()
			if !ok || !app.Fun().AlphaEquals(op) {
				return nil, false
			}
			return app.Arg(), true
		}
	}
	// monoid_pow at the carrier: (A → A → A) → A → A → num → A with A := τ.
	powConst, _ := laws.monoidPow.AsConst()
	powMeta := powConst.Meta()
	powType := core.MakeFun(core.MakeFun(carrier, core.MakeFun(carrier, carrier)),
		core.MakeFun(carrier, core.MakeFun(carrier, core.MakeFun(dsl.NumType, carrier))))
	monoidPow := core.MakeConstTerm(powMeta, powType)
	isMonoidPow := func(head Term) bool {
		h, ok := head.AsConst()
		return ok && h.Meta() == powMeta
	}
	powHead := ext.Apply(monoidPow, c.add, c.zero, c.one) // monoid_pow(add, zero, one) : num → A
	numeral := func(n _Integer) Term { return ext.Apply(powHead, numeralOf(n)) }
	// canonicalLiteral reads monoid_pow(add, zero, one, lit).
	canonicalLiteral := func(t Term) (_Integer, bool, bool) {
		head, args := ext.MatchesApply(t)
		if !isMonoidPow(head) || len(args) != 4 ||
			!args[0].AlphaEquals(c.add) || !args[1].AlphaEquals(c.zero) || !args[2].AlphaEquals(c.one) {
			return _Integer{}, false, false
		}
		x, numeralShaped := asNumeral(args[3])
		if !numeralShaped {
			return _Integer{}, false, false
		}
		n, exact := literalValue(x)
		return n, true, exact
	}
	dom := &Domain{
		name:      "ring(" + ext.PrintTerm(c.zero) + ")",
		plus:      func(a, b Term) Term { return ext.Apply(c.add, a, b) },
		star:      func(a, b Term) Term { return ext.Apply(c.mul, a, b) },
		numeral:   numeral,
		matchPlus: matchBin(c.add),
		matchStar: matchBin(c.mul),
		sub:       func(a, b Term) Term { return ext.Apply(c.sub, a, b) },
		neg:       func(a Term) Term { return ext.Apply(c.neg, a) },
		matchSub:  matchBin(c.sub),
		matchNeg:  matchUn(c.neg),
		matchLt:   never, matchLe: never, matchGt: never, matchGe: never,
		asLiteral: func(t Term) (_Integer, bool, bool) {
			if t.AlphaEquals(c.zero) {
				return _Integer{}, true, true
			}
			if t.AlphaEquals(c.one) {
				return integerOne, true, true
			}
			if n, shaped, ok := canonicalLiteral(t); shaped {
				return n, true, ok
			}
			if sr.instance != nil && sr.instance.Literal != nil {
				n, shaped, ok := sr.instance.Literal(t)
				if !shaped || !ok {
					return _Integer{}, shaped, false
				}
				return integerOfBig(n), true, true
			}
			return _Integer{}, false, false
		},
		isElem: func(t Term) bool { return t.Type().Equals(carrier) },
		matchPow: func(t Term) (Term, Term, bool) {
			head, args := ext.MatchesApply(t)
			if !isMonoidPow(head) || len(args) != 4 ||
				!args[0].AlphaEquals(c.mul) || !args[1].AlphaEquals(c.one) {
				return nil, nil, false
			}
			return args[2], args[3], true
		},
	}
	if c.fieldRecord != nil {
		dom.matchQuotient = matchBin(c.div)
		dom.quotientProduct = func(t Term) (Term, bool) {
			u, v, ok := dom.matchQuotient(t)
			if !ok {
				return nil, false
			}
			return dom.star(u, ext.Apply(c.inv, v)), true
		}
		dom.matchInverse = func(t Term) (Term, bool) {
			app, ok := t.AsAppliedTerm()
			if !ok || !app.Fun().AlphaEquals(c.inv) {
				return nil, false
			}
			return app.Arg(), true
		}
		dom.inverse = func(x Term) Term { return ext.Apply(c.inv, x) }
	}

	// pow0 / pow1 bridges: ⊢ monoid_pow(add, zero, one, 0) = zero and
	// Γ ⊢ monoid_pow(add, zero, one, 1) = one.
	pow0IsZero := func() *prop.PropWrapper {
		return laws.at(laws.PowZeroClause, []Term{c.add, c.zero, c.one}, nil)
	}
	pow1IsOne := func() *prop.PropWrapper { return bound.at(laws.PowOne, addMonoid, sr.monoidAdd, c.one) }

	ring := &ringVocab{dom: dom, plusOp: c.add, starOp: c.mul}
	ring.commuteADD = func(a, b Term) *prop.PropWrapper { return bound.at(laws.Comm, addMonoid, sr.monoidAdd, a, b) }
	ring.associateADD = func(a, b, d Term) *prop.PropWrapper {
		return bound.at(laws.Assoc, addMonoid, sr.monoidAdd, a, b, d).EqSym() // (a+b)+c = a+(b+c)
	}
	ring.commuteMUL = func(a, b Term) *prop.PropWrapper { return bound.at(laws.Comm, mulMonoid, sr.monoidMul, a, b) }
	ring.associateMUL = func(a, b, d Term) *prop.PropWrapper {
		return bound.at(laws.Assoc, mulMonoid, sr.monoidMul, a, b, d).EqSym()
	}
	ring.distributeMUL = func(a, b, d Term) *prop.PropWrapper { return atRing(laws.LeftDistrib, a, b, d) }
	ring.rightDistrib = func(a, b, d Term) *prop.PropWrapper { return atRing(laws.RightDistrib, a, b, d) }
	ring.oneMul = func(a Term) *prop.PropWrapper {
		// numeral(1)·a = one·a = a
		return pow1IsOne().LeftApply(c.mul).RightApply(a).
			EqTrans(bound.at(laws.LeftIdentity, mulMonoid, sr.monoidMul, a))
	}
	ring.addZeroR = func(a Term) *prop.PropWrapper {
		// a + numeral(0) = a + zero = a
		return pow0IsZero().LeftApply(ring.plusLeft(a)).
			EqTrans(bound.at(laws.RightIdentity, addMonoid, sr.monoidAdd, a))
	}
	ring.zeroMul = func(a Term) *prop.PropWrapper {
		// numeral(0)·a = zero·a = zero = numeral(0)
		z := pow0IsZero()
		return z.LeftApply(c.mul).RightApply(a).
			EqTrans(atRing(laws.MulLeftZero, a)).
			EqTrans(z.EqSym())
	}
	ring.mulZeroR = func(a Term) *prop.PropWrapper {
		z := pow0IsZero()
		return z.LeftApply(ring.starLeft(a)).
			EqTrans(atRing(laws.MulRightZero, a)).
			EqTrans(z.EqSym())
	}
	// Literal folds: numeral(a) + numeral(b) = numeral(a + b) by PowAdd at
	// the additive monoid and nat's norm_num under the power's congruence;
	// products by comm_ring.AddPowMulOn.
	literalPair := func(l, r Term) (_Integer, _Integer, bool) {
		a, shaped1, ok1 := canonicalLiteral(l)
		b, shaped2, ok2 := canonicalLiteral(r)
		return a, b, shaped1 && ok1 && shaped2 && ok2
	}
	ring.normAdd = func(l, r Term) (*prop.PropWrapper, bool) {
		a, b, ok := literalPair(l, r)
		if !ok {
			return nil, false
		}
		aT, bT := numeralOf(a), numeralOf(b)
		natEq, ok := NormNatAdd(aT, bT) // ⊢ a + b = k
		if !ok {
			return nil, false
		}
		bound.foldedLiterals.Store(true)
		fold := bound.at(laws.PowAdd, addMonoid, sr.monoidAdd, c.one, aT, bT) // ⊢ pow(a + b) = pow a + pow b
		return fold.EqSym().EqTrans(natEq.LeftApply(powHead)), true
	}
	ring.normMul = func(l, r Term) (*prop.PropWrapper, bool) {
		a, b, ok := literalPair(l, r)
		if !ok {
			return nil, false
		}
		aT, bT := numeralOf(a), numeralOf(b)
		natEq, ok := NormNatMul(aT, bT) // ⊢ a · b = k
		if !ok {
			return nil, false
		}
		bound.foldedLiterals.Store(true)
		fold := atRing(laws.AddPowMul, aT, bT) // ⊢ pow(a · b) = pow a · pow b
		return fold.EqSym().EqTrans(natEq.LeftApply(powHead)), true
	}
	ring.mulSort, ring.decomposeStar = buildMulSort(c.mul, dom.matchStar, ring.commuteMUL, ring.associateMUL)
	ring.literalBridge = func(t Term, n _Integer) *prop.PropWrapper {
		switch {
		case t.AlphaEquals(c.zero):
			return pow0IsZero().EqSym()
		case t.AlphaEquals(c.one):
			return pow1IsOne().EqSym()
		}
		if _, shaped, _ := canonicalLiteral(t); shaped {
			return prop.Refl(t)
		}
		if sr.instance != nil && sr.instance.LiteralBridge != nil {
			return sr.instance.LiteralBridge(t, n.bigInt())
		}
		panic(fmt.Sprintf("omega: structure ring read %s as the literal %s but has no bridge for its spelling", ext.PrintTerm(t), n))
	}
	// The power's unfold: monoid_pow(mul, one, m, c) = m·(m·(…·numeral(1))),
	// the twins' chain shape, ending in the canonical numeral one.
	ring.powUnfold = func(m Term, cnt uint64) *prop.PropWrapper {
		if cnt > expUnfoldMax {
			return nil
		}
		powM := ext.Apply(monoidPow, c.mul, c.one, m) // monoid_pow(mul, one, m) : num → A
		var unfold func(k uint64) *prop.PropWrapper
		unfold = func(k uint64) *prop.PropWrapper {
			if k == 0 {
				// pow(m, 0) = one = numeral(1)
				return laws.at(laws.PowZeroClause, []Term{c.mul, c.one, m}, nil).EqTrans(pow1IsOne().EqSym())
			}
			inner := unfold(k - 1) // ⊢ pow(m, k-1) = chain
			kMinus1 := Numeral(k - 1)
			powSuc := laws.at(laws.PowSucClause, []Term{c.mul, c.one, m}, nil, kMinus1) // ⊢ pow(m, suc(k-1)) = m·pow(m, k-1)
			sucEq := sucBits(kMinus1)                                                   // ⊢ suc(k-1) = k
			if sucEq == nil {
				return nil
			}
			cong := sucEq.LeftApply(powM) // ⊢ pow(m, suc(k-1)) = pow(m, k)
			return cong.EqSym().EqTrans(powSuc).EqTrans(inner.LeftApply(ring.starLeft(m)))
		}
		return unfold(cnt)
	}
	if c.fieldRecord != nil {
		ring.quotientUnfold = func(u, v Term) *prop.PropWrapper {
			return bound.at(laws.DivMulInv, []Term{c.fieldRecord}, sr.fieldFact, u, v)
		}
		ring.inverseUnfold = func(x, y Term) *prop.PropWrapper {
			return bound.at(laws.InvMul, []Term{c.fieldRecord}, sr.fieldFact, x, y)
		}
	}
	dom.polyMul = ring.polyMul

	subneg := &subnegVocab{
		ring:        ring,
		negOp:       c.neg,
		subToAddNeg: func(a, b Term) *prop.PropWrapper { return atRing(laws.SubAddNeg, a, b) },
		negAdd:      func(a, b Term) *prop.PropWrapper { return bound.at(laws.NegAdd, addGroupComps, sr.addGroup, a, b) },
		negNeg:      func(a Term) *prop.PropWrapper { return bound.at(laws.InvInv, addGroupComps, sr.group, a) },
		negZero: func() *prop.PropWrapper {
			// −numeral(0) = −zero = zero = numeral(0)
			z := pow0IsZero()
			return z.LeftApply(c.neg).
				EqTrans(laws.at(laws.InvOne, addGroupComps, sr.group)).
				EqTrans(z.EqSym())
		},
		mulRightNeg: func(x, b Term) *prop.PropWrapper { return atRing(laws.MulRightNeg, x, b) },
	}
	// The equality move-across laws are derived, not read: with
	//   cancelAdd(p, q): ⊢ (p − q) + q = p
	// (SubAddNeg, then reassociate, the inverse pair is zero, zero is
	// neutral) and the additive group's right cancellation
	//   op(y, x) = op(z, x) ⇔ y = z,
	//   (x − y) + y = z + y ⇔ x − y = z  reads, under cancelAdd(x, y),  as
	//   x = z + y ⇔ x − y = z,
	// and symmetrically for a subtraction on the right.
	cancelAdd := func(p, q Term) *prop.PropWrapper {
		negQ := dom.neg(q)
		return subneg.subToAddNeg(p, q).LeftApply(c.add).RightApply(q). // (p − q) + q = (p + −q) + q
										EqTrans(ring.associateADD(p, negQ, q)).                                                      // = p + (−q + q)
										EqTrans(bound.at(laws.LeftInverse, addGroupComps, sr.group, q).LeftApply(ring.plusLeft(p))). // = p + zero
										EqTrans(bound.at(laws.RightIdentity, addMonoid, sr.monoidAdd, p))                            // = p
	}
	// eqHead(l) is the partial application `(=) l`; eqConst the bare `=`
	// at the carrier.
	eqHead := func(l Term) Term { return core.Eq(l, l).Fun() }
	eqConst := func(l Term) Term {
		app, _ := eqHead(l).AsAppliedTerm()
		return app.Fun()
	}
	subneg.eqSubRightAdd = func(x, y, z Term) *prop.PropWrapper {
		// (x − y) + y = z + y ⇔ x − y = z
		cancel := bound.at(laws.RightCancel, addGroupComps, sr.group, y, dom.sub(x, y), z)
		// ((x − y) + y = z + y) ⇔ (x = z + y), by cancelAdd on the equation's left side
		read := cancelAdd(x, y).LeftApply(eqConst(x)).RightApply(dom.plus(z, y))
		return cancel.EqSym().EqTrans(read) // (x − y = z) ⇔ (x = z + y)
	}
	subneg.eqSubLeftAdd = func(x, y, z Term) *prop.PropWrapper {
		// x + z = (y − z) + z ⇔ x = y − z
		cancel := bound.at(laws.RightCancel, addGroupComps, sr.group, z, x, dom.sub(y, z))
		// (x + z = (y − z) + z) ⇔ (x + z = y), by cancelAdd on the right side
		read := cancelAdd(y, z).LeftApply(eqHead(dom.plus(x, z)))
		return cancel.EqSym().EqTrans(read) // (x = y − z) ⇔ (x + z = y)
	}
	bound.dom, bound.ring, bound.subneg = dom, ring, subneg
	return bound
}

// ── finding the fact for a goal ─────────────────────────────────────────────

// isNumberCarrier reports whether τ is a carrier a dedicated arith layer
// owns (num, real, int) or bool — never the structure ring's.
func isNumberCarrier(τ core.HolType) bool {
	return τ.Equals(dsl.NumType) || τ.Equals(dsl.RealType) || τ.Equals(dsl.IntType) || τ.Equals(core.TypeBool())
}

// structureFactsAt lists the facts available for carrier τ: the resident
// hypotheses headed by either form of comm_ring or field at τ (assumed),
// then the installed instances at τ.
func structureFactsAt(hyps []Term, τ core.HolType, instances bool, reader *LibraryReader) []*structureRing {
	if structureLaws == nil {
		return nil
	}
	reader = readerOrFallback(reader)
	var out []*structureRing
	for _, h := range hyps {
		carrier, ok := structureCarrierOf(h, structureLaws)
		if !ok || !carrier.Equals(τ) {
			continue
		}
		if sr := reader.ringFor(prop.Assume(h), nil); sr != nil {
			out = append(out, sr)
		}
	}
	for i := range structureInstances {
		if !instances {
			break
		}
		inst := &structureInstances[i]
		carrier, ok := structureCarrierOf(inst.Fact.Conclusion(), structureLaws)
		if !ok || !carrier.Equals(τ) {
			continue
		}
		if sr := reader.ringFor(inst.Fact, inst); sr != nil {
			out = append(out, sr)
		}
	}
	return out
}

// walkTerm visits t and every subterm — applications' functions and
// arguments, abstractions' bodies — until visit returns false. A plain
// structural descent: the subterm under a binder is seen as written
// (ext.SubTerms re-wraps it over the binder path).
func walkTerm(t Term, visit func(Term) bool) bool {
	if t == nil {
		return true
	}
	if !visit(t) {
		return false
	}
	if app, ok := t.AsAppliedTerm(); ok {
		return walkTerm(app.Fun(), visit) && walkTerm(app.Arg(), visit)
	}
	if abs, ok := t.AsAbsTerm(); ok {
		return walkTerm(abs.Body(), visit)
	}
	return true
}

// mentionsComponent reports whether some component of sr heads an
// application inside t, or t is one of sr's literals.
func (sr *structureRing) mentionsComponent(t Term) bool {
	hit := false
	walkTerm(t, func(s Term) bool {
		switch {
		case matches2(sr.dom.matchPlus, s), matches2(sr.dom.matchStar, s), matches2(sr.dom.matchSub, s),
			matches2(sr.dom.matchPow, s), matches1(sr.dom.matchNeg, s):
			hit = true
		case sr.dom.quotientProduct != nil && matchesQuotient(sr.dom, s):
			hit = true
		default:
			if _, shaped, _ := sr.dom.asLiteral(s); shaped {
				hit = true
			}
		}
		return !hit
	})
	return hit
}

func matches2(m func(Term) (Term, Term, bool), t Term) bool { _, _, ok := m(t); return ok }
func matches1(m func(Term) (Term, bool), t Term) bool       { _, ok := m(t); return ok }
func matchesQuotient(d *Domain, t Term) bool                { _, ok := d.quotientProduct(t); return ok }

// structureRingsForAtom lists the rings an equation atom between l and
// r at a non-number carrier may be decided at: the facts at that
// carrier whose components the atom mentions — or, when it mentions
// none (an equation between two atoms, `p = r`), every fact at the
// carrier, provided the context holds an equation there to combine it
// with (contextHoldsEquationAt): such an atom is no identity, so
// without one no ring decides it. Those on 𝕌 first (their memberships
// are free), then the rings on a set in the order found; the installed
// instances only when instances. Empty when there is none.
func structureRingsForAtom(hyps []Term, l, r Term, instances bool, reader *LibraryReader) []*structureRing {
	τ := l.Type()
	if isNumberCarrier(τ) {
		return nil
	}
	facts := structureFactsAt(hyps, τ, instances, reader)
	var universe, carrier []*structureRing
	admit := func(sr *structureRing) {
		if sr.universe {
			universe = append(universe, sr)
		} else {
			carrier = append(carrier, sr)
		}
	}
	for _, sr := range facts {
		if sr.mentionsComponent(l) || sr.mentionsComponent(r) {
			admit(sr)
		}
	}
	if len(universe)+len(carrier) == 0 && contextHoldsEquationAt(hyps, τ, l, r) {
		for _, sr := range facts {
			admit(sr)
		}
	}
	return append(universe, carrier...)
}

// contextHoldsEquationAt reports whether some hypothesis, or a conjunct
// of one, is an equation at carrier τ between distinct sides other than
// the atom `l = r` itself — an equation a combination could read.
func contextHoldsEquationAt(hyps []Term, τ core.HolType, l, r Term) bool {
	var holds func(t Term) bool
	holds = func(t Term) bool {
		if a, b, ok := prop.MatchesAND(t); ok {
			return holds(a) || holds(b)
		}
		hl, hr, ok := ext.MatchesEQ(t)
		if !ok || !hl.Type().Equals(τ) || hl.AlphaEquals(hr) {
			return false
		}
		return !(hl.AlphaEquals(l) && hr.AlphaEquals(r)) && !(hl.AlphaEquals(r) && hr.AlphaEquals(l))
	}
	return slices.ContainsFunc(hyps, holds)
}

// structureRingForAtom is the first of structureRingsForAtom with the
// instances admitted, for the content predicates and ScaleEquation,
// which read a fact's shape and no membership. nil when there is none.
func structureRingForAtom(hyps []Term, l, r Term, reader *LibraryReader) *structureRing {
	if rings := structureRingsForAtom(hyps, l, r, true, reader); len(rings) > 0 {
		return rings[0]
	}
	return nil
}

// IsStructureRingContent reports whether t is an equation (or its
// negation) at a non-number carrier whose sides the structure ring reads
// under a fact available in hyps or installed — the arith shape gate's
// question for this layer.
func IsStructureRingContent(hyps []Term, t Term) bool {
	if inner := ext.MatchesNOT(t); inner != nil {
		t = inner
	}
	l, r, ok := ext.MatchesEQ(t)
	if !ok {
		return false
	}
	return structureRingForAtom(hyps, l, r, nil) != nil
}

// StructureRingContent reports whether some atom of p (conclusion or
// hypothesis, under binders and connectives) is structure ring content,
// and whether an installed instance is among the facts that read one —
// the capability classifier's two questions: the laws are used by any
// such atom, an instance's roots only where an instance may decide it.
func StructureRingContent(p core.Prop) (content, viaInstance bool) {
	if structureLaws == nil {
		return false, false
	}
	hyps := p.Hyps()
	visit := func(root Term) {
		walkTerm(root, func(s Term) bool {
			if l, r, ok := ext.MatchesEQ(s); ok {
				for _, sr := range structureRingsForAtom(hyps, l, r, true, nil) {
					content = true
					if sr.instance != nil {
						viaInstance = true
					}
				}
			}
			return !viaInstance
		})
	}
	visit(p.Conclusion())
	for _, h := range hyps {
		if viaInstance {
			break
		}
		visit(h)
	}
	return content, viaInstance
}

// ── the leaves ──────────────────────────────────────────────────────────────

// structureLeaves are the two leaves of one decision context: the
// move-across of a structure ring's sub/neg into the positive two-sided
// form (the twin of realMoveAcrossLeaf) and the equation decider (⊤ for
// a ring identity or an integer combination of the context's equations,
// ⊥ for an equation the context denies, structure_refute.go). An atom is
// tried at each ring structureRingsForAtom
// lists, the first whose memberships the context holds deciding it;
// the rings are bound to the context once, shared by both leaves. The
// installed instances are read when policy admits them, and ℝ's
// arithmetic is evidence for an embedded real when it admits that, and
// for the argument of a modulus when it reads the modulus as well.
func structureLeaves(hyps []Term, policy ArithPolicy, reader *LibraryReader) (moveAcross, decide prop.Rewrite) {
	instances := policy.StructureInstances
	realEvidence := policy.Real && realLemmaBundle != nil
	// binder binds each ring to a context once.
	binder := func(context []Term) func(*structureRing) *boundRing {
		bound := map[*structureRing]*boundRing{}
		return func(sr *structureRing) *boundRing {
			if b, ok := bound[sr]; ok {
				return b
			}
			b := sr.bind(context)
			b.realEvidence = realEvidence
			bound[sr] = b
			return b
		}
	}
	at := func(context []Term, bind func(*structureRing) *boundRing, t Term,
		use func(b *boundRing, l, r Term) *prop.PropWrapper) *prop.PropWrapper {
		l, r, ok := ext.MatchesEQ(t)
		if !ok {
			return nil
		}
		for _, sr := range structureRingsForAtom(context, l, r, instances, reader) {
			b := bind(sr)
			if !b.members.proveAtoms(l, r) {
				continue
			}
			if w := use(b, l, r); w != nil {
				return w
			}
		}
		return nil
	}
	decideUnder := func(context []Term, bind func(*structureRing) *boundRing, t Term) *prop.PropWrapper {
		return at(context, bind, t, func(b *boundRing, l, r Term) *prop.PropWrapper {
			if w, ok := b.proveEq(context, l, r); ok {
				return eqtIntro(w)
			}
			if w := b.refuteEq(context, l, r); w != nil {
				return eqfIntro(w)
			}
			return nil
		})
	}
	bind := binder(hyps)
	moveAcross = func(t Term) *prop.PropWrapper {
		return at(hyps, bind, t, func(b *boundRing, _, _ Term) *prop.PropWrapper { return b.moveAcross(t) })
	}
	// The zero test of a modulus (modulus_zero.go): what ℝ's rows show of
	// the moduli the hypotheses spell is a fact about their arguments.
	// The facts are read where the hypotheses as written leave the atom
	// open, and are found once for the context, at the first such atom.
	var tested struct {
		done    bool
		facts   []*prop.PropWrapper
		context []Term
		bind    func(*structureRing) *boundRing
	}
	zeroTested := func() bool {
		if !tested.done {
			tested.done = true
			if policy.modulus() && realEvidence {
				tested.facts = modulusCarrierFacts(hyps)
			}
			tested.context = slices.Clone(hyps)
			for _, f := range tested.facts {
				tested.context = append(tested.context, f.Conclusion())
			}
			tested.bind = binder(tested.context)
		}
		return len(tested.facts) > 0
	}
	decide = func(t Term) *prop.PropWrapper {
		if w := decideUnder(hyps, bind, t); w != nil {
			return w
		}
		// Only an atom at the modulus's own carrier has anything to read
		// from the test.
		if l, _, ok := ext.MatchesEQ(t); !ok || !modulusCarrierIs(l.Type()) || !zeroTested() {
			return nil
		}
		w := decideUnder(tested.context, tested.bind, t)
		if w == nil {
			return nil
		}
		for _, f := range tested.facts {
			w = prop.WrapProp(f.MaybeDeriveTrans(w))
		}
		return w
	}
	return moveAcross, decide
}

// proveEq proves Γ ⊢ l = r at this ring from the context, the atoms'
// memberships checked by the caller: as a hypothesis, as a ring
// identity, or as an integer combination of the context's equations —
// at a field, of those, the cofactors of the context's zero products
// and what its equations leave once a common factor is cancelled
// (structure_refute.go), and the unit facts the sequent's inverse atoms
// ask for (structure_unit_facts.go), tried only once the context's
// equations alone decline.
func (b *boundRing) proveEq(hyps []Term, l, r Term) (*prop.PropWrapper, bool) {
	if w, ok := b.proveEqDirect(hyps, l, r); ok {
		return w, true
	}
	if b.subneg.hasSubNeg(l) || b.subneg.hasSubNeg(r) {
		return nil, false // the move-across leaf positivizes the goal first
	}
	eqs := b.equationHyps(hyps)
	if w, ok := b.proveByCombination(eqs, l, r); ok {
		return w, true
	}
	if units := b.unitEquations(hyps, eqs, l, r); len(units) > 0 {
		if w, ok := b.proveByCombination(append(slices.Clone(eqs), units...), l, r); ok {
			return w, true
		}
	}
	cofactors := append(b.zeroProductEquations(hyps), b.cancelledEquations(hyps)...)
	if len(cofactors) == 0 {
		return nil, false
	}
	all := append(slices.Clone(eqs), cofactors...)
	return b.proveByCombination(append(all, b.unitEquations(hyps, all, l, r)...), l, r)
}

// proveEqWithoutUnits is proveEq with no unit facts: what the evidence
// that a divisor is not zero reads, so that the search for evidence
// never asks for evidence in turn.
func (b *boundRing) proveEqWithoutUnits(hyps []Term, l, r Term) (*prop.PropWrapper, bool) {
	if w, ok := b.proveEqDirect(hyps, l, r); ok {
		return w, true
	}
	return b.proveByCombination(b.equationHyps(hyps), l, r)
}

// proveEqDirect proves `l = r` as a hypothesis or as a ring identity.
func (b *boundRing) proveEqDirect(hyps []Term, l, r Term) (*prop.PropWrapper, bool) {
	goal := core.Eq(l, r)
	if slices.ContainsFunc(hyps, goal.AlphaEquals) {
		return prop.Assume(goal), true
	}
	return b.proveRingEq(l, r)
}

// StructureRingMissingMemberships names, for an equation `l = r` (or its
// negation) that only rings on a carrier SET read, the atoms whose
// membership in the carrier the context does not hold — the atoms of
// its sides, and those of the context's equations at the carrier, which
// the combination does not read over an atom without one — the reason
// the structure ring declined the atom. Nil when the atom is not the
// structure ring's, when a ring on 𝕌 reads it, or when some ring on a
// set holds every membership; the set and the atoms are the first such
// ring's.
func StructureRingMissingMemberships(hyps []Term, t Term) (set Term, atoms []Term) {
	if inner := ext.MatchesNOT(t); inner != nil {
		t = inner
	}
	l, r, ok := ext.MatchesEQ(t)
	if !ok {
		return nil, nil
	}
	rings := structureRingsForAtom(hyps, l, r, true, nil)
	if len(rings) == 0 || rings[0].universe {
		return nil, nil
	}
	// held proves every membership the decision needs, recording in
	// the bound ring's memberCtx each it cannot; it runs over every
	// term, so the record is complete.
	held := func(b *boundRing) bool {
		ok := b.members.proveAtoms(l, r)
		for _, e := range b.sr.contextEquations(hyps) {
			if !b.members.proveAtoms(e.l, e.r) {
				ok = false
			}
		}
		return ok
	}
	for _, sr := range rings {
		if held(sr.bind(hyps)) {
			return nil, nil
		}
	}
	b := rings[0].bind(hyps)
	held(b)
	return rings[0].set, b.members.missing
}

// proveRingEq proves `l = r` as a ring identity: positive sides through
// the full ring; sides carrying sub/neg through the signed normalizer's
// move-across first.
func (b *boundRing) proveRingEq(l, r Term) (*prop.PropWrapper, bool) {
	if b.subneg.hasSubNeg(l) || b.subneg.hasSubNeg(r) {
		if mv := b.moveAcross(core.Eq(l, r)); mv != nil {
			pl, pr, ok := ext.MatchesEQ(prop.Rhs(mv))
			if !ok {
				return nil, false
			}
			w, ok := b.ring.ringProveFull(pl, pr)
			if !ok {
				return nil, false
			}
			return mv.EqSym().EqMP(w), true
		}
	}
	return b.ring.ringProveFull(l, r)
}

// ── integer combinations of the context's equations ────────────────────────

// ratPoly is the untrusted signed polynomial model over the ring's
// monomial basis: monomial key (the sorted atom keys of its factors
// joined, "" for the constant) → coefficient.
type ratPoly map[string]*big.Rat

func (p ratPoly) add(q ratPoly, scale *big.Rat) ratPoly {
	out := ratPoly{}
	for k, v := range p {
		out[k] = new(big.Rat).Set(v)
	}
	for k, v := range q {
		term := new(big.Rat).Mul(v, scale)
		if cur, ok := out[k]; ok {
			term.Add(term, cur)
		}
		if term.Sign() == 0 {
			delete(out, k)
		} else {
			out[k] = term
		}
	}
	return out
}

func monoKeyMul(a, b string) string {
	if a == "" {
		return b
	}
	if b == "" {
		return a
	}
	factors := append(strings.Split(a, "·"), strings.Split(b, "·")...)
	sort.Strings(factors)
	return strings.Join(factors, "·")
}

func (p ratPoly) mul(q ratPoly) ratPoly {
	out := ratPoly{}
	for ka, va := range p {
		for kb, vb := range q {
			k := monoKeyMul(ka, kb)
			term := new(big.Rat).Mul(va, vb)
			if cur, ok := out[k]; ok {
				term.Add(term, cur)
			}
			if term.Sign() == 0 {
				delete(out, k)
			} else {
				out[k] = term
			}
		}
	}
	return out
}

func ratConst(n _Integer) ratPoly {
	if n.isZero() {
		return ratPoly{}
	}
	return ratPoly{"": new(big.Rat).SetInt(n.bigInt())}
}

// poly reads t as a polynomial; ok is false on a term the ring does not
// read (a non-canonical literal, a power past the chain cap).
func (b *boundRing) poly(t Term) (ratPoly, bool) {
	d := b.dom
	if n, shaped, ok := d.asLiteral(t); shaped {
		if !ok {
			return nil, false
		}
		return ratConst(n), true
	}
	if l, r, ok := d.matchPlus(t); ok {
		pl, ok1 := b.poly(l)
		pr, ok2 := b.poly(r)
		if !ok1 || !ok2 {
			return nil, false
		}
		return pl.add(pr, big.NewRat(1, 1)), true
	}
	if l, r, ok := d.matchSub(t); ok {
		pl, ok1 := b.poly(l)
		pr, ok2 := b.poly(r)
		if !ok1 || !ok2 {
			return nil, false
		}
		return pl.add(pr, big.NewRat(-1, 1)), true
	}
	if a, ok := d.matchNeg(t); ok {
		pa, ok := b.poly(a)
		if !ok {
			return nil, false
		}
		return ratPoly{}.add(pa, big.NewRat(-1, 1)), true
	}
	if l, r, ok := d.matchStar(t); ok {
		pl, ok1 := b.poly(l)
		pr, ok2 := b.poly(r)
		if !ok1 || !ok2 {
			return nil, false
		}
		return pl.mul(pr), true
	}
	if base, cnt, ok := d.powLiteral(t); ok {
		pb, ok := b.poly(base)
		if !ok {
			return nil, false
		}
		out := ratConst(integerOne)
		for i := uint64(0); i < cnt; i++ {
			out = out.mul(pb)
		}
		return out, true
	}
	if product, ok := d.fieldProduct(t); ok {
		return b.poly(product)
	}
	if !d.isElem(t) {
		return nil, false
	}
	return ratPoly{string(t.AlphaKey()): big.NewRat(1, 1)}, true
}

// contextEquation is one equation the context holds at a ring's
// carrier: `l = r` with its proof Γ ⊢ l = r — the hypothesis itself, or
// its projection out of a conjunction hypothesis.
type contextEquation struct {
	eq    Term // l = r
	l, r  Term
	proof *prop.PropWrapper
}

// contextEquations lists the equations the hypotheses hold at this
// ring's carrier: a hypothesis `l = r`, or a conjunct of one — the
// shape a carrier law's guards arrive in, `x ∈ c ∧ y ∈ c ∧ l = r`, read
// as the memberships are (resident) and as the number domains read
// their constraints (splitConjuncts), each with its proof {h} ⊢ l = r.
func (sr *structureRing) contextEquations(hyps []Term) []contextEquation {
	var out []contextEquation
	for _, h := range hyps {
		if _, _, ok := prop.MatchesAND(h); ok {
			for _, part := range splitConjuncts(prop.Assume(h)) {
				eq := part.Conclusion()
				if l, r, ok := ext.MatchesEQ(eq); ok && sr.dom.isElem(l) {
					out = append(out, contextEquation{eq: eq, l: l, r: r, proof: part})
				}
			}
			continue
		}
		if l, r, ok := ext.MatchesEQ(h); ok && sr.dom.isElem(l) {
			out = append(out, contextEquation{eq: h, l: l, r: r, proof: prop.Assume(h)})
		}
	}
	return out
}

// equationHyp is one context equation at this ring in positive form:
// `lhs = rhs` with Γ' ⊢ lhs = rhs derived from the hypothesis (its
// move-across when it carried sub/neg).
type equationHyp struct {
	lhs, rhs Term
	proof    *prop.PropWrapper
	diff     ratPoly // poly(lhs) − poly(rhs)
}

func (b *boundRing) equationHyps(hyps []Term) []equationHyp {
	var out []equationHyp
	for _, e := range b.sr.contextEquations(hyps) {
		if eh, ok := b.equationHyp(e.proof); ok {
			out = append(out, eh)
		}
	}
	return out
}

// equationHyp reads the equation proof concludes as one the combination
// reads: in positive form, its atoms' memberships held, not a
// tautology.
func (b *boundRing) equationHyp(proof *prop.PropWrapper) (equationHyp, bool) {
	l, r, ok := ext.MatchesEQ(proof.Conclusion())
	if !ok {
		return equationHyp{}, false
	}
	// An equation over an atom whose membership the context lacks
	// cannot be read: its laws' guards would stay open.
	if !b.members.proveAtoms(l, r) {
		return equationHyp{}, false
	}
	if b.subneg.hasSubNeg(l) || b.subneg.hasSubNeg(r) {
		mv := b.moveAcross(proof.Conclusion())
		if mv == nil {
			return equationHyp{}, false
		}
		proof = mv.EqMP(proof) // {h} ⊢ positive
		l, r, ok = ext.MatchesEQ(prop.Rhs(mv))
		if !ok {
			return equationHyp{}, false
		}
	}
	pl, ok1 := b.poly(l)
	pr, ok2 := b.poly(r)
	if !ok1 || !ok2 {
		return equationHyp{}, false
	}
	diff := pl.add(pr, big.NewRat(-1, 1))
	if len(diff) == 0 {
		return equationHyp{}, false // a tautology contributes nothing
	}
	return equationHyp{lhs: l, rhs: r, proof: proof, diff: diff}, true
}

// proveByCombination proves `l = r` as an integer linear combination of
// the equations eqs: l − r = Σ cᵢ·(lᵢ − rᵢ) over the monomial
// basis, the cᵢ found by Gaussian elimination over ℚ and accepted only
// when every one is an integer. The replay: with Y := Σ_{c>0} c·rᵢ +
// Σ_{c<0} |c|·lᵢ and Y' := Σ_{c>0} c·lᵢ + Σ_{c<0} |c|·rᵢ, the ring proves
// ⊢ l + Y = r + Y', the equations prove ⊢ Y' = Y by congruence, and the
// additive group's right cancellation turns ⊢ l + Y = r + Y into ⊢ l = r.
func (b *boundRing) proveByCombination(eqs []equationHyp, l, r Term) (*prop.PropWrapper, bool) {
	sr := b.sr
	if b.subneg.hasSubNeg(l) || b.subneg.hasSubNeg(r) {
		return nil, false // the move-across leaf positivizes the goal first
	}
	if len(eqs) == 0 {
		return nil, false
	}
	pl, ok1 := b.poly(l)
	pr, ok2 := b.poly(r)
	if !ok1 || !ok2 {
		return nil, false
	}
	target := pl.add(pr, big.NewRat(-1, 1))
	if len(target) == 0 {
		return nil, false // a ring identity — proveRingEq's, and it declined
	}
	coeffs, ok := solveIntegerCombination(eqs, target)
	if !ok {
		return nil, false
	}
	d := b.dom
	var Y, Yprime Term
	var sides *prop.PropWrapper // ⊢ Y' = Y
	for i, e := range eqs {
		c := coeffs[i]
		if c == 0 {
			continue
		}
		var k _Integer
		var yTerm, yPrimeTerm Term
		var eqProof *prop.PropWrapper // Γ ⊢ k·(Y' summand) = k·(Y summand)
		if c > 0 {
			k = integerOf(c)
			yTerm, yPrimeTerm = e.rhs, e.lhs
			eqProof = e.proof
		} else {
			k = integerOf(-c)
			yTerm, yPrimeTerm = e.lhs, e.rhs
			eqProof = e.proof.EqSym()
		}
		kT := d.numeral(k)
		scaled := eqProof.LeftApply(b.ring.starLeft(kT)) // ⊢ k·y' = k·y
		yK, yPrimeK := d.star(kT, yTerm), d.star(kT, yPrimeTerm)
		if Y == nil {
			Y, Yprime, sides = yK, yPrimeK, scaled
			continue
		}
		sides = sides.LeftApply(b.ring.plusOp).Apply(scaled) // ⊢ (Y' + k·y') = (Y + k·y)
		Y, Yprime = d.plus(Y, yK), d.plus(Yprime, yPrimeK)
	}
	if Y == nil {
		return nil, false
	}
	ringEq, ok := b.ring.ringProveFull(d.plus(l, Y), d.plus(r, Yprime)) // ⊢ l + Y = r + Y'
	if !ok {
		return nil, false
	}
	// ⊢ r + Y' = r + Y, so ⊢ l + Y = r + Y.
	chain := ringEq.EqTrans(sides.LeftApply(b.ring.plusLeft(r)))
	// group right cancellation at the additive group: op(y, x) = op(z, x) ⇔ y = z
	// at x := Y, y := l, z := r.
	_, groupSubject := ext.MatchesApply(sr.group.Conclusion())
	cancel := b.at(sr.laws.RightCancel, groupSubject, sr.group, Y, l, r)
	lhs, _, ok := prop.MatchesIFF(cancel.Conclusion())
	if !ok || !lhs.AlphaEquals(chain.Conclusion()) {
		panic(fmt.Sprintf("omega: structure ring right cancellation does not read the combined equation: %s vs %s",
			ext.PrintTerm(lhs), ext.PrintTerm(chain.Conclusion())))
	}
	return cancel.EqMP(chain), true
}

// solveIntegerCombination finds integers cᵢ with Σ cᵢ·eqs[i].diff =
// target, by Gaussian elimination over ℚ (free unknowns set to zero);
// ok is false when there is no solution or the particular solution found
// is not integral.
func solveIntegerCombination(eqs []equationHyp, target ratPoly) ([]int64, bool) {
	// Monomial rows.
	keys := map[string]bool{}
	for k := range target {
		keys[k] = true
	}
	for _, e := range eqs {
		for k := range e.diff {
			keys[k] = true
		}
	}
	rows := make([]string, 0, len(keys))
	for k := range keys {
		rows = append(rows, k)
	}
	sort.Strings(rows)
	n := len(eqs)
	// Augmented matrix: one row per monomial, n coefficient columns + the target.
	mat := make([][]*big.Rat, len(rows))
	for i, k := range rows {
		mat[i] = make([]*big.Rat, n+1)
		for j := range mat[i] {
			mat[i][j] = new(big.Rat)
		}
		for j, e := range eqs {
			if v, ok := e.diff[k]; ok {
				mat[i][j].Set(v)
			}
		}
		if v, ok := target[k]; ok {
			mat[i][n].Set(v)
		}
	}
	// Row reduction.
	pivotCol := make([]int, 0, n)
	row := 0
	for col := 0; col < n && row < len(mat); col++ {
		pivot := -1
		for i := row; i < len(mat); i++ {
			if mat[i][col].Sign() != 0 {
				pivot = i
				break
			}
		}
		if pivot < 0 {
			continue
		}
		mat[row], mat[pivot] = mat[pivot], mat[row]
		inv := new(big.Rat).Inv(mat[row][col])
		for j := range mat[row] {
			mat[row][j].Mul(mat[row][j], inv)
		}
		for i := range mat {
			if i == row || mat[i][col].Sign() == 0 {
				continue
			}
			f := new(big.Rat).Set(mat[i][col])
			for j := range mat[i] {
				mat[i][j].Sub(mat[i][j], new(big.Rat).Mul(f, mat[row][j]))
			}
		}
		pivotCol = append(pivotCol, col)
		row++
	}
	// Consistency: a zero row with a nonzero target has no solution.
	for i := row; i < len(mat); i++ {
		if mat[i][n].Sign() != 0 {
			return nil, false
		}
	}
	coeffs := make([]int64, n)
	for i, col := range pivotCol {
		v := mat[i][n]
		if !v.IsInt() {
			return nil, false
		}
		if !v.Num().IsInt64() {
			return nil, false
		}
		c := v.Num().Int64()
		if c > 1<<31 || c < -(1<<31) {
			return nil, false
		}
		coeffs[col] = c
	}
	return coeffs, true
}

// ── scaling an equation (Lean's linear_combination coefficient) ───────────

// ScaleEquation reads eq as an equation `l = r` at a carrier an
// arithmetic layer owns — num, real, int, or a structure ring by a fact
// resident in hyps or installed — and returns its congruence under the
// carrier's multiplication by c, `c·l = c·r`, with the proof
// {eq} ⊢ c·l = c·r. This is what a Scaled(c, h) premise adds beside h:
// the author's polynomial coefficient, which the equality deciders then
// combine with the other equations by integers. ok is false when eq is
// not such an equation or c is not of its carrier's type.
func ScaleEquation(hyps []Term, c Term, eq Term, reader *LibraryReader) (Term, *prop.PropWrapper, bool) {
	l, r, ok := ext.MatchesEQ(eq)
	if !ok || !c.Type().Equals(l.Type()) {
		return nil, nil, false
	}
	var star func(a, b Term) Term
	switch {
	case l.Type().Equals(dsl.NumType):
		star = natDomain.star
	case l.Type().Equals(dsl.RealType):
		star = realDomain.star
	case l.Type().Equals(dsl.IntType):
		star = intDomain.star
	default:
		sr := structureRingForAtom(hyps, l, r, reader)
		if sr == nil {
			// The carrier may be a ring whose fact the atom itself does
			// not mention (two bare atoms): any fact at the carrier serves.
			facts := structureFactsAt(hyps, l.Type(), true, reader)
			if len(facts) == 0 {
				return nil, nil, false
			}
			sr = facts[0]
		}
		star = sr.dom.star
	}
	scaled := core.Eq(star(c, l), star(c, r))
	proof := prop.Assume(eq).LeftApply(starHead(star, c))
	if !proof.Conclusion().AlphaEquals(scaled) {
		panic("omega.ScaleEquation: the congruence does not spell the scaled equation")
	}
	return scaled, proof, true
}

// starHead returns the partial application `c · _` of a binary builder.
func starHead(star func(a, b Term) Term, c Term) Term {
	app, _ := star(c, c).AsAppliedTerm()
	return app.Fun()
}

// StructureRingContext binds the proved laws of one explicit ring to
// proved carrier memberships. It supplies identities and closure proofs
// without consulting installed concrete-carrier instances or equations.
type StructureRingContext struct {
	bound   *boundRing
	members []*prop.PropWrapper
}

// FoldedLiterals reports whether a proof this context has built folded a
// pair of numeral literals. The fold is nat's numeral arithmetic, so
// such a proof stands on the nat-arithmetic laws beside the ring's own.
func (c *StructureRingContext) FoldedLiterals() bool { return c.bound.foldedLiterals.Load() }

func BindStructureRing(laws *StructureRingLaws, read LibraryRead, fact *prop.PropWrapper, members ...*prop.PropWrapper) *StructureRingContext {
	if laws == nil {
		return nil
	}
	comps, ok := structureComponentsOf(fact.Conclusion(), laws)
	if !ok {
		return nil
	}
	reading := _ReadLaws{StructureRingLaws: laws}
	if laws.NormalizeWith != nil {
		reading.normalize = laws.NormalizeWith(read)
	}
	sr := &structureRing{fact: prop.Assume(fact.Conclusion()), comps: comps, laws: reading, unguardedLaws: map[unguardedKey]*prop.PropWrapper{}}
	sr.build()
	hyps := make([]Term, len(members))
	for i, w := range members {
		hyps[i] = w.Conclusion()
	}
	return &StructureRingContext{bound: sr.bind(hyps), members: append(append([]*prop.PropWrapper{}, members...), fact)}
}
func (c *StructureRingContext) restore(w *prop.PropWrapper) *prop.PropWrapper {
	for _, member := range c.members {
		w = prop.WrapProp(member.MaybeDeriveTrans(w))
	}
	return w
}
func (c *StructureRingContext) Member(t Term) (*prop.PropWrapper, bool) {
	w, ok := c.bound.members.prove(t)
	if !ok {
		return nil, false
	}
	return c.restore(w), true
}
func (c *StructureRingContext) Identity(l, r Term) (*prop.PropWrapper, bool) {
	if !c.bound.members.proveAtoms(l, r) {
		return nil, false
	}
	w, ok := c.bound.proveRingEq(l, r)
	if !ok {
		return nil, false
	}
	return c.restore(w), true
}
