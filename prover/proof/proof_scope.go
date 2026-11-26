package proof

import (
	"fmt"
	"sort"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/euc-ai/xugo/prover/tactic"
)

// Proof dependency capabilities are the non-cite dependencies hidden
// behind compound proof mechanisms.  They are deliberately named separately
// from theorem keys: a proof uses Arith or one IntOfReal instance; the
// installed capability manifest expands that name to the theorem roots
// which implement it.
const (
	CapabilityArithNat  = "arith:nat"
	CapabilityArithReal = "arith:real"
	CapabilityArithInt  = "arith:int"
	// CapabilityArithStructure is the structure ring (omega/structure_ring.go):
	// the ring at a comm_ring_on, comm_ring or field fact, whose roots are
	// the algebra chapters' carrier laws, the bridge to the whole type,
	// InUniv and the field's two whole-type laws.
	CapabilityArithStructure = "arith:structure"
	// CapabilityArithStructureInstances is the structure ring reading a
	// carrier through an installed instance theorem (ℂ:
	// complex_field.Field), whose roots are the instances: recorded only
	// where an instance may decide an atom, so a chapter over a ring of
	// its own does not depend on ℂ.
	CapabilityArithStructureInstances = "arith:structure-instances"
	// CapabilityArithModulus is the arith closer reading a carrier's
	// modulus (omega/modulus.go; ℂ's complex_abs): its sign and its laws
	// across the carrier's operations, whose roots are those laws.
	// Recorded where an Arith step's goal spells the modulus.
	CapabilityArithModulus = "arith:modulus"
	// CapabilityChase is the diagram-chase closer (prover/solver/chase):
	// its laws are the algebra and set chapters' carrier laws, installed
	// by library/serve, and a member they rest on may not use it.
	CapabilityChase     = "chase"
	CapabilityIntOfReal = "int_of_real:"
)

// CapabilitySpec is immutable installation-time metadata. Roots are the
// direct theorem dependencies exposed in the canonical proof graph;
// Foundation is their transitive closure and is used to reject a capability
// while proving any theorem it depends on.
//
// Foundation exists in two lifecycles: the install site computes a RAW
// closure — library/integrity/dag.Closure over the corpus DAG's dep edges
// (entries in own-key space) — and the canonical graph later REFINES it
// (RefineDependencyCapabilityFoundations; sole caller manifest.Build)
// to the complete reach once every proof's recorded capability is
// itself an edge to the bundle roots. The raw form is therefore an
// approximation: a reach that runs through another proof's capability
// use is invisible to a dep closure. ProofScope combines this closure
// with the complete graph's generated denial policy. `installed` keeps
// the raw form so a re-install (initEngine is
// reentrant by design; every serve/test entry point re-runs the corpus
// installs) is checked against what an install actually produces —
// comparing the fresh raw spec against the refined Foundation would
// report drift where there is none.
type CapabilitySpec struct {
	Roots      []core.PropKey
	Foundation map[core.PropKey]bool
	// installed is the raw install-time closure — the re-install
	// equality baseline. Refinement never touches it.
	installed map[core.PropKey]bool
}

var dependencyCapabilities = struct {
	sync.RWMutex
	m map[string]CapabilitySpec
}{m: make(map[string]CapabilitySpec)}

// InstallDependencyCapability installs an immutable capability description.
// Re-installing the same name is allowed only when it is byte-for-byte
// equivalent TO WHAT INSTALLATION PRODUCED for that name — roots plus the
// raw (pre-refinement) foundation closure; configuration drift fails
// loudly instead of changing proof semantics underneath already-created
// Scripts. A refined Foundation (see
// RefineDependencyCapabilityFoundations) is kept as the active closure
// and is NOT what a re-install is compared against — refinement is a
// designed completion, not drift.
func InstallDependencyCapability(name string, roots []core.PropKey, foundation map[core.PropKey]bool) {
	if name == "" {
		panic("InstallDependencyCapability: empty name")
	}
	spec := CapabilitySpec{
		Roots:      append([]core.PropKey(nil), roots...),
		Foundation: cloneKeySet(foundation),
		installed:  cloneKeySet(foundation),
	}
	sort.Slice(spec.Roots, func(i, j int) bool { return spec.Roots[i] < spec.Roots[j] })
	spec.Roots = compactKeys(spec.Roots)

	dependencyCapabilities.Lock()
	defer dependencyCapabilities.Unlock()
	if old, ok := dependencyCapabilities.m[name]; ok {
		if !sameCapabilityInstall(old, spec) {
			panic(fmt.Sprintf(
				"dependency capability %q reinstalled with different roots/foundation: had %d roots / %d foundation keys, reinstall has %d / %d",
				name, len(old.Roots), len(old.installed), len(spec.Roots), len(spec.installed)))
		}
		return
	}
	dependencyCapabilities.m[name] = spec
}

func cloneKeySet(in map[core.PropKey]bool) map[core.PropKey]bool {
	out := make(map[core.PropKey]bool, len(in))
	for k, v := range in {
		if v {
			out[k] = true
		}
	}
	return out
}

func compactKeys(in []core.PropKey) []core.PropKey {
	if len(in) == 0 {
		return in
	}
	out := in[:1]
	for _, k := range in[1:] {
		if k != out[len(out)-1] {
			out = append(out, k)
		}
	}
	return out
}

// sameCapabilityInstall compares what two INSTALL calls produced: sorted
// roots plus the raw install-time closure. The refined Foundation is
// deliberately not part of this — see InstallDependencyCapability.
func sameCapabilityInstall(a, b CapabilitySpec) bool {
	if len(a.Roots) != len(b.Roots) || len(a.installed) != len(b.installed) {
		return false
	}
	for i := range a.Roots {
		if a.Roots[i] != b.Roots[i] {
			return false
		}
	}
	for k := range a.installed {
		if !b.installed[k] {
			return false
		}
	}
	return true
}

// DependencyCapabilitySnapshot returns a defensive copy for the canonical
// merged-graph checker and dependency-witness generator.
func DependencyCapabilitySnapshot() map[string]CapabilitySpec {
	dependencyCapabilities.RLock()
	defer dependencyCapabilities.RUnlock()
	out := make(map[string]CapabilitySpec, len(dependencyCapabilities.m))
	for name, spec := range dependencyCapabilities.m {
		out[name] = CapabilitySpec{
			Roots:      append([]core.PropKey(nil), spec.Roots...),
			Foundation: cloneKeySet(spec.Foundation),
		}
	}
	return out
}

// RefineDependencyCapabilityFoundations replaces only the derived closure of
// already-installed capabilities. Roots are immutable; the canonical merged
// graph calls this after including every capability edge and rejecting cycles.
// Keeping this operation separate from installation makes configuration drift
// in direct roots a hard error while allowing the closure to become complete.
func RefineDependencyCapabilityFoundations(foundations map[string]map[core.PropKey]bool) {
	dependencyCapabilities.Lock()
	defer dependencyCapabilities.Unlock()
	for name, foundation := range foundations {
		spec, ok := dependencyCapabilities.m[name]
		if !ok {
			panic(fmt.Sprintf("refine unknown dependency capability %q", name))
		}
		spec.Foundation = cloneKeySet(foundation)
		dependencyCapabilities.m[name] = spec
	}
}

// ---------------------------------------------------------------------------
// The canonical proof-policy table
// ---------------------------------------------------------------------------
//
// Nobody declares a capability. A proof USES one — an Arith step consults
// a bundle, an int_of_real lift runs — and the use is observed on the
// proof's ProofScope, recorded by the family CNF recorder into the
// family's blob (CNFCache.member_capabilities), and read from there by
// the dependency manifest (manifest.Build) as the proof's capability
// edges. The policy records, per target, what its recorded proof used and
// what the complete dependency graph DENIES it: a capability whose
// bundle roots reach the target through the graph — possibly through
// OTHER proofs' uses, which no dep closure sees. A target absent from the
// table uses nothing and is denied nothing beyond what the raw
// install-time foundation already denies.
//
// The table itself is corpus content — one entry per target that uses or
// is denied something — so it lives at library/integrity/policy (generated
// by library/cmd/policy_gen) and is INSTALLED here at startup, the same
// inversion the omega bundles use. What stays in the tent is only the
// query.
//
// Not-installed is a legitimate state, not an error: policy_gen itself
// builds the graph with none installed. Callers for whom a missing policy
// would silently weaken the indirect-cycle check (the replay
// harness, the engine) assert ProofPolicyInstalled instead.

// Policy is one target's verdict: the capabilities its recorded proof
// used, and the capabilities the complete dependency graph denies it.
type Policy struct {
	Used   []string
	Denied []string
}

var (
	policies        map[core.PropKey]Policy
	policyDigest    string
	policyInstalled bool
)

// InstallProofPolicy installs the generated canonical policy table. Called at
// startup by serve.InstallProofPolicy. Idempotent by overwrite.
func InstallProofPolicy(table map[core.PropKey]Policy, digest string) {
	policies = table
	policyDigest = digest
	policyInstalled = true
}

// ProofPolicyInstalled reports whether a table has been installed. Harnesses
// that depend on the indirect-cycle check being live assert this.
func ProofPolicyInstalled() bool { return policyInstalled }

// ProofPolicyDigest is the installed table's digest ("" when none).
func ProofPolicyDigest() string { return policyDigest }

// LookupProofPolicy returns the target's recorded verdict. Callers must
// not mutate the returned slices.
func LookupProofPolicy(target core.PropKey) (Policy, bool) {
	p, ok := policies[target]
	return p, ok
}

// KnownPolicyTarget reports whether the table has a row for target — a
// target whose recorded proof uses a capability, or that some
// capability's foundation reaches.
func KnownPolicyTarget(target core.PropKey) bool {
	_, ok := policies[target]
	return ok
}

// ProofScope is lexical proof identity. It belongs to one Script/goal tree,
// so a nested Build of member Y naturally creates a Y scope and concurrent
// proofs do not communicate through ambient process state.
//
// It answers one question — may THIS proof use capability X — and records
// the uses it permits. A capability is refused for exactly two reasons,
// both read off the dependency graph, neither an author's declaration:
//
//   - the capability's raw foundation — the bundle roots' dep closure —
//     contains the target: using the bundle to prove a theorem the bundle
//     is built on is circular (direct cycle);
//   - the installed policy witness DENIES it: the complete dependency graph
//     (manifest.Build) found the bundle's roots reach the target through
//     the graph, which may run through other proofs' recorded uses that
//     no dep closure sees (indirect cycle).
//
// Everything else is allowed. A fresh target no member proves yet is
// gated by the raw foundation alone until the witness regenerates at its
// landing — the window the indirect-cycle check cannot see, closed by
// the same regeneration every landing already runs.
type ProofScope struct {
	Target core.PropKey
	denied map[string]bool

	mu   sync.Mutex
	used map[string]bool
	// unfolded is the constants the proof opened by their definitions
	// (the def-expand step), by name.
	unfolded map[string]bool

	// cite is the proof's read of a library theorem by its registered
	// name (Script.Dep's), set by the Script the scope arms: the read the
	// instance normal form takes its record equations through
	// (libraryRead).
	cite func(name string) ThmCert
	// reader is the proof's reading of the record equations for the
	// closers (libraryReader): cite, with the structure rings built
	// through it kept for the proof. Made at the first closer's read.
	reader *omega.LibraryReader

	// numerals is the arithmetic policy the rung's numeral reading runs
	// under (numeralPolicy), read once: the rung reads at every
	// comparison, and a proof's policy does not change.
	numeralsOnce sync.Once
	numerals     omega.ArithPolicy
}

// NewProofScope arms proof identity for target; the policy witness's
// verdict for target, when the table has one, is consulted on every use.
func NewProofScope(target core.PropKey) *ProofScope {
	s := &ProofScope{Target: target, used: map[string]bool{}}
	if p, ok := LookupProofPolicy(target); ok {
		s.denied = make(map[string]bool, len(p.Denied))
		for _, capability := range p.Denied {
			s.denied[capability] = true
		}
	}
	return s
}

// allows reports whether this proof may use capability. A nil scope
// (legacy hand-written callers, a session with no bound target) gates
// nothing here — the omega bundles apply their own raw foundation gate
// through UnscopedArithPolicy. It asks and records nothing, so it is
// the scope's own: a consumer of a capability goes through
// RequireCapability, or through ArithPolicy and RecordArith, and a use
// is then on the record.
func (s *ProofScope) allows(capability string) bool {
	_, refused := s.refusal(capability)
	return !refused
}

// refusal names why the proof may not use capability, when it may not.
func (s *ProofScope) refusal(capability string) (string, bool) {
	if s == nil {
		return "", false
	}
	spec, ok := capabilitySpec(capability)
	if !ok {
		return fmt.Sprintf("capability %q is not installed", capability), true
	}
	if s.Target == "" {
		return "", false
	}
	if spec.Foundation[s.Target] {
		return fmt.Sprintf("capability %q's foundation depends on the target", capability), true
	}
	if s.denied[capability] {
		return fmt.Sprintf("the canonical proof graph reaches the target from capability %q's roots (the policy witness denies it)", capability), true
	}
	return "", false
}

// note records a permitted use.
func (s *ProofScope) note(capability string) {
	s.mu.Lock()
	s.used[capability] = true
	s.mu.Unlock()
}

// Used returns the capabilities this proof has used so far, sorted — what
// the family CNF recorder writes as the member's declaration.
func (s *ProofScope) Used() []string {
	if s == nil {
		return nil
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	out := make([]string, 0, len(s.used))
	for capability := range s.used {
		out = append(out, capability)
	}
	sort.Strings(out)
	return out
}

// noteUnfolded records that the proof opened a constant by its
// definition. A nil scope — a session with no bound target — records
// nothing.
func (s *ProofScope) noteUnfolded(constant core.TermName) {
	if s == nil {
		return
	}
	s.mu.Lock()
	if s.unfolded == nil {
		s.unfolded = map[string]bool{}
	}
	s.unfolded[string(constant)] = true
	s.mu.Unlock()
}

// Unfolded returns the constants this proof has opened by their
// definitions so far, sorted — what the family CNF recorder reads the
// member's definition edges from.
func (s *ProofScope) Unfolded() []string {
	if s == nil {
		return nil
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	out := make([]string, 0, len(s.unfolded))
	for constant := range s.unfolded {
		out = append(out, constant)
	}
	sort.Strings(out)
	return out
}

// AllowsAnyArith reports whether the scope permits any arithmetic domain.
// Dispatchers that OPPORTUNISTICALLY reach for Arith (the engine's `auto`
// fast-path, the structural `arith` move) ask this first so a proof that
// may not use arithmetic sees a clean decline rather than an Arith step
// that records nothing it could replay. A nil scope permits nothing here —
// callers that treat nil as ungated must nil-check themselves.
func (s *ProofScope) AllowsAnyArith() bool {
	return s != nil && (s.allows(CapabilityArithNat) || s.allows(CapabilityArithReal) || s.allows(CapabilityArithInt) ||
		s.allows(CapabilityArithStructure))
}

func capabilitySpec(name string) (CapabilitySpec, bool) {
	dependencyCapabilities.RLock()
	defer dependencyCapabilities.RUnlock()
	spec, ok := dependencyCapabilities.m[name]
	return spec, ok
}

// ArithPolicy is the explicit bundle-selection policy threaded into omega
// for this proof: each domain the proof may use.
func (s *ProofScope) ArithPolicy() omega.ArithPolicy {
	if s == nil {
		return omega.ArithPolicy{}
	}
	return omega.ArithPolicy{
		Nat:                s.allows(CapabilityArithNat),
		Real:               s.allows(CapabilityArithReal),
		Int:                s.allows(CapabilityArithInt),
		Structure:          s.allows(CapabilityArithStructure),
		StructureInstances: s.allows(CapabilityArithStructureInstances),
		Modulus:            s.allows(CapabilityArithModulus),
	}
}

// numeralPolicy is ArithPolicy as the rung's numeral reading takes it:
// the same policy, computed once for the proof.
func (s *ProofScope) numeralPolicy() omega.ArithPolicy {
	s.numeralsOnce.Do(func() { s.numerals = s.ArithPolicy() })
	return s.numerals
}

// recordNumeralRead notes the bundles a numeral reading that fired on
// goal evaluated with: ℕ's, which every evaluation stands on, and ℝ's or
// ℤ's where the goal spells a numeral statement at that type
// (omega.NumeralDomains) — each only where the proof may use it, since a
// bundle the policy withheld was never consulted.
func (s *ProofScope) recordNumeralRead(goal core.Prop) {
	policy := s.numeralPolicy()
	if !policy.Nat {
		return
	}
	s.note(CapabilityArithNat)
	note := func(t core.Term) {
		real, integer := omega.NumeralDomains(t)
		if real && policy.Real {
			s.note(CapabilityArithReal)
		}
		if integer && policy.Int {
			s.note(CapabilityArithInt)
		}
	}
	note(goal.Conclusion())
	for h := range goal.HypIter() {
		note(h)
	}
}

// RecordArith notes the arithmetic domains an Arith step that fired on
// goal used: the domains the goal's term types name
// (ArithCapabilitiesForProp — the same classifier emit reads recorded
// steps with), restricted to the domains this scope permits, since a
// bundle the policy withheld was never consulted.
func (s *ProofScope) RecordArith(goal core.Prop) {
	if s == nil {
		return
	}
	policy := s.ArithPolicy()
	for _, capability := range ArithCapabilitiesForProp(goal) {
		switch capability {
		case CapabilityArithNat:
			if policy.Nat {
				s.note(capability)
			}
		case CapabilityArithReal:
			if policy.Real {
				s.note(capability)
			}
		case CapabilityArithInt:
			if policy.Int {
				s.note(capability)
			}
		case CapabilityArithStructure:
			if policy.Structure {
				s.note(capability)
			}
		case CapabilityArithStructureInstances:
			if policy.Structure && policy.StructureInstances {
				s.note(capability)
			}
		case CapabilityArithModulus:
			if policy.Modulus {
				s.note(capability)
			}
		}
	}
}

// libraryRead is the read the instance normal form (prover/tactic,
// InstanceNormal) takes a record equation through in scope's proof: the
// proof's own cite of the library theorem, so its recorded dependencies
// hold the equation. Nil without a scope, where the normal form reads
// through the fallback library/serve installs.
func libraryRead(scope *ProofScope) tactic.LibraryRead {
	if scope == nil || scope.cite == nil {
		return nil
	}
	return func(name string) *prop.PropWrapper { return prop.WrapProp(scope.cite(name)) }
}

// libraryReader is the reader omega's structure ring and the chase take
// a record equation through in scope's proof: libraryRead, with the
// rings built through it kept for the proof, one reader for every
// closer of the proof. Nil without a scope, where the closers read
// through the fallback library/serve installs.
func libraryReader(scope *ProofScope) *omega.LibraryReader {
	read := libraryRead(scope)
	if read == nil {
		return nil
	}
	scope.mu.Lock()
	defer scope.mu.Unlock()
	if scope.reader == nil {
		scope.reader = &omega.LibraryReader{Read: omega.LibraryRead(read)}
	}
	return scope.reader
}

// RequireCapability gates a non-Arith compound mechanism's use (an
// int_of_real lift) and records it: the proof may use capability unless
// it is not installed or its foundation reaches the target.
func (s *ProofScope) RequireCapability(capability string) {
	if s == nil {
		return // legacy hand-written caller
	}
	if reason, refused := s.refusal(capability); refused {
		panic(fmt.Sprintf("proof %s cannot use capability %q: %s", s.Target, capability, reason))
	}
	s.note(capability)
}

// ArithCapabilitiesForProp is the shared record/emit domain classifier. Nat
// is always present because real/int arithmetic uses the nat numeral layer;
// real and int are added only when those term types actually occur.
func ArithCapabilitiesForProp(p core.Prop) []string {
	seen := map[string]bool{CapabilityArithNat: true}
	var walk func(core.Term)
	walk = func(t core.Term) {
		if t == nil {
			return
		}
		if t.Type().Equals(dsl.RealType) {
			seen[CapabilityArithReal] = true
		}
		if t.Type().Equals(dsl.IntType) {
			seen[CapabilityArithInt] = true
		}
		if app, ok := t.AsAppliedTerm(); ok {
			walk(app.Fun())
			walk(app.Arg())
		}
		if abs, ok := t.AsAbsTerm(); ok {
			walk(abs.Var())
			walk(abs.Body())
		}
	}
	walk(p.Conclusion())
	for h := range p.HypIter() {
		walk(h)
	}
	// The structure ring is named by a FACT, not a type: an equation at a
	// carrier that is a comm_ring_on, comm_ring or field by a hypothesis
	// of p uses the laws, and one an installed instance may read uses
	// the instances as well (omega.StructureRingContent).
	if content, viaInstance := omega.StructureRingContent(p); content {
		seen[CapabilityArithStructure] = true
		if viaInstance {
			seen[CapabilityArithStructureInstances] = true
		}
	}
	// The modulus is named by its constant: a goal that spells it is
	// read through its laws (omega.ModulusContent).
	if omega.ModulusContent(p) {
		seen[CapabilityArithModulus] = true
	}
	out := make([]string, 0, len(seen))
	for capability := range seen {
		out = append(out, capability)
	}
	sort.Strings(out)
	return out
}
