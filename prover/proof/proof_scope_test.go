package proof

import (
	"strings"
	"sync"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/omega"
)

// installTestPolicy installs a synthetic policy table for one test and
// restores the previous state afterwards.
//
// These cases pin the MECHANISM — the three refusals, the recording —
// not any registry entry. The real table is corpus content
// (library/integrity/policy, one row per target that uses or is denied
// something) installed at startup, and deliberately not linked into this
// package; that the real table agrees with the canonical fixed point is
// pinned by manifest_test's Digest check, and exercised end-to-end by the
// replay harness.
func installTestPolicy(t *testing.T, table map[core.PropKey]Policy) {
	t.Helper()
	prevTable, prevDigest, prevInstalled := policies, policyDigest, policyInstalled
	t.Cleanup(func() {
		policies, policyDigest, policyInstalled = prevTable, prevDigest, prevInstalled
	})
	InstallProofPolicy(table, "test-policy-digest")
}

// The arithmetic capabilities are process-global and install ONCE (a
// re-install with a different foundation is configuration drift, by
// design), so every test here shares one foundation: nat's contains
// scopeTestNatBlocked, real's contains scopeTestRealBlocked, int's is
// empty.
var (
	scopeTestNatBlocked  = core.PropKey("prop_scope_test_nat_blocked")
	scopeTestRealBlocked = core.PropKey("prop_scope_test_real_blocked")
	scopeTestArithOnce   sync.Once
)

func installTestArith() {
	scopeTestArithOnce.Do(func() {
		InstallDependencyCapability(CapabilityArithNat, nil, map[core.PropKey]bool{scopeTestNatBlocked: true})
		InstallDependencyCapability(CapabilityArithReal, nil, map[core.PropKey]bool{scopeTestRealBlocked: true})
		InstallDependencyCapability(CapabilityArithInt, nil, nil)
	})
}

// The two refusals, and nothing else refuses: a target inside a
// bundle's raw foundation loses that bundle; a target the witness denies
// a bundle loses it. Every other target uses every installed capability.
func TestProofScopeRefusals(t *testing.T) {
	natBlocked := scopeTestNatBlocked
	witnessDenied := core.PropKey("prop_scope_refusal_witness")
	free := core.PropKey("prop_scope_refusal_free")
	installTestArith()
	installTestPolicy(t, map[core.PropKey]Policy{
		witnessDenied: {Used: []string{CapabilityArithNat}, Denied: []string{CapabilityArithInt}},
	})

	byFoundation := NewProofScope(natBlocked)
	if byFoundation.allows(CapabilityArithNat) || !byFoundation.allows(CapabilityArithReal) || !byFoundation.allows(CapabilityArithInt) {
		t.Fatalf("raw foundation: nat=%v real=%v int=%v", byFoundation.allows(CapabilityArithNat),
			byFoundation.allows(CapabilityArithReal), byFoundation.allows(CapabilityArithInt))
	}
	byWitness := NewProofScope(witnessDenied)
	if byWitness.allows(CapabilityArithInt) || !byWitness.allows(CapabilityArithNat) {
		t.Fatalf("witness denial: int=%v nat=%v", byWitness.allows(CapabilityArithInt), byWitness.allows(CapabilityArithNat))
	}
	open := NewProofScope(free)
	if got := open.ArithPolicy(); got != (omega.ArithPolicy{Nat: true, Real: true, Int: true}) {
		t.Fatalf("an unwitnessed, unexcluded target outside every foundation must use everything; got %+v", got)
	}
	if open.allows("int_of_real:prop_never_installed") {
		t.Fatal("an uninstalled capability was allowed")
	}
}

// A use is recorded, and only a permitted one: RecordArith notes the
// domains the goal names among those the policy enabled; a refused
// RequireCapability panics naming the reason and records nothing.
func TestProofScopeRecordsUse(t *testing.T) {
	natBlocked := scopeTestNatBlocked
	installTestArith()
	const lift = CapabilityIntOfReal + "prop_scope_record_source"
	InstallDependencyCapability(lift, nil, nil)

	x := ext.Var("x", dsl.RealType)
	realGoal := prop.MakeProp(x.Eq(x))

	scope := NewProofScope("prop_scope_record_free")
	if got := scope.Used(); len(got) != 0 {
		t.Fatalf("fresh scope has uses %v", got)
	}
	scope.RecordArith(realGoal)
	if got := strings.Join(scope.Used(), " "); got != CapabilityArithNat+" "+CapabilityArithReal {
		t.Fatalf("real goal should record nat and real; got %q", got)
	}
	scope.RequireCapability(lift)
	if got := scope.Used(); len(got) != 3 || got[2] != lift {
		t.Fatalf("lift use not recorded: %v", got)
	}

	blocked := NewProofScope(natBlocked)
	blocked.RecordArith(realGoal)
	if got := strings.Join(blocked.Used(), " "); got != CapabilityArithReal {
		t.Fatalf("a withheld domain must not be recorded as used; got %q", got)
	}

	const circularLift = CapabilityIntOfReal + "prop_scope_record_circular_source"
	InstallDependencyCapability(circularLift, nil, map[core.PropKey]bool{natBlocked: true})
	refused := NewProofScope(natBlocked)
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("a refused capability use did not panic")
		}
		if msg := r.(string); !strings.Contains(msg, "foundation depends on the target") {
			t.Fatalf("refusal names the wrong reason: %s", msg)
		}
		if got := strings.Join(refused.Used(), " "); got != CapabilityArithReal {
			t.Fatalf("a refused use was recorded: %q", got)
		}
	}()
	refused.RecordArith(realGoal)
	refused.RequireCapability(circularLift)
}

// With no table installed — the state library/cmd/policy_gen itself runs
// in, since it builds the graph in order to COMPUTE the table — only the
// raw foundation gates. It must not panic: not-installed is a legitimate
// state.
func TestProofPolicyUninstalledGatesByFoundationOnly(t *testing.T) {
	installTestPolicy(t, nil)
	policyInstalled = false
	installTestArith()

	scope := NewProofScope("prop_test_policy_absent")
	if !scope.allows(CapabilityArithNat) {
		t.Fatal("no table installed must not refuse an installed capability")
	}
	if ProofPolicyInstalled() {
		t.Fatal("ProofPolicyInstalled reported true with none installed")
	}
}

// TestInstallDependencyCapability_ReinstallAfterRefine pins the
// capability lifecycle initEngine exercises on every re-entry:
// install (raw closure) → manifest refine (complete closure) →
// re-install with the SAME raw closure. The re-install must be accepted
// — the refined Foundation is a designed completion, not configuration
// drift — and must not downgrade the refined closure. Genuine drift
// (different roots, or a different raw closure) must still panic.
func TestInstallDependencyCapability_ReinstallAfterRefine(t *testing.T) {
	const name = "test:reinstall_after_refine"
	rootA := core.PropKey("prop_reinstall_root_a")
	rawKey := core.PropKey("prop_reinstall_raw_dep")
	refinedKey := core.PropKey("prop_reinstall_refined_extra")
	raw := map[core.PropKey]bool{rootA: true, rawKey: true}

	InstallDependencyCapability(name, []core.PropKey{rootA}, raw)
	RefineDependencyCapabilityFoundations(map[string]map[core.PropKey]bool{
		name: {rootA: true, rawKey: true, refinedKey: true},
	})

	// Re-install with the identical raw spec: accepted, refined kept.
	InstallDependencyCapability(name, []core.PropKey{rootA}, raw)
	spec := DependencyCapabilitySnapshot()[name]
	if !spec.Foundation[refinedKey] {
		t.Fatal("re-install downgraded the refined foundation")
	}

	// A re-install whose RAW closure differs is genuine drift.
	func() {
		defer func() {
			if recover() == nil {
				t.Fatal("raw-foundation drift on re-install was accepted")
			}
		}()
		InstallDependencyCapability(name, []core.PropKey{rootA},
			map[core.PropKey]bool{rootA: true})
	}()

	// Different roots are genuine drift too.
	defer func() {
		if recover() == nil {
			t.Fatal("root drift on re-install was accepted")
		}
	}()
	InstallDependencyCapability(name, []core.PropKey{rootA, rawKey}, raw)
}

// The policy is lexical: two scopes read their own targets' verdicts,
// unmoved by the process-global legacy target or by each other.
func TestProofScopeArithPolicyIsLexical(t *testing.T) {
	natBlocked, realBlocked := scopeTestNatBlocked, scopeTestRealBlocked
	installTestArith()

	natScope := NewProofScope(natBlocked)
	realScope := NewProofScope(realBlocked)
	restore := omega.SetCurrentTarget(realBlocked)
	defer restore()

	const iterations = 100
	var wg sync.WaitGroup
	errs := make(chan string, 2)
	check := func(scope *ProofScope, want omega.ArithPolicy) {
		defer wg.Done()
		for range iterations {
			if got := scope.ArithPolicy(); got != want {
				errs <- "lexical policy changed under concurrent/global target state"
				return
			}
		}
	}
	wg.Add(2)
	go check(natScope, omega.ArithPolicy{Nat: false, Real: true, Int: true})
	go check(realScope, omega.ArithPolicy{Nat: true, Real: false, Int: true})
	wg.Wait()
	close(errs)
	for err := range errs {
		t.Error(err)
	}
}
