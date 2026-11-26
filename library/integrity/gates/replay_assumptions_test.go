package gates

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/registry"
)

// A permitted assumption through another door must not hide a TestThm
// of the same statement, within one certificate or across sections.
func TestCheckAssumptionsRejectsTestDoor(t *testing.T) {
	member, ok := registry.ByName("list.AppendAssoc")
	if !ok {
		t.Skip("datatypes/list is not in this build")
	}
	deps := member.DepEntries()
	if len(deps) == 0 {
		t.Fatal("the member needs a dependency for the permitted assumption")
	}
	statement := deps[0].Statement().Prop
	if len(statement.Hyps()) != 0 {
		t.Fatal("the dependency must be closed to compare all three doors")
	}
	promise := core.Promise(statement, func(core.Forcer) core.ThmCert {
		panic("the dependency is settled at the trust boundary")
	})
	boundary, _ := core.ForceWithBoundary(context.Background(), promise, func(core.Prop) bool { return true })
	axiom := core.NewAxiom(statement.Conclusion())
	fabricated := core.TestThm(statement.Conclusion())

	for _, tc := range []struct {
		name       string
		certs      []core.ThmCert
		wantRefuse bool
	}{
		{"boundary", []core.ThmCert{boundary}, false},
		{"axiom", []core.ThmCert{axiom}, false},
		{"test", []core.ThmCert{fabricated}, true},
		{"boundary_then_test", []core.ThmCert{boundary, fabricated}, true},
		{"test_then_boundary", []core.ThmCert{fabricated, boundary}, true},
		{"axiom_then_test", []core.ThmCert{axiom, fabricated}, true},
		{"test_then_axiom", []core.ThmCert{fabricated, axiom}, true},
		{"derived_from_boundary_and_test", []core.ThmCert{core.Deduct(boundary, fabricated).AsThmCert()}, true},
		{"derived_from_axiom_and_test", []core.ThmCert{core.Deduct(axiom, fabricated).AsThmCert()}, true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			err := checkAssumptions(member, deps, nil, tc.certs)
			if tc.wantRefuse {
				if err == nil || !strings.Contains(err.Error(), "a TestThm of ") {
					t.Fatalf("want the TestThm refused, got %v", err)
				}
			} else if err != nil {
				t.Fatalf("a permitted dependency was refused: %v", err)
			}
		})
	}
}

// sharingAKey is two statements that are not α-equal and have one key:
// p ⊢ p, and ⊢ x for a variable x whose name spells where the first
// statement's two keys meet (core.TermKey).
func sharingAKey(t *testing.T) (one, other core.Prop) {
	boolType := core.TypeBool()
	p := core.Var("p", boolType)
	one = core.MakeProp(p, p)
	other = core.MakeProp(core.Var("p_"+string(boolType.Key())+"var_p", boolType))
	if one.AlphaKey() != other.AlphaKey() || one.AlphaEquals(other) {
		t.Fatal("the two statements have two keys: this pair no longer shows what a shared key does")
	}
	return one, other
}

// The member's own statement is left out of the frontier by comparing
// statements: one that has its key and is not α-equal to it stays in.
func TestExceptSelfComparesStatements(t *testing.T) {
	self, other := sharingAKey(t)
	trust := exceptSelf(func(core.Prop) bool { return true }, self)
	if trust(self) {
		t.Error("the member's own statement is trusted")
	}
	if !trust(other) {
		t.Error("a statement with the key of the member's own was left out with it")
	}
}

// An assumption is not passed over for having the key of one already
// checked: each of two statements with one key is held to the cone.
func TestCheckAssumptionsChecksEachStatementUnderOneKey(t *testing.T) {
	member, ok := registry.ByName("list.AppendAssoc")
	if !ok {
		t.Skip("datatypes/list is not in this build")
	}
	one, other := sharingAKey(t)
	settle := func(p core.Prop) core.ThmCert {
		cert, _ := core.ForceWithBoundary(context.Background(), core.Promise(p, func(core.Forcer) core.ThmCert {
			panic("the statement is settled at the trust boundary")
		}), func(core.Prop) bool { return true })
		return cert
	}
	for _, certs := range [][]core.ThmCert{{settle(one), settle(other)}, {settle(other), settle(one)}} {
		err := checkAssumptions(member, member.DepEntries(), nil, certs)
		if err == nil || strings.Count(err.Error(), "which no entry states") != 2 {
			t.Fatalf("want each of the two statements refused, since no entry states either, got %v", err)
		}
	}
}
