package registry

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
)

// TypeArity is the engine's own types plus the vocabulary the
// registered constants spell: num is known with no chapter loaded, a
// mint adds its type's name at its arity, and a name nothing mentions
// is unknown.
func TestTypeArityFollowsTheRegistry(t *testing.T) {
	m := GetConstMetaManager()
	if a, ok := m.TypeArity("num"); !ok || a != 0 {
		t.Fatalf("num: (%d, %v), want (0, true) — num is the engine's own type", a, ok)
	}
	if a, ok := m.TypeArity("bool"); !ok || a != 0 {
		t.Fatalf("bool: (%d, %v)", a, ok)
	}
	if _, ok := m.TypeArity("zz_probe_type"); ok {
		t.Fatal("zz_probe_type known before any constant mentions it")
	}
	probe := core.MakeCompositeType(core.MakeMetaType("zz_probe_type", 2), core.MakeVarType("A"), core.MakeVarType("B"))
	meta := core.MakeConstMeta("zz_probe_const", core.MakeFun(probe, core.TypeBool()))
	if _, loaded := m.LoadOrStoreConstMeta(meta); loaded {
		t.Fatal("zz_probe_const already registered")
	}
	if a, ok := m.TypeArity("zz_probe_type"); !ok || a != 2 {
		t.Fatalf("zz_probe_type after the mint: (%d, %v), want (2, true)", a, ok)
	}
}

// A constant's type is read into the vocabulary once, as the constant
// registers: n mints are n reads, a name registered again is none, and
// asking an arity reads no constant however often it is asked.
func TestTypeArityReadsEachConstantOnce(t *testing.T) {
	m := GetConstMetaManager()
	before := m.typeReads
	const mints = 3
	var metas []core.ConstTermMeta
	for i := range mints {
		probe := core.MakeCompositeType(core.MakeMetaType(fmt.Sprintf("zz_probe_once_type_%d", i), 1), core.MakeVarType("A"))
		meta := core.MakeConstMeta(core.TermName(fmt.Sprintf("zz_probe_once_const_%d", i)), core.MakeFun(probe, core.TypeBool()))
		if _, loaded := m.LoadOrStoreConstMeta(meta); loaded {
			t.Fatalf("%s already registered", meta.Name())
		}
		metas = append(metas, meta)
	}
	for range 100 {
		for i := range mints {
			if a, ok := m.TypeArity(fmt.Sprintf("zz_probe_once_type_%d", i)); !ok || a != 1 {
				t.Fatalf("zz_probe_once_type_%d: (%d, %v), want (1, true)", i, a, ok)
			}
		}
		if _, ok := m.TypeArity("zz_probe_once_no_type"); ok {
			t.Fatal("zz_probe_once_no_type is known and no constant mentions it")
		}
	}
	if _, loaded := m.LoadOrStoreConstMeta(metas[0]); !loaded {
		t.Fatalf("%s registered twice", metas[0].Name())
	}
	if got := m.typeReads - before; got != mints {
		t.Fatalf("%d constants' types read for %d mints: each is read once, as it registers", got, mints)
	}

	// A manager knows the types of the constants registered with it and
	// of no other: one made with nothing seeded reads its own mint.
	var own ConstMetaManager
	if _, loaded := own.LoadOrStoreConstMeta(metas[0]); loaded {
		t.Fatalf("%s registered in a manager that holds nothing", metas[0].Name())
	}
	if a, ok := own.TypeArity("zz_probe_once_type_0"); !ok || a != 1 {
		t.Fatalf("zz_probe_once_type_0 in its own manager: (%d, %v), want (1, true)", a, ok)
	}
	if _, ok := own.TypeArity("zz_probe_once_type_1"); ok {
		t.Fatal("zz_probe_once_type_1 is known to a manager no constant of that type registered with")
	}
}
