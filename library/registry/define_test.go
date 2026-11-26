package registry

import (
	"context"
	"strings"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/require"
)

// TestFamilyDefine_DirectEntry: family.Define mints at registration
// (constant resolvable process-globally, exclusively), registers an
// entry with a computed key, and the entry's Build re-derives
// the characterizing theorem through the define composite under a
// harness-armed env — the twin of the session flow.
func TestFamilyDefine_DirectEntry(t *testing.T) {
	fam := NewFamily("zz_define_test", nil)
	entry := fam.Define(DefEntry{
		Name:      "XorDef",
		Const:     "zz_reg_xor",
		Type:      "bool → bool → bool",
		Equations: []string{"∀p q:bool. zz_reg_xor(p, q) ⇔ (p ∨ q) ∧ ¬(p ∧ q)"},
	})

	// Registration facts: family-prefixed name, the unminted sentinel
	// of an entry declared without a Key, and the constant registered
	// in the process-global manager.
	require.Equal(t, proof.DefinitionDirect, entry.Definition, "the entry carries the served shape")
	require.Equal(t, "zz_define_test.XorDef", entry.Name)
	require.Equal(t, UnmintedKeyPrefix+entry.Name, entry.Key,
		"declared without a Key, the definition carries the unminted sentinel: registration computes no key")
	meta, ok := GetConstMetaManager().LoadConstMeta(core.TermName("zz_reg_xor"))
	require.True(t, ok)
	require.False(t, meta.IsZero())

	// Build replays under a harness-armed env (the replay-harness
	// contract: identity in env.Scope, one Build per env).
	var cnfCache utils.Map[core.TermKey, core.Prop]
	env := &proof.ProverEnv{
		ProofService: &proof.ProofService{
			LoadConstMeta:        GetConstMetaManager().LoadConstMeta,
			LoadOrStoreConstMeta: GetConstMetaManager().LoadOrStoreConstMeta,
			Syntax:               GetConstMetaManager(),
		},
		CnfRefuterTimeout:     2 * time.Second,
		CnfNormalizationCache: &cnfCache,
		CnfNormalizeCache:     proof.NewCNFNormalizeCache(),
	}
	env.Scope = proof.NewProofScope(entry.Statement().Key())
	thm, _ := entry.Build.Fn(env)
	require.NotNil(t, thm)
	cert := core.Force(context.Background(), core.AsThm(thm))
	require.False(t, cert.IsZero())

	// The built theorem IS the entry's statement: the equation as the
	// MINT read it, with the constant in place.
	headline := entry.Statement().Prop
	require.NotNil(t, headline)
	require.True(t, cert.Conclusion().AlphaEquals(headline.Conclusion()),
		"built:\n  %s\nheadline:\n  %s",
		ext.PrintTerm(cert.Conclusion()), ext.PrintTerm(headline.Conclusion()))

	// The mint is exclusive: a second Define of the same constant (in a
	// sibling family) panics at init.
	sibling := NewFamily("zz_define_test_dup", nil)
	require.Panics(t, func() {
		sibling.Define(DefEntry{
			Name:      "XorAgain",
			Const:     "zz_reg_xor",
			Type:      "bool → bool → bool",
			Equations: []string{"∀p q:bool. zz_reg_xor(p, q) ⇔ p ∧ q"},
		})
	})
}

// TestFamilyDefine_NullaryPolymorphic: a definiendum that is nullary at
// a PARAMETERIZED type — the shape whose type letter nothing in the
// equation ties except the definiendum itself. The entry states the
// mint's own reading of the equation, so the statement carries the
// author's letter and the Build closes it; a second reading of the
// literal (where the definiendum is a constant whose letters freshen
// per occurrence) would land at an instance the author never wrote.
func TestFamilyDefine_NullaryPolymorphic(t *testing.T) {
	fam := NewFamily("zz_define_nullary_test", nil)
	// A parameterized type to be nullary at: the predicates on A, made
	// a type. Its inhabitation is trivial, so the mint proves it.
	box := fam.DefineType(TypeEntry{
		Name: "Box",
		Type: "zz_box",
		Abs:  "zz_mk_box",
		Rep:  "zz_dest_box",
		Pred: "λf:(A → bool). ⊤",
	})
	require.Equal(t, "zz_box", string(box.Meta.Name()))

	entry := fam.Define(DefEntry{
		Name:      "EmptyBoxDef",
		Const:     "zz_empty_box",
		Type:      "zz_box(A)",
		Equations: []string{"zz_empty_box = zz_mk_box(λx:A. ⊥)"},
		Deps:      []EntryLike{box.Retraction},
	})

	// The statement is over the minted type at the author's letter —
	// one letter, both sides.
	stated := entry.Statement().Prop
	lhs, rhs, isEq := core.MatchesEQ(stated.Conclusion())
	require.True(t, isEq, "states %s", ext.PrintTerm(stated.Conclusion()))
	require.True(t, lhs.Type().Equals(rhs.Type()),
		"the two sides are at one instance: %s vs %s",
		ext.FormatType(lhs.Type()), ext.FormatType(rhs.Type()))
	require.Len(t, lhs.Type().TypeVars(), 1, "still polymorphic: %s", ext.FormatType(lhs.Type()))

	var cnfCache utils.Map[core.TermKey, core.Prop]
	env := &proof.ProverEnv{
		ProofService: &proof.ProofService{
			LoadConstMeta:        GetConstMetaManager().LoadConstMeta,
			LoadOrStoreConstMeta: GetConstMetaManager().LoadOrStoreConstMeta,
			Syntax:               GetConstMetaManager(),
		},
		CnfRefuterTimeout:     2 * time.Second,
		CnfNormalizationCache: &cnfCache,
		CnfNormalizeCache:     proof.NewCNFNormalizeCache(),
	}
	env.Scope = proof.NewProofScope(entry.Statement().Key())
	thm, _ := entry.Build.Fn(env)
	cert := core.Force(context.Background(), core.AsThm(thm))
	require.True(t, cert.Conclusion().AlphaEquals(stated.Conclusion()),
		"built:\n  %s\nstated:\n  %s",
		ext.PrintTerm(cert.Conclusion()), ext.PrintTerm(stated.Conclusion()))
}

// TestFamilyDefine_EquationReadsNotationUnderInstance: a definition's
// equation reads the chapter's own dialect. A constant declared with a
// notation and an implicit component (`c • u` for `zz_reg_scale(mul, c,
// u)`) is written by that notation in every MEMBER of a family bound to
// an instance; the family's DEFINITIONS parse in a scope of their own,
// which carried neither the syntax table nor the instance bindings, so
// the same text panicked at init — `operator • has no instance for
// operand types … (no constant in scope declares it)` — and the corpus
// spelled every definition body longhand (vector/euclidean,
// vector/convex). The equation is the author's text like any other and
// reads the same way.
func TestFamilyDefine_EquationReadsNotationUnderInstance(t *testing.T) {
	generic := NewFamily("zz_define_notation_test", nil)
	// The vectors are indexed by bool. vec_scalar_mul declares • over
	// num-indexed vectors, every linked constant declaring a symbol is a
	// candidate for it, and operands two of them fit are refused.
	scale := generic.Define(DefEntry{
		Name:      "ScaleDef",
		Const:     "zz_reg_scale",
		Type:      "(A → A → A) → A → (bool → A) → bool → A",
		Implicit:  []string{"mul"},
		Notation:  "c • u",
		Equations: []string{"∀mul:(A → A → A). ∀c:A. ∀u:(bool → A). ∀i:bool. zz_reg_scale(mul, c, u, i) = mul(c, u(i))"},
	})
	require.Equal(t, "zz_define_notation_test.ScaleDef", scale.Name)
	// A stand-in for the instance's component: a minted constant the
	// binding can name. An instance theorem's argument is MONOMORPHIC
	// (`real_mul`), which is what lets the completion pass recognize
	// the longhand spelling — it matches the written argument against
	// the component's canonical print, and a polymorphic constant
	// prints at an instance.
	generic.Define(DefEntry{
		Name:      "TimesDef",
		Const:     "zz_reg_times",
		Type:      "num → num → num",
		Equations: []string{"∀x y:num. zz_reg_times(x, y) = x"},
	})
	timesMeta, ok := GetConstMetaManager().LoadConstMeta(core.TermName("zz_reg_times"))
	require.True(t, ok)

	bound := NewFamily("zz_define_notation_bound_test", nil)
	bound.implicit = map[string]core.Term{"mul": core.MakeConstTerm(timesMeta, timesMeta.AbsType())}

	// The longhand spelling reads today and keeps reading.
	long := bound.Define(DefEntry{
		Name:      "FixedLongDef",
		Const:     "zz_reg_fixed_long",
		Type:      "num → (bool → num) → bool",
		Equations: []string{"∀c:num. ∀u:(bool → num). zz_reg_fixed_long(c, u) ⇔ zz_reg_scale(zz_reg_times, c, u) = u"},
	})
	// The notation, under the bound family, is the same statement.
	short := bound.Define(DefEntry{
		Name:      "FixedDef",
		Const:     "zz_reg_fixed",
		Type:      "num → (bool → num) → bool",
		Equations: []string{"∀c:num. ∀u:(bool → num). zz_reg_fixed(c, u) ⇔ c • u = u"},
	})
	longBody := long.Statement().Prop.Conclusion()
	shortBody := short.Statement().Prop.Conclusion()
	// The two characterizing statements differ only in the constant
	// they define: print both with the definiendum's name masked.
	mask := func(s, name string) string { return strings.ReplaceAll(s, name, "DEFINIENDUM") }
	require.Equal(t,
		mask(ext.PrintTerm(longBody), "zz_reg_fixed_long"),
		mask(ext.PrintTerm(shortBody), "zz_reg_fixed"),
		"the notation reads to the longhand's statement")
}

// TestFamilyDefine_LimitMixfixNotation: the limit mixfix `f ⟶ l (at c)`
// is a declared notation like `c • u` — the constant declaring `⟶` at
// arity three owns the clause form, a later definition's equation
// reads it to the longhand's statement, and the chapter spelling folds
// the longhand back into it through the process syntax table.
func TestFamilyDefine_LimitMixfixNotation(t *testing.T) {
	fam := NewFamily("zz_define_limit_notation_test", nil)
	limit := fam.Define(DefEntry{
		Name:      "LimitAtDef",
		Const:     "zz_reg_limit_at",
		Type:      "(real → real) → real → real → bool",
		Notation:  "f ⟶ l (at c)",
		Equations: []string{"∀f:(real → real). ∀c l:real. zz_reg_limit_at(f, c, l) ⇔ ∀x:real. f(x) = l"},
	})
	require.Equal(t, "zz_define_limit_notation_test.LimitAtDef", limit.Name)
	long := fam.Define(DefEntry{
		Name:      "ContinuousLongDef",
		Const:     "zz_reg_continuous_long",
		Type:      "(real → real) → real → bool",
		Equations: []string{"∀f:(real → real). ∀c:real. zz_reg_continuous_long(f, c) ⇔ zz_reg_limit_at(f, c, f(c))"},
		Deps:      []EntryLike{limit},
	})
	short := fam.Define(DefEntry{
		Name:      "ContinuousDef",
		Const:     "zz_reg_continuous",
		Type:      "(real → real) → real → bool",
		Equations: []string{"∀f:(real → real). ∀c:real. zz_reg_continuous(f, c) ⇔ f ⟶ f(c) (at c)"},
		Deps:      []EntryLike{limit},
	})
	mask := func(s, name string) string { return strings.ReplaceAll(s, name, "DEFINIENDUM") }
	require.Equal(t,
		mask(ext.PrintTerm(long.Statement().Prop.Conclusion()), "zz_reg_continuous_long"),
		mask(ext.PrintTerm(short.Statement().Prop.Conclusion()), "zz_reg_continuous"),
		"the clause notation reads to the longhand's statement")
	// The printer's half: the longhand folds into the mixfix, with the
	// holes back in reading order.
	spelled, err := dsl.ChapterSpelling("f:(real → real), c:real ⊢ zz_reg_limit_at(f, c + c, f(c)) ∧ ¬zz_reg_limit_at(f, c, c)",
		GetConstMetaManager(), nil)
	require.NoError(t, err)
	require.Contains(t, spelled, "f ⟶ f(c) (at c + c) ∧ ¬(f ⟶ c (at c))")
}

// A definition's key is the one its source spells, read as spelled: the
// doors that register one entry from one literal compute none, and the
// key gate is what compares it with the statement's.
func TestFamilyDefine_ReadsTheSpelledKey(t *testing.T) {
	fam := NewFamily("zz_define_spelled_key", nil)
	const spelled = "prop_0123456789abcdef"
	def := fam.Define(DefEntry{
		Name: "AndDef", Key: spelled, Const: "zz_spelled_and", Type: "bool → bool → bool",
		Equations: []string{"∀p q:bool. zz_spelled_and(p, q) ⇔ p ∧ q"},
	})
	require.Equal(t, spelled, def.Key, "Define reads the key its literal spells")
	require.NotEqual(t, spelled, string(def.Statement().Key()), "the spelled key was not computed")

	const structureKey = "prop_fedcba9876543210"
	structure := fam.DefineStructure(DefEntry{
		Name: "Pointed", Key: structureKey, Const: "zz_spelled_pointed", Type: "A → bool",
		Equations: []string{"∀e:A. zz_spelled_pointed(e) ⇔ e = e"},
	})
	require.Equal(t, structureKey, structure.ProofEntry.Key, "DefineStructure reads the key its literal spells")
}
