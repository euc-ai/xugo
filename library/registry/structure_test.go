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

func structureTestEnv(t *testing.T, key string) *proof.ProverEnv {
	t.Helper()
	var cnfCache utils.Map[core.TermKey, core.Prop]
	env := &proof.ProverEnv{
		ProofService: &proof.ProofService{
			LoadConstMeta:        GetConstMetaManager().LoadConstMeta,
			LoadOrStoreConstMeta: GetConstMetaManager().LoadOrStoreConstMeta,
			Syntax:               GetConstMetaManager(),
		},
		CnfRefuterTimeout:     5 * time.Second,
		CnfNormalizationCache: &cnfCache,
		CnfNormalizeCache:     proof.NewCNFNormalizeCache(),
	}
	env.Scope = proof.NewProofScope(core.PropKey(key))
	return env
}

func forceStructureEntry(t *testing.T, entry *ProofEntry) core.Prop {
	t.Helper()
	env := structureTestEnv(t, string(entry.Statement().Key()))
	thm, _ := entry.Build.Fn(env)
	require.NotNil(t, thm, "%s: no theorem", entry.Name)
	cert := core.Force(context.Background(), core.AsThm(thm))
	require.False(t, cert.IsZero(), "%s: the certificate did not force", entry.Name)
	headline := entry.Statement().Prop
	require.NotNil(t, headline)
	require.True(t, cert.Conclusion().AlphaEquals(headline.Conclusion()),
		"%s built:\n  %s\nheadline:\n  %s", entry.Name,
		ext.PrintTerm(cert.Conclusion()), ext.PrintTerm(headline.Conclusion()))
	return cert
}

// TestDefineStructure: the components are read off the definition, a
// law's statement is the components ∀-bound then the predicate as
// antecedent, an Axiom entry force-builds by unfolding, and a Law
// entry's closure receives the hypothesis with the components in scope
// under their own names.
func TestDefineStructure(t *testing.T) {
	fam := NewFamily("zz_structure_test", nil)
	monoid := fam.DefineStructure(DefEntry{
		Name:  "CommMonoid",
		Const: "zz_reg_cmon",
		Type:  "(A → A → A) → A → bool",
		Equations: []string{
			"∀op:(A → A → A). ∀e:A. zz_reg_cmon(op, e) ⇔ " +
				"(∀x y:A. op(x, y) = op(y, x)) ∧ (∀x y z:A. op(x, op(y, z)) = op(op(x, y), z)) ∧ (∀x:A. op(e, x) = x)",
		},
	})
	require.Equal(t, "zz_reg_cmon", monoid.Const)
	require.Equal(t, proof.DefinitionDirect, monoid.Definition)
	require.Equal(t,
		"∀op:(A → A → A). ∀e x:A. zz_reg_cmon(op, e) ⇒ op(x, e) = x",
		statementText(t, monoid.Statement("∀x:A. op(x, e) = x")))
	require.Equal(t,
		"∀op:(A → A → A). ∀e:A. zz_reg_cmon(op, e) ⇒ (op(e, e) = e ⇔ op(e, e) = e)",
		statementText(t, monoid.Statement("op(e, e) = e ⇔ op(e, e) = e")),
		"a body whose top-level connective is ⇔ is parenthesized")
	require.Equal(t,
		"∀op:(A → A → A). ∀e:A. zz_reg_cmon(op, e) ⇒ (op(e, e) = e ∧ op(e, e) = e ⇔ op(e, e) = e)",
		statementText(t, monoid.Statement("(op(e, e) = e ∧ op(e, e) = e) ⇔ op(e, e) = e")),
		"a body that opens with a parenthesis but carries a top-level ⇔ is parenthesized too")
	require.Equal(t,
		"∀op:(A → A → A). ∀e:A. zz_reg_cmon(op, e) ⇒ (op(e, e) = e ⇔ op(e, e) = e) ∧ op(e, e) = e",
		statementText(t, monoid.Statement("(op(e, e) = e ⇔ op(e, e) = e) ∧ op(e, e) = e")),
		"a ⇔ inside parentheses is not at the top level")

	// Adjacent components of one type group in the statement.
	_, err := componentTypeTexts("(A → A → A) → (A → A → A) → A → bool", 3)
	require.NoError(t, err)
	_, err = componentTypeTexts("(A → A → A) → A", 2)
	require.Error(t, err)

	comm := fam.Add(ProofEntry{
		Name:  "Comm",
		Build: monoid.Axiom("∀x y:A. op(x, y) = op(y, x)"),
	})
	leftId := fam.Add(ProofEntry{
		Name:  "LeftId",
		Build: monoid.Axiom("∀x:A. op(e, x) = x"),
	})
	require.Equal(t,
		"∀op:(A → A → A). ∀e x y:A. zz_reg_cmon(op, e) ⇒ op(x, y) = op(y, x)",
		comm.Build.Headline)
	forceStructureEntry(t, comm)
	forceStructureEntry(t, leftId)

	// A law proved from the hypothesis alone: the closure sees the
	// components under their own names, so the clause texts spell them.
	rightId := fam.Add(ProofEntry{
		Name: "RightId",
		Build: monoid.Law("∀x:A. op(x, e) = x", func(a *proof.Argument, m proof.Fact) {
			a.Do(proof.Unfold(mintedByName("zz_reg_cmon")))
			commutes := a.Hyp("∀x y:A. op(x, y) = op(y, x)")
			leftIdentity := a.Hyp("∀x:A. op(e, x) = x")
			a.Show("commute the left identity", proof.By(commutes, leftIdentity))
		}),
	})
	forceStructureEntry(t, rightId)

	// The one-Action form: the unfold alone closes a law that spells a
	// conjunct as the definition does, so a law entry and an axiom entry
	// have the same shape.
	assoc := fam.Add(ProofEntry{
		Name:  "Assoc",
		Build: monoid.Law("∀x y z:A. op(x, op(y, z)) = op(op(x, y), z)", proof.Unfold(mintedByName("zz_reg_cmon"))),
	})
	forceStructureEntry(t, assoc)

	// An instance at a concrete carrier states the predicate at the
	// components and declares the definition by construction; its
	// cases are the carrier's own laws (the corpus instances at ℝ and
	// ℤ replay them — real_ring/instances.go, int_real_lift/instances.go).
	instance := fam.Add(ProofEntry{
		Name: "NatAddMonoid",
		Build: fam.Instance(monoid, "zz_reg_cmon((λm:num. λn:num. m + n), 0)",
			proof.MakeCase("addition commutes", proof.Arith()),
			proof.MakeCase("addition associates", proof.Arith()),
			proof.MakeCase("zero is a left identity", proof.Arith())),
	})
	require.Equal(t, "zz_reg_cmon((λm:num. λn:num. m + n), 0)", instance.Build.Headline)
	require.Len(t, instance.Deps, 1, "the definition is the instance's dep by construction")
	require.Same(t, monoid.ProofEntry, instance.Deps[0].Entry())
	require.Panics(t, func() { fam.Instance(monoid, "zz_reg_cmon((λm:num. λn:num. m + n), 0)") })
	require.Panics(t, func() {
		fam.Instance(monoid, "monoidal_op(λm:num. λn:num. m + n)", proof.MakeCase("not this predicate", proof.Arith()))
	})

	// A parametric instance states the predicate under a ∀-prefix; the
	// prefix is bound as the section's binders under their own names, so
	// a case's body spells the parameter. This entry is forced (the
	// concrete one above is not) at a structure whose obligations the
	// unfold's tidy leaves open — this env has no arithmetic.
	pointed := fam.DefineStructure(DefEntry{
		Name:  "Pointed",
		Const: "zz_reg_pt",
		Type:  "(A → A) → A → bool",
		Equations: []string{
			"∀f:(A → A). ∀e:A. zz_reg_pt(f, e) ⇔ (∃x:A. f(x) = f(e)) ∧ (∃x:A. f(e) = f(x))",
		},
	})
	parametric := fam.Add(ProofEntry{
		Name: "EveryPointIsPointed",
		Build: fam.Instance(pointed, "∀f:(A → A). ∀c:A. zz_reg_pt(f, c)",
			proof.MakeCase("the point itself", proof.Derive(func(a *proof.Argument) {
				a.Take(a.Term("c"))
				a.Show("f at c is f at c", proof.Refl())
			})),
			proof.MakeCase("and again", proof.Derive(func(a *proof.Argument) {
				a.Take(a.Term("c"))
				a.Show("f at c is f at c", proof.Refl())
			}))),
	})
	require.Len(t, parametric.Deps, 1)
	require.Same(t, pointed.ProofEntry, parametric.Deps[0].Entry())
	forceStructureEntry(t, parametric)
	require.Panics(t, func() {
		fam.Instance(pointed, "∀c:A. monoidal_op(λm:A. λn:A. n)", proof.MakeCase("not this predicate", proof.Refl()))
	})
	binders, body := instancePrefix("∀x y:A. ∀f:(A → A). zz_reg_cmon(f, x)")
	require.Equal(t, 3, binders)
	require.Equal(t, "zz_reg_cmon(f, x)", body)

	// The closure may bind the body's own leading binders after the
	// hypothesis, positionally, as a Theorem closure would.
	rightIdBound := fam.Add(ProofEntry{
		Name: "RightIdBound",
		Build: monoid.Law("∀x:A. op(x, e) = x", func(a *proof.Argument, m proof.Fact, x proof.Term) {
			a.Do(proof.Unfold(mintedByName("zz_reg_cmon")))
			commutes := a.Hyp("∀x y:A. op(x, y) = op(y, x)")
			leftIdentity := a.Hyp("∀x:A. op(e, x) = x")
			a.Show("commute the left identity at x", proof.By(proof.At(commutes, x, a.Term("e")), proof.At(leftIdentity, x)))
		}),
	})
	forceStructureEntry(t, rightIdBound)

	require.Panics(t, func() { monoid.Law("∀x:A. op(x, e) = x", 42) })
	require.Panics(t, func() { monoid.Law("∀x:A. op(x, e) = x", func(a *proof.Argument, x proof.Term) {}) })
}

// TestStructureSubscriptedComponent: a component the definition binds
// with a subscript (`N₀`, the kernel's `N_0`) is spelled with it in a
// law's statement, as the printer spells it, so the served text agrees
// with the body and with the same statement written by hand, at the
// same key. StructureOf reads an author's `N₀` as the same identifier.
func TestStructureSubscriptedComponent(t *testing.T) {
	fam := NewFamily("zz_structure_subscript_test", nil)
	s := fam.DefineStructure(DefEntry{
		Name:  "Aug",
		Const: "zz_reg_sub_aug",
		Type:  "(A → bool) → (A → bool) → bool",
		Equations: []string{
			"∀N₀:(A → bool). ∀M:(A → bool). zz_reg_sub_aug(N₀, M) ⇔ (∀x:A. N₀(x) ⇒ M(x))",
		},
	})
	const law = "∀N₀ M:(A → bool). ∀x:A. zz_reg_sub_aug(N₀, M) ∧ N₀(x) ⇒ M(x)"
	require.Equal(t, law, statementText(t, s.Statement("∀x:A. N₀(x) ⇒ M(x)")))
	inclusion := fam.Add(ProofEntry{Name: "Inclusion", Build: s.Axiom("∀x:A. N₀(x) ⇒ M(x)")})
	require.Equal(t, law, inclusion.StatementText())
	forceStructureEntry(t, inclusion)
	byHand := fam.Add(ProofEntry{Name: "InclusionByHand",
		Build: fam.Theorem("∀N₀:(A → bool). ∀M:(A → bool). zz_reg_sub_aug(N₀, M) ⇒ ∀x:A. N₀(x) ⇒ M(x)", proof.Unfold(mintedByName("zz_reg_sub_aug")))})
	require.Equal(t, byHand.Statement().Key(), inclusion.Statement().Key())

	named := fam.StructureOf("zz_reg_sub_named", "N₀:(A → bool)", "M:(A → bool)")
	require.Equal(t, s.comps, named.comps, "an author's N₀ is the definition's N_0")
	require.Equal(t, "∀N₀ M:(A → bool). ∀x:A. zz_reg_sub_named(N₀, M) ∧ N₀(x) ⇒ M(x)",
		statementText(t, named.Statement("∀x:A. N₀(x) ⇒ M(x)")))
}

// TestStructureOf: a predicate a plain Define mints (monoidal_op,
// iterate/monoidal's MonoidalOpDef) named as a structure — no
// structure-definition entry, the components spelled by the author —
// states its laws through the same door; an Axiom unfolds the
// predicate's definition, and a Law naming the components before the
// hypothesis is bound as the statement's plain closure.
// The subject is the component the entry declares, at any position;
// one naming no component is refused, as is a Subject on a plain
// Define.
func TestDefineStructureSubject(t *testing.T) {
	fam := NewFamily("zz_structure_subject_test", nil)
	fam.DefineStructure(DefEntry{
		Name:    "Metric",
		Const:   "zz_reg_metric",
		Type:    "(A → bool) → (A → A → A) → bool",
		Subject: "M",
		Equations: []string{
			"∀M:(A → bool). ∀d:(A → A → A). zz_reg_metric(M, d) ⇔ ∀x:A. x ∈ M ⇒ d(x, x) = x",
		},
	})
	syntax := GetConstMetaManager().ConstSyntax("zz_reg_metric")
	require.NotNil(t, syntax)
	require.NotNil(t, syntax.Bundle)
	require.Equal(t, 0, syntax.Bundle.Subject)
	fam.DefineStructure(DefEntry{
		Name:  "Plain",
		Const: "zz_reg_plain",
		Type:  "(A → A → A) → A → bool",
		Equations: []string{
			"∀op:(A → A → A). ∀e:A. zz_reg_plain(op, e) ⇔ ∀x:A. op(e, x) = x",
		},
	})
	require.Equal(t, -1, GetConstMetaManager().ConstSyntax("zz_reg_plain").Bundle.Subject,
		"a structure that declares no subject has none")
	require.PanicsWithValue(t,
		"registry.DefineStructure(Wrong): Subject \"c\" names none of the components op, e",
		func() {
			fam.DefineStructure(DefEntry{
				Name:    "Wrong",
				Const:   "zz_reg_wrong",
				Type:    "(A → A → A) → A → bool",
				Subject: "c",
				Equations: []string{
					"∀op:(A → A → A). ∀e:A. zz_reg_wrong(op, e) ⇔ ∀x:A. op(e, x) = x",
				},
			})
		})
	require.PanicsWithValue(t,
		"registry.Define(NotAStructure): Subject is a structure's declaration — DefineStructure",
		func() {
			fam.Define(DefEntry{
				Name:      "NotAStructure",
				Const:     "zz_reg_not_a_structure",
				Type:      "A → bool",
				Subject:   "x",
				Equations: []string{"∀x:A. zz_reg_not_a_structure(x) ⇔ x = x"},
			})
		})
}

// A structure with no subject may declare the letter its laws fold
// under; the letter beside a subject, or naming a component, is
// refused, as is one on a plain Define.
func TestDefineStructureLetter(t *testing.T) {
	fam := NewFamily("zz_structure_letter_test", nil)
	pair := fam.DefineStructure(DefEntry{
		Name:   "Pair",
		Const:  "zz_reg_pair",
		Type:   "(A → A → A) → (A → A → A) → bool",
		Letter: "S",
		Equations: []string{
			"∀op op':(A → A → A). zz_reg_pair(op, op') ⇔ ∀x:A. op(x, x) = op'(x, x)",
		},
	})
	syntax := GetConstMetaManager().ConstSyntax("zz_reg_pair")
	require.Equal(t, -1, syntax.Bundle.Subject)
	require.Equal(t, "S", syntax.Bundle.Letter)
	stated, err := pair.Statement("∀x:A. op(op'(x, x), x) = x").Text()
	require.NoError(t, err)
	folded, err := dsl.ChapterSpelling(stated, GetConstMetaManager(), nil)
	require.NoError(t, err)
	require.Equal(t, "∀S:zz_reg_pair(A). ∀x:A. op(op'(x, x), x) = x", folded)
	for _, tc := range []struct{ name, subject, letter, want string }{
		{"Both", "op", "S", "registry.DefineStructure(Both): Letter \"S\" beside Subject \"op\": a structure with a subject is named after it"},
		{"Component", "", "op", "registry.DefineStructure(Component): Letter \"op\" names a component: declare it the Subject"},
	} {
		require.PanicsWithValue(t, tc.want, func() {
			fam.DefineStructure(DefEntry{
				Name: tc.name, Const: "zz_reg_letter_" + strings.ToLower(tc.name), Type: "(A → A → A) → bool",
				Subject: tc.subject, Letter: tc.letter,
				Equations: []string{"∀op:(A → A → A). zz_reg_letter_" + strings.ToLower(tc.name) + "(op) ⇔ ∀x:A. op(x, x) = x"},
			})
		})
	}
	require.PanicsWithValue(t,
		"registry.Define(PlainLetter): Letter is a structure's declaration — DefineStructure",
		func() {
			fam.Define(DefEntry{
				Name: "PlainLetter", Const: "zz_reg_plain_letter", Type: "A → bool", Letter: "S",
				Equations: []string{"∀x:A. zz_reg_plain_letter(x) ⇔ x = x"},
			})
		})
}

// A conjunct under ∀ binders states an INDEXED layout: a fact of the
// structure states the fibres as a family, named by applying the
// subject; the definition's own body passes them once its first
// conjunct states them; a definition's declared layouts are in scope
// for its own body; and the served spelling leaves the stating
// conjunct spelled in full and folds the passing one.
func TestDefineStructureFibres(t *testing.T) {
	fam := NewFamily("zz_structure_fibre_test", nil)
	fam.DefineStructure(DefEntry{
		Name:    "Mod",
		Const:   "zz_fib_mod",
		Type:    "(B → B → B) → (B → bool) → bool",
		Subject: "c",
		Equations: []string{
			"∀op:(B → B → B). ∀c:(B → bool). zz_fib_mod(op, c) ⇔ ∀x:B. x ∈ c ⇒ op(x, x) ∈ c",
		},
	})
	fam.Define(DefEntry{
		Name:    "Hom",
		Const:   "zz_fib_hom",
		Type:    "(B → B → B) → (B → B → B) → (B → bool) → (B → bool) → (B → B) → bool",
		Bundles: []string{"zz_fib_mod(op, c)", "zz_fib_mod(op', c')"},
		Equations: []string{
			"∀op op':(B → B → B). ∀c c':(B → bool). ∀f:(B → B). zz_fib_hom(op, op', c, c', f) ⇔ ∀x:B. x ∈ c ⇒ f(x) ∈ c'",
		},
	})
	// The second conjunct passes the fibres the first states.
	complex := fam.DefineStructure(DefEntry{
		Name:    "Complex",
		Const:   "zz_fib_cx",
		Type:    "(B → B → B) → (num → B → bool) → (num → B → B) → bool",
		Subject: "P",
		Equations: []string{
			"∀op:(B → B → B). ∀P:(num → B → bool). ∀d:(num → B → B). zz_fib_cx(op, P, d) ⇔ " +
				"(∀n:num. zz_fib_mod(op, P(n))) ∧ (∀n:num. zz_fib_hom(P(n + 1), P(n), d(n + 1)))",
		},
	})
	syntax := GetConstMetaManager().ConstSyntax("zz_fib_cx").Bundle
	require.Len(t, syntax.Layouts, 2, "the own layout and the module fibres; zz_fib_hom is no structure")
	fibre := syntax.Layouts[1]
	require.Equal(t, "zz_fib_mod", fibre.Structure)
	require.Equal(t, []int{0, -1}, fibre.Slots)
	require.Len(t, fibre.Index, 1)
	require.Equal(t, "n", fibre.Index[0].Name)
	require.NotNil(t, fibre.Templates[1])
	// Served, the definition's own fibres are in scope for its body:
	// the stating conjunct is the layout's statement and keeps its
	// components, and the second passes two fibres.
	require.Equal(t, "∀op:(B → B → B). ∀P:(num → B → bool). ∀d:(num → B → B). zz_fib_cx(op, P, d) ⇔ "+
		"(∀n:num. zz_fib_mod(op, P(n))) ∧ (∀n:num. zz_fib_hom(P(n + 1), P(n), d(n + 1)))",
		complex.StatementText())
	// A law over the complex names a fibre; served, it folds back.
	law := fam.Add(ProofEntry{
		Name:  "Fibre",
		Build: complex.Axiom("∀n:num. zz_fib_mod(op, P(n))"),
	})
	folded, err := dsl.ChapterSpelling(law.Build.Headline, GetConstMetaManager(), nil)
	require.NoError(t, err)
	require.Equal(t, "∀P:zz_fib_cx(B). ∀n:num. zz_fib_mod(P(n))", folded)
	key, err := law.KeyOfText(folded)
	require.NoError(t, err)
	require.Equal(t, string(law.Statement().Key()), key)
	forceStructureEntry(t, law)
	// A definition declaring two complexes passes their fibres in its
	// own body, read before the equation is built.
	iso := fam.Define(DefEntry{
		Name:    "Iso",
		Const:   "zz_fib_iso",
		Type:    "(B → B → B) → (num → B → bool) → (num → B → B) → (B → B → B) → (num → B → bool) → (num → B → B) → (num → B → B) → bool",
		Bundles: []string{"zz_fib_cx(op, P, d)", "zz_fib_cx(op', Q, e)"},
		Equations: []string{
			"∀op:(B → B → B). ∀P:(num → B → bool). ∀d:(num → B → B). ∀op':(B → B → B). ∀Q:(num → B → bool). ∀e:(num → B → B). ∀f:(num → B → B). " +
				"zz_fib_iso(op, P, d, op', Q, e, f) ⇔ ∀n:num. zz_fib_hom(P(n), Q(n), f(n))",
		},
	})
	require.Contains(t, iso.StatementText(), "⇔ ∀n:num. zz_fib_hom(P(n), Q(n), f(n))")
	key, err = iso.KeyOfText("∀op:(B → B → B). ∀P:(num → B → bool). ∀d:(num → B → B). ∀op':(B → B → B). ∀Q:(num → B → bool). ∀e:(num → B → B). ∀f:(num → B → B). " +
		"zz_fib_iso(op, P, d, op', Q, e, f) ⇔ ∀n:num. zz_fib_hom(op, op', P(n), Q(n), f(n))")
	require.NoError(t, err)
	require.Equal(t, string(iso.Statement().Key()), key)
}

func TestStructureOf(t *testing.T) {
	vocab := NewVocabSpec(nil).
		Spelled("monoidal_op", ext.HolTypeOf[ext.Fun[ext.Op[ext.B], ext.Bool]]).
		Spelled("neutral_elem", ext.HolTypeOf[ext.Fun[ext.Op[ext.B], ext.B]])
	fam := NewFamily("zz_structure_of_test", nil).WithVocabSpec(vocab)
	monoidal := fam.StructureOf("monoidal_op", "op:(B → B → B)")
	require.Nil(t, monoidal.ProofEntry, "a StructureOf structure has no definition entry")
	require.Equal(t, "monoidal_op", monoidal.Const)
	require.Equal(t,
		"∀op:(B → B → B). ∀x:B. monoidal_op(op) ⇒ op(neutral_elem(op), x) = x",
		statementText(t, monoidal.Statement("∀x:B. op(neutral_elem(op), x) = x")))

	leftNeutral := fam.Add(ProofEntry{
		Name:  "LeftNeutral",
		Build: monoidal.Axiom("∀x:B. op(neutral_elem(op), x) = x"),
	})
	require.Empty(t, leftNeutral.Deps, "no definition entry to declare")
	forceStructureEntry(t, leftNeutral)

	// The components-first form: the closure names `op` itself, typed,
	// and grounds a cite at it.
	rightNeutral := fam.Add(ProofEntry{
		Name: "RightNeutral",
		Build: monoidal.Law("∀x:B. op(x, neutral_elem(op)) = x",
			func(a *proof.Argument, op *ext.TermWrapper, m proof.Fact, x proof.Term) {
				a.Do(proof.Unfold(mintedByName("monoidal_op")))
				commutes := a.Hyp("∀x y:B. op(x, y) = op(y, x)")
				leftNeutral := a.Hyp("∀x:B. op(neutral_elem(op), x) = x")
				a.Show("commute the left neutral",
					proof.By(proof.At(commutes, x, a.Term("neutral_elem(op)")), proof.At(leftNeutral, x)))
			}),
	})
	forceStructureEntry(t, rightNeutral)

	require.Panics(t, func() { fam.StructureOf("monoidal_op") })
	require.Panics(t, func() { fam.StructureOf("monoidal_op", "op") })
	require.Panics(t, func() { fam.StructureOf("monoidal_op", "op:(B → B → B)", "op:B") })
	require.Panics(t, func() {
		monoidal.Law("∀x:B. op(x, neutral_elem(op)) = x", func(a *proof.Argument, op *ext.TermWrapper, x proof.Term) {})
	})
}

// DefineStructure's Symbols: each declared component carries its symbol
// at the arity its type gives it, registered with the predicate's
// syntax; every way of getting it wrong is refused at the definition.
func TestDefineStructureSymbols(t *testing.T) {
	fam := NewFamily("zz_structure_symbols_test", nil)
	ring := fam.DefineStructure(DefEntry{
		Name:  "Ring",
		Const: "zz_reg_ring",
		Type:  "(A → A → A) → A → (A → A) → bool",
		Equations: []string{
			"∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). zz_reg_ring(add, zero, neg) ⇔ (∀x:A. add(neg(x), x) = zero)",
		},
		Symbols: map[string]string{"add": "+", "neg": "-"},
	})
	s := GetConstMetaManager().ConstSyntax(ring.Const)
	require.NotNil(t, s)
	require.NotNil(t, s.Structure)
	require.Equal(t, []dsl.StructureComponent{{Symbol: "+", Arity: 2}, {}, {Symbol: "-", Arity: 1}}, s.Structure.Components)

	// The law's body reads the symbols off the antecedent the door writes.
	law := fam.Add(ProofEntry{
		Name:  "LeftInverse",
		Build: ring.Axiom("∀x:A. -x + x = zero"),
	})
	require.Equal(t, "∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). ∀x:A. zz_reg_ring(add, zero, neg) ⇒ -x + x = zero", law.Build.Headline)
	forceStructureEntry(t, law)

	for name, bad := range map[string]map[string]string{
		"not a component":             {"mul": "*"},
		"a symbol at the wrong arity": {"add": "-", "neg": "+"},
		"an element carries none":     {"zero": "+"},
		"one symbol twice":            {"add": "+", "neg": "+"},
	} {
		func() {
			defer func() {
				if r := recover(); r == nil {
					t.Errorf("%s: expected the definition to refuse %v", name, bad)
				}
			}()
			NewFamily("zz_structure_symbols_bad_"+name, nil).DefineStructure(DefEntry{
				Name:  "Bad",
				Const: "zz_reg_ring_bad",
				Type:  "(A → A → A) → A → (A → A) → bool",
				Equations: []string{
					"∀add:(A → A → A). ∀zero:A. ∀neg:(A → A). zz_reg_ring_bad(add, zero, neg) ⇔ (∀x:A. add(neg(x), x) = zero)",
				},
				Symbols: bad,
			})
		}()
	}

	// Define refuses the declaration: it is a structure's.
	func() {
		defer func() {
			if r := recover(); r == nil {
				t.Errorf("Define must refuse Symbols")
			}
		}()
		fam.Define(DefEntry{Name: "NotAStructure", Const: "zz_reg_plain", Type: "A → A", Equations: []string{"∀x:A. zz_reg_plain(x) = x"}, Symbols: map[string]string{"x": "+"}})
	}()
}

// TestDefineStructureSymbolsTwoCarriers: two components of different
// carriers may carry one symbol — a homomorphism's source and target
// additions — and a law body reads each `+` at its own operands; two
// components of one type carrying one symbol are refused.
func TestDefineStructureSymbolsTwoCarriers(t *testing.T) {
	fam := NewFamily("zz_structure_two_carriers_test", nil)
	hom := fam.DefineStructure(DefEntry{
		Name:  "Hom",
		Const: "zz_reg_hom",
		Type:  "(A → A → A) → (B → B → B) → (A → B) → bool",
		Equations: []string{
			"∀add:(A → A → A). ∀add':(B → B → B). ∀f:(A → B). zz_reg_hom(add, add', f) ⇔ (∀x y:A. f(add(x, y)) = add'(f(x), f(y)))",
		},
		Symbols: map[string]string{"add": "+", "add'": "+"},
	})
	s := GetConstMetaManager().ConstSyntax(hom.Const)
	require.NotNil(t, s)
	require.Equal(t, []dsl.StructureComponent{{Symbol: "+", Arity: 2}, {Symbol: "+", Arity: 2}, {}}, s.Structure.Components)

	law := fam.Add(ProofEntry{
		Name:  "MapAdd",
		Build: hom.Axiom("∀x y:A. f(x + y) = f(x) + f(y)"),
	})
	forceStructureEntry(t, law)

	func() {
		defer func() {
			if r := recover(); r == nil {
				t.Errorf("expected the definition to refuse one symbol on two components of one type")
			}
		}()
		NewFamily("zz_structure_two_carriers_bad", nil).DefineStructure(DefEntry{
			Name:  "Bad",
			Const: "zz_reg_hom_bad",
			Type:  "(A → A → A) → (A → A → A) → bool",
			Equations: []string{
				"∀add mul:(A → A → A). zz_reg_hom_bad(add, mul) ⇔ (∀x y:A. add(x, y) = mul(x, y))",
			},
			Symbols: map[string]string{"add": "+", "mul": "+"},
		})
	}()
}

// TestDefinitionConjunct: a predicate definition that is not a structure
// states each conjunct as a law through Conjunct — the left side's
// variables ∀-bound as the definition binds them, the predicate as
// antecedent, the definition declared by construction — and each
// force-builds by unfolding. A structure's entry, an entry that is not a
// definition, and a definition that is not a predicate are refused.
func TestDefinitionConjunct(t *testing.T) {
	fam := NewFamily("zz_conjunct_test", nil)
	closed := fam.Define(DefEntry{
		Name:  "ClosedDef",
		Const: "zz_reg_closed",
		Type:  "(A → A → A) → A → (A → bool) → bool",
		Equations: []string{
			"∀op:(A → A → A). ∀e:A. ∀p:(A → bool). zz_reg_closed(op, e, p) ⇔ " +
				"p(e) ∧ (∀x y:A. p(x) ∧ p(y) ⇒ p(op(x, y)))",
		},
	})
	holdsE := fam.Add(ProofEntry{
		Name:  "ClosedHoldsE",
		Build: closed.Conjunct("p(e)"),
	})
	holdsOp := fam.Add(ProofEntry{
		Name:  "ClosedHoldsOp",
		Build: closed.Conjunct("∀x y:A. p(x) ∧ p(y) ⇒ p(op(x, y))"),
	})
	require.Equal(t,
		"∀op:(A → A → A). ∀e:A. ∀p:(A → bool). zz_reg_closed(op, e, p) ⇒ p(e)",
		holdsE.Build.Headline)
	require.Len(t, holdsOp.Deps, 1, "the definition is the law's dep by construction")
	require.Same(t, closed, holdsOp.Deps[0].Entry())
	forceStructureEntry(t, holdsE)
	forceStructureEntry(t, holdsOp)

	monoid := fam.DefineStructure(DefEntry{
		Name:      "Pointed",
		Const:     "zz_reg_pointed",
		Type:      "(A → A → A) → A → bool",
		Equations: []string{"∀op:(A → A → A). ∀e:A. zz_reg_pointed(op, e) ⇔ (∀x:A. op(e, x) = x) ∧ (∀x:A. op(x, e) = x)"},
	})
	require.Panics(t, func() { monoid.ProofEntry.Conjunct("∀x:A. op(e, x) = x") },
		"a structure's conjuncts are its Axioms")
	require.Panics(t, func() { holdsE.Conjunct("p(e)") }, "a law is not a definition")
	twice := fam.Define(DefEntry{
		Name:      "TwiceDef",
		Const:     "zz_reg_twice",
		Type:      "(A → A → A) → A → A",
		Equations: []string{"∀op:(A → A → A). ∀x:A. zz_reg_twice(op, x) = op(x, x)"},
	})
	require.Panics(t, func() { twice.Conjunct("x = x") }, "a definition that is not a predicate has no conjuncts")
}

// TestDefinitionLaw: a predicate definition that is not a structure
// states any other law over it through Law — the statement Conjunct
// renders, the definition declared by construction — and the proof
// closure binds only the hypothesis (and the body's leading binders),
// the components in scope under their own names. A structure's entry,
// an entry that is not a definition, and a definition that is not a
// predicate are refused.
func TestDefinitionLaw(t *testing.T) {
	fam := NewFamily("zz_definition_law_test", nil)
	closed := fam.Define(DefEntry{
		Name:  "ClosedDef",
		Const: "zz_reg_closed_law",
		Type:  "(A → A → A) → A → (A → bool) → bool",
		Equations: []string{
			"∀op:(A → A → A). ∀e:A. ∀p:(A → bool). zz_reg_closed_law(op, e, p) ⇔ " +
				"p(e) ∧ (∀x y:A. p(x) ∧ p(y) ⇒ p(op(x, y)))",
		},
	})
	squares := fam.Add(ProofEntry{
		Name: "ClosedHoldsSquare",
		Build: closed.Law("p(op(e, e))", func(a *proof.Argument, h proof.Fact) {
			a.Do(proof.Unfold(mintedByName("zz_reg_closed_law")))
			a.Show("e lies in p, and p is closed under op",
				proof.By(a.Hyp("p(e)"), a.Hyp("∀x y:A. p(x) ∧ p(y) ⇒ p(op(x, y))")))
		}),
	})
	require.Equal(t,
		"∀op:(A → A → A). ∀e:A. ∀p:(A → bool). zz_reg_closed_law(op, e, p) ⇒ p(op(e, e))",
		squares.Build.Headline)
	require.Len(t, squares.Deps, 1, "the definition is the law's dep by construction")
	require.Same(t, closed, squares.Deps[0].Entry())
	forceStructureEntry(t, squares)

	// The body's leading binder and premise bind after the hypothesis,
	// as a structure law's do.
	withE := fam.Add(ProofEntry{
		Name: "ClosedHoldsWithE",
		Build: closed.Law("∀x:A. p(x) ⇒ p(op(x, e))", func(a *proof.Argument, h proof.Fact, x proof.Term, inP proof.Fact) {
			a.Do(proof.Unfold(mintedByName("zz_reg_closed_law")))
			a.Show("x and e lie in p, and p is closed under op",
				proof.By(inP, a.Hyp("p(e)"), a.Hyp("∀x y:A. p(x) ∧ p(y) ⇒ p(op(x, y))")))
		}),
	})
	forceStructureEntry(t, withE)

	pointed := fam.DefineStructure(DefEntry{
		Name:      "PointedLaw",
		Const:     "zz_reg_pointed_law",
		Type:      "(A → A → A) → A → bool",
		Equations: []string{"∀op:(A → A → A). ∀e:A. zz_reg_pointed_law(op, e) ⇔ (∀x:A. op(e, x) = x)"},
	})
	require.Panics(t, func() { pointed.ProofEntry.Law("op(e, e) = e", proof.Unfold(mintedByName("zz_reg_pointed_law"))) },
		"a structure's laws are the structure's own Law")
	require.Panics(t, func() { squares.Law("p(e)", proof.Unfold(mintedByName("zz_reg_closed_law"))) }, "a law is not a definition")
	twice := fam.Define(DefEntry{
		Name:      "TwiceLawDef",
		Const:     "zz_reg_twice_law",
		Type:      "(A → A → A) → A → A",
		Equations: []string{"∀op:(A → A → A). ∀x:A. zz_reg_twice_law(op, x) = op(x, x)"},
	})
	require.Panics(t, func() { twice.Law("x = x", proof.Unfold(mintedByName("zz_reg_twice_law"))) },
		"a definition that is not a predicate has no components to state a law over")
}

// statementText is a door statement's text.
func statementText(t *testing.T, st dsl.Statement) string {
	t.Helper()
	text, err := st.Text()
	require.NoError(t, err)
	return text
}
