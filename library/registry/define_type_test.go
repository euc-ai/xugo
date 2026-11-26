package registry

import (
	"context"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/require"
)

// TestFamilyDefineType: family.DefineType mints the type and its
// abs/rep pair at registration on the PROMISE of the inhabitation
// entry, registers the two type-definition theorems with computed
// keys, and each Build derives its theorem from the inhabitation
// certificate under a harness-armed env. Forcing the recorded source
// runs the inhabitation entry through ForceEntry — never a trust.
func TestFamilyDefineType(t *testing.T) {
	// The shape: numbers fixed by adding zero — every number, but the
	// normalizer does no arithmetic, so the inhabitation is an entry
	// (built here by a test-only trusted theorem; a chapter proves it).
	fam := NewFamily("zz_define_type_test", nil)
	inhabited := fam.Add(ProofEntry{
		Name: "Inhabited",
		Build: BuildSpec{Headline: "∃n:num. n = n + 0", Fn: func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
			ctx := proof.NewScript(env)
			return core.TestThm(fam.Entries()[0].Statement().Prop.Conclusion()), &ctx.Proof
		}},
	})

	te := fam.DefineType(TypeEntry{
		Name:      "Self",
		Type:      "zz_selfnum",
		Abs:       "zz_mk_selfnum",
		Rep:       "zz_dest_selfnum",
		Pred:      "λn:num. n = n + 0",
		Existence: inhabited,
	})

	// Registration facts: the pair is registered, the type is theirs,
	// and the two entries state the axioms in closed, reduced form.
	mgr := GetConstMetaManager()
	absMeta, ok := mgr.LoadConstMeta("zz_mk_selfnum")
	require.True(t, ok)
	require.True(t, absMeta.IsTypeDefAbs())
	require.Equal(t, "zz_selfnum", string(te.Meta.Name()))
	require.Equal(t, "zz_define_type_test.SelfRetraction", te.Retraction.Name)
	require.Equal(t, "zz_define_type_test.SelfMembership", te.Membership.Name)
	// The package reaches each theorem through the handle's field, as the
	// chapter spells it (`NaddDef.Membership`): no variable carries the name.
	require.Equal(t, "SelfDef.Retraction", te.Retraction.GoRef())
	require.Equal(t, "SelfDef.Membership", te.Membership.GoRef())
	require.Contains(t, te.Retraction.Key, "prop_")
	require.Contains(t, te.Membership.Key, "prop_")
	stated := func(text string) core.Prop {
		res := dsl.ParsePropTextInScope(text, &dsl.ParseScope{
			ConstResolver: func(name string) core.ConstTermMeta {
				if meta, ok := mgr.LoadConstMeta(core.TermName(name)); ok {
					return meta
				}
				return core.ConstTermMeta{}
			},
			StrictResolution: true, FreshenMetaLetters: true,
		})
		require.Empty(t, res.Errors, "%s", text)
		return res.Prop
	}
	require.True(t, te.Retraction.Statement().Prop.AlphaEquals(
		stated("∀a:zz_selfnum. zz_mk_selfnum(zz_dest_selfnum(a)) = a")),
		"retraction states %s", ext.PrintTerm(te.Retraction.Statement().Prop.Conclusion()))
	require.True(t, te.Membership.Statement().Prop.AlphaEquals(
		stated("∀r:num. r = r + 0 ⇔ zz_dest_selfnum(zz_mk_selfnum(r)) = r")),
		"membership states %s", ext.PrintTerm(te.Membership.Statement().Prop.Conclusion()))
	require.Equal(t, []*ProofEntry{inhabited}, te.Retraction.DepEntries())

	// Replay: each Build under a harness-armed env with the
	// inhabitation dep preloaded, the built theorem α-equal to the
	// statement.
	harness := func(e *ProofEntry) *proof.ProverEnv {
		var cnfCache utils.Map[core.TermKey, core.Prop]
		env := &proof.ProverEnv{
			ProofService: &proof.ProofService{
				LoadConstMeta:        mgr.LoadConstMeta,
				LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
				Syntax:               mgr,
			},
			CnfRefuterTimeout:     2 * time.Second,
			CnfNormalizationCache: &cnfCache,
			CnfNormalizeCache:     proof.NewCNFNormalizeCache(),
			LibraryThms:           map[string]core.Thm{},
		}
		env.Scope = proof.NewProofScope(e.Statement().Key())
		return env
	}
	inhabitedThm, _ := inhabited.Build.Fn(harness(inhabited))
	inhabitedCert := core.Force(context.Background(), core.AsThm(inhabitedThm))
	for _, e := range []*ProofEntry{te.Retraction, te.Membership} {
		env := harness(e)
		InstallLibraryDep(env, inhabited, inhabitedCert)
		thm, _ := e.Build.Fn(env)
		cert := core.Force(context.Background(), core.AsThm(thm))
		require.True(t, cert.Conclusion().AlphaEquals(e.Statement().Prop.Conclusion()),
			"%s built:\n  %s\nstated:\n  %s", e.Name,
			ext.PrintTerm(cert.Conclusion()), ext.PrintTerm(e.Statement().Prop.Conclusion()))
	}

	// The recorded source is a promise; forcing it runs the entry
	// through ForceEntry and yields ⊢ Pred(εPred).
	prev := ForceEntry
	defer func() { ForceEntry = prev }()
	ForceEntry = func(f core.Forcer, e *ProofEntry) core.ThmCert {
		thm, _ := e.Build.Fn(harness(e))
		return f.Force(core.AsThm(thm))
	}
	source := ext.TypeDefSourceThm(absMeta, core.NewForcer(context.Background()))
	analyzed, aerr := proof.AnalyzeTypeDefinition(te.Pred, nil)
	require.NoError(t, aerr)
	require.True(t, source.Conclusion().AlphaEquals(analyzed.Applied.Conclusion()),
		"forced source:\n  %s", ext.PrintTerm(source.Conclusion()))

	// The mint is exclusive: the abs name is taken.
	require.Panics(t, func() {
		NewFamily("zz_define_type_test_dup", nil).DefineType(TypeEntry{
			Name: "Again", Type: "zz_selfnum2", Abs: "zz_mk_selfnum", Rep: "zz_dest_selfnum2",
			Pred: "λn:num. n = n + 0", Existence: inhabited,
		})
	})
}

// TestFamilyDefineType_Trivial: an inhabitation the normalizer decides
// is proved at registration and recorded as a certificate; the entries
// derive from it with no dep. An inhabitation the normalizer refutes
// is refused, and an Existence entry for a trivial one is refused too.
func TestFamilyDefineType_Trivial(t *testing.T) {
	fam := NewFamily("zz_define_type_trivial_test", nil)
	te := fam.DefineType(TypeEntry{
		Name: "Unit",
		Type: "zz_unitbool",
		Abs:  "zz_mk_unitbool",
		Rep:  "zz_dest_unitbool",
		Pred: "λb:bool. b = b",
	})
	require.Empty(t, te.Retraction.DepEntries())
	mgr := GetConstMetaManager()
	absMeta, ok := mgr.LoadConstMeta("zz_mk_unitbool")
	require.True(t, ok)
	require.True(t, absMeta.DefSource().Proved(), "a trivial inhabitation is a certificate at the mint")
	for _, e := range []*ProofEntry{te.Retraction, te.Membership} {
		var cnfCache utils.Map[core.TermKey, core.Prop]
		env := &proof.ProverEnv{
			ProofService: &proof.ProofService{
				LoadConstMeta:        mgr.LoadConstMeta,
				LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
				Syntax:               mgr,
			},
			CnfRefuterTimeout:     2 * time.Second,
			CnfNormalizationCache: &cnfCache,
			CnfNormalizeCache:     proof.NewCNFNormalizeCache(),
			LibraryThms:           map[string]core.Thm{},
		}
		env.Scope = proof.NewProofScope(e.Statement().Key())
		thm, _ := e.Build.Fn(env)
		cert := core.Force(context.Background(), core.AsThm(thm))
		require.True(t, cert.Conclusion().AlphaEquals(e.Statement().Prop.Conclusion()),
			"%s built:\n  %s\nstated:\n  %s", e.Name,
			ext.PrintTerm(cert.Conclusion()), ext.PrintTerm(e.Statement().Prop.Conclusion()))
	}
	// An empty shape is refused at the mint.
	require.Panics(t, func() {
		NewFamily("zz_define_type_trivial_bad", nil).DefineType(TypeEntry{
			Name: "Bad", Type: "zz_badbool", Abs: "zz_mk_badbool", Rep: "zz_dest_badbool",
			Pred: "λb:bool. b ∧ ¬b",
		})
	})
	// An Existence entry for a trivial inhabitation is refused: it
	// would carry the key of ⊤.
	require.Panics(t, func() {
		bad := NewFamily("zz_define_type_trivial_dup", nil)
		bad.DefineType(TypeEntry{
			Name: "Again", Type: "zz_unitbool2", Abs: "zz_mk_unitbool2", Rep: "zz_dest_unitbool2",
			Pred: "λb:bool. b = b",
			Existence: bad.Add(ProofEntry{
				Name: "Trivial", Build: BuildSpec{Headline: "∃b:bool. b = b", Fn: func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
			}),
		})
	})
}

// TestFamilyDefineType_LambdaWitness: a λ-predicate with a Witness —
// the Existence entry states the membership at the witness with the
// redex REDUCED (the form a chapter states), and the door bridges to
// the recorded Pred(w) by β: the forced source is the applied form,
// and each Build derives its axiom from the entry's certificate.
func TestFamilyDefineType_LambdaWitness(t *testing.T) {
	fam := NewFamily("zz_define_type_lambda_witness_test", nil)
	atZero := fam.Add(ProofEntry{
		Name: "AtZero",
		Build: BuildSpec{Headline: "0 = 0 + 0", Fn: func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
			ctx := proof.NewScript(env)
			return core.TestThm(fam.Entries()[0].Statement().Prop.Conclusion()), &ctx.Proof
		}},
	})
	te := fam.DefineType(TypeEntry{
		Name:      "Fixed",
		Type:      "zz_fixednum",
		Abs:       "zz_mk_fixednum",
		Rep:       "zz_dest_fixednum",
		Pred:      "λn:num. n = n + 0",
		Existence: atZero,
		Witness:   "0",
	})
	mgr := GetConstMetaManager()
	absMeta, ok := mgr.LoadConstMeta("zz_mk_fixednum")
	require.True(t, ok)
	require.Equal(t, []*ProofEntry{atZero}, te.Membership.DepEntries())

	harness := func(e *ProofEntry) *proof.ProverEnv {
		var cnfCache utils.Map[core.TermKey, core.Prop]
		env := &proof.ProverEnv{
			ProofService: &proof.ProofService{
				LoadConstMeta:        mgr.LoadConstMeta,
				LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
				Syntax:               mgr,
			},
			CnfRefuterTimeout:     2 * time.Second,
			CnfNormalizationCache: &cnfCache,
			CnfNormalizeCache:     proof.NewCNFNormalizeCache(),
			LibraryThms:           map[string]core.Thm{},
		}
		env.Scope = proof.NewProofScope(e.Statement().Key())
		return env
	}
	atZeroThm, _ := atZero.Build.Fn(harness(atZero))
	atZeroCert := core.Force(context.Background(), core.AsThm(atZeroThm))
	for _, e := range []*ProofEntry{te.Retraction, te.Membership} {
		env := harness(e)
		InstallLibraryDep(env, atZero, atZeroCert)
		thm, _ := e.Build.Fn(env)
		cert := core.Force(context.Background(), core.AsThm(thm))
		require.True(t, cert.Conclusion().AlphaEquals(e.Statement().Prop.Conclusion()),
			"%s built:\n  %s\nstated:\n  %s", e.Name,
			ext.PrintTerm(cert.Conclusion()), ext.PrintTerm(e.Statement().Prop.Conclusion()))
	}

	// Forcing the recorded source runs the entry and bridges by β to
	// the applied form (λn. n = n + 0)(0).
	prev := ForceEntry
	defer func() { ForceEntry = prev }()
	ForceEntry = func(f core.Forcer, e *ProofEntry) core.ThmCert {
		thm, _ := e.Build.Fn(harness(e))
		return f.Force(core.AsThm(thm))
	}
	zero, _, isEq := core.MatchesEQ(atZeroCert.Conclusion())
	require.True(t, isEq)
	source := ext.TypeDefSourceThm(absMeta, core.NewForcer(context.Background()))
	require.True(t, source.Conclusion().AlphaEquals(core.Apply(te.Pred, zero)),
		"forced source:\n  %s", ext.PrintTerm(source.Conclusion()))

	// An entry proving something else is refused when the Build runs:
	// the composite's child is the reduced membership, and the dep must
	// state exactly that.
	bad := NewFamily("zz_define_type_lambda_witness_bad", nil)
	other := bad.Add(ProofEntry{
		Name: "Other", Build: BuildSpec{Headline: "0 + 0 = 0", Fn: func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
			ctx := proof.NewScript(env)
			return core.TestThm(bad.Entries()[0].Statement().Prop.Conclusion()), &ctx.Proof
		}},
	})
	badTe := bad.DefineType(TypeEntry{
		Name: "Bad", Type: "zz_badfixednum", Abs: "zz_mk_badfixednum", Rep: "zz_dest_badfixednum",
		Pred: "λn:num. n = n + 0", Existence: other, Witness: "0",
	})
	otherThm, _ := other.Build.Fn(harness(other))
	env := harness(badTe.Retraction)
	InstallLibraryDep(env, other, core.Force(context.Background(), core.AsThm(otherThm)))
	require.Panics(t, func() { badTe.Retraction.Build.Fn(env) })
}

// TestFamilyDefineType_RefusesATypeNameInUse: a type name is minted
// once. MetaType identity is by name and arity, so a second definition
// under a name in use — the kernel's own bool, or a type another family
// minted at the same arity — would give one type two bijections, with
// subsets of any two sizes; the Go door refuses it as the session door
// does, through the one check in proof.MintTypeDefinition.
func TestFamilyDefineType_RefusesATypeNameInUse(t *testing.T) {
	require.Panics(t, func() {
		NewFamily("zz_define_type_bool", nil).DefineType(TypeEntry{
			Name: "Bool", Type: "bool", Abs: "zz_mk_bool_again", Rep: "zz_dest_bool_again",
			Pred: "λn:num. n = n",
		})
	})

	NewFamily("zz_define_type_inuse_a", nil).DefineType(TypeEntry{
		Name: "All", Type: "zz_inuse", Abs: "zz_mk_inuse_all", Rep: "zz_dest_inuse_all",
		Pred: "λn:num. n = n",
	})
	require.Panics(t, func() {
		NewFamily("zz_define_type_inuse_b", nil).DefineType(TypeEntry{
			Name: "Zero", Type: "zz_inuse", Abs: "zz_mk_inuse_zero", Rep: "zz_dest_inuse_zero",
			Pred: "λn:num. n = 0",
		})
	})
}
