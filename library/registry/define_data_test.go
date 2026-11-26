// External test package — the corpus-backed force tests (see
// define_recursive_test.go's header note).
package registry_test

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/stretchr/testify/require"
)

// TestFamilyDefineDataBtreeForced is transcript B1's twin,
// kernel-forced end to end against the REAL recspace entries: DefineData
// mints btree at registration, each derived entry's composite
// re-derives its theorem from the corpus-served recspace_recursion /
// recspace_node_injective / family_cons / suc_not_zero entries, and a recursive Define over the
// carrier compiles against the Recursion entry through the typed
// schema dep.
func TestFamilyDefineDataBtreeForced(t *testing.T) {
	// Forcing the recspace entries' own Builds (suc_injective /
	// suc_not_zero run Arith ministeps) needs omega's nat bundle promise-
	// backed — the same production wiring the engine env gets.
	serve.InstallNatBundle()
	fam := registry.NewFamily("zz_define_data_test", nil)
	de := fam.DefineData(registry.DataEntry{
		Name:   "Btree",
		Type:   "zz_reg_btree",
		Params: []string{"A"},
		Constructors: []proof.DataConstructorSpec{
			{Name: "zz_reg_bleaf", Args: []string{"A"}},
			{Name: "zz_reg_bnode", Args: []string{"zz_reg_btree(A)", "zz_reg_btree(A)"}},
		},
		Principles: registry.DataPrinciples{
			Induction: "Induction", Recursion: "Recursion",
			Injective: "NodeInjective", Distinct: "LeafNotNode",
		},
		// The entries serving the library names the derivations read.
		Deps: []registry.EntryLike{
			datatype_universe.Recursion, datatype_universe.FamilyCons, datatype_universe.NodeInjective,
			peano.SucNotZero, peano.SucInjective,
			pairs.Fst, pairs.Snd, pairs.PairEq,
		},
	})
	require.NotNil(t, de.Induct)
	require.NotNil(t, de.Recursion)
	require.Equal(t, proof.DefinitionDataInduct, de.Induct.Definition)
	require.Equal(t, proof.DefinitionDataRecursion, de.Recursion.Definition)
	require.Equal(t, proof.DefinitionDataInj, de.Inj.Definition)
	require.Equal(t, proof.DefinitionDataDistinct, de.Distinct.Definition)
	require.NotNil(t, de.Inj)
	require.NotNil(t, de.Distinct)
	require.Equal(t, "zz_define_data_test.Induction", de.Induct.Name, "the door registers the chapter's name, not a suffix")
	require.Equal(t, "zz_define_data_test.LeafNotNode", de.Distinct.Name)
	require.Equal(t, "zz_reg_btree_induction", de.Induct.ServesAs)
	require.Equal(t, "zz_reg_btree_recursion", de.Recursion.ServesAs)
	require.Contains(t, de.Recursion.DepEntries(), datatype_universe.Recursion.Entry())
	require.Contains(t, de.Recursion.DepEntries(), datatype_universe.FamilyCons.Entry())
	require.Empty(t, de.Induct.Deps, "INDUCT is pure logic over the typedef")

	// Force every derived entry against the real corpus entries it cites.
	ctx := context.Background()
	for _, entry := range []*registry.ProofEntry{de.Induct, de.Recursion, de.Inj, de.Distinct} {
		env := serve.NewSeedEnv()
		env.Scope = proof.NewProofScope(entry.Statement().Key())
		thm, _ := entry.Build.Fn(env)
		require.NotNil(t, thm, "%s builds", entry.Name)
		cert := core.Force(ctx, core.AsThm(thm))
		require.False(t, cert.IsZero(), "%s forces to a kernel cert", entry.Name)
		require.True(t, cert.AlphaEquals(entry.Statement().Prop),
			"%s's forced certificate proves the declared statement", entry.Name)
	}

	// The harness's ServesAs binding serves the Induct entry as stated,
	// in the standard form the analyzer reads: after InstallLibraryDep,
	// the replay side's own template lookup (Script.Induct's path)
	// analyzes it.
	{
		env := serve.NewSeedEnv()
		registry.InstallLibraryDep(env, de.Induct, core.TestThm(
			de.Induct.Statement().Prop.Conclusion(), de.Induct.Statement().Prop.Hyps()...))
		thm, ok := env.LookupLibraryThm("zz_reg_btree_induction")
		require.True(t, ok, "ServesAs binds the principle name")
		tmpl, terr := tactic.AnalyzeInductionPrinciple(thm)
		require.NoError(t, terr, "the served statement IS the shape the analyzer reads")
		require.Len(t, tmpl.Cases, 2)
	}

	// A recursive define over the new carrier: the schema resolves
	// through the TYPED dep on the Recursion entry.
	sizeEntry := fam.Define(registry.DefEntry{
		Name:  "Bsize",
		Const: "zz_reg_bsize",
		Type:  "zz_reg_btree(A) → num",
		Equations: []string{
			"∀a:A. zz_reg_bsize(zz_reg_bleaf(a)) = 1",
			"∀l r:zz_reg_btree(A). zz_reg_bsize(zz_reg_bnode(l, r)) = zz_reg_bsize(l) + zz_reg_bsize(r)",
		},
	})
	require.Len(t, sizeEntry.Deps, 1)
	require.Equal(t, de.Recursion, sizeEntry.Deps[0].Entry())

	// Build it with the Recursion entry preloaded the way the replay
	// harness does — InstallLibraryDep binds the ServesAs alias; the
	// promise settles from the Recursion entry's own Build, so the
	// final force runs the whole cone (schema derivation included) to
	// kernel certificates.
	env := serve.NewSeedEnv()
	schemaThm := core.Promise(de.Recursion.Statement().Prop, func(f core.Forcer) core.ThmCert {
		fenv := serve.NewSeedEnv()
		fenv.Scope = proof.NewProofScope(de.Recursion.Statement().Key())
		fthm, _ := de.Recursion.Build.Fn(fenv)
		return f.Force(core.AsThm(fthm))
	})
	registry.InstallLibraryDep(env, de.Recursion, schemaThm)
	env.Scope = proof.NewProofScope(sizeEntry.Statement().Key())
	thm, _ := sizeEntry.Build.Fn(env)
	require.NotNil(t, thm)
	cert := core.Force(ctx, core.AsThm(thm))
	require.False(t, cert.IsZero())
	require.True(t, cert.AlphaEquals(sizeEntry.Statement().Prop),
		"bsize's forced certificate proves its characterizing statement")
}

// The door refuses a shape whose principles are not all named, and a
// name for a principle the shape does not derive — before minting
// anything, so nothing is left behind.
func TestFamilyDefineDataPrinciplesChecked(t *testing.T) {
	fam := registry.NewFamily("zz_define_data_names_test", nil)
	deps := []registry.EntryLike{
		datatype_universe.Recursion, datatype_universe.FamilyCons, datatype_universe.NodeInjective,
		peano.SucNotZero, peano.SucInjective,
		pairs.Fst, pairs.Snd, pairs.PairEq,
	}
	require.PanicsWithValue(t,
		"registry.DefineData(Two): the distinct derivation has no registered name — spell it in Principles (Distinct)",
		func() {
			fam.DefineData(registry.DataEntry{
				Name: "Two", Type: "zz_names_two",
				Constructors: []proof.DataConstructorSpec{{Name: "zz_names_a"}, {Name: "zz_names_b"}},
				Principles:   registry.DataPrinciples{Induction: "Induction", Recursion: "Recursion"},
				Deps:         deps,
			})
		})
	require.Panics(t, func() {
		fam.DefineData(registry.DataEntry{
			Name: "One", Type: "zz_names_one",
			Constructors: []proof.DataConstructorSpec{{Name: "zz_names_only"}},
			Principles: registry.DataPrinciples{
				Induction: "Induction", Recursion: "Recursion", Distinct: "Distinct", // one constructor: no distinctness law
			},
			Deps: deps,
		})
	})
}

// A record's Fields: the door defines each part by its projection
// equation, derives the extensionality law under the chapter's name, and
// hands back Parts — the law and the projections as one rule set — with
// the entries a consumer declares. (The derivation is forced end to end
// by complex_field.ComplexEq's replay.)
func TestFamilyDefineDataRecordParts(t *testing.T) {
	fam := registry.NewFamily("zz_define_data_record_test", nil)
	de := fam.DefineData(registry.DataEntry{
		Name: "Point", Type: "zz_rec_point",
		Constructors: []proof.DataConstructorSpec{{Name: "zz_rec_mk", Args: []string{"num", "num"}}},
		Fields: []registry.DataField{
			{Name: "XDef", Const: "zz_rec_x"},
			{Name: "YDef", Const: "zz_rec_y"},
		},
		Principles: registry.DataPrinciples{
			Induction: "Induction", Recursion: "Recursion", Injective: "MkInjective", Extensionality: "PointEq",
		},
		Deps: []registry.EntryLike{
			datatype_universe.Recursion, datatype_universe.FamilyCons, datatype_universe.NodeInjective,
			pairs.Fst, pairs.Snd, pairs.PairEq,
		},
	})
	require.Len(t, de.Fields, 2)
	require.Equal(t, "zz_define_data_record_test.XDef", de.Fields[0].Name)
	require.Equal(t, proof.DefinitionRecursive, de.Fields[0].Definition, "a projection is a definition by cases")
	require.Contains(t, ext.PrintTerm(de.Fields[0].Statement().Prop.Conclusion()), "zz_rec_x(zz_rec_mk(a, b)) = a")
	for _, field := range de.Fields {
		require.Equal(t, string(field.Statement().Key()), field.Key,
			"a projection's key is computed from its statement: the record's literal gives it none to spell")
	}
	require.NotNil(t, de.Ext)
	require.Equal(t, "zz_define_data_record_test.PointEq", de.Ext.Name)
	extStmt := ext.PrintTerm(de.Ext.Statement().Prop.Conclusion())
	require.Contains(t, extStmt, "zz_rec_x(u) = zz_rec_x(v)")
	require.Contains(t, extStmt, "zz_rec_y(u) = zz_rec_y(v)")
	require.NotNil(t, de.Parts)
}

// Fields are refused where a projection would be partial or ill-matched,
// and an Extensionality name without Fields is refused — before
// anything is minted.
func TestFamilyDefineDataFieldsChecked(t *testing.T) {
	fam := registry.NewFamily("zz_define_data_fields_test", nil)
	deps := []registry.EntryLike{
		datatype_universe.Recursion, datatype_universe.FamilyCons, datatype_universe.NodeInjective,
		peano.SucNotZero, peano.SucInjective,
		pairs.Fst, pairs.Snd, pairs.PairEq,
	}
	full := registry.DataPrinciples{Induction: "Induction", Recursion: "Recursion", Injective: "Inj", Extensionality: "Ext"}
	require.PanicsWithValue(t,
		"registry.DefineData(Two): Fields are the parts of a record — a datatype with ONE constructor; this one has 2, so a projection would be partial",
		func() {
			fam.DefineData(registry.DataEntry{
				Name: "Two", Type: "zz_fields_two",
				Constructors: []proof.DataConstructorSpec{{Name: "zz_fields_a", Args: []string{"num"}}, {Name: "zz_fields_b"}},
				Fields:       []registry.DataField{{Name: "ADef", Const: "zz_fields_get"}},
				Principles:   full, Deps: deps,
			})
		})
	require.PanicsWithValue(t,
		"registry.DefineData(Short): 1 field(s) for a constructor of 2 argument(s) — one field per argument, in the constructor's order",
		func() {
			fam.DefineData(registry.DataEntry{
				Name: "Short", Type: "zz_fields_short",
				Constructors: []proof.DataConstructorSpec{{Name: "zz_fields_mk", Args: []string{"num", "num"}}},
				Fields:       []registry.DataField{{Name: "XDef", Const: "zz_fields_x"}},
				Principles:   full, Deps: deps,
			})
		})
	require.PanicsWithValue(t,
		"registry.DefineData(Unnamed): a record's Fields derive its extensionality — name it in Principles.Extensionality",
		func() {
			fam.DefineData(registry.DataEntry{
				Name: "Unnamed", Type: "zz_fields_unnamed",
				Constructors: []proof.DataConstructorSpec{{Name: "zz_fields_mk2", Args: []string{"num"}}},
				Fields:       []registry.DataField{{Name: "XDef", Const: "zz_fields_x2"}},
				Principles:   registry.DataPrinciples{Induction: "Induction", Recursion: "Recursion", Injective: "Inj"},
				Deps:         deps,
			})
		})
	require.PanicsWithValue(t,
		"registry.DefineData(NoFields): Principles names Extensionality \"Ext\", but the datatype declares no Fields",
		func() {
			fam.DefineData(registry.DataEntry{
				Name: "NoFields", Type: "zz_fields_none",
				Constructors: []proof.DataConstructorSpec{{Name: "zz_fields_mk3", Args: []string{"num"}}},
				Principles:   full, Deps: deps,
			})
		})
}

// A record whose fields name a Field reads, under a binder of its
// type, `S.e` as the projection applied to S and `x + y` as the
// operation field applied to the operands; the chapter spelling writes
// both back. A symbol with no Field to read it off, and a Field named
// twice, are refused before anything is minted.
func TestFamilyDefineDataRecordFieldSyntax(t *testing.T) {
	fam := registry.NewFamily("zz_define_data_struct_test", nil)
	deps := []registry.EntryLike{
		datatype_universe.Recursion, datatype_universe.FamilyCons, datatype_universe.NodeInjective,
		pairs.Fst, pairs.Snd, pairs.PairEq,
	}
	principles := registry.DataPrinciples{Induction: "Induction", Recursion: "Recursion", Injective: "MkInjective", Extensionality: "OpsEq"}
	fam.DefineData(registry.DataEntry{
		Name: "Ops", Type: "zz_struct_ops", Params: []string{"A"},
		Constructors: []proof.DataConstructorSpec{{Name: "zz_struct_mk", Args: []string{"A → A → A", "A", "A → A"}}},
		Fields: []registry.DataField{
			{Name: "OpDef", Const: "zz_struct_op", Field: "op", Symbol: "+"},
			{Name: "EDef", Const: "zz_struct_e", Field: "e"},
			{Name: "InvDef", Const: "zz_struct_inv", Field: "inv", Symbol: "-"},
		},
		Principles: principles, Deps: deps,
	})
	mgr := registry.GetConstMetaManager()
	syntax := mgr.StructSyntax("zz_struct_ops")
	require.NotNil(t, syntax)
	require.Len(t, syntax.Fields, 3)
	scope := &dsl.ParseScope{
		ConstResolver: func(name string) core.ConstTermMeta {
			meta, _ := mgr.LoadConstMeta(core.TermName(name))
			return meta
		},
		Syntax: mgr, TypeResolver: mgr.TypeArity,
	}
	parse := func(text string) core.Prop {
		res := dsl.ParsePropTextInScope(text, scope)
		require.Empty(t, res.Errors, text)
		return res.Prop
	}
	spelled := "∀S:zz_struct_ops(A). ∀x y:A. zz_struct_op(S)(x, y) = zz_struct_e(S) ⇒ zz_struct_inv(S)(x) = y"
	short := "∀S:zz_struct_ops(A). ∀x y:A. x + y = S.e ⇒ -x = y"
	require.Equal(t, parse(spelled).AlphaKey(), parse(short).AlphaKey())
	out, err := dsl.ChapterSpelling(spelled, mgr, nil)
	require.NoError(t, err)
	require.Equal(t, short, out)
	for _, tc := range []struct{ raw, want string }{
		{"∀S T:zz_struct_ops(A). ∀x y:A. zz_struct_op(S, x, y) = zz_struct_op(T, y, x)",
			"∀S T:zz_struct_ops(A). ∀x y:A. S.op(x, y) = T.op(y, x)"},
		{"∀S:zz_struct_ops(num). ∀x y:num. zz_struct_op(S, x, y) = x + y",
			"∀S:zz_struct_ops(num). ∀x y:num. S.op(x, y) = x + y"},
		{"∀P:(num → zz_struct_ops(B)). ∀n:num. ∀x:B. zz_struct_op(P(n), x, zz_struct_e(P(n))) = x",
			"∀P:(num → zz_struct_ops(B)). ∀n:num. ∀x:B. P(n).op(x, P(n).e) = x"},
		{"∀op:(A → A → A). ∀e:A. ∀inv:(A → A). zz_struct_e(zz_struct_mk(op, e, inv)) = e",
			"∀op:(A → A → A). ∀e:A. ∀inv:(A → A). zz_struct_mk(op, e, inv).e = e"},
	} {
		out, err := dsl.ChapterSpelling(tc.raw, mgr, nil)
		require.NoError(t, err)
		require.Equal(t, tc.want, out)
		require.Equal(t, parse(tc.raw).AlphaKey(), parse(out).AlphaKey())
	}

	require.PanicsWithValue(t,
		"registry.DefineData(Bare): field OpDef carries + but has no Field name — a symbol is read off a value's field",
		func() {
			fam.DefineData(registry.DataEntry{
				Name: "Bare", Type: "zz_struct_bare", Params: []string{"A"},
				Constructors: []proof.DataConstructorSpec{{Name: "zz_struct_mk2", Args: []string{"A → A → A"}}},
				Fields:       []registry.DataField{{Name: "OpDef", Const: "zz_struct_op2", Symbol: "+"}},
				Principles:   principles, Deps: deps,
			})
		})
	require.PanicsWithValue(t,
		"registry.DefineData(Twice): Field op is named twice",
		func() {
			fam.DefineData(registry.DataEntry{
				Name: "Twice", Type: "zz_struct_twice", Params: []string{"A"},
				Constructors: []proof.DataConstructorSpec{{Name: "zz_struct_mk3", Args: []string{"A → A → A", "A → A → A"}}},
				Fields: []registry.DataField{
					{Name: "ADef", Const: "zz_struct_a", Field: "op"},
					{Name: "BDef", Const: "zz_struct_b", Field: "op"},
				},
				Principles: principles, Deps: deps,
			})
		})
}
