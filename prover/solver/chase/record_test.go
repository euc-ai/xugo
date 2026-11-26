package chase

import (
	"github.com/euc-ai/xugo/prover/solver/omega"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// _RecordWorld supplies abstract records and the same carrier laws as the
// production bundle. Its projection equations are theorem fixtures, just as
// the algebraic laws in _FakeWorld are.
type _RecordWorld struct {
	*_FakeWorld
	ringType, moduleType                                                core.HolType
	moduleOn, recordHom, mkRing, mkModule, additiveGroup                core.Term
	ringCarrier, addField, zeroField, negField, smulField, carrierField core.Term
	ring                                                                core.Term
	recordLaws                                                          map[string]*prop.PropWrapper
	projections                                                         map[string]*prop.PropWrapper
}

func opaqueRecordConst(name string, args []core.HolType, result core.HolType) core.Term {
	ty := result
	for i := len(args) - 1; i >= 0; i-- {
		ty = core.MakeFun(args[i], ty)
	}
	return core.NewConstDef(core.Hilbert(core.Var("chosen", ty), ext.T), core.TermName(name))
}

func newRecordWorld() *_RecordWorld {
	w := &_RecordWorld{_FakeWorld: newFakeWorldBase()}
	S, T := w.S, w.T
	setS := core.MakeFun(S, core.TypeBool())
	w.ringType, w.moduleType = core.MakeFun(setS, S), core.MakeFun(w.setT, T)
	V := core.MakeVarType("V")
	targetModule := core.MakeFun(core.MakeFun(V, core.TypeBool()), V)
	TT, TTT, STT := core.MakeFun(T, T), core.MakeFun(T, core.MakeFun(T, T)), core.MakeFun(S, core.MakeFun(T, T))
	w.moduleOn = defConst(moduleOnName, []core.HolType{w.ringType, w.moduleType}, core.TypeBool())
	w._FakeWorld.submodule = defConst(submoduleName, []core.HolType{w.ringType, w.moduleType, w.setT}, core.TypeBool())
	w.recordHom = defConst(homomorphismName, []core.HolType{w.ringType, w.moduleType, targetModule, core.MakeFun(T, V)}, core.TypeBool())
	w.mkRing = opaqueRecordConst("mk_ring", []core.HolType{setS}, w.ringType)
	w.mkModule = opaqueRecordConst("mk_module", []core.HolType{TTT, T, TT, STT, w.setT}, w.moduleType)
	w.additiveGroup = opaqueRecordConst("module_additive_group", []core.HolType{w.moduleType}, w.groupType)
	w.ringCarrier = opaqueRecordConst("ring_carrier", []core.HolType{w.ringType}, setS)
	w.addField = opaqueRecordConst("mod_add", []core.HolType{w.moduleType}, TTT)
	w.zeroField = opaqueRecordConst("mod_zero", []core.HolType{w.moduleType}, T)
	w.negField = opaqueRecordConst("mod_neg", []core.HolType{w.moduleType}, TT)
	w.smulField = opaqueRecordConst("mod_smul", []core.HolType{w.moduleType}, STT)
	w.carrierField = opaqueRecordConst("mod_carrier", []core.HolType{w.moduleType}, w.setT)
	w.ring = w.ap(w.mkRing, w.R)
	R := core.Var("r", w.ringType)
	M, N := core.Var("m", w.moduleType), core.Var("n", targetModule)
	f, u, v, c := core.Var("f", core.MakeFun(T, V)), w.elem("u"), w.elem("v"), core.Var("c", S)
	module := w.ap(w.moduleOn, R, M)
	lead := []core.Term{R, M}
	ml := func(body core.Term) *prop.PropWrapper { return thm(all(lead, imp(module, body))) }
	inM := func(x core.Term) core.Term { return w.in(x, w.carrier(M)) }
	hp := w.ap(w.recordHom, R, M, N, f)
	hl := func(body core.Term) *prop.PropWrapper { return thm(all([]core.Term{R, M, N, f}, imp(hp, body))) }
	K := w.set("K")
	w.recordLaws = map[string]*prop.PropWrapper{
		"AddGroupOn": ml(w.ap(w.groupOn, w.ap(w.additiveGroup, M))),
		"AddComm":    ml(all([]core.Term{u, v}, imp(and(inM(u), inM(v)), eq(w.sum(M, u, v), w.sum(M, v, u))))),
		"SmulIn":     ml(all([]core.Term{c, u}, imp(and(w.in(c, w.ap(w.ringCarrier, R)), inM(u)), inM(w.ap(w.smulField, M, c, u))))),
		"SubmoduleSubgroup": thm(all([]core.Term{R, M, K}, imp(w.ap(w.submodule, R, M, K),
			w.ap(w.subgroup, w.ap(w.additiveGroup, M), K)))),
		"HomSource": hl(w.ap(w.moduleOn, R, M)),
		"HomTarget": hl(recordApply(w.moduleOn, R, N)),
		"HomIn":     hl(all([]core.Term{u}, imp(inM(u), w.in(w.ap(f, u), w.carrier(N))))),
		"HomAdd":    hl(all([]core.Term{u, v}, imp(and(inM(u), inM(v)), eq(w.ap(f, w.sum(M, u, v)), w.sum(N, w.ap(f, u), w.ap(f, v)))))),
	}
	a, z, n, s, C := core.Var("a", TTT), core.Var("z", T), core.Var("n", TT), core.Var("s", STT), w.set("C")
	args := []core.Term{a, z, n, s, C}
	packed := w.ap(w.mkModule, args...)
	w.projections = map[string]*prop.PropWrapper{
		"RingCarrier": thm(all([]core.Term{w.R}, eq(w.ap(w.ringCarrier, w.ap(w.mkRing, w.R)), w.R))),
	}
	for i, row := range []struct {
		name  string
		field core.Term
	}{{"ModuleAdd", w.addField}, {"ModuleZero", w.zeroField}, {"ModuleNeg", w.negField}, {"ModuleSmul", w.smulField}, {"ModuleCarrier", w.carrierField}} {
		w.projections[row.name] = thm(all(args, eq(w.ap(row.field, packed), args[i])))
	}
	w._FakeWorld.records = w
	l := w.laws
	// The forgetful definition computes under group projections while its
	// record subject keeps its spelling in group and subgroup facts.
	forget := recordDefinition(thm(all([]core.Term{M}, eq(w.ap(w.additiveGroup, M), w.ap(w.mkGroup, w.ap(w.addField, M), w.ap(w.zeroField, M), w.ap(w.negField, M), w.carrier(M))))))
	previous := l.NormalizeWith
	l.NormalizeWith = func(read omega.LibraryRead) prop.Rewrite {
		return prop.DeepRewrite(previous(read), func(t core.Term) *prop.PropWrapper {
			app, ok := t.AsAppliedTerm()
			if !ok {
				return nil
			}
			isProjection := false
			for _, selector := range []core.Term{w.groupMul, w.groupOne, w.groupInv, w.groupCarrier} {
				if a, aok := app.Fun().AsConst(); aok {
					if b, _ := selector.AsConst(); a.Meta() == b.Meta() {
						isProjection = true
						break
					}
				}
			}
			if !isProjection {
				return nil
			}
			if eq := forget(app.Arg()); eq != nil {
				return eq.LeftApply(app.Fun())
			}
			return nil
		})
	}
	l.AddGroupOn, l.AddComm, l.SmulIn = w.recordLaws["AddGroupOn"], w.recordLaws["AddComm"], w.recordLaws["SmulIn"]
	l.SubmoduleSubgroup = w.recordLaws["SubmoduleSubgroup"]
	l.HomSource, l.HomTarget = w.recordLaws["HomSource"], w.recordLaws["HomTarget"]
	l.HomIn, l.HomAdd = w.recordLaws["HomIn"], w.recordLaws["HomAdd"]
	l.Rewrites = RecordRewrites{
		RingCarrier: w.projections["RingCarrier"], ModuleAdd: w.projections["ModuleAdd"],
		ModuleZero: w.projections["ModuleZero"], ModuleNeg: w.projections["ModuleNeg"],
		ModuleSmul: w.projections["ModuleSmul"], ModuleCarrier: w.projections["ModuleCarrier"],
	}
	return w
}

func recordApply(fn core.Term, args ...core.Term) core.Term {
	var types []core.TypeSubst
	binders := ext.MatchesFun(fn.Type())
	for i, arg := range args {
		if !core.MatchTypeInto(binders[i], arg.Type(), func(core.VarType) bool { return true }, &types) {
			panic("record fixture type mismatch")
		}
	}
	return ext.Apply(fn.TypeSubstitute(types...), args...)
}

func (w *_RecordWorld) record(name string) core.Term {
	return core.Var(core.TermName(name), w.moduleType)
}
func (w *_RecordWorld) carrier(M core.Term) core.Term   { return recordApply(w.carrierField, M) }
func (w *_RecordWorld) sum(M, x, y core.Term) core.Term { return recordApply(w.addField, M, x, y) }
func (w *_RecordWorld) homRecord(f, M, N core.Term) core.Term {
	return recordApply(w.recordHom, w.ring, M, N, f)
}
func (w *_RecordWorld) packed(M core.Term) core.Term {
	return w.ap(w.mkModule, w.add, w.zero, w.neg, w.smul, M)
}

func (w *_RecordWorld) install(t *testing.T) {
	t.Helper()
	SetLaws(w.laws)
	t.Cleanup(func() { SetLaws(nil) })
}

func TestChase_RecordHomSuppliesItsModules(t *testing.T) {
	w := newRecordWorld()
	w.install(t)
	M, N := w.record("M"), w.record("N")
	f, x, y := w.fn("f"), w.elem("x"), w.elem("y")
	hyps := []core.Term{w.homRecord(f, M, N), w.in(x, w.carrier(M)), w.in(y, w.carrier(M))}
	closes(t, core.MakeProp(eq(w.ap(f, w.sum(M, x, w.ap(w.negField, M, y))), w.sum(N, w.ap(f, x), w.ap(w.negField, N, w.ap(f, y)))), hyps...), 0)
	closes(t, core.MakeProp(eq(w.ap(f, w.ap(w.zeroField, M)), w.ap(w.zeroField, N)), hyps...), 0)
}

func TestChase_RecordPackedModuleMeetsItsHomomorphism(t *testing.T) {
	w := newRecordWorld()
	w.install(t)
	M, N := w.set("M"), w.set("N")
	f, x, y := w.fn("f"), w.elem("x"), w.elem("y")
	hyps := []core.Term{w.module(M), w.homRecord(f, w.packed(M), w.packed(N)), w.in(x, M), w.in(y, M)}
	closes(t, core.MakeProp(eq(w.ap(f, w.plus(x, y)), w.plus(w.ap(f, x), w.ap(f, y))), hyps...), 0)
}

func TestChase_RecordModuleClosure(t *testing.T) {
	w := newRecordWorld()
	w.install(t)
	M := w.record("M")
	x := w.elem("x")
	c := core.Var("c", w.S)
	hyps := []core.Term{w.ap(w.moduleOn, w.ring, M), w.in(x, w.carrier(M)), w.in(c, w.R)}
	closes(t, core.MakeProp(w.in(w.ap(w.smulField, M, c, x), w.carrier(M)), hyps...), 0)
	th, _, err := Close(core.MakeProp(w.in(w.ap(w.smulField, M, c, x), w.carrier(M)), hyps[:2]...), Options{})
	require.NoError(t, err)
	require.Nil(t, th)
}

func TestChase_RecordProjectionNeedsItsEquation(t *testing.T) {
	w := newRecordWorld()
	w.laws.Rewrites.ModuleCarrier = nil
	w.install(t)
	M, N, f, x := w.set("M"), w.set("N"), w.fn("f"), w.elem("x")
	goal := core.MakeProp(w.in(w.ap(f, x), N), w.homRecord(f, w.packed(M), w.packed(N)), w.in(x, M))
	fails(t, goal, 0)
}

func TestChase_RecordConflictingCarrierIsRefused(t *testing.T) {
	w := newRecordWorld()
	w.install(t)
	M, x := w.set("M"), w.elem("x")
	otherAdd := core.Var("other_add", w.add.Type())
	packed := w.ap(w.mkModule, otherAdd, w.zero, w.neg, w.smul, M)
	goal := core.MakeProp(w.in(x, M), w.module(M), w.ap(w.moduleOn, w.ring, packed), w.in(x, M))
	th, _, err := Close(goal, Options{})
	require.Nil(t, th)
	require.ErrorContains(t, err, "conflicting module operations")
}

func TestChase_RecordScalarMembershipUsesItsCarrier(t *testing.T) {
	w := newRecordWorld()
	w.install(t)
	M, N := w.record("M"), w.record("N")
	R2 := core.Var("R2", w.R.Type())
	c, x := core.Var("c", w.S), w.elem("x")
	goal := core.MakeProp(w.in(w.ap(w.smulField, M, c, x), w.carrier(M)),
		w.ap(w.moduleOn, w.ring, M), w.ap(w.moduleOn, w.ap(w.mkRing, R2), N), w.in(c, R2), w.in(x, w.carrier(M)))
	fails(t, goal, 0)
}

func TestChase_RecordComplexDefinitionAtEachDegree(t *testing.T) {
	w := newRecordWorld()
	P, d, n, x := w.family("P"), w.mapFamily("d"), numVar("n"), w.elem("x")
	at := opaqueRecordConst("complex_module", []core.HolType{P.Type(), dslNum()}, w.moduleType)
	w.laws.Rewrites.ComplexModule = thm(all([]core.Term{P, n}, eq(w.ap(at, P, n), w.packed(w.ap(P, n)))))
	w.install(t)
	s := func(k core.Term) core.Term { return w.ap(nxtOf(), k) }
	facts := []core.Term{
		allDegrees(func(k core.Term) core.Term { return w.homRecord(w.ap(d, s(k)), w.ap(at, P, s(k)), w.ap(at, P, k)) }),
		allDegrees(func(k core.Term) core.Term {
			u := w.elem("u")
			return all([]core.Term{u}, imp(w.in(u, w.ap(P, s(s(k)))), eq(w.ap(w.ap(d, s(k)), w.ap(w.ap(d, s(s(k))), u)), w.zero)))
		}),
		w.in(x, w.imageOf(w.ap(d, s(s(n))), w.ap(P, s(s(n))))),
	}
	// The conclusion keeps a projected zero; the certificate returns to this
	// spelling after the proof has used the packed module's actual zero.
	closes(t, core.MakeProp(eq(w.ap(w.ap(d, s(n)), x), w.ap(w.zeroField, w.ap(at, P, n))), facts...), 0)
}

func TestChase_RecordRewriteInstantiatesTypes(t *testing.T) {
	w := newRecordWorld()
	w.install(t)
	targetType := core.MakeFun(w.T, core.TypeBool())
	mapping := []core.TypeSubst{{VarType: w.T.(core.VarType), HolType: targetType}}
	ctor := w.mkModule.TypeSubstitute(mapping...)
	proj := w.carrierField.TypeSubstitute(mapping...)
	add := core.Var("add_sets", core.MakeFun(targetType, core.MakeFun(targetType, targetType)))
	zero := core.Var("zero_set", targetType)
	neg := core.Var("neg_sets", core.MakeFun(targetType, targetType))
	smul := core.Var("smul_sets", core.MakeFun(w.S, core.MakeFun(targetType, targetType)))
	carrier := core.Var("set_carrier", core.MakeFun(targetType, core.TypeBool()))
	term := w.ap(proj, w.ap(ctor, add, zero, neg, smul, carrier))
	eq := w.laws.reading(nil).leaf(term)
	require.NotNil(t, eq)
	require.True(t, prop.Rhs(eq).AlphaEquals(carrier))
	require.Empty(t, eq.Hyps())
}

func TestChase_RecordHomBetweenDifferentElementTypes(t *testing.T) {
	w := newRecordWorld()
	w.install(t)
	V := core.MakeVarType("OtherVector")
	M := w.record("M")
	N := core.Var("N", core.MakeFun(core.MakeFun(V, core.TypeBool()), V))
	f := core.Var("f", core.MakeFun(w.T, V))
	x, y := w.elem("x"), w.elem("y")
	hyps := []core.Term{w.homRecord(f, M, N), w.in(x, w.carrier(M)), w.in(y, w.carrier(M))}
	closes(t, core.MakeProp(eq(w.ap(f, w.sum(M, x, w.ap(w.negField, M, y))), w.sum(N, w.ap(f, x), recordApply(w.negField, N, w.ap(f, y)))), hyps...), 0)
	closes(t, core.MakeProp(eq(w.ap(f, w.ap(w.zeroField, M)), recordApply(w.zeroField, N)), hyps...), 0)
}

// A class is a set-valued vector. The named cohomology carrier and the
// nested quotient/restriction record must reduce to the same carrier before
// an outgoing homomorphism can carry a difference of classes into its target.
func TestChase_RecordCohomologyCarrierAndNestedModule(t *testing.T) {
	w := newRecordWorld()
	Q, n := w.family("Q"), numVar("n")
	classType := w.setT
	classModule := core.MakeFun(core.MakeFun(classType, core.TypeBool()), classType)
	classCarrier := core.MakeFun(classType, core.TypeBool())
	indexed := []core.HolType{Q.Type(), dslNum()}
	at := opaqueRecordConst("complex_module", indexed, w.moduleType)
	cycles := opaqueRecordConst("cocycles", indexed, w.setT)
	boundaries := opaqueRecordConst("coboundaries", indexed, w.setT)
	cohomology := opaqueRecordConst("cohomology", indexed, classCarrier)
	cohomologyModule := opaqueRecordConst("cohomology_module", indexed, classModule)
	restrict := opaqueRecordConst("restrict_module", []core.HolType{w.moduleType, w.setT}, w.moduleType)
	quotient := opaqueRecordConst("quotient_module", []core.HolType{w.moduleType, w.setT}, classModule)
	cosets := opaqueRecordConst("left_cosets", []core.HolType{w.add.Type(), w.setT, w.setT}, classCarrier)
	setAdd := opaqueRecordConst("set_mul", []core.HolType{w.add.Type()}, core.MakeFun(classType, core.MakeFun(classType, classType)))
	setNeg := opaqueRecordConst("set_inv", []core.HolType{w.neg.Type()}, core.MakeFun(classType, classType))
	quotientSmul := opaqueRecordConst("quotient_smul", []core.HolType{w.add.Type(), w.smul.Type(), w.setT}, core.MakeFun(w.S, core.MakeFun(classType, classType)))
	M, K := w.record("M"), w.set("K")
	add, zero, neg, smul := w.ap(w.addField, M), w.ap(w.zeroField, M), w.ap(w.negField, M), w.ap(w.smulField, M)
	Z, B := w.ap(cycles, Q, n), w.ap(boundaries, Q, n)
	rewrites := &w.laws.Rewrites
	rewrites.ComplexModule = thm(all([]core.Term{Q, n}, eq(w.ap(at, Q, n), w.packed(w.ap(Q, n)))))
	rewrites.RestrictModule = thm(all([]core.Term{M, K}, eq(w.ap(restrict, M, K), w.ap(w.mkModule, add, zero, neg, smul, K))))
	rewrites.QuotientModule = thm(all([]core.Term{M, K}, eq(w.ap(quotient, M, K),
		recordApply(w.mkModule, w.ap(setAdd, add), K, w.ap(setNeg, neg), w.ap(quotientSmul, add, smul, K), w.ap(cosets, add, w.carrier(M), K)))))
	rewrites.CohomologyModule = thm(all([]core.Term{Q, n}, eq(w.ap(cohomologyModule, Q, n), w.ap(quotient, w.ap(restrict, w.ap(at, Q, n), Z), B))))
	rewrites.CohomologyCarrier = thm(all([]core.Term{Q, n}, eq(w.ap(cohomology, Q, n), w.ap(cosets, w.add, Z, B))))
	source := w.ap(cohomologyModule, Q, n)
	target := core.Var("N", classModule)
	f := core.Var("f", core.MakeFun(classType, classType))
	x, y := core.Var("x", classType), core.Var("y", classType)
	difference := w.sum(source, x, recordApply(w.negField, source, y))
	goal := core.MakeProp(w.in(w.ap(f, difference), w.carrier(target)),
		w.homRecord(f, source, target), w.in(x, w.ap(cohomology, Q, n)), w.in(y, w.ap(cohomology, Q, n)))
	complete := w.laws.Rewrites
	for _, row := range []struct {
		name                          string
		missingModule, missingCarrier bool
	}{
		{name: "both definitions"},
		{name: "module equation absent", missingModule: true},
		{name: "carrier equation absent", missingCarrier: true},
	} {
		t.Run(row.name, func(t *testing.T) {
			w.laws.Rewrites = complete
			if row.missingModule {
				w.laws.Rewrites.CohomologyModule = nil
			}
			if row.missingCarrier {
				w.laws.Rewrites.CohomologyCarrier = nil
			}
			w.install(t)
			if row.missingModule || row.missingCarrier {
				fails(t, goal, 0)
			} else {
				closes(t, goal, 0)
			}
		})
	}
}

// A definition reduction retains the goal's projected identity spelling
// while its sub-chases compute that projection in their own reading.
func TestChase_RecordExactnessGoalPreservesProjection(t *testing.T) {
	w := newRecordWorld()
	w.install(t)
	A, B, C := w.set("A"), w.set("B"), w.set("C")
	g, f := w.fn("g"), w.fn("f")
	projectedZero := w.ap(w.zeroField, w.packed(C))
	goal := w.ap(w.exactAt, projectedZero, A, B, g, f)
	closes(t, core.MakeProp(goal, w.module(A), w.module(B), w.module(C), w.homOf(g, A, B), w.homOf(f, B, C), w.exact(A, B, g, f)), 1)
}
