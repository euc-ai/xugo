package core_test

// The kernel's objects, probed from outside: this is an external test
// package, so it holds exactly what any importing package holds.
//
// A kernel object is a handle passed by value over a node only core can
// reach, the kernel keeps lists of its own, and it reads a Term it is
// handed through the unexported kernel() method. Each test makes one
// move an importing package can make against that and checks what the
// kernel holds afterwards. The moves that no longer compile — assigning
// through a pointer to a kernel object, assigning an exported variable —
// are held by TestExportSurface.

import (
	"context"
	"reflect"
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/require"
)

// keepsItself embeds a term, keeps itself behind Core() and answers yes
// to every AlphaEquals.
type keepsItself struct{ core.Term }

func (k keepsItself) Core() core.Term            { return k }
func (k keepsItself) AlphaEquals(core.Term) bool { return true }
func (k keepsItself) Equals(core.Term) bool      { return true }

// claimsBool embeds a term of another type and reports bool.
type claimsBool struct{ core.Term }

func (c claimsBool) Core() core.Term    { return c }
func (c claimsBool) Type() core.HolType { return core.TypeBool() }

// claimsEqual embeds a type and answers yes to every Equals.
type claimsEqual struct{ core.HolType }

func (c claimsEqual) Equals(core.HolType) bool { return true }

func TestATermEmbedderIsReadAsTheTermItEmbeds(t *testing.T) {
	x, y := core.Var("x", core.TypeBool()), core.Var("y", core.TypeBool())
	wrapped := keepsItself{x}

	// What a constructor keeps is the embedded term.
	refl := core.Refl(wrapped)
	require.True(t, refl.AlphaEquals(core.Refl(x)))
	l, r, ok := core.MatchesEQ(refl.Conclusion())
	require.True(t, ok)
	require.True(t, any(l) == any(x) && any(r) == any(x), "a certificate holds the wrapper")

	// So a rule's side condition is checked on it: ⊢ x = x and ⊢ y = y
	// do not meet, whatever the wrapper answers.
	require.Panics(t, func() { core.EqMP(refl, core.Refl(y)) })
	require.Panics(t, func() { core.EqTrans(refl, core.Refl(y)) })

	// Every door that takes a term.
	fn := core.Var("f", core.MakeFun(core.TypeBool(), core.TypeBool()))
	kept := map[string]core.Term{
		"Apply":    core.Apply(fn, wrapped).Arg(),
		"Abs":      core.Abs(y, wrapped).Body(),
		"Assume":   core.Assume(wrapped).Conclusion(),
		"NewAxiom": core.NewAxiom(core.Eq(wrapped, wrapped)).Conclusion().(core.AppliedTerm).Arg(),
		"MakeProp": core.MakeProp(wrapped, wrapped).Hyp(0),
		"Subst":    core.MakeTermSubst(y, wrapped).Term,
	}
	for door, got := range kept {
		require.True(t, any(got) == any(x), "%s kept the wrapper", door)
	}

	// A wrapper's account of its type is not the type a door checks.
	n := core.Var("n", core.MakeFun(core.TypeBool(), core.TypeBool()))
	require.Panics(t, func() { core.Assume(claimsBool{n}) })
	require.Panics(t, func() { core.NewAxiom(claimsBool{n}) })
	require.Panics(t, func() { core.MakeProp(claimsBool{n}) })
}

func TestATypeEmbedderIsReadAsTheTypeItEmbeds(t *testing.T) {
	A := core.TypeA()
	lying := claimsEqual{A}

	v := core.Var("v", lying)
	require.True(t, any(v.Type()) == any(A), "a variable holds the wrapper")
	fun := core.MakeFun(lying, core.TypeBool())
	require.True(t, any(fun.SubType(0)) == any(A), "a function type holds the wrapper")
	composite := core.MakeCompositeType(core.MetaTypeFun(), lying, lying)
	require.True(t, any(composite.SubType(1)) == any(A), "a composite type holds the wrapper")

	// An application is typed by the embedded types: f : A → bool does not
	// take a bool, whatever the wrapper says of itself.
	f := core.Var("f", fun)
	require.Panics(t, func() { core.Apply(f, core.Var("b", core.TypeBool())) })

	// A substitution hands over the embedded type.
	subst := core.TypeSubst{VarType: A, HolType: claimsEqual{core.TypeBool()}}
	got := core.Var("w", A).TypeSubstitute(subst)
	require.True(t, any(got.Type()) == any(core.TypeBool()))
}

func TestTheKernelKeepsListsOfItsOwn(t *testing.T) {
	boolType := core.TypeBool()
	fn := core.MakeFun(boolType, boolType)
	v, g := core.Var("v", fn), core.Var("g", fn)

	// A composite type's arguments.
	args := []core.HolType{boolType, boolType}
	sameAsFn := core.MakeCompositeType(core.MetaTypeFun(), args...)
	w := core.Var("v", sameAsFn)                                   // v again, its type over args
	step := core.EqTrans(core.Refl(v), core.Assume(core.Eq(w, g))) // w = g ⊢ v = g
	args[0] = core.TypeA()
	require.True(t, sameAsFn.Equals(fn), "the caller's slice is the type's")
	require.True(t, w.Equals(v))
	// v is still free in the hypothesis, so it is not abstracted.
	require.Panics(t, func() { core.PropAbs(v, step) })

	// A proposition's hypotheses: kept sorted in a list of its own, the
	// caller's slice left as it was.
	a, b := core.Var("a", boolType), core.Var("b", boolType)
	hyps := []core.Term{b, a}
	p := core.MakeProp(a, hyps...)
	require.True(t, any(hyps[0]) == any(b) && any(hyps[1]) == any(a), "MakeProp reordered the caller's slice")
	hyps[0], hyps[1] = g, g
	require.True(t, p.HasHyp(a) && p.HasHyp(b) && p.NumHyps() == 2)

	// What is handed out is a copy.
	out := p.Hyps()
	out[0] = g
	require.True(t, p.HasHyp(a) && p.HasHyp(b))

	x := core.Var("x", core.TypeA())
	identity := core.NewConstDef(core.Abs(x, x), "zz_object_model_identity") // of type A → A
	atBool := core.MakeConstTerm(identity.Meta(), fn)
	substs := atBool.TypeSubsts()
	require.Len(t, substs, 1)
	substs[0] = core.MakeTypeSubst(core.TypeA(), fn)
	require.True(t, atBool.DefThm().AlphaEquals(
		core.PropTypeInst(identity.DefThm(), core.MakeTypeSubst(core.TypeA(), boolType))))
}

func TestASubstitutionIsCheckedWhereItIsRead(t *testing.T) {
	boolType := core.TypeBool()
	x := core.Var("x", boolType)
	wrongType := core.Var("n", core.MakeFun(boolType, boolType))
	literal := core.TermSubst{VarTerm: x, Term: wrongType}

	require.Panics(t, func() { x.Substitute(literal) })
	require.Panics(t, func() { core.Abs(core.Var("y", boolType), x).Substitute(literal) })
	require.Panics(t, func() { core.PropTermInst(core.Assume(x), literal) })

	// A wrapper as the replacement is read as the term it embeds.
	y := core.Var("y", boolType)
	got := x.Substitute(core.TermSubst{VarTerm: x, Term: keepsItself{y}})
	require.True(t, any(got) == any(y))
}

func TestAHandleIsACopy(t *testing.T) {
	boolType := core.TypeBool()
	x, y := core.Var("x", boolType), core.Var("y", boolType)

	// Overwriting a holder's copy of a certificate, of its statement or of
	// one of its terms leaves the certificate.
	cert := core.Refl(x)
	mine := cert
	mine = core.Refl(y)
	require.True(t, mine.AlphaEquals(core.Refl(y)))
	statement := cert.AsProp()
	statement = core.MakeProp(y)
	require.False(t, statement.Proved())
	node := cert.Conclusion().(core.AppliedTerm)
	node = core.Eq(x, y)
	require.False(t, node.IsZero())
	require.True(t, cert.AlphaEquals(core.Refl(x)))

	// A derived promise forces the dependency it was derived over, whatever
	// a holder does with its own copy of that dependency's handle.
	lie := core.Promise(core.MakeProp(core.Eq(x, y)), func(core.Forcer) core.ThmCert { panic("unprovable") })
	derived := core.EqSym(lie)
	lie = core.Promise(core.MakeProp(core.Eq(x, x)), func(core.Forcer) core.ThmCert { return core.Refl(x) })
	require.True(t, core.Force(context.Background(), lie).Proved())
	require.Panics(t, func() { core.Force(context.Background(), core.AsThm(derived)) })
}

// reflect reaches a node through a handle's one field, which is
// unexported, so every value it reaches there is read-only to Set. (What
// can still write one is reflect.NewAt over Value.UnsafePointer, which
// the audit greps for, and Value.Clear, which the next test holds.)
func TestReflectCannotSetANodeThroughItsHandle(t *testing.T) {
	x := core.Var("x", core.TypeBool())
	for name, handle := range map[string]any{
		"a certificate": core.Refl(x),
		"a term":        core.Eq(x, x),
		"a type":        core.TypeBool(),
	} {
		held := reflect.New(reflect.TypeOf(handle)).Elem() // the holder's own, addressable copy
		held.Set(reflect.ValueOf(handle))
		node := held.Field(0).Elem()
		require.False(t, held.Field(0).CanSet(), "%s: the handle's field is settable", name)
		require.False(t, node.CanSet(), "%s: the node is settable", name)
		for i := range node.NumField() {
			require.False(t, node.Field(i).CanSet(), "%s: field %d of the node is settable", name, i)
		}
		require.Panics(t, func() { node.Set(reflect.Zero(node.Type())) }, "%s: the node was set", name)
	}
}

// reachedLists is every slice and map reflect reaches from a kernel
// value by the types of its fields, each as "node.field": what
// Value.Clear can be called on. A pointer, a struct and an array are
// followed. An interface is not: a kernel interface holds one of the
// handles kernelValues lists, and the others here hold a context and
// what a builder panicked with. Nor is a function, a channel or an
// unsafe pointer, through which reflect reads nothing typed.
func reachedLists() []string {
	found := map[string]struct{}{}
	seen := map[reflect.Type]bool{}
	var walk func(t reflect.Type, at string)
	walk = func(t reflect.Type, at string) {
		switch t.Kind() {
		case reflect.Pointer, reflect.Array:
			walk(t.Elem(), at)
		case reflect.Struct:
			if seen[t] {
				return
			}
			seen[t] = true
			for i := range t.NumField() {
				walk(t.Field(i).Type, t.Name()+"."+t.Field(i).Name)
			}
		case reflect.Slice:
			found[at] = struct{}{}
			walk(t.Elem(), at+"[]")
		case reflect.Map:
			found[at] = struct{}{}
			walk(t.Key(), at+"[key]")
			walk(t.Elem(), at+"[value]")
		}
	}
	for _, v := range kernelValues() {
		walk(reflect.TypeOf(v), "")
	}
	lists := make([]string, 0, len(found))
	for at := range found {
		lists = append(lists, at)
	}
	slices.Sort(lists)
	return lists
}

// Value.Clear is the one write reflect makes through a read-only value:
// it zeroes the elements of a slice, or empties a map, without asking
// whether the value may be set. The lists a kernel value reaches are the
// six below, all slices, and the zero of each element type is no kernel
// value. So a cleared list keeps its length — no hypothesis, assumption
// or dependency is dropped — and holds nothing the kernel reads past:
// the node proves nothing it did not, and what next reads it panics.
func TestReflectClearLeavesAListTheKernelPanicsOn(t *testing.T) {
	require.Equal(t, []string{
		"_Assumptions.members",
		"_CompositeTypeNode.subTypes",
		"_ConstTermNode.typeSubsts",
		"_ForceBoundary.hit",
		"_PromiseCell.deps",
		"_Statement.hyps",
	}, reachedLists(), "the lists Value.Clear reaches from a kernel value: each is cleared below")

	zero := func(list reflect.Value) {
		t.Helper()
		require.True(t, list.IsValid() && list.Kind() == reflect.Slice && list.Len() > 0, "no list to clear")
		require.False(t, list.CanSet(), "the list is settable")
		length := list.Len()
		list.Clear()
		require.Equal(t, length, list.Len(), "clearing shortened the list")
	}
	ctx := context.Background()
	boolType := core.TypeBool()
	x, other := core.Var("x", boolType), core.Var("zz_reflect_clear_other", boolType)

	// A statement's hypotheses: the certificate still has one, and no
	// rule reads past it.
	hypothesis := core.Var("zz_reflect_clear_hypothesis", boolType)
	assumed := core.Assume(hypothesis)
	zero(reflect.ValueOf(assumed).FieldByName("hyps"))
	require.Equal(t, 1, assumed.NumHyps(), "a hypothesis was dropped")
	require.Panics(t, func() { core.PropTermInst(assumed, core.MakeTermSubst(hypothesis, other)) })
	require.Panics(t, func() { core.Deduct(assumed, assumed) })

	// A composite type's arguments.
	made := core.MakeCompositeType(core.MakeMetaType("zz_reflect_clear_type", 1), boolType)
	zero(reflect.ValueOf(made).FieldByName("subTypes"))
	require.Panics(t, func() {
		made.Equals(core.MakeCompositeType(core.MakeMetaType("zz_reflect_clear_type", 1), boolType))
	})
	require.Panics(t, func() { made.Key() })

	// A constant's type instantiation: its definition is not handed out
	// at another type, nor at none.
	a := core.Var("x", core.TypeA())
	identity := core.NewConstDef(core.Abs(a, a), "zz_reflect_clear_identity")
	atBool := core.MakeConstTerm(identity.Meta(), core.MakeFun(boolType, boolType))
	zero(reflect.ValueOf(atBool).FieldByName("typeSubsts"))
	require.Panics(t, func() { atBool.DefThm() })

	// A derived promise's dependencies: it is not settled without them,
	// before its dependency is proved or after.
	root := core.Promise(core.MakeProp(core.Eq(x, x)), func(core.Forcer) core.ThmCert { return core.Refl(x) })
	derived := core.AsThm(core.EqSym(root))
	zero(reflect.ValueOf(derived).FieldByName("deps"))
	require.Panics(t, func() { core.Force(ctx, derived) })
	require.True(t, core.Force(ctx, root).Proved())
	require.Panics(t, func() { core.Force(ctx, derived) })

	// A certificate's assumptions: it does not come to assume nothing,
	// and neither does a certificate a rule derives from it.
	fabricated := core.TestThm(core.Var("zz_reflect_clear_fabricated", boolType))
	zero(reflect.ValueOf(fabricated).FieldByName("assumes").Elem().FieldByName("members"))
	require.Panics(t, func() { fabricated.Assumes() })
	instance := core.PropTermInst(fabricated, core.MakeTermSubst(x, other)).AsThmCert()
	require.Panics(t, func() { instance.Assumes() })

	// A bounded force's record of what it settled from trust, reached
	// from the Forcer a builder is handed: the record no longer reads,
	// and the certificate still says what it stands on.
	l, r := core.Var("zz_reflect_clear_l", boolType), core.Var("zz_reflect_clear_r", boolType)
	trusted := core.Promise(core.MakeProp(core.Eq(l, r)), func(core.Forcer) core.ThmCert { panic("never built") })
	standing := core.Promise(core.MakeProp(core.Eq(r, l)), func(f core.Forcer) core.ThmCert {
		cert := core.EqSym(f.Force(trusted)).AsThmCert()
		zero(reflect.ValueOf(f).FieldByName("boundary").Elem().FieldByName("hit"))
		return cert
	})
	cert, settled := core.ForceWithBoundary(ctx, standing, func(p core.Prop) bool { return p.AlphaEquals(trusted) })
	require.Len(t, settled, 1)
	require.Panics(t, func() { settled[0].Conclusion() })
	stands := cert.Assumes()
	require.Len(t, stands, 1)
	require.Equal(t, core.BoundaryDoor, stands[0].Door)
	require.True(t, stands[0].Statement.AlphaEquals(trusted))
}

// kernelValues is one value of every kind of kernel object an importing
// package comes to hold, under the name a failure reports it by.
func kernelValues() map[string]any {
	boolType := core.TypeBool()
	x := core.Var("x", boolType)
	return map[string]any{
		"a proposition":     core.MakeProp(x),
		"a certificate":     core.Refl(x),
		"a promise":         core.Promise(core.MakeProp(x), func(core.Forcer) core.ThmCert { panic("never built") }),
		"a forcer":          core.NewForcer(context.Background()),
		"a variable":        x,
		"a constant":        core.MakeConstTerm(core.MetaEq(), core.MakeFun(boolType, boolType, boolType)),
		"an application":    core.Eq(x, x),
		"an abstraction":    core.Abs(x, x),
		"a constant's meta": core.MetaEq(),
		"a type variable":   core.TypeA(),
		"a composite type":  boolType,
		"a meta type":       core.MetaTypeBool(),
	}
}

// converts reports whether reflect turns a value of type from into one
// of type to, by the conversion itself and not only by what
// ConvertibleTo says of it.
func converts(from, to reflect.Type) (converted bool) {
	defer func() {
		if recover() != nil {
			converted = false
		}
	}()
	return reflect.New(from).Elem().Convert(to).IsValid()
}

// Value.Convert makes every conversion Go allows, between types its
// caller cannot name as between those it can: one struct type to another
// of the same underlying type, and a pointer to the one to a pointer to
// the other. A handle is the one type over its node, so nothing an
// importer holds converts to a handle of another kind, and an unproved
// statement converts to no certificate.
func TestReflectCannotConvertAKernelValueToAnotherKind(t *testing.T) {
	values := kernelValues()
	kinds := map[reflect.Type]string{}
	for name, v := range values {
		kinds[reflect.TypeOf(v)] = name
	}
	require.Len(t, kinds, len(values), "two of the values are of one type")

	for from, fromName := range kinds {
		// reflect.New makes its caller a pointer to a handle, and from the
		// type of the handle's one field a pointer to a node, with no value
		// of either in hand.
		node := from.Field(0).Type
		for to, toName := range kinds {
			if from == to {
				continue
			}
			for _, route := range []struct {
				how      string
				from, to reflect.Type
			}{
				{"converts", from, to},
				{"converts, behind a pointer,", reflect.PointerTo(from), reflect.PointerTo(to)},
				{"has a node that converts", node, to},
				{"has a node that converts to the node of", node, to.Field(0).Type},
			} {
				require.False(t, route.from.ConvertibleTo(route.to), "%s %s to %s", fromName, route.how, toName)
				require.False(t, converts(route.from, route.to), "%s %s to %s", fromName, route.how, toName)
			}
		}
	}

	// Every unproved statement the kernel hands out, against the certificate.
	x := core.Var("x", core.TypeBool())
	promise := core.Promise(core.MakeProp(x), func(core.Forcer) core.ThmCert { panic("never built") })
	_, trusted := core.ForceWithBoundary(context.Background(), promise, func(core.Prop) bool { return true })
	require.Len(t, trusted, 1)
	certificate := reflect.TypeFor[core.ThmCert]()
	for name, unproved := range map[string]core.Prop{
		"a proposition":                 core.MakeProp(x),
		"a certificate's statement":     core.Refl(x).AsProp(),
		"a promise's statement":         promise.AsProp(),
		"an assumption's statement":     core.TestThm(x).Assumes()[0].Statement,
		"a bounded force's trusted one": trusted[0],
		"a rule's unproved result":      core.EqSym(core.MakeProp(core.Eq(x, x))),
	} {
		require.False(t, unproved.Proved(), "%s is proved", name)
		held := reflect.New(reflect.TypeOf(unproved)) // the holder's own, addressable copy
		held.Elem().Set(reflect.ValueOf(unproved))
		require.Panics(t, func() { held.Elem().Convert(certificate) }, "%s converted to a certificate", name)
		require.Panics(t, func() { held.Convert(reflect.PointerTo(certificate)) },
			"a pointer to %s converted to a pointer to a certificate", name)
	}

	// A struct type reflect builds of the certificate's one field is not
	// the certificate's underlying type: StructOf refuses an embedded
	// field of an unexported type, and a named field makes another type.
	field := certificate.Field(0)
	for _, anonymous := range []bool{true, false} {
		field.Anonymous = anonymous
		built := func() (made reflect.Type) {
			defer func() { _ = recover() }()
			return reflect.StructOf([]reflect.StructField{field})
		}()
		if built != nil {
			require.False(t, built.ConvertibleTo(certificate), "a struct reflect built converts to a certificate")
			require.False(t, converts(built, certificate), "a struct reflect built converts to a certificate")
		}
	}
}

// The zero value of every handle stands for nothing: it reports itself
// zero, and a door handed one panics.
func TestAZeroHandleStandsForNothing(t *testing.T) {
	x := core.Var("x", core.TypeBool())
	require.True(t, core.VarTerm{}.IsZero() && core.ConstTerm{}.IsZero() &&
		core.AppliedTerm{}.IsZero() && core.AbsTerm{}.IsZero() &&
		core.VarType{}.IsZero() && core.CompositeType{}.IsZero() && core.MetaType{}.IsZero() &&
		core.ConstTermMeta{}.IsZero() && core.ThmCert{}.IsZero() && core.ThmPromise{}.IsZero())
	require.False(t, x.IsZero())
	require.False(t, core.ThmPromise{}.Proved())

	doors := map[string]func(){
		"Abs":               func() { core.Abs(core.VarTerm{}, x) },
		"PropAbs":           func() { core.PropAbs(core.VarTerm{}, core.Refl(x)) },
		"Beta":              func() { core.Beta(core.AppliedTerm{}) },
		"Eta":               func() { core.Eta(core.AppliedTerm{}) },
		"Select":            func() { core.Select(core.AppliedTerm{}) },
		"Refl":              func() { core.Refl(core.VarTerm{}) },
		"Var":               func() { core.Var("v", core.CompositeType{}) },
		"MakeFun":           func() { core.MakeFun(core.VarType{}, core.TypeBool()) },
		"MakeCompositeType": func() { core.MakeCompositeType(core.MetaType{}) },
		"MakeConstTerm":     func() { core.MakeConstTerm(core.ConstTermMeta{}, core.TypeBool()) },
		"MakeTermSubst":     func() { core.MakeTermSubst(core.VarTerm{}, x) },
		"PropTermInst":      func() { core.PropTermInst(core.Refl(x), core.TermSubst{Term: x}) },
		"Promise":           func() { core.Promise(core.ThmCert{}, func(core.Forcer) core.ThmCert { return core.Refl(x) }) },
		"Force":             func() { core.Force(context.Background(), core.ThmPromise{}) },
		"a builder's zero certificate": func() {
			core.Force(context.Background(), core.Promise(core.MakeProp(x), func(core.Forcer) core.ThmCert { return core.ThmCert{} }))
		},
	}
	for name, door := range doors {
		require.Panics(t, door, "%s took a zero handle", name)
	}
}
