package proof

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// reading_section_test.go — a proved LOCAL section stated over the
// structure binder is read at an instance as an entry's law is:
// `Read(section, instance)`. Measured: a `ctx.Lemma("∀L:field_on(A).
// …")` could not be read at the bundle fact, so citing it at a second
// instance spelled every component, and algebraic_curve's chart
// sandwich became a member for that alone.

// sectionLaw proves, as a local section of e.ctx, the identity law of
// the reading fixture at the letter A — `∀op e. mon(op, e) ⇒ ∀x. op(e,
// x) = x` — by reading the served law under the section's own
// structure hypothesis.
func (e *readingTestEnv) sectionLaw(t *testing.T) *GoalStackNode {
	t.Helper()
	sec := e.ctx.Section(e.law)
	sec.Do(Derive(func(arg *Argument) {
		arg.Fix()
		arg.Fix()
		structure := arg.Assume()
		arg.Show("the served law read under the section's structure hypothesis", By(Read(depName("zz_read_law"), structure)))
	}))
	require.True(t, sec.Proved(), "the local section is proved")
	return sec
}

// At an instance entry: the reading is the section's law at the
// instance's components with the hypothesis gone, as an entry's is.
func TestRead_SectionLawAtAnInstanceEntry(t *testing.T) {
	e := makeReadingTestEnv()
	law := e.sectionLaw(t)
	reading := Read(law, depName("zz_read_inst"))

	x := Var("x", TypeInd)
	want := ext.ForAll(x)(e.plus.Apply(e.zero, x).Eq(x)).Core()
	got := resolveLemmaTarget("test", e.ctx, reading)
	require.True(t, got.Conclusion().AlphaEquals(want), "reading reads %s", prop.PrintProp(got))
	require.Zero(t, got.NumHyps())

	sec := e.ctx.Section(prop.MakeProp(e.Q.Apply(e.plus.Apply(e.zero, e.a)).Core()))
	sec.Do(Simp(Fwd(reading)))
	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(e.Q.Apply(e.a).Core()),
		"plus(zero, a) ↦ a under Q; got %s", ext.PrintTerm(leaves[0].Goal.Conclusion()))
}

// At a resident structure fact — the bundle fact a chapter's closure
// receives: the reading is the section's law under that fact, and a By
// closes on it, bare and grounded.
func TestRead_SectionLawAtAResidentFact(t *testing.T) {
	e := makeReadingTestEnv()
	law := e.sectionLaw(t)
	for _, grounded := range []bool{false, true} {
		sec := e.residentReadingGoal(e.plus.Apply(e.zero, e.a).Eq(e.a))
		sec.Do(Derive(func(arg *Argument) {
			structure := arg.Assume()
			reading := Read(law, structure)
			if grounded {
				reading = reading.At(e.a)
			}
			arg.Show("the local section read at the resident structure fact", By(reading))
		}))
		require.True(t, sec.Proved(), "grounded=%v", grounded)
	}
}

// A section law with a type letter no component fixes is cited, as an
// entry's is, as the law beside the hypothesis (expandLooseReadings) —
// here the section itself, its tuple prefixed with the components.
func TestRead_SectionLawWithALooseLetter(t *testing.T) {
	e := makeReadingTestEnv()
	typeB := core.MakeVarType("B")
	opA := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	monA := MakeFun(opA, MakeFun(core.TypeA(), TypeBool))
	op := Var("op", opA)
	unit := Var("e", core.TypeA())
	f := Var("f", MakeFun(typeB, core.TypeA()))
	y := Var("y", typeB)
	fy := ext.WrapTerm(f).Apply(y)
	statement := ext.ForAll(op, unit)(e.ctx.Const("readMon", monA).Apply(op, unit).Imply(
		ext.ForAll(f, y)(ext.WrapTerm(op).Apply(unit, fy).Eq(fy))))
	law := e.ctx.Section(prop.MakeProp(statement.Core()))
	law.Do(Derive(func(arg *Argument) {
		arg.Fix()
		arg.Fix()
		structure := arg.Assume()
		arg.Show("the identity law at an applied point", By(Read(depName("zz_read_law"), structure)))
	}))
	require.True(t, law.Proved(), "the loose local section is proved")

	g := ext.WrapTerm(Var("g", MakeFun(TypeBool, TypeInd)))
	c := ext.WrapTerm(Var("c", TypeBool))
	body := e.plus.Apply(e.zero, g.Apply(c)).Eq(g.Apply(c))
	for _, grounded := range []bool{false, true} {
		sec := e.residentReadingGoal(body)
		sec.Do(Derive(func(arg *Argument) {
			structure := arg.Assume()
			reading := Read(law, structure)
			if grounded {
				reading = reading.At(g, c)
			}
			arg.Show("the local section read under the instance, at the index type bool", By(reading))
		}))
		require.True(t, sec.Proved(), "grounded=%v", grounded)
	}
}

// What a section law is not: an open section, and a value that is
// neither an entry nor a section.
func TestRead_SectionLawRefusals(t *testing.T) {
	e := makeReadingTestEnv()
	open := e.ctx.Section(e.law)
	sec := e.ctx.Section(prop.MakeProp(e.Q.Apply(e.plus.Apply(e.zero, e.a)).Core()))
	requirePanicContains(t, "the section is not proved", func() { sec.Do(Simp(Fwd(Read(open, depName("zz_read_inst"))))) })
	requirePanicContains(t, "the law is a registry entry or a proved local section", func() { Read(e.law, depName("zz_read_inst")) })
}

// A section of a member built in the define-then-run corpus holds a
// PROMISE, not a certificate: its derivation went lazy at the first
// unforced dependency (core.deriveProp — replay serves every dep and
// every bundle field as one, forced only after the Build returns).
// Reading such a section at an instance derives the reading as a
// promise of its own, settled with the consumer's; nothing forces the
// section at the read. Measured: `Read(agreement, c).At(n, F,
// multiple)` at a section whose proof had recorded refute keys
// panicked at replay — "Should not happen." in ThmPromise.AsThmCert —
// where the untyped `At(agreement, ring, n, F, multiple)` of the same
// section carried the promise through.
func TestRead_SectionLawOnADeferredCertificate(t *testing.T) {
	e := makeReadingTestEnv()
	law := e.sectionLaw(t)
	cert := law.PromisedThm()
	built := 0
	deferSection := func() {
		built = 0
		law.provedThm = core.Promise(cert, func(f core.Forcer) core.ThmCert { built++; return f.Force(cert) })
	}

	// At an instance entry: the closed reading is a promise over the section's.
	deferSection()
	closed := resolveLemmaTarget("test", e.ctx, Read(law, depName("zz_read_inst")))
	require.True(t, core.IsPromised(closed), "the reading of a promised section is a promise; got %T", closed)
	require.Zero(t, built, "resolving the reading must not force the section")

	// At a resident structure fact, bare and grounded: the consumer
	// closes on it, and the section is built once, at the consumer's force.
	for _, grounded := range []bool{false, true} {
		deferSection()
		sec := e.residentReadingGoal(e.plus.Apply(e.zero, e.a).Eq(e.a))
		sec.Do(Derive(func(arg *Argument) {
			structure := arg.Assume()
			reading := Read(law, structure)
			if grounded {
				reading = reading.At(e.a)
			}
			arg.Show("the promised section read at the resident structure fact", By(reading))
		}))
		require.True(t, sec.Proved(), "grounded=%v", grounded)
		require.Zero(t, built, "closing on the reading must not force the section (grounded=%v)", grounded)
		core.Force(t.Context(), sec.PromisedThm())
		require.Equal(t, 1, built, "the section's builder ran once, at the consumer's force (grounded=%v)", grounded)
	}
}
