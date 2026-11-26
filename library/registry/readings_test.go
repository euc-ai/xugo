package registry

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

// readableThrough is the whole view's readables whose chain starts at
// root, in the view's order.
func readableThrough(root *ProofEntry) []Readable {
	var out []Readable
	for _, r := range Readables() {
		if r.Root() == root {
			out = append(out, r)
		}
	}
	return out
}

// A tower of three structures for the readings view: a pointed
// magma projects to a magma (its operation), a magma projects to a
// point (its own distinguished element, a derived component), and
// each level states one law besides. The projections and the laws are
// registered with stub builds — the view reads statements, never
// proofs — and the derived statements are checked letter for letter.
func TestReadingsView(t *testing.T) {
	fam := NewFamily("zz_readings_view", nil)
	stub := Bare(func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil })
	magma := fam.DefineStructure(DefEntry{
		Name: "Magma", Const: "zz_rv_magma", Type: "(A → A → A) → A → bool",
		Equations: []string{"∀op:(A → A → A). ∀e:A. zz_rv_magma(op, e) ⇔ (∀x y:A. op(x, y) = op(x, y))"},
	})
	pointed := fam.DefineStructure(DefEntry{
		Name: "PointedMagma", Const: "zz_rv_pointed", Type: "(A → A → A) → A → bool",
		Equations: []string{"∀op:(A → A → A). ∀e:A. zz_rv_pointed(op, e) ⇔ zz_rv_magma(op, e) ∧ op(e, e) = e"},
	})
	point := fam.DefineStructure(DefEntry{
		Name: "Point", Const: "zz_rv_point", Type: "A → bool",
		Equations: []string{"∀e:A. zz_rv_point(e) ⇔ e = e"},
	})
	law := func(name string, statement dsl.Statement) *ProofEntry {
		headline, err := statement.Text()
		require.NoError(t, err)
		return fam.Add(ProofEntry{Name: name, Build: BuildSpec{Fn: stub.Fn, Headline: headline}})
	}
	// The magma: one law, and a projection to the point at a DERIVED
	// component, the operation at the element.
	law("Idem", magma.Statement("∀x:A. op(x, x) = op(x, x)"))
	law("ToPoint", magma.Statement("zz_rv_point(op(e, e))"))
	// The pointed magma: the projection to its magma, and one law.
	underlying := law("Underlying", pointed.Statement("zz_rv_magma(op, e)"))
	fixed := law("Fixed", pointed.Statement("op(e, e) = e"))
	// The point: one law, and a projection BACK to a pointed magma — a
	// cycle the walk must not follow into a structure it has visited.
	law("Trivial", point.Statement("e = e"))
	back := law("Back", point.Statement("zz_rv_pointed((λx:A. λy:A. e), e)"))
	// A law of the magma stated at a fixed type: not readable through
	// a projection whose components are at a letter.
	atNum := law("AtNum", dsl.Statement{Binders: "∀op:(num → num → num). ∀e:num. ∀x:num.", Hypotheses: []string{"zz_rv_magma(op, e)"}, Conclusion: "op(x, x) = op(x, x)"})

	names := func(entries []*ProofEntry) []string {
		var out []string
		for _, e := range entries {
			out = append(out, e.Name)
		}
		return out
	}
	laws := func(root *ProofEntry) []string {
		var out []string
		for _, r := range readableThrough(root) {
			out = append(out, r.Law.Name)
		}
		return out
	}
	readable := func(root *ProofEntry) map[string]Readable {
		out := map[string]Readable{}
		for _, r := range readableThrough(root) {
			out[r.Law.Name] = r
		}
		return out
	}

	var projections []string
	for _, p := range Projections() {
		if p.Law.Family() == fam {
			projections = append(projections, p.Law.Name+": "+p.From+" -> "+p.To)
		}
	}
	require.Equal(t, []string{
		"zz_readings_view.ToPoint: zz_rv_magma -> zz_rv_point",
		"zz_readings_view.Underlying: zz_rv_pointed -> zz_rv_magma",
		"zz_readings_view.Back: zz_rv_point -> zz_rv_pointed",
	}, projections, "a projection is a law whose body states another structure; Idem, Fixed, Trivial and AtNum are none")
	_, isProjection := ProjectionOf(fixed)
	require.False(t, isProjection)
	require.Nil(t, readableThrough(fixed))

	// Through Underlying, breadth-first: the magma's laws at the pointed
	// magma's components, then the point's through ToPoint. Back states
	// a pointed magma, which the chain has visited, so the walk stops at
	// it; AtNum does not read at a letter.
	through := readable(underlying)
	require.Equal(t, []string{"zz_readings_view.Idem", "zz_readings_view.ToPoint", "zz_readings_view.Trivial", "zz_readings_view.Back"}, laws(underlying))
	require.Equal(t, []string{"zz_readings_view.Underlying"}, names(through["zz_readings_view.Idem"].Through))
	require.Equal(t, "⊢ ∀op.∀e.(zz_rv_pointed(op, e) ⇒ (∀x.(op(x, x) = op(x, x))))",
		prop.PrintProp(through["zz_readings_view.Idem"].Statement),
		"the derived statement is the law's body at the projection's components, closed over the root's")
	require.Equal(t, []string{"zz_readings_view.Underlying", "zz_readings_view.ToPoint"}, names(through["zz_readings_view.Trivial"].Through))
	require.Equal(t, 2, through["zz_readings_view.Trivial"].Depth())
	require.Same(t, underlying, through["zz_readings_view.Trivial"].Root())
	require.Equal(t, "⊢ ∀op.∀e.(zz_rv_pointed(op, e) ⇒ (op(e, e) = op(e, e)))",
		prop.PrintProp(through["zz_readings_view.Trivial"].Statement),
		"the point's law at the derived component")
	require.False(t, through["zz_readings_view.Idem"].StandsOnCard())

	// Through Back: the pointed magma's laws at the trivial operation,
	// then the magma's through Underlying; ToPoint states a point, which
	// the chain has visited, so the point's laws are not read again.
	viaBack := readable(back)
	require.Equal(t, []string{"zz_readings_view.Underlying", "zz_readings_view.Fixed", "zz_readings_view.Idem", "zz_readings_view.ToPoint"}, laws(back))
	require.Equal(t, "⊢ ∀e.(zz_rv_point(e) ⇒ (e = e))", prop.PrintProp(viaBack["zz_readings_view.Fixed"].Statement),
		"a derived component is substituted as the term it is, and the body handed over β-normal")
	require.Equal(t, []string{"zz_readings_view.Back", "zz_readings_view.Underlying"}, names(viaBack["zz_readings_view.Idem"].Through))

	// The unreadable law is reported with the reading's refusal, once
	// per chain that reached it.
	var refusals []string
	for _, s := range UnreadableLaws() {
		if strings.HasPrefix(s, atNum.Name+" ") {
			refusals = append(refusals, s)
		}
	}
	require.Len(t, refusals, 2, "AtNum is reached through Underlying and through Back → Underlying: %v", refusals)
	require.Contains(t, refusals[0], "does not fit the binder")
}

// A law whose type letter no component fixes is read with that letter
// kept apart from the instance's: the reading pins the components'
// letters and leaves the loose one a variable of the derived
// statement, renamed where the instance already carries it.
func TestReadingsLooseLetterStaysApart(t *testing.T) {
	fam := NewFamily("zz_readings_loose", nil)
	stub := Bare(func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil })
	tagged := fam.DefineStructure(DefEntry{
		Name: "Tagged", Const: "zz_rl_tagged", Type: "A → B → bool",
		Equations: []string{"∀a:A. ∀b:B. zz_rl_tagged(a, b) ⇔ a = a ∧ b = b"},
	})
	one := fam.DefineStructure(DefEntry{
		Name: "One", Const: "zz_rl_one", Type: "A → bool",
		Equations: []string{"∀a:A. zz_rl_one(a) ⇔ a = a"},
	})
	law := func(name string, statement dsl.Statement) *ProofEntry {
		headline, err := statement.Text()
		require.NoError(t, err)
		return fam.Add(ProofEntry{Name: name, Build: BuildSpec{Fn: stub.Fn, Headline: headline}})
	}
	first := law("First", tagged.Statement("zz_rl_one(a)"))
	// The law's B is loose: no component of zz_rl_one carries it, and
	// the instance — the tagged pair — carries a B of its own.
	law("Loose", one.Statement("∀f:(A → B). f(a) = f(a)"))
	through := readableThrough(first)
	require.Len(t, through, 1)
	require.Equal(t, "⊢ ∀a.∀b.(zz_rl_tagged(a, b) ⇒ (∀f.(f(a) = f(a))))", prop.PrintProp(through[0].Statement))
	f := ext.MatchesFORALL(ext.MatchesFORALL(through[0].Statement.Conclusion()).Body())
	_, body, _ := ext.MatchesIMPLY(f.Body())
	loose := ext.MatchesFORALL(body).Var()
	var letters []string
	for _, v := range loose.Type().TypeVars() {
		letters = append(letters, string(v.Name()))
	}
	require.Equal(t, []string{"A", "C"}, letters,
		"the law's loose B is renamed away from the instance's B; the instance's A is the law's A")
}

// A statement two chains derive is read once, through the shorter
// chain, and a different statement of the same size is still read: a
// root projects to a group, the group to a monoid, and the group's
// right unit law is the monoid's, while the monoid's left unit law is
// a law of its own.
func TestReadingsOneStatementOnce(t *testing.T) {
	fam := NewFamily("zz_readings_once", nil)
	stub := Bare(func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil })
	monoid := fam.DefineStructure(DefEntry{
		Name: "Monoid", Const: "zz_ro_monoid", Type: "(A → A → A) → A → bool",
		Equations: []string{"∀op:(A → A → A). ∀e:A. zz_ro_monoid(op, e) ⇔ (∀x:A. op(x, e) = x) ∧ (∀x:A. op(e, x) = x)"},
	})
	group := fam.DefineStructure(DefEntry{
		Name: "Group", Const: "zz_ro_group", Type: "(A → A → A) → A → bool",
		Equations: []string{"∀op:(A → A → A). ∀e:A. zz_ro_group(op, e) ⇔ zz_ro_monoid(op, e) ∧ (∀x:A. op(x, e) = x)"},
	})
	root := fam.DefineStructure(DefEntry{
		Name: "Root", Const: "zz_ro_root", Type: "(A → A → A) → A → bool",
		Equations: []string{"∀op:(A → A → A). ∀e:A. zz_ro_root(op, e) ⇔ zz_ro_group(op, e)"},
	})
	law := func(name string, statement dsl.Statement) *ProofEntry {
		headline, err := statement.Text()
		require.NoError(t, err)
		return fam.Add(ProofEntry{Name: name, Build: BuildSpec{Fn: stub.Fn, Headline: headline}})
	}
	toGroup := law("ToGroup", root.Statement("zz_ro_group(op, e)"))
	law("ToMonoid", group.Statement("zz_ro_monoid(op, e)"))
	law("RightUnit", group.Statement("∀x:A. op(x, e) = x"))
	law("MonoidRightUnit", monoid.Statement("∀x:A. op(x, e) = x"))
	law("MonoidLeftUnit", monoid.Statement("∀x:A. op(e, x) = x"))

	through := map[string]Readable{}
	var laws []string
	for _, r := range readableThrough(toGroup) {
		laws = append(laws, r.Law.Name)
		through[r.Law.Name] = r
	}
	require.Equal(t, []string{"zz_readings_once.ToMonoid", "zz_readings_once.RightUnit", "zz_readings_once.MonoidLeftUnit"}, laws,
		"the monoid's right unit law, read through ToMonoid, states what the group's states through ToGroup alone")
	require.Equal(t, 1, through["zz_readings_once.RightUnit"].Depth(), "the statement is kept at its shorter chain")
	right, left := through["zz_readings_once.RightUnit"].Statement, through["zz_readings_once.MonoidLeftUnit"].Statement
	require.Equal(t, right.Size(), left.Size(), "the two unit laws are of one size")
	require.Equal(t, "⊢ ∀op.∀e.(zz_ro_root(op, e) ⇒ (∀x.(op(e, x) = x)))", prop.PrintProp(left),
		"a statement of the same size and another shape is read")
}

// The view keeps its readables under the rigid head of their
// statement's conclusion, and ReadablesFor serves, at a target, the
// ones at the target's head and the wild ones, in the view's order:
// exactly the readables whose head may match the target, so a scan
// reading the candidates alone skips nothing the plan would read.
func TestReadablesForServesTheHeadsCandidates(t *testing.T) {
	fam := NewFamily("zz_readings_heads", nil)
	stub := Bare(func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil })
	inner := fam.DefineStructure(DefEntry{
		Name: "Inner", Const: "zz_rh_inner", Type: "(A → A → A) → A → bool",
		Equations: []string{"∀op:(A → A → A). ∀e:A. zz_rh_inner(op, e) ⇔ op(e, e) = e"},
	})
	outer := fam.DefineStructure(DefEntry{
		Name: "Outer", Const: "zz_rh_outer", Type: "(A → A → A) → A → bool",
		Equations: []string{"∀op:(A → A → A). ∀e:A. zz_rh_outer(op, e) ⇔ zz_rh_inner(op, e)"},
	})
	law := func(name string, statement dsl.Statement) *ProofEntry {
		headline, err := statement.Text()
		require.NoError(t, err)
		return fam.Add(ProofEntry{Name: name, Build: BuildSpec{Fn: stub.Fn, Headline: headline}})
	}
	toInner := law("ToInner", outer.Statement("zz_rh_inner(op, e)"))
	// Four laws of the inner structure: at an equation, at the
	// structure's own predicate, at both as a conjunction — which the
	// plan reads conjunct by conjunct, so the law is kept under both
	// heads — and at a variable, wild.
	law("Equation", inner.Statement("∀x:A. op(x, e) = x"))
	law("Again", inner.Statement("zz_rh_inner(op, op(e, e))"))
	law("Both", inner.Statement("∀x:A. op(x, e) = x ∧ zz_rh_inner(op, op(e, e))"))
	law("Wild", inner.Statement("∀P:(A → bool). P(e) ⇒ P(e)"))

	names := func(readables []Readable) []string {
		var out []string
		for _, r := range readables {
			if r.Law.Family() == fam {
				out = append(out, r.Law.Name)
			}
		}
		return out
	}
	require.Equal(t, []string{"zz_readings_heads.Equation", "zz_readings_heads.Again", "zz_readings_heads.Both", "zz_readings_heads.Wild"}, names(readableThrough(toInner)))
	var again core.Term
	for _, r := range readableThrough(toInner) {
		if r.Law.Name == "zz_readings_heads.Again" {
			// The derived statement `∀op e. zz_rh_outer(op, e) ⇒ zz_rh_inner(op, op(e, e))`, at its body.
			_, again, _ = ext.MatchesIMPLY(ext.MatchesFORALL(ext.MatchesFORALL(r.Statement.Conclusion()).Body()).Body())
		}
	}
	require.NotNil(t, again)

	x, y := ext.Var("x", core.TypeBool()), ext.Var("y", core.TypeBool())
	g := ext.Const(core.MakeConstMeta("zz_rh_g", core.MakeFun(core.TypeBool(), core.TypeBool())), core.MakeFun(core.TypeBool(), core.TypeBool()))
	P := ext.Var("P", core.MakeFun(core.TypeBool(), core.TypeBool()))
	_, args := ext.MatchesApply(ext.ForAll(x)(x.Eq(x)))
	lambda := args[0]
	require.Equal(t, []string{"zz_readings_heads.Equation", "zz_readings_heads.Both", "zz_readings_heads.Wild"}, names(ReadablesFor(x.Eq(y))), "an equation: the equations, the conjunction with one, and the wild")
	require.Equal(t, []string{"zz_readings_heads.Again", "zz_readings_heads.Both", "zz_readings_heads.Wild"}, names(ReadablesFor(again)), "the structure's predicate: its laws, the conjunction with one, and the wild")
	require.Equal(t, []string{"zz_readings_heads.Wild"}, names(ReadablesFor(g.Apply(x))), "a constant no reading concludes in: the wild alone")
	require.Equal(t, []string{"zz_readings_heads.Wild"}, names(ReadablesFor(P.Apply(x))), "a goal headed by a variable: the wild alone")
	require.Equal(t, []string{"zz_readings_heads.Wild"}, names(ReadablesFor(lambda)), "an abstraction: no law concludes in one")

	// Over the whole view, every family's readables included: the
	// candidates are the readables one of whose readings' heads may
	// match the target, in the view's order, each once, and no other.
	for _, target := range []core.Term{x.Eq(y), again, g.Apply(x), P.Apply(x), lambda} {
		var want []Readable
		for _, r := range Readables() {
			for _, rigid := range r.Head().Rigids() {
				if rigid.MayMatch(target) {
					want = append(want, r)
					break
				}
			}
		}
		got := ReadablesFor(target)
		require.Len(t, got, len(want), ext.PrintTerm(target))
		for i := range want {
			require.True(t, got[i].Law == want[i].Law && got[i].Statement == want[i].Statement, "%s: candidate %d", ext.PrintTerm(target), i)
		}
	}
	all, ready := ReadablesForIfReady(x.Eq(y))
	require.True(t, ready, "the view is walked")
	require.Equal(t, names(ReadablesFor(x.Eq(y))), names(all))
}

// The first-level door reads the laws of the structure a projection
// states and no chain further, and walks nothing of the view: the index
// lists them under the projection law, and `xugo query` reads the
// corpus once per question. What it serves is the whole view's first
// level from that root, statement for statement.
func TestReadableDirectlyThroughIsTheFirstLevel(t *testing.T) {
	fam := NewFamily("zz_readings_direct", nil)
	stub := Bare(func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil })
	inner := fam.DefineStructure(DefEntry{
		Name: "Inner", Const: "zz_rd_inner", Type: "(A → A → A) → A → bool",
		Equations: []string{"∀op:(A → A → A). ∀e:A. zz_rd_inner(op, e) ⇔ op(e, e) = e"},
	})
	point := fam.DefineStructure(DefEntry{
		Name: "Point", Const: "zz_rd_point", Type: "A → bool",
		Equations: []string{"∀e:A. zz_rd_point(e) ⇔ e = e"},
	})
	left := fam.DefineStructure(DefEntry{
		Name: "Left", Const: "zz_rd_left", Type: "(A → A → A) → A → bool",
		Equations: []string{"∀op:(A → A → A). ∀e:A. zz_rd_left(op, e) ⇔ zz_rd_inner(op, e)"},
	})
	law := func(name string, statement dsl.Statement) *ProofEntry {
		headline, err := statement.Text()
		require.NoError(t, err)
		return fam.Add(ProofEntry{Name: name, Build: BuildSpec{Fn: stub.Fn, Headline: headline}})
	}
	fromLeft := law("FromLeft", left.Statement("zz_rd_inner(op, e)"))
	fixed := law("Fixed", inner.Statement("op(e, e) = e"))
	law("ToPoint", inner.Statement("zz_rd_point(op(e, e))"))
	law("Trivial", point.Statement("e = e"))

	names := func(readables []Readable) []string {
		var out []string
		for _, r := range readables {
			out = append(out, r.Law.Name)
		}
		return out
	}
	direct := ReadableDirectlyThrough(fromLeft)
	require.Equal(t, []string{"zz_readings_direct.Fixed", "zz_readings_direct.ToPoint"}, names(direct),
		"the inner structure's laws, its projection to the point among them; the point's law is a chain further")
	for _, r := range direct {
		require.Equal(t, []*ProofEntry{fromLeft}, r.Through)
		require.Nil(t, r.Head(), "no goal is matched against the door's readables")
	}
	require.Nil(t, ReadableDirectlyThrough(fixed), "a law that is no projection reads nothing")

	readings.mu.Lock()
	v := readings.view
	readings.mu.Unlock()
	require.True(t, v == view(), "the view is the registry's as it stands")
	require.Nil(t, v.roots[fromLeft].readables, "the door walks no root")
	select {
	case <-v.ready:
		t.Fatal("the door walked the whole view")
	default:
	}

	whole := readableThrough(fromLeft)
	require.Equal(t, []string{"zz_readings_direct.Fixed", "zz_readings_direct.ToPoint", "zz_readings_direct.Trivial"}, names(whole))
	for i, r := range direct {
		require.Equal(t, whole[i].Through, r.Through, "%s", r.Law.Name)
		require.True(t, whole[i].Statement.AlphaEquals(r.Statement), "%s: the door derives the whole view's statement", r.Law.Name)
		require.Equal(t, whole[i].BodyText(), r.BodyText(), "%s", r.Law.Name)
	}
}

// The view moves with what its walk reads and nothing else: an entry
// that is no structure law leaves it as it stands; a law of a
// structure replaces it, and so does a predicate becoming a structure
// with no entry registered, which makes a law read before it a
// projection.
func TestReadingsViewMovesWithWhatTheWalkReads(t *testing.T) {
	fam := NewFamily("zz_readings_moves", nil)
	stub := Bare(func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil })
	law := func(name string, statement dsl.Statement) *ProofEntry {
		headline, err := statement.Text()
		require.NoError(t, err)
		return fam.Add(ProofEntry{Name: name, Build: BuildSpec{Fn: stub.Fn, Headline: headline}})
	}
	fam.Define(DefEntry{
		Name: "Body", Const: "zz_rm_body", Type: "(B → B → B) → bool",
		Equations: []string{"∀op:(B → B → B). zz_rm_body(op) ⇔ (∀x y:B. op(x, y) = op(y, x))"},
	})
	magma := fam.DefineStructure(DefEntry{
		Name: "Magma", Const: "zz_rm_magma", Type: "(B → B → B) → bool",
		Equations: []string{"∀op:(B → B → B). zz_rm_magma(op) ⇔ (∀x:B. op(x, x) = op(x, x))"},
	})
	toBody := law("ToBody", magma.Statement("zz_rm_body(op)"))
	before := view()

	law("Plain", dsl.Statement{Binders: "∀a:bool.", Hypotheses: []string{"a"}, Conclusion: "a"})
	require.True(t, before == view(), "an entry that is no structure law leaves the view as it stands")
	require.False(t, before.replaced())

	law("Idem", magma.Statement("∀x:B. op(x, x) = op(x, x)"))
	withLaw := view()
	require.False(t, before == withLaw, "a law of a structure replaces it")
	require.True(t, before.replaced())
	_, isProjection := ProjectionOf(toBody)
	require.False(t, isProjection, "zz_rm_body is no structure yet")

	fam.StructureOf("zz_rm_body", "op:(B → B → B)")
	require.False(t, withLaw == view(), "a predicate becoming a structure replaces it")
	p, isProjection := ProjectionOf(toBody)
	require.True(t, isProjection, "the law read before is a projection now")
	require.Equal(t, "zz_rm_body", p.To)
}

// A view replaced before its whole walk dispatches a root walks none:
// the walk closes ready cut, with nothing indexed, and the doors that
// read the whole view read the view that replaced it.
func TestReadingsReplacedViewWalksNoFurtherRoot(t *testing.T) {
	fam := NewFamily("zz_readings_replaced", nil)
	stub := Bare(func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil })
	law := func(name string, statement dsl.Statement) *ProofEntry {
		headline, err := statement.Text()
		require.NoError(t, err)
		return fam.Add(ProofEntry{Name: name, Build: BuildSpec{Fn: stub.Fn, Headline: headline}})
	}
	inner := fam.DefineStructure(DefEntry{
		Name: "Inner", Const: "zz_rx_inner", Type: "(A → A → A) → A → bool",
		Equations: []string{"∀op:(A → A → A). ∀e:A. zz_rx_inner(op, e) ⇔ op(e, e) = e"},
	})
	outer := fam.DefineStructure(DefEntry{
		Name: "Outer", Const: "zz_rx_outer", Type: "(A → A → A) → A → bool",
		Equations: []string{"∀op:(A → A → A). ∀e:A. zz_rx_outer(op, e) ⇔ zz_rx_inner(op, e)"},
	})
	toInner := law("ToInner", outer.Statement("zz_rx_inner(op, e)"))
	law("Fixed", inner.Statement("op(e, e) = e"))
	replaced := view()

	law("Twice", inner.Statement("op(op(e, e), e) = e"))
	require.False(t, replaced == view())
	replaced.start()
	<-replaced.ready
	require.True(t, replaced.cut, "the walk of a replaced view is cut")
	require.Nil(t, replaced.roots[toInner].readables, "and walks no root")
	require.Empty(t, replaced.all)

	var fromWhole []string
	for _, r := range Readables() {
		if r.Root() == toInner {
			fromWhole = append(fromWhole, r.Law.Name)
		}
	}
	require.Equal(t, []string{"zz_readings_replaced.Fixed", "zz_readings_replaced.Twice"}, fromWhole,
		"the whole view read is the one that replaced it")
}
