package prop

import (
	"fmt"
	"math/rand"
	"slices"
	"sort"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// acKey quotients exactly the symmetries the normalizer sorts out:
// chain association and order, equation orientation, bound names.
func TestACKeyQuotientsChainOrderEquationsAndBoundNames(t *testing.T) {
	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	c := Var("c", TypeBool)
	x := Var("x", TypeInd)
	y := Var("y", TypeInd)
	f := Var("f", MakeFun(TypeInd, TypeInd))
	R := Var("R", MakeFun(TypeInd, TypeInd, TypeBool))

	assert.Equal(t,
		acKey(a.And(b.And(c))),
		acKey(c.And(a).And(b)), "∧ association and order")
	assert.Equal(t,
		acKey(a.Or(b).Or(c)),
		acKey(b.Or(c.Or(a))), "∨ association and order")
	assert.Equal(t,
		acKey(f.Apply(x).Eq(y)),
		acKey(y.Eq(f.Apply(x))), "equation orientation")
	assert.Equal(t,
		acKey(ForAll(x)(f.Apply(x).Eq(x))),
		acKey(ForAll(y)(f.Apply(y).Eq(y))), "bound names")
	assert.NotEqual(t,
		acKey(a.And(b)),
		acKey(a.Or(b)), "∧ and ∨ stay distinct")
	assert.NotEqual(t,
		acKey(R.Apply(x, y)),
		acKey(R.Apply(y, x)), "argument order is not a symmetry")
}

// The template and the recursive serialization give the same bytes for
// each token assignment, including shadowed variables, variables of the
// same name at different types, and closed subterms.
func TestKeyTemplateIsTheACKey(t *testing.T) {
	P := Var("P", MakeFun(TypeInd, TypeBool))
	R := Var("R", MakeFun(TypeInd, TypeInd, TypeBool))
	f := Var("f", MakeFun(TypeInd, TypeInd))
	g := Var("g", MakeFun(MakeFun(TypeInd, TypeBool), TypeBool))
	x, y, z, w := Var("x", TypeInd), Var("y", TypeInd), Var("z", TypeInd), Var("w", TypeInd)
	xb := Var("x", TypeBool)
	bodies := []struct {
		name string
		body Term
	}{
		{"open variable", x},
		{"closed variable", w},
		{"constant", T},
		{"open chains", P.Apply(x).And(R.Apply(x, y)).And(P.Apply(z).Or(R.Apply(f.Apply(z), x)))},
		{"open equation", f.Apply(x).Eq(f.Apply(f.Apply(y))).Or(Not(R.Apply(y, z)))},
		{"shadowed open variable", ForAll(x)(R.Apply(x, y)).And(P.Apply(x))},
		{"nested binders", ForAll(w)(Exists(x)(R.Apply(w, x).And(R.Apply(x, y)).Or(w.Eq(z))))},
		{"shadowed nested binder", ForAll(x)(P.Apply(x).And(Exists(x)(R.Apply(x, y))))},
		{"open abstraction", g.Apply(WrapTerm(core.Abs(w.Core().(VarTerm), R.Apply(w, z).Core()))).Or(P.Apply(y))},
		{"closed abstraction", WrapTerm(core.Abs(w.Core().(VarTerm), P.Apply(w).Core()))},
		{"closed chains", P.Apply(w).And(R.Apply(w, w).Or(w.Eq(w)))},
		{"same name different types", ForAll(x)(P.Apply(x).Or(xb)).And(ForAll(xb)(P.Apply(x).Or(xb)))},
	}
	open := []VarTerm{x.Core().(VarTerm), y.Core().(VarTerm), z.Core().(VarTerm), xb.Core().(VarTerm), f.Core().(VarTerm)}
	ids := make([]string, len(open))
	for i, v := range open {
		ids[i] = varID(v)
	}
	pool := append([]string{"", "μ", "κ0", "κ1", "#0", "#1", "μ1", "μ2", "(,)", "\x00"}, ids...)
	for _, tc := range bodies {
		t.Run(tc.name, func(t *testing.T) {
			template := openKey(tc.body, ids)
			rng := rand.New(rand.NewSource(1))
			for range 20 {
				tokens := make([]string, len(open))
				subst := map[string]string{}
				for i := range tokens {
					tokens[i] = pool[rng.Intn(len(pool))]
					subst[ids[i]] = tokens[i]
				}
				assert.Equal(t, referenceACKey(tc.body, subst, nil), template.eval(tokens), "tokens %q", tokens)
			}
			assert.Equal(t, referenceACKey(tc.body, nil, nil), openKey(tc.body, nil).eval(nil), "no open variables")
		})
	}
}

// referenceACKey serializes a term up to the normalizer's symmetries in
// one walk, a free variable mapped by subst written as its token: the
// specification keyTemplate is checked against.
func referenceACKey(t Term, subst map[string]string, bound []VarTerm) string {
	switch t := t.Core().(type) {
	case VarTerm:
		for i := len(bound) - 1; i >= 0; i-- {
			if bound[i].EqualsVar(t) {
				return fmt.Sprintf("b%d", len(bound)-1-i)
			}
		}
		if token, ok := subst[varID(t)]; ok {
			return token
		}
		return "v" + varID(t)
	case ConstTerm:
		return "c" + string(t.Name()) + ":" + ext.FormatTypeForParser(t.Type())
	case AbsTerm:
		return "λ" + ext.FormatTypeForParser(t.Var().Type()) + "." +
			referenceACKey(t.Body(), subst, append(bound, t.Var()))
	case AppliedTerm:
		sorted := func(parts []Term) string {
			keys := make([]string, len(parts))
			for i, p := range parts {
				keys[i] = referenceACKey(p, subst, bound)
			}
			sort.Strings(keys)
			return "(" + strings.Join(keys, ",") + ")"
		}
		if parts := DecomposesAND(t); len(parts) > 1 {
			return "∧" + sorted(parts)
		}
		if parts := DecomposesOR(t); len(parts) > 1 {
			return "∨" + sorted(parts)
		}
		if l, r, ok := MatchesEQ(t); ok {
			return "=" + sorted([]Term{l, r})
		}
		return "(" + referenceACKey(t.Fun(), subst, bound) + " " + referenceACKey(t.Arg(), subst, bound) + ")"
	default:
		panic("referenceACKey: unknown term shape")
	}
}

// The canonical order is a function of the block's α-class: renaming
// the binders, permuting the binder list, and re-associating or
// permuting the body's chains all give the same order (up to the
// renaming).
func TestCanonicalBinderOrderIsAlphaInvariant(t *testing.T) {
	s := Var("s", MakeFun(TypeInd, TypeBool))
	R := Var("R", MakeFun(TypeInd, TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))
	f := Var("f", MakeFun(TypeInd, TypeInd))

	// body(x, y, z, u): distinguishable by structure — z is the only one
	// under Q, x and y sit in different argument positions of R, u only
	// appears through f. Written as a list of clauses so the test can
	// permute and re-associate them.
	clauses := func(x, y, z, u *ext.TermWrapper) []Term {
		return []Term{
			s.Apply(x),
			s.Apply(y),
			R.Apply(x, y),
			s.Apply(z).And(Q.Apply(z)),
			R.Apply(f.Apply(u), x).Or(Q.Apply(u)),
		}
	}
	conj := func(cs []Term, seed int64) Term {
		rng := rand.New(rand.NewSource(seed))
		cs = slices.Clone(cs)
		rng.Shuffle(len(cs), func(i, j int) { cs[i], cs[j] = cs[j], cs[i] })
		// Random association.
		for len(cs) > 1 {
			i := rng.Intn(len(cs) - 1)
			merged := ext.WrapTerm(cs[i]).And(cs[i+1])
			cs = append(cs[:i], append([]Term{merged}, cs[i+2:]...)...)
		}
		return cs[0]
	}

	x, y, z, u := Var("x", TypeInd), Var("y", TypeInd), Var("z", TypeInd), Var("u", TypeInd)
	reference := canonicalBinderOrder([]VarTerm{x.Core().(VarTerm), y.Core().(VarTerm), z.Core().(VarTerm), u.Core().(VarTerm)},
		conj(clauses(x, y, z, u), 1))
	refNames := names(reference)

	// Rename (order-reversing names), permute the binder list, reshuffle
	// the body: the canonical order must map to the same roles.
	rename := map[string]string{"x": "d", "y": "c", "z": "b", "u": "a"}
	back := map[string]string{"d": "x", "c": "y", "b": "z", "a": "u"}
	d, c2, b2, a2 := Var("d", TypeInd), Var("c", TypeInd), Var("b", TypeInd), Var("a", TypeInd)
	_ = rename
	for seed := int64(2); seed < 12; seed++ {
		vars := []VarTerm{a2.Core().(VarTerm), b2.Core().(VarTerm), c2.Core().(VarTerm), d.Core().(VarTerm)}
		rng := rand.New(rand.NewSource(seed))
		rng.Shuffle(len(vars), func(i, j int) { vars[i], vars[j] = vars[j], vars[i] })
		got := canonicalBinderOrder(vars, conj(clauses(d, c2, b2, a2), seed))
		gotNames := names(got)
		for i := range gotNames {
			gotNames[i] = back[gotNames[i]]
		}
		assert.Equal(t, refNames, gotNames, "seed %d", seed)
	}
}

// A block the refinement cannot split (x and y are automorphic in
// R(x,y) ∧ R(y,x)) still gets one canonical form: the individualization
// search returns a total order, and both leaves give the same key.
func TestCanonicalBinderOrderBreaksAutomorphicTies(t *testing.T) {
	R := Var("R", MakeFun(TypeInd, TypeInd, TypeBool))
	x, y := Var("x", TypeInd), Var("y", TypeInd)
	xv, yv := x.Core().(VarTerm), y.Core().(VarTerm)
	body := R.Apply(x, y).And(R.Apply(y, x))
	o1 := canonicalBinderOrder([]VarTerm{xv, yv}, body)
	o2 := canonicalBinderOrder([]VarTerm{yv, xv}, body)
	assert.Len(t, o1, 2)
	assert.Len(t, o2, 2)
	// Whatever the order, the De Bruijn'd bodies coincide.
	keyOf := func(o []VarTerm) string {
		ids := make([]string, len(o))
		tokens := make([]string, len(o))
		for pos, v := range o {
			ids[pos] = varID(v)
			tokens[pos] = fmt.Sprintf("#%d", pos)
		}
		return openKey(body, ids).eval(tokens)
	}
	assert.Equal(t, keyOf(o1), keyOf(o2))
}

// A block of many independent, mutually symmetric binders is one leaf,
// not k! of them: the transposition pruning must keep this instant.
func TestCanonicalBinderOrderPrunesIndependentSymmetricBinders(t *testing.T) {
	P := Var("P", MakeFun(TypeInd, TypeBool))
	var vars []VarTerm
	var body *ext.TermWrapper
	for i := 0; i < 12; i++ {
		v := Var(TermName(fmt.Sprintf("x%d", i)), TypeInd)
		vars = append(vars, v.Core().(VarTerm))
		if body == nil {
			body = P.Apply(v)
		} else {
			body = body.And(P.Apply(v))
		}
	}
	got := canonicalBinderOrder(vars, body)
	assert.Len(t, got, 12)
}

// Normalize is α-invariant on a clause set whose free (Skolem-like)
// variables are symmetric enough that the previous first-appearance
// rule chose its fixed point by their names: renaming the free
// variables by an order-reversing map must not move the key.
func TestNormalizeFreeVariableNameOrderDoesNotReachTheKey(t *testing.T) {
	s := Var("s", MakeFun(TypeInd, TypeBool))
	P := Var("P", MakeFun(TypeInd, TypeInd, TypeBool))
	f := Var("f", MakeFun(TypeInd, TypeInd))
	mk := func(u, v, w, z *ext.TermWrapper) Prop {
		// Modelled on set_image's image lemma refute set: four Skolem
		// witnesses of one type, pairwise related through s, f and P.
		return core.MakeProp(F,
			s.Apply(u).Or(s.Apply(v)),
			s.Apply(u).Or(Not(P.Apply(f.Apply(v), f.Apply(w)))),
			s.Apply(v).Or(s.Apply(z)),
			s.Apply(w).Or(s.Apply(z)),
			s.Apply(z).Or(Not(P.Apply(u, w))),
			Not(P.Apply(u, w)).Or(Not(P.Apply(f.Apply(v), f.Apply(w)))),
			Not(P.Apply(f.Apply(v), f.Apply(w))).Or(u.Eq(f.Apply(z))),
		)
	}
	a, b, c, d := Var("a", TypeInd), Var("b", TypeInd), Var("c", TypeInd), Var("d", TypeInd)
	n1, _ := Normalize(mk(a, b, c, d))
	n2, _ := Normalize(mk(d, c, b, a))
	assert.Equal(t, n1.AlphaKey(), n2.AlphaKey())
}

func acKey(t Term) string { return openKey(t, nil).eval(nil) }

func names(vs []VarTerm) []string {
	out := make([]string, len(vs))
	for i, v := range vs {
		out[i] = string(v.Name())
	}
	return out
}

// A chain of clauses alike up to their own binders — canonicalBlock's
// distributed chain for a block whose clauses are x ∈ S over different
// binders — has an automorphism per pair of clauses that swaps the two
// clauses' binders together, never one binder alone, so a pruning that
// saw transpositions alone would explore 6!·5! leaves of this chain.
// The search reads the automorphism off the refined colorings and
// explores one branch per node.
func TestCanonicalBinderOrderPrunesClausesAlikeUpToTheirBinders(t *testing.T) {
	carrier := Var("carrier", MakeFun(TypeInd, MakeFun(TypeInd, TypeBool)))
	var vars []VarTerm
	var body *ext.TermWrapper
	add := func(clause *ext.TermWrapper) {
		if body == nil {
			body = clause
		} else {
			body = body.And(clause)
		}
	}
	for i := range 6 {
		x := Var(TermName(fmt.Sprintf("x%d", i)), TypeInd)
		S := Var(TermName(fmt.Sprintf("S%d", i)), MakeFun(TypeInd, TypeBool))
		vars = append(vars, x.Core().(VarTerm), S.Core().(VarTerm))
		add(S.Apply(x))
	}
	for i := range 5 {
		y := Var(TermName(fmt.Sprintf("y%d", i)), TypeInd)
		F := Var(TermName(fmt.Sprintf("F%d", i)), TypeInd)
		vars = append(vars, y.Core().(VarTerm), F.Core().(VarTerm))
		add(carrier.Apply(F).Apply(y))
	}
	c := newCanonicalLabeling(vars, body)
	order, key := c.search(c.typeColors())
	assert.Len(t, order, len(vars))
	assert.LessOrEqual(t, c.nodes, len(vars), "one branch per node")

	// The order is canonical: the clauses listed backwards, their
	// binders renamed, give the same De Bruijn'd body.
	var rvars []VarTerm
	var rbody *ext.TermWrapper
	for i := 4; i >= 0; i-- {
		y := Var(TermName(fmt.Sprintf("b%d", i)), TypeInd)
		F := Var(TermName(fmt.Sprintf("G%d", i)), TypeInd)
		rvars = append(rvars, F.Core().(VarTerm), y.Core().(VarTerm))
		clause := carrier.Apply(F).Apply(y)
		if rbody == nil {
			rbody = clause
		} else {
			rbody = rbody.And(clause)
		}
	}
	for i := 5; i >= 0; i-- {
		x := Var(TermName(fmt.Sprintf("a%d", i)), TypeInd)
		S := Var(TermName(fmt.Sprintf("T%d", i)), MakeFun(TypeInd, TypeBool))
		rvars = append(rvars, S.Core().(VarTerm), x.Core().(VarTerm))
		rbody = rbody.And(S.Apply(x))
	}
	rc := newCanonicalLabeling(rvars, rbody)
	_, rkey := rc.search(rc.typeColors())
	assert.Equal(t, key, rkey)
}
