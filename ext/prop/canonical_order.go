package prop

import (
	"slices"
	"sort"
	"strconv"
	"strings"

	"github.com/euc-ai/xugo/ext"
)

// canonicalBinderOrder orders the binders of one same-kind quantifier
// block by a rule that depends only on the block's α-class — never on
// the binders' names, on the order they were pulled in, or on the order
// the body's chains happen to be associated.
//
// The rule is a canonical labeling of the binders under the body's
// symmetries. Every binder starts with its type as its color. A round
// of refinement gives each binder a signature — the body's AC-key with
// that binder marked and every other binder replaced by its current
// color — and re-colors the binders by (previous color, signature); the
// partition can only split, so it reaches a fixed point. A class the
// refinement cannot split holds binders the body cannot tell apart by
// any invariant of this kind, so one member is individualized (given a
// color of its own) and the refinement rerun, recursively; each leaf is
// a total order, and the leaf whose De Bruijn'd body has the least
// AC-key wins. Two members of a class whose individualizations refine
// to colorings an automorphism of the body carries onto each other
// head isomorphic branches with the same leaf keys, so one of them is
// explored (automorphismBetween) — the pruning that keeps a block of k
// independent, mutually symmetric binders (P(x₁) ∧ … ∧ P(xₖ), which the
// merge pass collapses only later) at one leaf instead of k!, and a
// chain of k clauses alike up to their own binders (x₁ ∈ S₁ ∧ … ∧
// xₖ ∈ Sₖ, canonicalBlock's distributed chain, whose automorphisms
// swap two clauses' binders together) at k leaves instead of k!.
//
// Every key the search compares is the body's AC-key with each binder
// standing for a token, so the body is serialized once with the binders
// left open (keyTemplate) and each key fills in the tokens.
//
// vars are the block's binders the body mentions, in any order; the
// result lists them outermost-first by (type, canonical rank).
func canonicalBinderOrder(vars []VarTerm, body Term) []VarTerm {
	n := len(vars)
	if n < 2 {
		return slices.Clone(vars)
	}
	c := newCanonicalLabeling(vars, body)
	order, _ := c.search(c.typeColors())
	out := make([]VarTerm, n)
	for pos, i := range order {
		out[pos] = vars[i]
	}
	return out
}

type canonicalLabeling struct {
	vars     []VarTerm
	ids      []string
	template *keyTemplate
	// identity is the body's AC-key with every binder standing for
	// itself: the key a permutation of the binders gives exactly when it
	// is an automorphism of the body.
	identity string
	// nodes counts the search's calls, the measure of its pruning.
	nodes int
}

func newCanonicalLabeling(vars []VarTerm, body Term) *canonicalLabeling {
	c := &canonicalLabeling{vars: vars, ids: make([]string, len(vars))}
	for i, v := range vars {
		c.ids[i] = varID(v)
	}
	c.template = openKey(body, c.ids)
	c.identity = c.template.eval(c.ids)
	return c
}

// typeColors is the initial coloring: the dense rank of each binder's
// type.
func (c *canonicalLabeling) typeColors() []int {
	types := make([]HolType, 0, len(c.vars))
	for _, v := range c.vars {
		if !slices.ContainsFunc(types, v.Type().Equals) {
			types = append(types, v.Type())
		}
	}
	sort.Slice(types, func(i, j int) bool { return HolType.Compare(types[i], types[j]) < 0 })
	color := make([]int, len(c.vars))
	for i, v := range c.vars {
		color[i] = slices.IndexFunc(types, v.Type().Equals)
	}
	return color
}

// search refines color to a fixed point, then either returns the total
// order it induces (binder indices by color) or individualizes each
// member of the first unsplit class in turn, explores the branches no
// explored branch is carried onto by an automorphism, and returns the
// best leaf below.
func (c *canonicalLabeling) search(color []int) (order []int, key string) {
	c.nodes++
	n := len(c.vars)
	color = c.refine(color)
	if countColors(color) == n {
		order = make([]int, n)
		for i := range order {
			order[i] = i
		}
		sort.Slice(order, func(a, b int) bool { return color[order[a]] < color[order[b]] })
		return order, c.leafKey(order)
	}
	class := -1
	for cl := 0; cl < n && class < 0; cl++ {
		members := 0
		for i := range color {
			if color[i] == cl {
				members++
			}
		}
		if members > 1 {
			class = cl
		}
	}
	var explored [][]int
	var bestOrder []int
	bestKey := ""
	for i := range color {
		if color[i] != class {
			continue
		}
		branch := c.refine(individualized(color, class, i))
		if slices.ContainsFunc(explored, func(e []int) bool { return c.automorphismBetween(e, branch) != nil }) {
			continue
		}
		explored = append(explored, branch)
		o, k := c.search(branch)
		if bestOrder == nil || k < bestKey {
			bestOrder, bestKey = o, k
		}
	}
	return bestOrder, bestKey
}

// individualized is color with binder i of the class given a color of
// its own: i sorts first within its class, everything else keeps its
// relative order.
func individualized(color []int, class, i int) []int {
	next := make([]int, len(color))
	for j := range color {
		next[j] = 2 * color[j]
		if color[j] > class {
			next[j]++
		}
	}
	next[i] = 2*class - 1
	return denseRanks(next)
}

// automorphismBetween is a permutation σ of the binders that is an
// automorphism of the body and carries the coloring a onto b (binder j
// has in a the color σ(j) has in b): the witness that the search below
// b is the search below a relabeled, so exploring both finds no leaf
// key the one does not; nil when the candidate is none. The candidate
// is read off the colorings — each class of a onto the class of its
// color in b, the binders both classes hold fixed, the rest matched in
// index order — and checked exactly: its key is the identity's iff the
// body is invariant under it. A branch whose candidate fails is
// explored.
func (c *canonicalLabeling) automorphismBetween(a, b []int) []int {
	n := len(a)
	classes := countColors(a)
	if countColors(b) != classes {
		return nil
	}
	byColorA := make([][]int, classes)
	byColorB := make([][]int, classes)
	for j := range n {
		byColorA[a[j]] = append(byColorA[a[j]], j)
		byColorB[b[j]] = append(byColorB[b[j]], j)
	}
	sigma := make([]int, n)
	for col := range classes {
		A, B := byColorA[col], byColorB[col]
		if len(A) != len(B) {
			return nil
		}
		var onlyA, onlyB []int
		i, k := 0, 0
		for i < len(A) || k < len(B) {
			switch {
			case k == len(B) || (i < len(A) && A[i] < B[k]):
				onlyA = append(onlyA, A[i])
				i++
			case i == len(A) || B[k] < A[i]:
				onlyB = append(onlyB, B[k])
				k++
			default:
				sigma[A[i]] = A[i]
				i++
				k++
			}
		}
		for m := range onlyA {
			sigma[onlyA[m]] = onlyB[m]
		}
	}
	tokens := make([]string, n)
	for j, image := range sigma {
		tokens[j] = c.ids[image]
	}
	if c.template.eval(tokens) != c.identity {
		return nil
	}
	return sigma
}

// refine reruns the signature refinement until the partition is stable.
// The new color is the dense rank of (previous color, signature), so
// classes only ever split.
func (c *canonicalLabeling) refine(color []int) []int {
	n := len(c.vars)
	tokens := make([]string, n)
	for {
		for j := range tokens {
			tokens[j] = "κ" + strconv.Itoa(color[j])
		}
		sigs := make([]string, n)
		for i := range c.vars {
			own := tokens[i]
			tokens[i] = "μ"
			sigs[i] = c.template.eval(tokens)
			tokens[i] = own
		}
		idx := make([]int, n)
		for i := range idx {
			idx[i] = i
		}
		sort.SliceStable(idx, func(a, b int) bool {
			ia, ib := idx[a], idx[b]
			if color[ia] != color[ib] {
				return color[ia] < color[ib]
			}
			return sigs[ia] < sigs[ib]
		})
		next := make([]int, n)
		rank := -1
		for k, i := range idx {
			if k == 0 || color[i] != color[idx[k-1]] || sigs[i] != sigs[idx[k-1]] {
				rank++
			}
			next[i] = rank
		}
		if countColors(next) == countColors(color) {
			return next
		}
		color = next
	}
}

// leafKey is the AC-key of the body with the binders replaced by their
// positions in order — the value two leaves of the search are compared
// by.
func (c *canonicalLabeling) leafKey(order []int) string {
	tokens := make([]string, len(order))
	for pos, i := range order {
		tokens[i] = "#" + strconv.Itoa(pos)
	}
	return c.template.eval(tokens)
}

func countColors(color []int) int {
	seen := map[int]bool{}
	for _, c := range color {
		seen[c] = true
	}
	return len(seen)
}

func denseRanks(color []int) []int {
	distinct := slices.Clone(color)
	slices.Sort(distinct)
	distinct = slices.Compact(distinct)
	out := make([]int, len(color))
	for i, c := range color {
		out[i], _ = slices.BinarySearch(distinct, c)
	}
	return out
}

// varID names a variable by its kernel identity: name and type.
func varID(v VarTerm) string {
	return string(v.Name()) + "\x00" + ext.FormatTypeForParser(v.Type())
}

// keyTemplate is a term's AC-key with some free variables left open.
// The AC-key serializes a term up to the symmetries the normalizer
// quotients out: ∧ and ∨ chains are flattened and their members
// sorted, the two sides of an equation are sorted, and a λ-bound
// variable is written as its De Bruijn index. A free variable is
// written by its identity, except an open one, which is written as the
// token eval is given for it — the hook by which canonicalBinderOrder
// marks and colors a block's binders, which are free in the body it
// inspects. A subterm no open variable occurs in is serialized once,
// into lit.
type keyTemplate struct {
	lit    string         // the whole key, when nothing open occurs
	slot   int            // an open variable's index + 1, else 0
	head   string         // written before the parts: ∧, ∨, = or λ<type>.
	sorted bool           // the parts are a chain's members or an equation's sides
	parts  []*keyTemplate // [fun, arg] for an application, [body] for λ
}

// openKey is t's keyTemplate with the variables whose varIDs are open
// left open, open[i] filled by the token at index i.
func openKey(t Term, open []string) *keyTemplate {
	slots := make(map[string]int, len(open))
	for i, id := range open {
		slots[id] = i + 1
	}
	return compileKey(t, slots, nil)
}

func compileKey(t Term, slots map[string]int, bound []VarTerm) *keyTemplate {
	switch t := t.Core().(type) {
	case VarTerm:
		for i := len(bound) - 1; i >= 0; i-- {
			if bound[i].EqualsVar(t) {
				return &keyTemplate{lit: "b" + strconv.Itoa(len(bound)-1-i)}
			}
		}
		id := varID(t)
		if slot, ok := slots[id]; ok {
			return &keyTemplate{slot: slot}
		}
		return &keyTemplate{lit: "v" + id}
	case ConstTerm:
		return &keyTemplate{lit: "c" + string(t.Name()) + ":" + ext.FormatTypeForParser(t.Type())}
	case AbsTerm:
		head := "λ" + ext.FormatTypeForParser(t.Var().Type()) + "."
		body := compileKey(t.Body(), slots, append(bound, t.Var()))
		if body.closed() {
			return &keyTemplate{lit: head + body.lit}
		}
		return &keyTemplate{head: head, parts: []*keyTemplate{body}}
	case AppliedTerm:
		if parts := DecomposesAND(t); len(parts) > 1 {
			return compileSorted("∧", parts, slots, bound)
		}
		if parts := DecomposesOR(t); len(parts) > 1 {
			return compileSorted("∨", parts, slots, bound)
		}
		if l, r, ok := MatchesEQ(t); ok {
			return compileSorted("=", []Term{l, r}, slots, bound)
		}
		f, a := compileKey(t.Fun(), slots, bound), compileKey(t.Arg(), slots, bound)
		if f.closed() && a.closed() {
			return &keyTemplate{lit: "(" + f.lit + " " + a.lit + ")"}
		}
		return &keyTemplate{parts: []*keyTemplate{f, a}}
	default:
		panic("compileKey: unknown term shape")
	}
}

func compileSorted(head string, terms []Term, slots map[string]int, bound []VarTerm) *keyTemplate {
	parts := make([]*keyTemplate, len(terms))
	closed := true
	for i, p := range terms {
		parts[i] = compileKey(p, slots, bound)
		closed = closed && parts[i].closed()
	}
	if closed {
		keys := make([]string, len(parts))
		for i, p := range parts {
			keys[i] = p.lit
		}
		sort.Strings(keys)
		return &keyTemplate{lit: head + "(" + strings.Join(keys, ",") + ")"}
	}
	return &keyTemplate{head: head, sorted: true, parts: parts}
}

func (k *keyTemplate) closed() bool { return k.slot == 0 && k.parts == nil }

// eval is the key with the open variable of slot i written as
// tokens[i-1].
func (k *keyTemplate) eval(tokens []string) string {
	switch {
	case k.closed():
		return k.lit
	case k.slot > 0:
		return tokens[k.slot-1]
	}
	var b strings.Builder
	k.write(&b, tokens)
	return b.String()
}

// write appends the key to b. A chain's members and an equation's
// sides are materialized for sorting; other nodes are written in place.
func (k *keyTemplate) write(b *strings.Builder, tokens []string) {
	switch {
	case k.closed():
		b.WriteString(k.lit)
	case k.slot > 0:
		b.WriteString(tokens[k.slot-1])
	case k.sorted:
		keys := make([]string, len(k.parts))
		for i, p := range k.parts {
			keys[i] = p.eval(tokens)
		}
		sort.Strings(keys)
		b.WriteString(k.head)
		b.WriteByte('(')
		for i, key := range keys {
			if i > 0 {
				b.WriteByte(',')
			}
			b.WriteString(key)
		}
		b.WriteByte(')')
	case len(k.parts) == 1:
		b.WriteString(k.head)
		k.parts[0].write(b, tokens)
	default:
		b.WriteByte('(')
		k.parts[0].write(b, tokens)
		b.WriteByte(' ')
		k.parts[1].write(b, tokens)
		b.WriteByte(')')
	}
}
