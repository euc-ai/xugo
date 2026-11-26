package core

import (
	"slices"
	"sync/atomic"

	"github.com/euc-ai/xugo/utils"
)

type TermName string

// A TermKey is a digest of a term. α-equal terms have one key, so a key
// indexes terms and files what is known of them. Two terms that are not
// α-equal have one key in two ways only, and neither comes up in
// ordinary use:
//
//   - the 64-bit hash a key is cut from collides: among a million
//     terms, three chances in a hundred million;
//   - a name spells a piece of a key: the variable p_type_boolvar_p, or
//     a type constant var_A beside a type variable A. No name of the
//     library does, and TestLintNamesSpellNoKeyWord holds that.
//
// Either can be made on purpose by whoever picks the names. A table of
// keys loses nothing by that where a wrong answer is found by what
// reads it, as a rule checks the terms it is handed. Where nothing
// checks afterwards — is this statement one the caller trusts, are
// these two assumptions one — the terms are compared (AlphaEquals),
// and the key only says which to compare.
type TermKey string

type Term interface {
	Type() HolType
	Size() int

	// exactly equal
	Equals(Term) bool

	// α-equal
	AlphaEquals(Term) bool

	// α-compare
	Compare(Term) int

	// α-compare with abstracted vars environment.
	CompareWithEnv(Term, []VarPair) int

	// The term's key, one for α-equal terms. See TermKey for what an
	// equal key says of two terms.
	AlphaKey() TermKey

	// The free vars in the term that satisfies the given predicate,
	// in the order of their occurrences.
	// If the predicate is nil, return all free vars.
	Frees(VarPredicate) []VarTerm

	// Whether a given var is free in this term.
	HasFree(VarTerm) bool

	// Whether all free vars in the term satisfy the given predicate.
	AllFree(VarPredicate) bool

	// Whether a free var in the term has the given name.
	HasFreeName(TermName) bool

	// Whether a var/const name is used in this term (type doesn't matter).
	HasName(TermName) bool

	// Term instantiation
	// This action depends on the set of the substitutions in the list but not the order.
	// It is not equivalent to a series of substitutions applied sequentially.
	// E.g. the original term is x + y,
	// making substitutions {x ↦ y, y ↦ x} gives y + x,
	// making substitutions {y ↦ x, x ↦ y} also gives y + x,
	// making substitution {x ↦ y} then {y ↦ x} gives x + x.
	Substitute(...TermSubst) Term

	// Type instantiation
	TypeSubstitute(...TypeSubst) Term

	// Converts bound variables in lambda abstractions to De Bruijn indices.
	// De Bruijn indices represent variables by their binding depth rather than names.
	//
	// Parameter:
	//   maxDepth: Controls how many levels of abstractions to convert
	//     - 0: Convert all abstractions (full De Bruijn conversion)
	//     - n > 0: Convert only the outermost n levels of abstractions
	//
	// Examples:
	//   λx.λy.x  with DeBruijn(0) → λ%1.λ%2.%1
	//   λx.λy.x  with DeBruijn(1) → λ%1.λy.%1  (only outer lambda converted)
	//
	// The indices start from 1 and increase with nesting depth.
	// Free variables remain unchanged.
	DeBruijn(maxDepth int) Term

	// α-equal with abstracted vars environment.
	AlphaEqualsWithEnv(Term, []VarPair) bool

	// Returns the term itself.
	// This is to make sure wrappers of the term get unwrapped.
	// The kernel does not read it; see kernel().
	Core() Term

	// kernel returns the kernel value this Term stands on: a VarTerm, a
	// ConstTerm, an AppliedTerm or an AbsTerm, the four kinds core
	// defines. Every constructor and every rule reads a Term it is handed
	// through this method before anything else, and a kernel object holds
	// kernel values only. The method is unexported, so a type outside
	// core satisfies Term only by embedding a core value, and Go's
	// promotion makes that value's kernel() the embedder's: whatever the
	// embedder's own Core, Type, Equals or AlphaEquals say, the kernel
	// sees the embedded value.
	kernel() Term

	// Returns the term as a particular kind.
	AsVar() (VarTerm, bool)
	AsConst() (ConstTerm, bool)
	AsAppliedTerm() (AppliedTerm, bool)
	AsAbsTerm() (AbsTerm, bool)

	// Unique key for exactly equal terms.
	// Internally used for α-key calculation.
	key() TermKey

	// Type variables relevant in a term.
	// Not same as the vars of the type of this term.
	// e.g. x:A, f:A->bool,
	// Applying this function on term f(x) returns {A}
	// while the type of f(x) itself is bool.
	typeVars() []VarType

	// Internal implementation of term instantiation.
	// The second return value indicates whether the term is changed.
	// The memo is the walk's record of the nodes already substituted
	// under this list, nil until the shared-DAG gate arms it (see
	// shared_dag.go).
	substituteImpl([]TermSubst, _SubstituteMemo) (Term, bool)

	// Internal implementation of type instantiation.
	// input var pair is the cache for the abstracted vars.
	// Returns the substituted term and whether there is a clashed var.
	// The memo is the walk's record of the nodes already substituted
	// under this list and this var pair environment, nil until the
	// shared-DAG gate arms it (see shared_dag.go).
	typeSubstituteImpl([]TypeSubst, []VarPair, _TypeSubstituteMemo) (Term, VarTerm)

	// Internal implementation of de Bruijn level conversion.
	// Converts bound variables to De Bruijn indices within a specified index range.
	//
	// Parameters:
	//   nextFreeIndex: The next available De Bruijn index to use (must be >= 1)
	//   stopAtIndex: Stop converting when we would need index >= this (0 = no limit)
	//   memo: The walk's record of the nodes converted under this window,
	//     nil until the shared-DAG gate arms it (see shared_dag.go)
	//
	// The function maintains a "window" of De Bruijn indices [nextFreeIndex, stopAtIndex).
	// When stopAtIndex > 0, only abstractions within this window are converted.
	//
	// Auto-adjustment behavior:
	//   If there are existing De Bruijn variables that would conflict with nextFreeIndex,
	//   both parameters are adjusted upward together to maintain the window size.
	//   This ensures the conversion avoids naming conflicts while preserving the
	//   relative depth limit.
	//
	// Examples:
	//   deBruijnImpl(1, 0): Convert all abstractions starting from index 1
	//   deBruijnImpl(1, 3): Convert using indices 1 and 2 only (stop at 3)
	//   deBruijnImpl(2, 5): Convert using indices 2, 3, and 4 only
	deBruijnImpl(nextFreeIndex, stopAtIndex int, memo _DeBruijnMemo) Term
}

// A TermSubst is a value a caller may build as a literal, so the
// constructor's check is made again where a substitution is read
// (kernelTermSubsts).
type TermSubst struct {
	VarTerm
	Term
}

func MakeTermSubst(v VarTerm, t Term) TermSubst {
	t = t.kernel()
	// For a valid substitution, the types of the terms must be equal.
	utils.Assert(v.holType.Equals(t.Type()))
	return TermSubst{v, t}
}

// kernelTermSubsts is substs as a substitution walk may read it: every
// replacement a kernel value of its variable's type. It is substs
// itself when that already holds, and a list of its own otherwise.
func kernelTermSubsts(substs []TermSubst) []TermSubst {
	for i := range substs {
		k := substs[i].Term.kernel()
		utils.Assert(substs[i].VarTerm.holType.Equals(k.Type()))
		if k != substs[i].Term {
			own := make([]TermSubst, len(substs))
			for j := range substs {
				kj := substs[j].Term.kernel()
				utils.Assert(substs[j].VarTerm.holType.Equals(kj.Type()))
				own[j] = TermSubst{substs[j].VarTerm, kj}
			}
			return own
		}
	}
	return substs
}

// _NodeMemo is what an applied or abstraction node remembers once
// asked: its keys, whether it holds an abstraction, the names it was
// asked about. A node carries one word for it, a _NodeMemoSlot, and
// makes it on the first question. A term is mostly nodes that are never
// asked anything — a rewrite inside a proof step builds them and the
// step drops them — and such a node pays the word alone.
type _NodeMemo struct {
	// lazyAlphaKey memoizes AlphaKey.
	lazyAlphaKey utils.Lazy[TermKey]

	// lazyKey memoizes key(), the α-sensitive key AbsTerm.AlphaKey reads
	// of its body: it cannot read body.AlphaKey, since a de Bruijn
	// normalized body may have no legal α-key (see AbsTerm.AlphaKey).
	// Without the memo, key() on an applied node recurses through both
	// children on every visit; with it and lazyHasAbstraction below,
	// key() is O(unique nodes) on shared-DAG shapes (set_comprehension
	// and nested-binder towers) instead of O(2^depth).
	lazyKey utils.Lazy[TermKey]

	// lazyHasAbstraction memoizes hasAbstraction on an applied node —
	// the guard key() consults on every invocation to decide whether to
	// fall back to AlphaKey. Without the memo this guard by itself would
	// blow the shared-DAG bound even on ground subtrees (the walk
	// descends fun/arg until it hits an AbsTerm or bottoms out), and
	// would be re-invoked at every level of key()'s recursion.
	lazyHasAbstraction utils.Lazy[bool]

	// hasNames memoizes HasName(n) on an applied node per queried name,
	// as a list of the names asked and their answers, the latest first.
	// Without it, HasName recurses through both children on every call;
	// on deeply-nested terms with shared subtrees, that is O(2ⁿ). A node
	// is asked about few names, so an answer costs one small cell.
	hasNames atomic.Pointer[_HasNameCell]
}

// _NodeMemoSlot is the word a node carries for its memo: nil until the
// first question, then one memo for the node's lifetime.
type _NodeMemoSlot struct{ p atomic.Pointer[_NodeMemo] }

// get is the node's memo, made on the first call. Two callers asking at
// once race to publish one, and the loser reads the winner's.
func (s *_NodeMemoSlot) get() *_NodeMemo {
	if m := s.p.Load(); m != nil {
		return m
	}
	m := new(_NodeMemo)
	if s.p.CompareAndSwap(nil, m) {
		return m
	}
	return s.p.Load()
}

// A term is a DAG: a subterm built once and used in several places is
// one node reached by several paths, and its tree, which Size counts,
// may be exponentially larger than the DAG that holds it. The
// higher-order unifier builds such terms at every imitation step, where
// each fresh head is applied to the one argument tuple.
//
// Every walk over one term in this package is bounded by the DAG's
// nodes, not by its tree. Past the gate below, a walk remembers the
// nodes it has visited and visits a shared node once. A walk whose
// answer at a node is a fact of the node alone (HasFree, Frees,
// AllFree, HasFreeName, typeVars, the keys) carries one memo for the
// whole walk. A rewrite whose answer at a node also depends on the
// walk's parameters — Substitute on its substitution list,
// TypeSubstitute on its list and on the binders above the node, the de
// Bruijn conversion on its index window — carries one memo per region
// of fixed parameters: a binder that changes them for its body is
// itself remembered under the outer parameters, and its body is walked
// with a memo of its own. Below the gate a walk is the plain recursion
// and allocates nothing.
//
// A walk over two terms (Equals, AlphaEquals, Compare)
// is not bounded this way. It stops at a pair of identical pointers,
// which is how the unchanged parts of a rewritten term compare with
// the original.

// NaiveWalkMemoThreshold is the tree size above which a structural
// walk over a term remembers the nodes it has visited. Below it the
// walk costs at most this many visits and allocates nothing; above it
// the tree may be far larger than the DAG that holds it — a shared
// subterm counts once per path — and the walk is bounded by the DAG
// instead. ext's walkers read the same gate.
const NaiveWalkMemoThreshold = 1 << 12

// NaiveWalkNeedsMemo reports whether a structural recursion over t
// must memoize pointer-shared subtrees. A Size() below zero is the
// eagerly summed tree size overflowed: the DAG is astronomically
// shared, and such a term always takes the memoized path.
func NaiveWalkNeedsMemo(t Term) bool {
	s := t.Size()
	return s < 0 || s > NaiveWalkMemoThreshold
}

// _SubstituteMemo is one Substitute walk's record of the nodes it has
// rewritten under one substitution list: the node's result and whether
// it changed. A nil memo is the plain walk.
type _SubstituteMemo map[Term]_Substituted

type _Substituted struct {
	term    Term
	changed bool
}

// _TypeSubstituteMemo is one TypeSubstitute walk's record of the nodes
// it has rewritten under one type substitution list and one binder
// environment: the node's result, or the variable it clashed with. A
// nil memo is the plain walk.
type _TypeSubstituteMemo map[Term]_TypeSubstituted

type _TypeSubstituted struct {
	term    Term
	clashed VarTerm
}

// _DeBruijnMemo is one de Bruijn conversion's record of the nodes it
// has converted under one index window. A nil memo is the plain walk.
type _DeBruijnMemo map[Term]Term

// hasFreeIn is HasFree over a shared DAG; seen holds the applied nodes
// visited so far.
func hasFreeIn(t Term, v VarTerm, seen map[AppliedTerm]struct{}) bool {
	switch t := t.(type) {
	case AppliedTerm:
		if _, ok := seen[t]; ok {
			return false
		}
		seen[t] = struct{}{}
		return hasFreeIn(t.fun, v, seen) || hasFreeIn(t.arg, v, seen)
	case AbsTerm:
		return !t.v.Equals(v) && hasFreeIn(t.body, v, seen)
	default:
		return t.HasFree(v)
	}
}

// freeVarsIn is the free variables of t, distinct and in order of
// first occurrence, over a shared DAG: memo holds the answer at the
// applied and abstraction nodes visited so far. The answer at a node
// depends on the node alone — a binder takes its variable out of its
// body's — so a shared node is walked once. Frees, AllFree and
// HasFreeName read it past the gate: each is a question about this
// list, and a walk per tree path over the higher-order unifier's pair
// terms, whose tree doubles per imitation level, never ends.
func freeVarsIn(t Term, memo map[Term][]VarTerm) []VarTerm {
	switch t := t.(type) {
	case AppliedTerm:
		if r, ok := memo[t]; ok {
			return r
		}
		r := appendDistinctVars(freeVarsIn(t.fun, memo), freeVarsIn(t.arg, memo))
		memo[t] = r
		return r
	case AbsTerm:
		if r, ok := memo[t]; ok {
			return r
		}
		r := withoutVar(freeVarsIn(t.body, memo), t.v)
		memo[t] = r
		return r
	default:
		return t.Frees(nil)
	}
}

// appendDistinctVars is first followed by the variables of second it
// lacks, in a slice of its own: both inputs are memo entries.
func appendDistinctVars(first, second []VarTerm) []VarTerm {
	out := make([]VarTerm, len(first), len(first)+len(second))
	copy(out, first)
	for _, v := range second {
		if utils.None(first, v.EqualsVar) {
			out = append(out, v)
		}
	}
	return out
}

// withoutVar is vars with v left out; vars itself when v is absent.
func withoutVar(vars []VarTerm, v VarTerm) []VarTerm {
	if utils.None(vars, v.EqualsVar) {
		return vars
	}
	out := make([]VarTerm, 0, len(vars)-1)
	for _, w := range vars {
		if !w.EqualsVar(v) {
			out = append(out, w)
		}
	}
	return out
}

// typeVarsIn is the type variables of t, in the order typeVars gives
// them, over a shared DAG: memo holds the answer at the applied and
// abstraction nodes visited so far, a fact of the node alone. The
// union writes into the slices it is handed, so a memo entry is never
// handed to it: each is cloned first.
func typeVarsIn(t Term, memo map[Term][]VarType) []VarType {
	switch t := t.(type) {
	case AppliedTerm:
		if r, ok := memo[t]; ok {
			return r
		}
		r := unionTypeVars(typeVarsIn(t.fun, memo), typeVarsIn(t.arg, memo))
		memo[t] = r
		return r
	case AbsTerm:
		if r, ok := memo[t]; ok {
			return r
		}
		r := unionTypeVars(t.v.typeVars(), typeVarsIn(t.body, memo))
		memo[t] = r
		return r
	default:
		return t.typeVars()
	}
}

// unionTypeVars is the ordered union of two type variable lists, in a
// slice of its own.
func unionTypeVars(first, second []VarType) []VarType {
	return utils.OrderedSlicesUnion(
		slices.Clone(first), slices.Clone(second),
		(VarType).equalsVar, (VarType).CompareVar)
}
