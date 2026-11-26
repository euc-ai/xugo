// alphabet.go — the chapter's alphabet served at any type instance.
//
// vocab.go declares this chapter's constants for THIS chapter, at one
// type instance per Script: that is what a member's own statements need
// and it is all they need. A consumer builds in its own Script, and
// `prod` is a polymorphic type it meets at its own instance — the integer
// division chapter at (int, int), the monoidal iterates at (A, C) — so a
// consumer cannot use the chapter's declarations as they stand.
//
// The functions here are that alphabet parameterized by the component
// types. They are the chapter's declaration surface, the same way the
// entry vars are its theorem surface: a consumer names the types it
// works at, and the family — which owns `prod` — answers with the
// types and handles, so the spelling lives in one place.
//
// They declare into ctx's ParseScope and return build handles, which is
// what `ctx.Const` does; re-declaring a name a Script already carries
// does not displace the existing binding, so a consumer may call these
// alongside its own vocabulary rows without ordering care.

package pairs

import (
	"github.com/euc-ai/xugo/core"
	. "github.com/euc-ai/xugo/library/authoring"
)

// ProdType is `prod(a, b)`, the product of two component types.
//
// Exported because the type is as much part of the chapter's surface as
// the projections are: a consumer that states a function on pairs needs
// to name it, and `MakeType("prod", …)` spelled at a call site is a
// claim about this chapter's representation made outside it.
func ProdType(a, b core.HolType) core.HolType { return MakeType("prod", a, b) }

// ProjectionsAt declares fst and snd at component types (a, b) and
// returns their build handles — `prod(a, b) → a` and `prod(a, b) → b`.
//
// The two are returned together because no consumer has ever wanted one
// alone: a projection pair is how a pair-valued term is taken apart, and
// `PairCollapse` consumes both certificates in one call.
func ProjectionsAt(ctx *Script, a, b core.HolType) (fst, snd *TermWrapper) {
	prod := ProdType(a, b)
	return ctx.Const("fst", MakeFun(prod, a)), ctx.Const("snd", MakeFun(prod, b))
}

// PairAt declares the pairing constructor `,` at component types (a, b)
// and returns its handle — `a → b → prod(a, b)`.
//
// The constructor a consumer needs to BUILD a pair term with. Statements
// get `(x, y)` from the text-DSL without any declaration; this is for
// the build side.
func PairAt(ctx *Script, a, b core.HolType) *TermWrapper {
	return ctx.Const(",", MakeFun(a, MakeFun(b, ProdType(a, b))))
}

// Collapse drives every fst/snd-of-a-literal-pair redex out of the goal,
// to fixpoint — `proof.PairCollapse` at this chapter's own projection
// theorems.
//
// The primitive takes the two rules as arguments because it is general:
// it collapses ANY pair of projections against ANY constructor, and
// `prover/proof` sits below the corpus so it cannot reach `Fst` and `Snd`
// itself. That layering is right and is not the thing to change — the
// argument-passing it forces is what this function removes, from the
// side that CAN name them. The caller still reads `pairs.Fst` and
// `pairs.Snd` itself — `ctx.Dep` on the caller's own script claims
// them — so the caller's recorded deps carry them and bound its replay.
func Collapse(ctx *Script) Action {
	return PairCollapse(ctx.Dep(Fst), ctx.Dep(Snd))
}
