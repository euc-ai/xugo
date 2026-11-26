// Function-space constants for the text DSL — today just composition.
//
// These are neither arithmetic (arith.go) nor set theory (setops.go):
// they are operations on FUNCTIONS, and they enter the surface because
// theorems about maps between sets state them. `image(f ∘ g, s) =
// image(f, image(g, s))` is the motivating case — functoriality of the
// image, whose headline reads as machine text when the composition has
// to be spelled `o(f, g)`.
//
// The meta here is a SURFACE meta: a def-less α-variant of the registered
// `o` meta, used only when nothing better is available. Same precedence
// discipline as setops.go — caller scope wins, then the caller's const
// resolver, then this. The resolver has to be reached deliberately,
// because a `∘` surface never mentions `o` as a source-text name and so
// the resolver walk cannot find it on its own; walkResolverNames visits
// "o" for the ∘ binop exactly as it visits "pattern_abstraction"/"," for a pattern
// lambda.

package dsl

import (
	"github.com/euc-ai/xugo/core"
)

// The three type variables composition relates: g maps A to B, f maps B
// to C, and f ∘ g maps A to C. Kept as shared *VarTypes so the generated
// ConstTermMeta AbsType is structurally stable, mirroring setops.go's
// setElemVar discipline.
var (
	composeAVar = core.MakeVarType("A")
	composeBVar = core.MakeVarType("B")
	composeCVar = core.MakeVarType("C")
)

// ComposeMeta is `o : (B → C) → (A → B) → A → C`, function
// composition. Note the arity: `f ∘ g` is a PARTIAL application of a
// three-argument curried const, which buildAppViaMeta handles by
// instantiating from the two arguments it is given.
var ComposeMeta = core.MakeConstMeta("o",
	core.MakeFun(
		core.MakeFun(composeBVar, composeCVar),
		core.MakeFun(composeAVar, composeBVar),
		composeAVar, composeCVar))

// funcOperator returns the const meta for a recognized function-space
// infix operator symbol, or nil. Mirrors setOperator's shape so
// buildBinOp dispatches uniformly.
func funcOperator(op string) core.ConstTermMeta {
	if op == "∘" {
		return ComposeMeta
	}
	return core.ConstTermMeta{}
}
