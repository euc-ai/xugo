package proof

import (
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

var (
	setBuilderOnce  sync.Once
	setBuilderMetas map[string]core.ConstTermMeta
)

// setBuilderVocabulary is the three constants a set-builder membership
// is spelled with, each minted with its definition as the set_basic
// chapter defines it — set_member = λx s. s(x), set_comprehension =
// λp. p, comprehension_spec = λv p t. p ∧ v = t — for a parse scope's
// ConstMetas, so the membership reading applies in a test that serves
// no library (a surface constant without a definition is not read).
// Minted once: a constant's name is unique.
func setBuilderVocabulary() map[string]core.ConstTermMeta {
	setBuilderOnce.Do(func() {
		A := core.TypeA()
		set := core.MakeFun(A, core.TypeBool())
		x, s := ext.Var("x", A), ext.Var("s", set)
		member := core.NewConstDef(x.To(s.To(s.Apply(x))), "set_member")
		q := ext.Var("q", set)
		comprehension := core.NewConstDef(q.To(q), "set_comprehension")
		v, condition, t := ext.Var("v", A), ext.Var("condition", core.TypeBool()), ext.Var("t", A)
		spec := core.NewConstDef(v.To(condition.To(t.To(condition.And(v.Eq(t))))), "comprehension_spec")
		setBuilderMetas = map[string]core.ConstTermMeta{
			"set_member":         member.Meta(),
			"set_comprehension":  comprehension.Meta(),
			"comprehension_spec": spec.Meta(),
		}
	})
	return setBuilderMetas
}
