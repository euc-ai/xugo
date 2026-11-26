// external_leaf.go — the classified external references a member cites:
// statements no section of the member proves, which the rendering must
// reach by name. The engine's resolver (EmitOptions.ResolveExternalLeaf)
// classifies each key; renderExternalLeaf lowers the classification to
// the Script call that serves the statement at replay.

package emit

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/registry"
)

// ExternalLeafKind classifies a cited statement no section proves.
type ExternalLeafKind int

const (
	// LeafConstDef: a const's defining equation (⊢ c = body), served by
	// `ctx.ConstDef(ConstName)` — or `ctx.ConstDefNormalized` when the
	// payload is the equation's normal form.
	LeafConstDef ExternalLeafKind = iota
	// LeafLibraryThm: a named theorem — a registry entry, or the
	// future entry of a session definition — served by
	// `ctx.Dep(ThmName)`, which the replay harness serves from the
	// member's dependencies.
	LeafLibraryThm
	// LeafTypeDefAxiom: one of the two axioms a type definition makes
	// available,
	//
	//	TypeDefAbsRep:  ⊢ abs(rep a) = a
	//	TypeDefPredRep: ⊢ P(r) ⇔ rep(abs r) = r
	//
	// served by `ctx.TypeDefAxiom(ConstName, TypeDefWhich)`. ConstName is
	// either half of the pair (the helper resolves orientation off the
	// pair).
	LeafTypeDefAxiom
)

// TypeDefAxiomSel picks which of a type definition's two axioms a
// LeafTypeDefAxiom names.
type TypeDefAxiomSel int

const (
	// TypeDefAbsRep: ⊢ abs(rep a) = a (TypeDefExpand's first output).
	TypeDefAbsRep TypeDefAxiomSel = iota
	// TypeDefPredRep: ⊢ P(r) ⇔ rep(abs r) = r (TypeDefExpand's second
	// output).
	TypeDefPredRep
)

// ExternalLeaf is one classified external reference.
type ExternalLeaf struct {
	Key          core.PropKey
	Kind         ExternalLeafKind
	ConstName    string          // LeafConstDef / LeafTypeDefAxiom: the const whose meta carries the statement
	ThmName      string          // LeafLibraryThm: the name ctx.Dep resolves
	TypeDefWhich TypeDefAxiomSel // LeafTypeDefAxiom: which of the two axioms
	// Stated, for a LeafLibraryThm, is the statement `ctx.Dep(ThmName)`
	// serves at replay — a registry entry's own statement, the form
	// the harness preloads under the name. nil when the resolver cannot
	// say (a session definition's theorem that has not landed as an
	// entry). Two renderings read it: a
	// payload that is a type instance of it renders as
	// ctx.AtTypes(ctx.Dep(name), τ…) with σ derived against it, and a
	// Simp rule's marker is computed against it rather than copied from
	// the record, whose bit reads against the form the SESSION served.
	Stated core.Prop
}

// ExternalLeafFromConstDefRef classifies a key the const-def index
// (registry.ConstDefIndex) maps to a definition: a const's defining equation (LeafConstDef)
// or one of a type definition's two axioms (LeafTypeDefAxiom). The
// engine's leaf resolver (EmitOptions.ResolveExternalLeaf wiring in
// engine/emit_section.go) consults it first.
func ExternalLeafFromConstDefRef(key core.PropKey, ref registry.ConstDefRef) (ExternalLeaf, bool) {
	switch ref.Kind {
	case registry.ConstDefThm:
		return ExternalLeaf{
			Key:       key,
			Kind:      LeafConstDef,
			ConstName: ref.ConstName,
		}, true
	case registry.TypeDefAbsRepEq:
		return ExternalLeaf{
			Key:          key,
			Kind:         LeafTypeDefAxiom,
			ConstName:    ref.ConstName,
			TypeDefWhich: TypeDefAbsRep,
		}, true
	case registry.TypeDefPredRepEq:
		return ExternalLeaf{
			Key:          key,
			Kind:         LeafTypeDefAxiom,
			ConstName:    ref.ConstName,
			TypeDefWhich: TypeDefPredRep,
		}, true
	}
	return ExternalLeaf{}, false
}
