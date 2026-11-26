// define_rules.go — the default use rules a definition carries, derived
// from its SHAPE (the manual's R4: installation is part of definition; the
// rules are not stored with the declaration, they are derived from the
// shape it was served in).
//
// One function answers "what does this definition install into a simp
// set?" for every door: the session `define` RPC's three install points
// (the equation shapes on return, the WF and spec shapes on the close
// of their obligation, the data shape's derived-theorem sections) and a
// family import reading a registered entry. Each door hands over the
// shape it served and the proved characterizing theorem — the session
// its section's promise, an importer the entry's replay promise — and
// gets back the rules with their certificates, so the two sides cannot
// drift: there is no second copy of the dispatch to keep aligned, and
// the shape travels as a VALUE on the entry (registry.ProofEntry.
// Definition), computed once at registration, never re-analyzed from
// the equations at import.
//
// The dispatch, per shape:
//
//   - DIRECT / RECURSIVE: the characterizing theorem WHOLE (a
//     conjunction is a valid simp_with rule; the per-clause projection
//     was measured a phantom — define-move notes).
//   - WF: the guarded readings derived from the COND equation
//     (DeriveWFReadings) — an unconditional unfold rule would rewrite
//     every occurrence on sight.
//   - DATA: the INJ and DISTINCT derived theorems are rules, each its
//     own; INDUCT and RECURSION are principles (induction and the
//     equation compiler read them by name), never rewrites.
//   - SPEC: nothing — a specification is not a directed rewrite
//     (divmod's `m = nat_div(m, n) * n + nat_mod(m, n)` has a bare-variable LHS);
//     the author cites the characterizing theorem.

package proof

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
)

// DefinitionShape names the shape a definition door served — the one
// input the default-rule derivation dispatches on. The zero value marks
// an entry that is not a definition.
type DefinitionShape int

const (
	NotADefinition DefinitionShape = iota
	// DefinitionDirect — one definiendum-free
	// equation, λ-mint.
	DefinitionDirect
	// DefinitionRecursive — constructor-clause equations compiled
	// against the carrier's recursion schema.
	DefinitionRecursive
	// DefinitionWF — one total COND equation with a measure; the
	// termination obligation is the author's.
	DefinitionWF
	// DefinitionSpec — constants introduced by
	// choice against a specification.
	DefinitionSpec
	// The datatype shape registers one theorem per derived kind; each
	// carries its kind as its shape.
	DefinitionDataInduct
	DefinitionDataRecursion
	DefinitionDataInj
	DefinitionDataDistinct
	// The inductive shape registers one theorem per derived kind
	// (Rules / Induct / Cases); none is a rewrite rule.
	DefinitionInductiveRules
	DefinitionInductiveInduct
	DefinitionInductiveCases
	DefinitionInductiveInductStrong
	// The quotient shape registers one theorem per derived kind; Eq
	// (mk(x) = mk(y) ⇔ R(x, y)) is the one rewrite rule among them —
	// Lean's simp-marked Quotient.eq.
	DefinitionQuotientSurjectivity
	DefinitionQuotientInduct
	DefinitionQuotientSound
	DefinitionQuotientExact
	DefinitionQuotientEq
	DefinitionQuotientForallOnImage
	DefinitionQuotientExistsOnImage
	// DefinitionLift — a function on classes, stated by its computation
	// rules at the class map (define_lift.go); the rules install whole,
	// as the recursive shape's equations do.
	DefinitionLift
)

func (s DefinitionShape) String() string {
	switch s {
	case NotADefinition:
		return "not a definition"
	case DefinitionDirect:
		return "direct"
	case DefinitionRecursive:
		return "recursive"
	case DefinitionWF:
		return "wf"
	case DefinitionSpec:
		return "spec"
	case DefinitionDataInduct:
		return "data:INDUCT"
	case DefinitionDataRecursion:
		return "data:RECURSION"
	case DefinitionDataInj:
		return "data:INJ"
	case DefinitionDataDistinct:
		return "data:DISTINCT"
	case DefinitionInductiveRules:
		return "inductive:RULES"
	case DefinitionInductiveInduct:
		return "inductive:INDUCT"
	case DefinitionInductiveCases:
		return "inductive:CASES"
	case DefinitionInductiveInductStrong:
		return "inductive:INDUCT_STRONG"
	case DefinitionQuotientSurjectivity:
		return "quotient:SURJECTIVITY"
	case DefinitionQuotientInduct:
		return "quotient:INDUCT"
	case DefinitionQuotientSound:
		return "quotient:SOUND"
	case DefinitionQuotientExact:
		return "quotient:EXACT"
	case DefinitionQuotientEq:
		return "quotient:EQ"
	case DefinitionQuotientForallOnImage:
		return "quotient:FORALL_ON_IMAGE"
	case DefinitionQuotientExistsOnImage:
		return "quotient:EXISTS_ON_IMAGE"
	case DefinitionLift:
		return "lift"
	}
	return fmt.Sprintf("DefinitionShape(%d)", int(s))
}

// QuotientDefinitionShape maps a quotient's derived-theorem kind to
// the shape its entry carries.
func QuotientDefinitionShape(k QuotientTheoremKind) DefinitionShape {
	switch k {
	case QuotientSurjectivity:
		return DefinitionQuotientSurjectivity
	case QuotientInduct:
		return DefinitionQuotientInduct
	case QuotientSound:
		return DefinitionQuotientSound
	case QuotientExact:
		return DefinitionQuotientExact
	case QuotientEq:
		return DefinitionQuotientEq
	case QuotientForallOnImage:
		return DefinitionQuotientForallOnImage
	case QuotientExistsOnImage:
		return DefinitionQuotientExistsOnImage
	}
	panic(fmt.Sprintf("QuotientDefinitionShape: unknown kind %v", k))
}

// InductiveDefinitionShape maps an inductive definition's derived
// theorem kind to the shape its entry carries.
func InductiveDefinitionShape(k InductiveTheoremKind) DefinitionShape {
	switch k {
	case InductiveRules:
		return DefinitionInductiveRules
	case InductiveInduct:
		return DefinitionInductiveInduct
	case InductiveCases:
		return DefinitionInductiveCases
	case InductiveInductStrong:
		return DefinitionInductiveInductStrong
	}
	panic(fmt.Sprintf("InductiveDefinitionShape: unknown kind %v", k))
}

// DataDefinitionShape maps a datatype's derived-theorem kind to the
// shape its entry carries.
func DataDefinitionShape(k DataTheoremKind) DefinitionShape {
	switch k {
	case DataInduct:
		return DefinitionDataInduct
	case DataRecursion:
		return DefinitionDataRecursion
	case DataInj:
		return DefinitionDataInj
	case DataDistinct:
		return DefinitionDataDistinct
	}
	panic(fmt.Sprintf("DataDefinitionShape: unknown kind %v", k))
}

// DefinitionRule is one default use rule: the statement a simp set
// installs and the proved backing that closes the rule child simp_with
// surfaces.
type DefinitionRule struct {
	Rule core.Prop
	Cert core.Thm
}

// DefinitionSimpRules derives the default simp rules of a definition
// from the shape it was served in and its PROVED characterizing
// theorem (a promise is fine — the derivations are promise-
// transparent). The certificate currency is the caller's: a session
// passes its definition section's promise, an importer the entry's
// replay promise. Every rule returned certifies from `characterizing`
// alone.
//
// An error is an engine fault, not an authoring outcome: the
// characterizing statement is machine-made by the door that served
// the shape, so a shape whose derivation does not apply to it is a
// contract break between the door and this function.
func DefinitionSimpRules(shape DefinitionShape, characterizing core.Thm) ([]DefinitionRule, error) {
	if characterizing == nil {
		return nil, fmt.Errorf("definition rules (%s): nil characterizing theorem", shape)
	}
	switch shape {
	case DefinitionDirect, DefinitionRecursive, DefinitionDataInj, DefinitionDataDistinct,
		DefinitionQuotientEq, DefinitionLift:
		return []DefinitionRule{{Rule: characterizing, Cert: characterizing}}, nil
	case DefinitionWF:
		readings, err := DeriveWFReadings(characterizing)
		if err != nil {
			return nil, fmt.Errorf("definition rules (%s): %w", shape, err)
		}
		rules := make([]DefinitionRule, len(readings))
		for i, r := range readings {
			thm, ok := r.(core.Thm)
			if !ok {
				return nil, fmt.Errorf("definition rules (%s): reading %d is not promise-backed (%T)",
					shape, i, r)
			}
			rules[i] = DefinitionRule{Rule: r, Cert: thm}
		}
		return rules, nil
	case DefinitionSpec, DefinitionDataInduct, DefinitionDataRecursion,
		DefinitionInductiveRules, DefinitionInductiveInduct, DefinitionInductiveCases,
		DefinitionInductiveInductStrong,
		DefinitionQuotientSurjectivity, DefinitionQuotientInduct, DefinitionQuotientSound,
		DefinitionQuotientExact, DefinitionQuotientForallOnImage, DefinitionQuotientExistsOnImage:
		// Nothing installs: a specification and the principles are
		// not rewrite rules, an inductive definition's Cases theorem
		// would rewrite the relation into itself, and a quotient's
		// bridges are implications and image laws, not rewrites.
		return nil, nil
	case NotADefinition:
		return nil, fmt.Errorf("definition rules: the entry is not a definition")
	}
	return nil, fmt.Errorf("definition rules: unknown shape %s", shape)
}
