// INPUT LAYER — the agent-facing prop text DSL lives in `ext/dsl`. This
// file re-exports its types under engine names.

package engine

import "github.com/euc-ai/xugo/ext/dsl"

// ---------------------------------------------------------------------------
// Re-exports of ext types/functions kept for back-compat with existing
// engine callers and tests. New code should call ext directly.
// ---------------------------------------------------------------------------

type ParseResult = dsl.ParseResult
type InputDiagnostic = dsl.InputDiagnostic
type Normalization = dsl.TextSymbol

const (
	CodeParseError    = dsl.CodeParseError
	CodeMissingType   = dsl.CodeMissingType
	CodeTypeMismatch  = dsl.CodeTypeMismatch
	CodeArityMismatch = dsl.CodeArityMismatch
	CodeUnknownSymbol = dsl.CodeUnknownSymbol
	CodeCorePanic     = dsl.CodeCorePanic
	CodeValidation    = dsl.CodeValidation
)

// Parse parses a text-format proposition. JSON proposition ingress was
// removed with the json_cleanup migration — agents pass propositions
// either as text (here) or via PropInput in JSON envelopes.
func Parse(raw string) ParseResult { return dsl.ParsePropText(raw) }

// NormalizeSymbols re-exports the ext-level symbol normalizer.
func NormalizeSymbols(input string) (string, []Normalization) {
	return dsl.NormalizeTextSymbols(input)
}
