package proof

import (
	"strings"
	"testing"
)

// The text DSL spells τ → bool as set(τ); no datatype may take that
// name — a type minted under it could never be spelled.
func TestAnalyzeDataDefinitionRefusesTheSetAlias(t *testing.T) {
	_, err := AnalyzeDataDefinition("set", []string{"A"}, []DataConstructorSpec{
		{Name: "mkset", Args: []string{"A"}},
	}, nil, nil)
	if err == nil || !strings.Contains(err.Error(), "τ → bool") {
		t.Fatalf("expected the alias refusal, got %v", err)
	}
}
