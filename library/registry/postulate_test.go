package registry

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// The corpus has one postulate, the axiom of infinity: it registers
// like a card — a statement, a key, no proof — but is no card; it
// introduces the type `ind`, which the parser knows from it alone; it
// is served at the term its chapter builds, which must be its
// statement; and the registry refuses a second.
func TestPostulate_TheAxiomOfInfinityAlone(t *testing.T) {
	var postulates []*ProofEntry
	for _, e := range All() {
		if e.IsPostulate() {
			postulates = append(postulates, e)
		}
	}
	require.Len(t, postulates, 1, "the corpus assumes one axiom outright")
	infinity := postulates[0]
	require.Equal(t, "peano.Infinity", infinity.Name)
	require.True(t, infinity.ServedAsAxiom())
	require.False(t, infinity.IsCard(), "the postulate is no card: it is not debt")
	require.Nil(t, infinity.Build.Fn)
	require.True(t, infinity.PostulateTerm().AlphaEquals(infinity.Statement().Prop))
	require.Equal(t, "ind", infinity.Build.Postulate.Type)
	arity, known := GetConstMetaManager().TypeArity("ind")
	require.True(t, known, "the type the postulate introduces is in the parser's vocabulary")
	require.Equal(t, 0, arity)

	p := ext.Var("p", core.TypeBool())
	fam := NewFamily("zz_postulate", nil)
	require.PanicsWithValue(t,
		"proof registry: zz_postulate.Second is a second postulate — the corpus assumes one axiom outright, peano.Infinity",
		func() {
			fam.Add(ProofEntry{
				Name:  "Second",
				Build: fam.Postulate("atom", "∀p:bool. p ⇒ p", func() ext.Term { return ext.ForAll(p)(p.Imply(p)) }),
			})
		})

	// A term that is not the statement is refused where it is minted.
	built := infinity.Build.Postulate.Term
	defer func() { infinity.Build.Postulate.Term = built }()
	infinity.Build.Postulate.Term = func() ext.Term { return ext.ForAll(p)(p.Imply(p)) }
	require.Panics(t, func() { infinity.PostulateTerm() })
}
