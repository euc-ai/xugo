package de_rham_thom

import (
	_ "embed"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/compact_de_rham"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/smooth_projection_bundle"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed de_rham_thom.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/de_rham_thom", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
