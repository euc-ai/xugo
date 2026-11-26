// Package tower is the aggregator for the real-number construction
// tower's five family sub-packages (internal/eudoxus_slope,
// internal/nonneg_real, internal/nonneg_real_formal_diff,
// real_construction, real_completeness).
//
// The blank imports below are the package's whole content, and they do
// two jobs: they compile the tower's typed-dep DAG — a cross-family
// cycle is an import cycle — and they trigger the families'
// registration into registry. The ℝ domain aggregator one level
// up (proofs/real) imports this one package rather than five, because
// Go's internal/ rule keeps it from reaching the construction families
// directly.
//
// That rule is also why the tower is a directory and not five siblings
// under real/: internal/{eudoxus_slope,nonneg_real,nonneg_real_formal_diff}
// are importable only from packages rooted HERE, so a future ℝ theory
// chapter (proofs/real/…, outside this directory) cannot reach past the
// tower's output layer. "Downstream cites real_construction and
// real_completeness, never the construction" is a compile error rather
// than a convention.
//
// The chapter narrative — what the tower constructs and why each layer
// exists — is README.md here.
package tower

import (
	_ "github.com/euc-ai/xugo/library/proofs/real/tower/internal/eudoxus_slope"
	_ "github.com/euc-ai/xugo/library/proofs/real/tower/internal/nonneg_real"
	_ "github.com/euc-ai/xugo/library/proofs/real/tower/internal/nonneg_real_formal_diff"
	_ "github.com/euc-ai/xugo/library/proofs/real/tower/real_completeness"
	_ "github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
)
