// Package iterate collects folds over sets and their numerical sums and products.
//
// The domain has four parts:
//
// - monoidal proves the general mechanism: the neutral element, support,
// recursion, transport, regrouping and algebra of iterated_op.
// - nat, real and int each hold one carrier's chapters, a sum and a
// product, which read the mechanism at the carrier's addition and its
// multiplication. A chapter sits on its carrier's algebra and on no
// other carrier's, so each directory is one height: ℕ's chapters sit
// lowest, and ℤ's above ℝ's, since ℤ is built inside ℝ.
// - nat_sum and real_sum develop counting, order and interval laws;
// int_sum provides recursion and transport into the reals. The products
// give recursion, constant products, signs, bounds and zero factors.
//
// # The boundary
//
// Placement follows the definitional layer, and this domain is the
// join point the definitions name. An instance constant is DEFINED as
// `iterated_op` at a fixed operation — `real_sum = iterated_op real_add` — so its
// definitional layer closes above the fold mechanism AND above the
// carrier's algebra at once: below this domain sit `sets/` (the index
// side) and the carrier domain (the value side), and neither alone can
// hold the definition. Placing Σ under `real/` would read the value
// type and ignore the mechanism; scattering the instances across their
// carrier domains would hide that they are one subject read at six
// operations.
//
// The mechanism's index sets connect it to sets/. The finite-set
// cardinality function `card`, in sets/cardinality, is an
// invariant of the set itself. A fold consumes an operation and an
// arbitrary function, with the set supplying its indices. Its subject
// is the operation's algebra, which places the mechanism in this domain.
package iterate

import (
	_ "github.com/euc-ai/xugo/library/proofs/iterate/int/int_product"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/int/int_sum"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_product"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/real/real_product"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
)
