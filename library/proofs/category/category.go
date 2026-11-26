// Package category is the aggregator for category theory: a category
// as a record of two carrier sets with its source, target, identity
// and composition, the functors between categories, and the
// construction of a category from its hom data, by which every category
// the corpus builds is assembled with its laws proved once — the
// subsets of a type, a preorder. Above them: the Yoneda lemma with
// presheaves valued in the sets of any type. The simplex category, the
// nerve, the quasi-categories and the homotopy category are
// simplicial/'s.
package category

import (
	_ "github.com/euc-ai/xugo/library/proofs/category/category"
	_ "github.com/euc-ai/xugo/library/proofs/category/preorder_category"
	_ "github.com/euc-ai/xugo/library/proofs/category/set_category"
	_ "github.com/euc-ai/xugo/library/proofs/category/yoneda"
)
