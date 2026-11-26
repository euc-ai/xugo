// Package datatypes is the aggregator for the inductive-datatype
// chapters — the types the datatype door introduces, one family
// per type: list (nil / cons), whose family carries the theory of
// lists; option (none / some), whose family holds the type's principles
// alone; tree (Leaf / Node), the binary tree, whose operations reach
// across to the list theory when a tree is flattened; and first_order,
// named-variable formulas with parameterized atoms, carrier semantics
// and the uniform QE and transfer composition theorems. Each mints
// its type through the datatype door (family.DefineData), which derives
// the four principles a datatype comes with — induction, which the `induction` tactic
// dispatches on; the primitive-recursion schema, which the define
// door's equation compiler instantiates; injectivity and distinctness
// of the constructors — so a chapter's own members begin at the
// operations.
//
// # The boundary
//
// Placement follows the definitional layer. A datatype is
// carved out of the recursive-type universe `recspace(A)` by a type
// definition whose representatives are the
// recspace_node-trees its constructors build, so a datatype's principles are
// derived through that type definition — the abs/rep bijection and the
// inductive predicate that picks the representatives out — and through
// the universe's own theorems, never through a number domain. That is
// why these chapters are a domain of their own rather than families
// under nat_num, whose objects the universe merely mentions: the
// definitions close here. The universe's own theory — the pairing
// functions and injections that encode a tree as a predicate, the
// inductive universe is_recspace and the type carved from it, the
// constructors' injectivity, induction and recursion theorems — is the
// domain's floor, datatype_universe, which the datatype door's derivations read.
package datatypes

import (
	_ "github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	_ "github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	_ "github.com/euc-ai/xugo/library/proofs/datatypes/list"
	_ "github.com/euc-ai/xugo/library/proofs/datatypes/option"
	_ "github.com/euc-ai/xugo/library/proofs/datatypes/tree"
)
