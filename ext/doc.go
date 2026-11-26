// Package ext is the term layer over the kernel: the wrapper terms are
// built and read through, and the logical constants defined from
// equality and the choice operator.
//
// The wrapper has an untyped face (TermWrapper, term_wrapper.go) and a
// typed one (Expr, expr.go), whose Go type parameter is a phantom
// standing for the term's HOL type (holtype_phantom.go). basic_defs.go
// defines ⊤, ⊥, ¬, ∧, ∨, ⇒, ∀, ∃ and ∃! and states the axiom of
// infinity; excluded middle is a theorem, derived from the choice
// operator in prop/bootstrap.go. Beside them sit β- and η-reduction, subterm access, the
// numeral encoding, the printers, and the protobuf form of a type and
// of a term.
//
// The sub-packages build on this one: prop (propositions and
// rewriting), unify (higher-order unification), clause (clausal form),
// dsl (the statement text), dimtypes (the dimension phantoms), on (the
// carrier phantoms) and skeleton (a term's structural skeleton).
package ext
