// Package prop is the proposition layer over ext: a wrapper around the
// kernel's propositions whose methods are the inference rules, the
// laws of the logical constants, and the rewriting system.
//
// prop_wrapper.go spells the kernel's rules, and the rules derived from
// them, as methods of PropWrapper. bootstrap.go states the laws of the
// connectives and the quantifiers, and bootstrap_proof.go proves them.
// A Rewrite (rewrite.go) takes a term t to a theorem ⊢ t = t′;
// normalize.go composes rewrites into the normalization of a term and
// of a proposition.
package prop
