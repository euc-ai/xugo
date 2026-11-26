// Package core is the kernel: the types, terms and theorems of
// higher-order logic, and the primitive inference rules every theorem
// is derived by.
//
// A proved theorem is a ThmCert. Outside this package a certificate
// comes from a primitive rule — those of primitives.go, and
// ConstTermMeta.TypeDefExpand, which yields the two theorems a type
// definition stands for — or from a promise (ThmPromise) the kernel
// has settled against one; the constructor the rules share is
// unexported, so the packages above — ext, prover, engine, the library
// — derive theorems and do not make them. TestThm is the one
// exported constructor, and is named for the test binaries it is for.
// A violated invariant panics. Of the rules, two state assumptions
// rather than reasoning steps: η-conversion and the axiom of choice.
// The kernel states no axiom; every axiom is the library's, minted by
// NewAxiom. README.md lists the rules, and describes how what the
// kernel trusts is audited.
package core
