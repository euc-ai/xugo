// Package authoring is the bare-name surface a proof file is written
// in: the constructors, values and types a chapter's proof body spells
// without a qualifier.
//
// A proof file brings the surface into its own scope with a dot
// import, the one dot import in the module:
//
//	import . "github.com/euc-ai/xugo/library/authoring"
//
// A dot-imported name belongs to the importing FILE and is no
// declaration of the importing package. A chapter's package therefore
// exports its own members and nothing of this surface: `go doc` on a
// chapter lists the chapter, and the surface is documented once, here.
// What an author meets of the mechanism:
//
//   - A file that spells a name of the surface without the import
//     fails "undefined: By". A file that spells none carries no
//     import: Go refuses an unused one.
//   - A chapter's package-level declaration that takes a name of the
//     surface is a compile error, "By already declared through
//     dot-import". The chapter's name is the one renamed: the surface
//     has priority, which keeps emit-section output paste-clean.
//   - Generated theorem wrappers use these same aliases and import
//     this package where they use its names. Pipeline names outside
//     the surface retain their own package qualifiers.
//   - The names are another package's, initialized before any
//     variable of a chapter. An entry whose proof spells them waits
//     for nothing on their account, so a chapter's entries register in
//     declaration order — its files taken by name — moved only by the
//     entry variables an initializer names.
//
// Two files hold the surface. This one is written by hand: the names
// that are not prover constructors (core, ext, dsl, prop), the Script
// entry points, the corpus's own spellings (Case, Arith), By's shaping
// options, and the types — the proof types, the typed surface's
// shorthands, and the phantoms of the types no chapter mints.
// zz_constructors_gen.go is generated: every exported constructor of
// prover/proof that library/registry/aliasgen's rule selects, minus the
// names this file declares, which win. After adding a constructor to
// prover/proof, regenerate:
//
//	go generate ./library/authoring/
//
// TestAliasGenCurrent re-renders the generated file and fails while it
// is stale.
//
// The phantom of a type a chapter mints (list.List,
// complex_field.Complex) is declared beside its mint and is not here:
// this package imports no chapter. Where a chapter's statements name
// such a type, its generated wrapper file aliases the phantom from its
// owner.
//
//go:generate go run github.com/euc-ai/xugo/library/cmd/gen_authoring
package authoring

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dimtypes"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/on"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

var (
	MakeFun     = core.MakeFun
	MakeVarType = core.MakeVarType[string]
	TypeBool    = core.TypeBool()
	NumType     = dsl.NumType
	MakeType    = ext.MakeType

	Var    = ext.Var
	ForAll = ext.ForAll
	Exists = ext.Exists
	Not    = ext.Not
	Cond   = ext.Cond

	// True and False are the truth constants, under full names: the only
	// capital letters this surface exports are the statement letters A–E
	// (TestSurfaceSpellsNoOtherLetter), so that a letter a family's
	// statements bind beyond them is the family's own phantom.
	True  = ext.T
	False = ext.F

	MakeProp    = prop.MakeProp
	Normalize   = prop.Normalize
	DerivesTrue = prop.DerivesTrue

	NewScript         = proof.NewScript
	NewScriptForEntry = proof.NewScriptForEntry

	// Equal is the equation l = r as a term, over typed wrappers and core
	// terms alike (proof.Equal); a typed wrapper has no untyped method set.
	Equal = proof.Equal

	// Lambda is the abstraction λv. body as a term (proof.Lambda): the
	// Go-built λ over typed handles, where text cannot type a closure's
	// parameter applied inside it.
	Lambda              = proof.Lambda
	CapabilityArithNat  = proof.CapabilityArithNat
	CapabilityArithReal = proof.CapabilityArithReal

	// CoerceDomain's arguments — a chapter's ambient numeric domain
	// (a VocabSpec.CoerceDomain row, or Script.CoerceDomain directly).
	RealDomain = proof.RealDomain
	IntDomain  = proof.IntDomain

	// Script.TypeDefAxiom's selector — which of a type definition's two
	// axioms a cite names: ⊢ abs(rep a) = a, or ⊢ P(r) ⇔ rep(abs r) = r.
	TypeDefAbsRep  = proof.TypeDefAbsRep
	TypeDefPredRep = proof.TypeDefPredRep

	// NewHypHandle — named hypothesis references (prover/proof/hyp_handle.go):
	// bind with <handle>.From(<introducing action>), use with .Ground /
	// .Rw / .Subst / Clear(...). A proof body names a hypothesis by its
	// handle and never by a positional index.
	NewHypHandle = proof.NewHypHandle

	// Arith is the unified arithmetic ministep, gated by the per-proof
	// self-circularity check (prover/solver/omega/circularity.go): while a
	// target is being built, any bundle whose foundation list
	// contains the target is silently removed from Arith's dispatch, so
	// Arith is sound by construction in proofs. A member's constructors
	// go through NewScriptForEntry, so Arith reads the target's identity
	// and its capabilities from the harness-armed ProofScope (the
	// registry entry) and never from the proof text. The general rule
	// still applies: do not expand a proof's tool base beyond what its
	// seed used.
	Arith = proof.Arith

	// Case — the corpus name for proof.MakeCase (the label+body wrapper
	// every Split*/Assert/ByCase step takes). The generated file also
	// declares MakeCase; both resolve to the same func.
	Case = proof.MakeCase

	// Opening — the opened section: `Theorem(text, Opening(Unfold(RealSumDef),
	// func(a *Argument, …) {…}))` runs the opening move on the section
	// root before the closure's binders are bound. It returns `any` (a
	// body wrapper), which the generator's result-type rule does not
	// select, so it is declared here.
	Opening = proof.Opening

	// By's shaping options — VALUES in a premise list, not verbs
	// (prover/proof/fact.go). The denote shaping is DenotedAs(name,
	// term) / HilbertDenotedAs(name, term), in the generated file: it
	// says what is being named. The size-threshold Denoted() is a search
	// stage and is not on this surface (aliasgen's retiredNames).
	//
	// TWO triggers, both in prover/proof/fact.go, and only the first is
	// a failure diagnosis: (1) a By close fails with NO cleared hyps to
	// blame — a shape problem rather than a missing premise; (2) the
	// close would REACH THE REFUTER on a leaf Basic() settles, where
	// nothing is wrong with the premise list and the cost is a minted
	// CNF key. By's own MISS message decides case (2) for you.
	Normalized     = proof.Normalized
	HilbertDenoted = proof.HilbertDenoted
	PreNormalized  = proof.PreNormalized
	Raw            = proof.Raw

	// Broadcast — the premise-list option that runs a By's terminal
	// closer over EVERY leaf the shaping left open (opt-in; for the
	// close whose Normalized/Denoted shaping fans the residual into
	// leaves that each close by the same refutation).
	Broadcast = proof.Broadcast

	// TypeBinder — the letter-binding namespace for explicit type
	// instances: TypeBinder.BindA[Real]() reads "bind the statement's A
	// to Real". It is a VALUE carrying generic methods, which is what
	// lets one line put the whole alphabet in scope — the letters as
	// generic FUNCTIONS could not be aliased at all
	// (utils/generic_test.go).
	TypeBinder = proof.TypeBinder
)

// The proof types.
type (
	ProverEnv        = proof.ProverEnv
	Thm              = proof.Thm     // the interface — Build returns this
	ThmCert          = proof.ThmCert // the realized certificate
	Proof            = proof.Proof
	Script           = proof.Script
	GoalStackNode    = proof.GoalStackNode
	TermWrapper      = ext.TermWrapper
	Prop             = core.Prop
	HolType          = core.HolType
	Action           = proof.Action
	PolyConstWrapper = proof.PolyConstWrapper
	HypHandle        = proof.HypHandle
	CalcRel          = proof.CalcRel
	CalcOrder        = proof.CalcOrder
	Term             = proof.Term
	TermLike         = proof.TermLike    // a core term or a typed wrapper: what a term-taking verb accepts
	Fact             = proof.Fact        // the fact VALUE (noun); the verb is Cite
	Argument         = proof.Argument    // Derive's deduction context
	TypeBinding      = proof.TypeBinding // one letter of an explicit type instance
)

// The shorthands for ext's typed surface: TypePhantom is the phantom
// constraint, Expr the generic typed term, Typed the parameter currency
// every theorem wrapper flows into, Arrow/Arrow2 the arrow family
// binder closures declare their function parameters in (born
// applicable), and the rest the phantom vocabulary — the letter
// phantoms A–E (hand code instantiates at them: Inst[B], BindA[B]()),
// Bool and the concrete `:num`, and the structural constructors. A
// letter beyond E is declared by the generated wrapper file of each
// family whose statements bind it (library/registry/typedgen,
// OwnerOfLetter).
type (
	TypePhantom                  = ext.TypePhantom
	Expr[T TypePhantom]          = ext.Expr[T]
	Typed[T TypePhantom]         = ext.Typed[T]
	Arrow[X, Y TypePhantom]      = ext.Arrow[X, Y]
	Arrow2[X, Y, R TypePhantom]  = ext.Arrow2[X, Y, R]
	Bool                         = ext.Bool
	Nat                          = ext.Nat
	A                            = ext.A
	B                            = ext.B
	C                            = ext.C
	D                            = ext.D
	E                            = ext.E
	Fun[X, Y TypePhantom]        = ext.Fun[X, Y]
	Fun2[X, Y, R TypePhantom]    = ext.Fun2[X, Y, R]
	Fun3[X, Y, Z, R TypePhantom] = ext.Fun3[X, Y, Z, R]
	Set[X TypePhantom]           = ext.Set[X]
	Op[X TypePhantom]            = ext.Op[X]
	Prod[X, Y TypePhantom]       = ext.Prod[X, Y]
)

// The phantoms of the types no chapter mints: a phantom is declared
// beside its type's mint (ext/holtype_phantom.go), and these two are
// minted below the chapters, so every chapter reads them from here.
// TestAuthoringDeclaresTheFrameworkPhantoms (library/registry/typedgen)
// holds this block against the generator's table of mints.
type (
	Real = dsl.Real
	Int  = dsl.Int

	// A member's statement written in parts, and the abbreviations
	// its texts spell as «Name» (ext/dsl/statement.go).
	Statement    = dsl.Statement
	Abbrev       = dsl.Abbrev
	Abbreviation = dsl.Abbreviation
)

// IntegerPolynomial is the Go type of an integer polynomial, the HOL type
// (num → num) → int: a coefficient for every monomial, a monomial an
// exponent for every variable name. It is the atom of a first-order
// formula over a ring or a field. A function type has no constructor a
// generated wrapper could name it by, so every chapter that spells the
// type reads it here.
type IntegerPolynomial = Fun[Fun[Nat, Nat], Int]

// The dimension-refined surface (ext/dimtypes, prover/proof/vec.go): a
// vector read at one dimension is a Vec at that dimension's phantom,
// a matrix read at a row and a column dimension is a Mat at both, and a
// map between two vector spaces is a VecFun at the dimension it is read on
// and the dimension its values are read at.
// A vector or matrix whose membership is an antecedent of the statement
// cited arrives as an Inhabited / InhabitedMat, its evidence bundled
// with the cite. DimN, DimM and DimK are the dimension letters n, m and
// k, named apart from the statement letters N, M and K; SomeDim is the
// dimension no letter spells, the phantom of a vector anchored at a
// given term (a.VecAt) or at the dimension its membership fact spells
// (proof.InhabitFrom).
type (
	DimPhantom                                            = dimtypes.DimPhantom
	Vec[Elem TypePhantom, Dim DimPhantom]                 = dimtypes.Vec[Elem, Dim]
	Mat[Elem TypePhantom, Rows, Cols DimPhantom]          = dimtypes.Mat[Elem, Rows, Cols]
	VecFun[Elem TypePhantom, Source, Target DimPhantom]   = dimtypes.VecFun[Elem, Source, Target]
	Inhabited[Elem TypePhantom, Dim DimPhantom]           = proof.Inhabited[Elem, Dim]
	InhabitedMat[Elem TypePhantom, Rows, Cols DimPhantom] = proof.InhabitedMat[Elem, Rows, Cols]
	DimN                                                  = dimtypes.DimN
	DimM                                                  = dimtypes.DimM
	DimK                                                  = dimtypes.DimK
	SomeDim                                               = dimtypes.SomeDim
)

// Member is a point with its membership in a carrier of the structure
// a law is read at (prover/proof/member.go), the carrier a phantom of
// package on (`*Member[A, on.C]`): a reading whose antecedent holds the
// memberships of its witnesses takes Members of its carrier and bundles
// their evidence with the cite, as an Inhabited vector's rides its own.
// A structure law's closure binds its guarded points as Members.
type Member[X TypePhantom, Car on.Carrier] = proof.Member[X, Car]
