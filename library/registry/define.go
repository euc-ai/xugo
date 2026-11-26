// define.go — family.Define: the form of the definition move.
// The emitted / hand-written twin of the session `define` RPC:
// ONE entry whose registration MINTS the constant and whose Build
// re-derives the characterizing theorem through the same composite
// step the session recorded — the record/emit/replay principle at
// ENTRY granularity.
//
// Two-phase by necessity, and the phases are the nat_divides pattern
// promoted into the framework:
//
// - REGISTRATION TIME (package var init): parse the equation with
// the definiendum declared (the strict door — prover/proof
// ParseDefinitionEquation), mint via core.NewConstDef, register
// the meta process-globally with the EXCLUSIVE check. Eager
// because constant identity must exist before any later parse —
// other members' headlines, other chapters' texts — and Go
// package-init order is what sequences "definition before use".
// - BUILD TIME (replay): re-parse the SAME equation literal under
// the family vocabulary — the constant now resolves as a CONST,
// so the literal reads as the characterizing statement — and
// close it with the one composite _DefineStep. An init-parse vs
// vocab-parse divergence in MEANING cannot close and fails the
// replay loudly (the two-scope tripwire).
//
// The entry's statement is the door's own — the characterizing
// statement; its Key is spelled in source (DefEntry.Key), as a
// theorem's is, and registration computes none.

package registry

import (
	"fmt"
	"regexp"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/tactic"
)

// DefEntry declares one defined constant: the entry name, the
// constant, its type (text form), and the defining equations — a
// single definiendum-free equation (the DIRECT shape)
// or one equation per constructor (the RECURSIVE
// shape, compiled against the carrier's recursion schema).
type DefEntry struct {
	// Name is the registered entry's bare name (family-prefixed by
	// Add, like any member).
	Name string
	// Key is the entry's own key, its characterizing statement's
	// normalized key (ProofEntry.Key), spelled in source like every
	// member's. Registration reads it and computes nothing; the key
	// gate and the replay harness check it against the statement. An
	// entry registered without one carries the UnmintedKeyPrefix
	// sentinel, which they turn into the paste-ready value
	// (XUGO_PASTE_KEYS writes it).
	Key string
	// Const is the minted constant's name.
	Const string
	// Type is the constant's type in text form ("num → num → bool").
	Type string
	// Equations are the defining statement literals; each parses with
	// the definiendum declared at Type and both strict switches on.
	Equations []string
	// Abbrev is the definition's own abbreviation table, read under the
	// chapter's (Family.WithAbbrev) as a member's Statement.Abbrev is:
	// the names the Equations spell as «Name» for a compound term that
	// recurs, each a spelling and nothing more — the constant, its
	// characterizing statement and its key are the expanded equations'.
	// An entry is written over the equations' leading ∀-binders; a name
	// an equation rebinds further in is refused as a capture, and a name
	// the chapter's table declares is refused as declared twice.
	Abbrev dsl.Abbrev
	// Measure routes the definition to the WF shape (transcript
	// D): a term over the RECURSION ARGUMENT alone (carrier → num),
	// its λ-binder matched BY NAME against the LHS argument it
	// measures. With a measure the equation must be the ONE total
	// COND form, and Termination carries the author's obligation
	// proof.
	Measure string
	// Termination is the WF shape's termination proof — the actions
	// that close the obligation the composite surfaces (for every
	// recursive call site, under its COND guards, the measure
	// decreases). Required exactly when Measure is set.
	Termination []proof.Action
	// Respects is the LIFT shape's respectfulness proof — the actions
	// closing the obligation the define composite opens when some
	// equation argument is a quotient's class pattern (`∀a b:ρ.
	// op(⁅a⁆, ⁅b⁆) = ⁅a + b⁆`; prover/proof/define_lift.go): the value
	// respects the relation in every class argument. Required exactly
	// for a lift; the quotient's Sound and Exact entries join Deps by
	// the door itself.
	Respects []proof.Action
	// Deps declares, for the WF and lift shapes, the entries the Build
	// reads: the WF rows the WF shape discharges from (the entries
	// serving wellfounded_recursion and wellfounded_measure_less) and
	// whatever the termination or respectfulness proof cites.
	// Registration panics when a library name the shape reads has no
	// dep serving it. A DIRECT or RECURSIVE definition's build reads
	// nothing the door does not find itself — the recursive shape's
	// schema is the carrier's Recursion entry for a DefineData'd type,
	// else the entry serving num_recursion / <T>_RECURSION — and its
	// edge to the definer of every constant its equation spells is read
	// off the equation (ProofEntry.DepEntries). Its Deps name only
	// entries of its own family, and they are load-bearing, not
	// documentation: the equation parses at the package's init, so
	// every constant it spells must be minted first; another family's
	// mint is ordered by the import, and a same-family one by the typed
	// reference — Go initializes a variable after the variables it
	// references, and a type door is deferred past the inhabitation
	// proof it references, so declaration order alone does not do it
	// (ZeroDef spells mk_num, NumDef waits for isNumZero).
	// TestLintDefinitionMintsOrdered checks both, and registration
	// refuses an entry of another family here.
	Deps []EntryLike
	// Reading is the definition's statement read in this encoding — the
	// degenerate cases the definiens decides (the intersection of no
	// closed sets is the whole type), the argument the short spelling
	// leaves out — as ProofEntry.Reading.
	Reading string
	// Spelled is the definiendum's stand-in spelling in Equations, for
	// a Const the text DSL cannot spell in head position — an operator
	// (`,`, `+`), a name the DSL reserves for its own surface (`_0`,
	// `suc`). The equations are read with Spelled declared as the
	// definiendum, the constant is minted under Const, and the
	// characterizing statement carries Const.
	Spelled string
	// Implicit names the constant's leading IMPLICIT binders — the
	// structure components the operation reads (`vadd`: add; `dot`:
	// add, mul; `vec`: zero), a prefix of the equations' ∀-binders in
	// order. Under a scope that binds those names — a structure law's
	// ∀-prefix, a section whose binders they are, a family working at
	// an instance (Family.WithInstance) — a statement may leave them
	// out: `vadd(u, v)` reads `vadd(add, u, v)`, a bare `vadd` reads
	// `vadd(add)`. The explicit spelling stays legal, and where nothing
	// binds the names it is the only one. The definition's own
	// equations always spell every binder of the constant they define;
	// for every OTHER constant they read as a member's text does — a
	// declared notation lowers (`c • x` is `vsmul(mul, c, x)`) and the
	// family's instance bindings complete the components it leaves
	// out, so `c • x + d • y` in a definition under
	// WithInstance(comm_ring.CommRingOn, real_ring.CommRing) is
	// `vadd(real_add, vsmul(real_mul, c, x), vsmul(real_mul, d, y))`.
	// See ext/dsl/implicit.go.
	Implicit []string
	// Notation declares the constant's notation, spelled as the
	// equations' own binders in one of three forms, the holes being
	// exactly the constant's explicit binders (its ∀-prefix minus
	// Implicit), each once. A statement writes it, and every text the
	// session serves back and every label emit writes spells it (the
	// output door, engine/spelling.go — dsl.ChapterSpelling folds a
	// full application into the notation; the kernel term is the plain
	// application throughout):
	//
	//   - OUTFIX — `"‖u‖_n"` for `vnorm(n, u)`, `"⟪u, v⟫_n"` for
	//     `dot⟨n⟩(add, mul, u, v)`, `"⁅x⁆"` for a quotient's class map,
	//     `"⟦a, b⟭"` for a half-open interval: the body between an
	//     opening delimiter of the DSL's outfix alphabet (`‖…‖`, `⟪…⟫`,
	//     `⁅…⁆`, `⟦` or `⟬` closed by `⟧` or `⟭`) and its close,
	//     comma-separated, then an optional `_binder` subscript. A
	//     statement writes `‖u‖_n`, `‖u‖_(m + 1)`. See ext/dsl/outfix.go.
	//   - INFIX — `"u + v"` for `vadd(add, u, v)`, `"c • u"` for
	//     `vsmul(mul, c, u)`, `"a ⟶ l"` for `real_converges_to(a, l)`: two
	//     holes around a symbol the grammar parses (`+ - * / • ⟶`). The
	//     build resolves the symbol to this constant where no built-in
	//     domain serves the operand types, so `u + v` at `num → real` is
	//     `vadd(real_add, u, v)` and `x + y` at real stays `real_add`;
	//     `•` and `⟶` have no built-in domain and are the declaring
	//     constant's outright. See ext/dsl/operator.go.
	//   - PREFIX — `"-u"` for `vneg(neg, u)`: the symbol `-` before one
	//     hole, resolved like the infix.
	//
	// The printer folds a full application back into its notation.
	Notation string
	// Symbols is a STRUCTURE definition's declaration of the operator
	// symbols its components carry — `{"add": "+", "sub": "-", "mul":
	// "*", "neg": "-"}` on a structure over the component variables
	// add, zero, neg, mul and sub, each key a component, each symbol one
	// the grammar parses at the component's arity (`+ - * / •` for an
	// operation, `-` for a map). Under a law over the structure, and
	// under a goal whose resident hypotheses apply it to variables,
	// `x + y` at the carrier is `add(x, y)` and `-x` is `neg(x)`; a
	// component with no fixed reading (a commutative monoid's `op`)
	// declares nothing and keeps its applied spelling. Two components of
	// one type never share a symbol; two of different carriers may, each
	// read at its own operands. A structure on a record declares none:
	// the record's fields carry their symbols (DataField.Symbol).
	// DefineStructure only. See ext/dsl/structure.go.
	Symbols map[string]string
	// BigOp declares the constant the big operator at its carrier —
	// `"Σ"` on `sum : (A → bool) → (A → real) → real` makes `Σ_{i<m} body`
	// at a real body `real_sum({i:num | i < m}, λi:num. body)`; `"Π"` is the
	// product. The constant's type must be `(α → bool) → (α → β) → β`
	// with β a carrier (no type variables). A carrier no constant
	// declares folds through `iterate` at the carrier's `+` (`*`). See
	// ext/dsl/bigop.go.
	BigOp string
	// Overload is the word a text may write for the constant among the
	// constants of its kind — `"sum"` on real_sum, nat_sum and int_sum
	// lets `sum(s, f)` stand for whichever one f's values select. The
	// parser picks by the arguments (their number, then their types),
	// and the chapter spelling prints the word where it reads back to
	// this constant; a verb naming the constant (Unfold, a vocabulary
	// row) keeps the constant's own name. The word is never a constant's
	// name, and a constant taking implicit arguments declares none. See
	// ext/dsl/overload.go.
	Overload string
	// Coercion marks the constant as the `&` into its codomain: a
	// constant of type `real → τ` (complex_of_real) through which a
	// text's `&x` lifts a real x, and `&n` a num through the real line,
	// wherever τ is expected or a partner has it, and wherever the
	// chapter declared τ as its domain (WithCoerceDomain); the chapter
	// spelling writes the application back as `&`. One constant per
	// codomain. See ext/dsl/syntax.go's Coercion.
	Coercion bool
	// NumeralCoercion marks the constant as the `&` into its codomain
	// for numerals alone: a constant of type `real → τ` that embeds the
	// nonnegative line and not the whole of it (extended_of_real into
	// ⟦0, ∞⟧ sends a negative real to 0). A text's `&n` for a num n
	// lifts through the real line wherever τ is expected or a partner
	// has it, and the chapter spelling writes such an application back
	// as `&n`; `&x` of a real is refused, and the constant applied to a
	// real keeps its name in the text. A constant declares Coercion or
	// NumeralCoercion, not both.
	NumeralCoercion bool
	// MembershipRead declares that the closers read a membership in the
	// constant as the set-builder its definiens is: for a definition
	// `∀ā. c(ā) = {x | φ}` (or the three-part form), `y ∈ c(ā)` reads as
	// φ at y in By's conditioning (the refuter, Arith), the apply rung
	// and a hypothesis opened, and the set driver opens c — the
	// constant reads exactly as the set-builder it names, in every
	// closer, as mathlib marks `mem_Icc` a simp lemma. A constant
	// without it stays closed until a proof opens it, whatever its
	// definiens. The door refuses a definition that is no set-builder
	// over its arguments. See prover/tactic/membership_declared.go.
	MembershipRead bool
	// Dim names the equations' binder that is the constant's DIMENSION
	// slot — `"n"` for `vec⟨n⟩(zero, u)`, `dot⟨n⟩(add, mul, u, v)`,
	// `vnorm(n, u)`: the num argument the operation reads its vector
	// arguments at. The typed wrapper generator pairs a statement's
	// vector binders with their dimension through it and writes the
	// dimension off the vector (ext/dimtypes; library/cmd/gen_family).
	// Registered with the mint (DimSlot).
	//
	// The dimensions an entry declares — this one, RowDim/ColumnDim,
	// SourceDim/TargetDim, Dimensions — are the equation's binders right
	// after its implicit prefix, and the text writes them in the ⟨…⟩
	// after the constant's name: `vec⟨n⟩(u)`, `matrix⟨n, m⟩(A)`, and in
	// the equation itself `vec⟨n⟩(zero, u)` (ext/dsl/dimension.go).
	Dim string
	// Bundles declares where a bundle of a structure goes among the
	// constant's parameters, so that a text may pass the bundle in
	// their place (ext/dsl/bundle.go): each declaration is a structure
	// applied to the binders of the definition it fills, `_` for a
	// component the constant does not take —
	// `locally_ringed_space(T, F, res)` lets
	// `spec_adjunct_point(X, R, α, x)` stand for the application at X's
	// topology, section rings and restriction. A second
	// declaration of one structure is where a second bundle of it goes.
	// The layouts are registered before the equation is read, so its
	// body may pass the binders as the bundles they lay out:
	// `lrs_isomorphism` over two sheaves writes `ring_isomorphism(F'(V),
	// F(…), ψ(V))`. A structure needs none: its own components and its
	// sub-structures, indexed or not, are read off its definition
	// (library/registry/bundle.go).
	Bundles []string
	// Subject names, on a DefineStructure entry, the component the
	// predicate is said of — `"R"` for `comm_ring_on(R)`, the record R
	// is a ring; `"f"` for `ring_homomorphism(R, S, f)`, f is a
	// homomorphism; `"F"` for `sheaf_of_rings(T, F, res)`, F is a sheaf
	// of rings; `"R"` for `preorder(R)`. A bundle of the structure is
	// named after it, so the bundle binder `∀S:comm_ring_on(B).` binds
	// the ring record as S and `∀f:ring_homomorphism(A, B).` the map as
	// f. A structure on a whole type over components —
	// `comm_monoid(op, e)` — declares none: its subject is the type, and
	// its bundle has only the binder's name (ext/dsl/bundle.go).
	Subject string
	// Letter names, on a DefineStructure entry with no Subject, the
	// name a bundle binder of it is written under when the chapter
	// spelling folds a law's components back: `"S"` for
	// `short_exact_complexes(R, P', P, P'', i, p)`, three complexes and
	// two maps over a ring, whose laws then read
	// `∀S:short_exact_complexes(A, B, C, D). …`. No component is so
	// named; the binder's own name stands for the bundle alone.
	Letter string
	// RowDim and ColumnDim are Dim for a constant that reads MATRIX
	// arguments — `"n"` and `"m"` for `matrix⟨n, m⟩(zero, A)`, membership
	// in the n×m matrices. Declared together or not at all, and
	// independent of Dim: `matrix_act⟨k⟩(add, mul, A, x)` declares
	// `Dim: "k"` for the vector it acts on and nothing for the matrix,
	// whose row count the term does not carry. The generator refines a
	// statement's matrix binders to dimtypes.Mat[Elem, R, C] through
	// them and writes both dimensions off the matrix at the cite.
	// Registered with the mint (MatrixDimSlots).
	RowDim, ColumnDim string
	// SourceDim and TargetDim are Dim for a constant that reads MAPS
	// between two vector spaces, arguments of type `(num → τ) → num → τ` —
	// `"n"` and `"m"` for `vec_op_norm⟨n, m⟩(L)`, which reads L on
	// n-vectors and its values as m-vectors. Declared together or not at
	// all, independent of Dim and of RowDim/ColumnDim, and the two may
	// name one binder: `vec_inverse_on⟨n⟩(L, K)` declares `"n"` for both.
	// The generator refines a statement's map binders to
	// dimtypes.VecFun[Elem, Source, Target] through them and writes both
	// dimensions off the map at the cite. Registered with the mint
	// (VecFunDimSlots).
	SourceDim, TargetDim string
	// Dimensions names the binders the text writes in the ⟨…⟩ that read
	// no vector, matrix or map argument at them — the dimensions of
	// spaces whose points are no vectors: `smooth_manifold_map⟨n,
	// m⟩(T, 𝒜, S, ℬ, f)` is a map from an n-manifold to an m-manifold,
	// and none of its arguments is a sequence read at n or at m. A name
	// here registers no slot and refines no wrapper parameter; it places
	// the argument in the suffix and nothing else. Each is a num binder,
	// named once, and named by no other dimension declaration.
	Dimensions []string
	// ServesAs is the library name the entry serves under, when the
	// engine reads the definition by name — a datatype kit reading the
	// recspace rows (family_cons) — exactly ProofEntry.ServesAs.
	ServesAs string

	// computedKey marks an entry a multi-entry door declares itself — a
	// record's field projection, which DefineData registers from the
	// record's one literal — whose key is computed from the
	// characterizing statement rather than read from Key
	// (ProofEntry.Key says why).
	computedKey bool
}

// ownKey is the key the entry registers under: Key as the source
// spells it, or, for an entry a multi-entry door declares, the
// characterizing statement's normalized key.
func (e DefEntry) ownKey(characterizing core.Prop) string {
	if !e.computedKey {
		return e.Key
	}
	normalized, _ := prop.Normalize(characterizing)
	return string(normalized.AlphaKey())
}

// Define registers a definition member: mints the constant NOW (see
// the file comment for why registration time), and registers an entry
// whose Build re-derives the characterizing theorem via the define
// composite. Init-time failures panic — a definition that cannot
// parse, analyze, or mint is a broken package, not a replay finding.
//
// Both `recursive:` shapes are served: a single definiendum-free
// equation is the DIRECT case (λ-mint, headline
// entry); constructor-clause equations are the RECURSIVE case
// (ε-mint; the Build's composite discharges the existence obligation
// through the equation compiler against the carrier's recursion
// schema, which the entry declares as its dep). The compile itself
// runs at BUILD time, not registration — package init has no schema
// theorems in scope — so a schema gap fails the replay loudly, never
// the package load.
func (f *Family) Define(e DefEntry) *ProofEntry {
	if len(e.Symbols) > 0 {
		panic(fmt.Sprintf("registry.Define(%s): Symbols is a structure's declaration — DefineStructure", e.Name))
	}
	if e.Subject != "" {
		panic(fmt.Sprintf("registry.Define(%s): Subject is a structure's declaration — DefineStructure", e.Name))
	}
	if e.Letter != "" {
		panic(fmt.Sprintf("registry.Define(%s): Letter is a structure's declaration — DefineStructure", e.Name))
	}
	entry, _ := f.define(e)
	return entry
}

// define is Define returning also the direct shape's analysis — the
// LHS argument variables and the body — which DefineStructure reads
// for the structure's components. nil for the other shapes.
func (f *Family) define(e DefEntry) (*ProofEntry, *proof.DirectDefinition) {
	e.Type, e.Measure, e.Equations = dsl.OneLine(e.Type), dsl.OneLine(e.Measure), oneLineTexts(e.Equations)
	if e.Name == "" || e.Const == "" || e.Type == "" {
		panic("registry.Define: Name, Const and Type are all required")
	}
	if len(e.Equations) == 0 {
		panic(fmt.Sprintf("registry.Define(%s): at least one equation is required", e.Name))
	}

	mgr := GetConstMetaManager()
	// The chapter takes the name first: a name that is not free names
	// why (another chapter's mint, or an engine built-in).
	if err := mgr.ClaimName(core.TermName(e.Const)); err != nil {
		panic(fmt.Sprintf("registry.Define(%s): %v", e.Name, err))
	}
	// The equations read in the chapter's own dialect: the syntax table
	// lowers a declared notation (`c • u` is `vsmul(mul, c, u)`) and the
	// family's instance bindings complete the implicit components the
	// notation leaves out — exactly the scope every MEMBER statement
	// parses in (applyVocab). Without them a definition body had to
	// spell every derived operation longhand while the theorems beside
	// it wrote the notation.
	base := &dsl.ParseScope{
		ConstResolver: func(name string) core.ConstTermMeta {
			if meta, ok := mgr.LoadConstMeta(core.TermName(name)); ok {
				return meta
			}
			return core.ConstTermMeta{}
		},
		Syntax:           mgr,
		TypeResolver:     mgr.TypeArity,
		ImplicitBindings: f.implicit,
		CoerceDomain:     f.CoerceDomain(),
	}
	// The equations read under the chapter's abbreviation table with the
	// entry's own beneath it, as every member statement does
	// (BuildSpec.installAbbreviations); the entries are written over the
	// leading ∀-binders, each equation's own for the capture check.
	abbrev := f.definitionAbbrev(e)
	base.Abbreviations = abbrev.merged
	mintEnv := &proof.ProverEnv{ProofService: &proof.ProofService{
		LoadConstMeta:        mgr.LoadConstMeta,
		LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
		Syntax:               mgr,
		TypeArity:            mgr.TypeArity,
	}}
	spelled := e.Const
	surface := declaredSurface(e)
	if e.Spelled != "" {
		spelled = e.Spelled
	}
	// The layouts the entry declares are registered first, off the
	// equation's leading binders, so that the body may pass the binders
	// as the bundles they lay out (`ring_isomorphism(F'(V), F(…), ψ(V))`
	// under two sheaves); the full syntax replaces the provisional one.
	var declaredLayouts *dsl.BundleSyntax
	if len(e.Bundles) > 0 {
		params, err := dsl.LeadingBinders(e.Equations[0])
		if err != nil {
			panic(fmt.Sprintf("registry.Define(%s): Bundles: %v", e.Name, err))
		}
		declaredLayouts, err = declaredBundleSyntaxFor(e.Bundles, params)
		if err != nil {
			panic(fmt.Sprintf("registry.Define(%s): Bundles: %v", e.Name, err))
		}
		mgr.ProvisionalBundleSyntax(core.TermName(e.Const), declaredLayouts)
	}
	// The equation writes the definiendum's dimensions in its ⟨…⟩, as
	// every later text writes the constant's (ext/dsl/dimension.go), so
	// how many it declares is settled before the equation is read.
	if (e.RowDim == "") != (e.ColumnDim == "") {
		panic(fmt.Sprintf("registry.Define(%s): RowDim/ColumnDim: a matrix dimension declaration needs both RowDim and ColumnDim", e.Name))
	}
	if (e.SourceDim == "") != (e.TargetDim == "") {
		panic(fmt.Sprintf("registry.Define(%s): SourceDim/TargetDim: a map dimension declaration needs both SourceDim and TargetDim", e.Name))
	}
	if err := checkDimensionsField(e); err != nil {
		panic(fmt.Sprintf("registry.Define(%s): Dimensions: %v", e.Name, err))
	}
	dimensions := declaredDimensions(e)
	if len(dimensions) > 0 {
		base.Definiendum = &dsl.Definiendum{Name: spelled, Implicit: e.Implicit, Dims: len(dimensions)}
	}
	equations := make([]core.Prop, len(e.Equations))
	var defVar core.VarTerm
	for i, text := range e.Equations {
		base.AbbreviationBinders = leadingBinderSet(text)
		eq, dv, err := proof.ParseDefinitionEquation(text, spelled, e.Type, base)
		if err != nil {
			panic(fmt.Sprintf("registry.Define(%s): %v", e.Name, err))
		}
		equations[i], defVar = eq, dv
	}
	base.Definiendum = nil
	if e.Coercion && e.NumeralCoercion {
		panic(fmt.Sprintf("registry.Define(%s): a constant declares Coercion or NumeralCoercion, not both", e.Name))
	}
	if len(e.Implicit) > 0 || e.Notation != "" || e.BigOp != "" || len(e.Symbols) > 0 || e.Overload != "" || e.Coercion || e.NumeralCoercion || len(e.Bundles) > 0 || len(dimensions) > 0 {
		syntax, err := constSyntaxOf(e.Const, fullestEquation(equations), defVar.Type(), e.Implicit, e.Notation, e.BigOp, e.Overload, e.Symbols, e.Coercion || e.NumeralCoercion)
		if err != nil {
			panic(fmt.Sprintf("registry.Define(%s): %v", e.Name, err))
		}
		syntax.Dims = len(dimensions)
		if e.NumeralCoercion {
			syntax.Coercion.NumeralsOnly = true
		}
		if len(e.Bundles) > 0 {
			b, err := declaredBundleSyntax(e.Bundles, fullestEquation(equations))
			if err != nil {
				panic(fmt.Sprintf("registry.Define(%s): Bundles: %v", e.Name, err))
			}
			for i := range b.Layouts {
				if !slices.Equal(b.Layouts[i].Slots, declaredLayouts.Layouts[i].Slots) {
					panic(fmt.Sprintf("registry.Define(%s): Bundles: the equation's binders read %v before the equation was built and %v after",
						e.Name, declaredLayouts.Layouts[i].Slots, b.Layouts[i].Slots))
				}
			}
			syntax.Bundle = b
		}
		mgr.RegisterConstSyntax(core.TermName(e.Const), syntax)
	}
	if e.Dim != "" {
		if err := registerDimSlot(e.Const, equations[0], e.Dim); err != nil {
			panic(fmt.Sprintf("registry.Define(%s): Dim: %v", e.Name, err))
		}
	}
	if e.RowDim != "" || e.ColumnDim != "" {
		if err := registerMatrixDimSlots(e.Const, equations[0], e.RowDim, e.ColumnDim); err != nil {
			panic(fmt.Sprintf("registry.Define(%s): RowDim/ColumnDim: %v", e.Name, err))
		}
	}
	if e.SourceDim != "" || e.TargetDim != "" {
		if err := registerVecFunDimSlots(e.Const, equations[0], e.SourceDim, e.TargetDim); err != nil {
			panic(fmt.Sprintf("registry.Define(%s): SourceDim/TargetDim: %v", e.Name, err))
		}
	}
	if len(e.Dimensions) > 0 {
		if err := checkNumBinders(equations[0], e.Dimensions); err != nil {
			panic(fmt.Sprintf("registry.Define(%s): Dimensions: %v", e.Name, err))
		}
	}
	if len(dimensions) > 0 {
		if err := checkLeadingDimensions(fullestEquation(equations), len(e.Implicit), dimensions); err != nil {
			panic(fmt.Sprintf("registry.Define(%s): %v", e.Name, err))
		}
	}
	if e.MembershipRead && (e.Measure != "" || len(equations) != 1 ||
		proof.IsQuotientLiftEquation(equations[0], defVar) || proof.IsCompiledDefinitionEquation(equations[0], defVar)) {
		panic(fmt.Sprintf("registry.Define(%s): MembershipRead declares a set-builder definition, "+
			"one direct equation `∀ā. c(ā) = {x | φ}`, and this one is not direct", e.Name))
	}
	if e.Measure != "" {
		if e.Spelled != "" {
			panic(fmt.Sprintf("registry.Define(%s): the WF shape takes no Spelled stand-in", e.Name))
		}
		return f.defineWF(e, equations, defVar, mintEnv, base, abbrev), nil
	}
	if e.Termination != nil {
		panic(fmt.Sprintf("registry.Define(%s): Termination without Measure — the "+
			"termination obligation exists only for the WF shape", e.Name))
	}
	if len(equations) == 1 && proof.IsQuotientLiftEquation(equations[0], defVar) {
		return f.defineLift(e, equations, defVar, mintEnv, abbrev), nil
	}
	if e.Respects != nil {
		panic(fmt.Sprintf("registry.Define(%s): Respects without a class pattern among the "+
			"equation's arguments — the respectfulness obligation exists only for a lift", e.Name))
	}

	if len(equations) == 1 && !proof.IsCompiledDefinitionEquation(equations[0], defVar) {
		dd, err := proof.AnalyzeDirectDefinition(equations[0], defVar)
		if err != nil {
			panic(fmt.Sprintf("registry.Define(%s): %v", e.Name, err))
		}
		c, characterizing, err := proof.MintDirectDefinitionAs(mintEnv, dd, core.TermName(e.Const))
		if err != nil {
			panic(fmt.Sprintf("registry.Define(%s): %v", e.Name, err))
		}
		if e.MembershipRead {
			if _, err := tactic.MembershipReadArity(c); err != nil {
				panic(fmt.Sprintf("registry.Define(%s): MembershipRead: %v", e.Name, err))
			}
			tactic.DeclareMembershipRead(c)
		}
		checkOwnFamilyDeps(f, e)
		entry := ProofEntry{
			Name:        e.Name,
			ServesAs:    e.ServesAs,
			Reading:     e.Reading,
			Key:         e.ownKey(characterizing),
			Definition:  proof.DefinitionDirect,
			Deps:        e.Deps,
			depsSpelled: true,
		}
		// The MINT's characterizing statement is the entry's, as it is
		// for the recursive and WF shapes: the equation was already read
		// once, at the mint, with the definiendum declared at Type, and
		// what came out of that read is what the constant means. Reading
		// the literal a SECOND time under the family vocabulary would be
		// a different parse — the definiendum is a constant there, and
		// its type letters freshen per occurrence, so an equation whose
		// letter is tied only through the definiendum's own type (a
		// nullary polymorphic one like recspace_bottom : recspace(A), or a
		// λ-bodied one like inject_num) reads at an instance the author never
		// wrote and fails to type. Same composite either way.
		entry.stated = characterizing
		entry.predicate = &definedPredicate{constName: e.Const, typeText: e.Type}
		for _, v := range dd.Args {
			entry.predicate.args = append(entry.predicate.args, string(v.Name()))
		}
		entry.Build = bareDefinition(abbrev, func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
			ctx := f.NewScript(env)
			sec := ctx.Section(characterizing)
			sec.Do(proof.DefineStep(c))
			if !sec.Proved() {
				panic(fmt.Sprintf("registry.Define(%s): the definition step did not close", e.Name))
			}
			return sec.PromisedThm(), &ctx.Proof
		})
		entry.defines = []string{e.Const}
		entry.notations = notationsOf(e.Const, surface)
		return f.addDeclared(entry), dd
	}

	rd, err := proof.AnalyzeRecursiveDefinition(equations, defVar)
	if err != nil {
		panic(fmt.Sprintf("registry.Define(%s): %v", e.Name, err))
	}
	c, characterizing, err := proof.MintRecursiveDefinitionAs(mintEnv, rd, core.TermName(e.Const))
	if err != nil {
		panic(fmt.Sprintf("registry.Define(%s): %v", e.Name, err))
	}
	// The schema is the entry's dep: the replay harness serves a
	// definition ONLY its declared entries, and the composite's
	// compile resolves the schema there by its conventional name
	// (tried in candidate order, the FIRST being the corpus convention
	// — num_recursion, <T>_RECURSION). A DefineData'd carrier's schema is
	// its Recursion entry, added here (its ServesAs binds the name);
	// for a corpus-served carrier the member declares the entry that
	// serves the name.
	candidates := tactic.RecursionPrincipleNameCandidates(rd.CarrierType)
	if len(candidates) == 0 {
		panic(fmt.Sprintf(
			"registry.Define(%s): carrier %s is not an inductive composite type",
			e.Name, e.Type))
	}
	checkOwnFamilyDeps(f, e)
	deps := e.Deps
	if recEntry, ok := dataRecursionDep(rd.CarrierType); ok {
		deps = withDep(deps, recEntry)
	} else if schema, ok := servingEntry(candidates); ok {
		deps = withDep(deps, schema)
	} else {
		panic(fmt.Sprintf(
			"registry.Define(%s): no entry serves the carrier's recursion schema %v — "+
				"the entry that proves it is registered under that ServesAs, in a family this one imports",
			e.Name, candidates))
	}
	return f.addDeclared(ProofEntry{
		Name:        e.Name,
		ServesAs:    e.ServesAs,
		Reading:     e.Reading,
		Key:         e.ownKey(characterizing),
		Definition:  proof.DefinitionRecursive,
		defines:     []string{e.Const},
		notations:   notationsOf(e.Const, surface),
		Deps:        deps,
		depsSpelled: true,
		// The characterizing statement was computed at registration
		// (the equations at the minted constant): the entry's statement
		// and the Build's section goal are one value, not two spellings.
		stated: characterizing,
		Build: bareDefinition(abbrev, func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
			ctx := f.NewScript(env)
			sec := ctx.Section(characterizing)
			sec.Do(proof.DefineStep(c))
			if !sec.Proved() {
				panic(fmt.Sprintf(
					"registry.Define(%s): the existence obligation did not "+
						"discharge — is %s preloaded (Deps)?", e.Name, candidates[0]))
			}
			return sec.PromisedThm(), &ctx.Proof
		}),
	}), nil
}

// withDep appends dep to deps unless it is already declared.
// definitionAbbrev is a definition's abbreviation table as its equations
// and its entry read it: the chapter's (Family.WithAbbrev) with the
// entry's own (DefEntry.Abbrev) under it, a name both declare refused,
// written over the leading ∀-binders of its equations. A definition
// under no table reads none.
func (f *Family) definitionAbbrev(e DefEntry) *memberAbbrev {
	merged, err := f.AbbrevTable().Extend(e.Abbrev)
	if err != nil {
		panic(fmt.Sprintf("registry.Define(%s): %v", e.Name, err))
	}
	binders := map[string]bool{}
	for _, text := range e.Equations {
		for name := range leadingBinderSet(text) {
			binders[name] = true
		}
	}
	return &memberAbbrev{own: e.Abbrev, merged: merged, binders: binders}
}

// leadingBinderSet is the names a statement's leading ∀-prefix binds
// (dsl.LeadingBinderNames), which an abbreviation entry may spell.
func leadingBinderSet(text string) map[string]bool {
	binders := map[string]bool{}
	for _, name := range dsl.LeadingBinderNames(text) {
		binders[name] = true
	}
	return binders
}

// bareDefinition is Bare for a definition's build, carrying the table
// its equations were read under (definitionAbbrev) so that the entry
// serves it as a member serves its own (ProofEntry.Abbreviations).
func bareDefinition(abbrev *memberAbbrev, fn BuildFunc) BuildSpec {
	return BuildSpec{Fn: fn, abbrev: abbrev}
}

func withDep(deps []EntryLike, dep *ProofEntry) []EntryLike {
	for _, d := range deps {
		if d.Entry() == dep {
			return deps
		}
	}
	return append(append([]EntryLike(nil), deps...), dep)
}

// servingEntry is the registered entry serving the first of names
// that some entry serves: a corpus-served carrier's recursion schema,
// found by its conventional name rather than declared.
func servingEntry(names []string) (*ProofEntry, bool) {
	for _, n := range names {
		if e, ok := byServesAs[n]; ok {
			return e, true
		}
		if e, ok := byName[n]; ok {
			return e, true
		}
	}
	return nil, false
}

// checkOwnFamilyDeps refuses a Deps entry of another family on a direct
// or recursive definition. Such a definition's build reads nothing but
// its own equation and, for the recursive shape, the carrier's schema
// the door adds itself; its edge to each constant its equation spells
// is read off the equation (DepEntries); and a constant another family
// mints is initialized first because this family imports that one. What
// Deps still carries is the order of this family's own mints: Go
// initializes a variable after the ones its initializer references, so
// a definition names the same-family definitions whose constants its
// equation spells (TestLintDefinitionMintsOrdered).
func checkOwnFamilyDeps(f *Family, e DefEntry) {
	for _, d := range e.Deps {
		if d == nil || d.Entry() == nil {
			continue
		}
		if other := d.Entry().family; other != nil && other != f {
			panic(fmt.Sprintf(
				"registry.Define(%s): Deps names %s, an entry of %s — a definition's Deps name only "+
					"entries of its own family, the mints its equation must initialize after; the edge to "+
					"a constant another family mints is read off the equation, and the import orders the mint",
				e.Name, d.Entry().Name, other.Name))
		}
	}
}

// wfTerminationLabel is the WF obligation Case's fixed label — the
// section's one child, whatever the definition.
const wfTerminationLabel = "termination: the measure decreases at every recursive call"

// defineWF is Define's WF branch: ONE total COND equation plus a
// measure; the Build's composite surfaces the termination obligation
// and the entry's Termination actions close it, after which the WF
// equation compiler (CompileWFExistence) discharges the existence from
// the served wellfounded_recursion/wellfounded_measure_less rows — declared as the entry's by-name
// deps alongside any rows the termination proof cites.
func (f *Family) defineWF(e DefEntry, equations []core.Prop, defVar core.VarTerm, mintEnv *proof.ProverEnv, base *dsl.ParseScope, abbrev *memberAbbrev) *ProofEntry {
	if len(equations) != 1 {
		panic(fmt.Sprintf(
			"registry.Define(%s): the WF v1 shape is ONE total COND equation "+
				"(got %d) — spell the guards as COND branches", e.Name, len(equations)))
	}
	if len(e.Termination) == 0 {
		panic(fmt.Sprintf(
			"registry.Define(%s): the WF shape needs the Termination proof — the "+
				"obligation is the author's (R1)", e.Name))
	}
	mRes := dsl.ParseTermTextInScope(e.Measure, nil, &dsl.ParseScope{
		ConstResolver:      base.ConstResolver,
		TypeResolver:       base.TypeResolver,
		StrictResolution:   true,
		StrictMint:         true,
		FreshenMetaLetters: true,
	}, nil)
	if len(mRes.Errors) > 0 {
		panic(fmt.Sprintf("registry.Define(%s): parse measure %q: %s",
			e.Name, e.Measure, mRes.Errors[0].Message))
	}
	wfd, err := proof.AnalyzeWFDefinition(equations[0], defVar, mRes.Term)
	if err != nil {
		panic(fmt.Sprintf("registry.Define(%s): %v", e.Name, err))
	}
	c, characterizing, err := proof.MintWFDefinition(mintEnv, wfd)
	if err != nil {
		panic(fmt.Sprintf("registry.Define(%s): %v", e.Name, err))
	}

	for _, row := range []string{proof.WFRecName, proof.WFMeasureName} {
		if !Serves(e.Deps, row) {
			panic(fmt.Sprintf(
				"registry.Define(%s): no dep serves %s — the WF shape discharges its "+
					"existence from the served WF rows; declare the entry that proves it in Deps",
				e.Name, row))
		}
	}
	termination := e.Termination
	return f.addDeclared(ProofEntry{
		Name:        e.Name,
		ServesAs:    e.ServesAs,
		Reading:     e.Reading,
		Key:         e.ownKey(characterizing),
		Definition:  proof.DefinitionWF,
		defines:     []string{e.Const},
		notations:   notationsOf(e.Const, declaredSurface(e)),
		Deps:        e.Deps,
		depsSpelled: true,
		stated:      characterizing,
		Build: bareDefinition(abbrev, func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
			ctx := f.NewScript(env)
			sec := ctx.Section(characterizing)
			sec.Do(proof.DefineWFStep(c, wfd.Measure,
				proof.MakeCase(wfTerminationLabel, termination...)))
			if !sec.Proved() {
				panic(fmt.Sprintf(
					"registry.Define(%s): the WF definition section did not close — "+
						"are %s and %s preloaded (Deps), and does the Termination "+
						"proof close the obligation?", e.Name,
					proof.WFRecName, proof.WFMeasureName))
			}
			return sec.PromisedThm(), &ctx.Proof
		}),
	})
}

// liftRespectsLabel is the lift obligation Case's fixed label — the
// section's one child, whatever the definition.
const liftRespectsLabel = "respectfulness: the value respects the relation in every class argument"

// defineLift is Define's LIFT branch: ONE equation with a quotient's
// class map as a constructor pattern among its arguments; the Build's
// composite surfaces the respectfulness obligation and the entry's
// Respects actions close it, after which the lift compiler
// (CompileLiftExistence) discharges the existence from the quotient's
// Sound and Exact — declared as the entry's deps by the door, the
// datatype schema precedent.
func (f *Family) defineLift(e DefEntry, equations []core.Prop, defVar core.VarTerm, mintEnv *proof.ProverEnv, abbrev *memberAbbrev) *ProofEntry {
	if len(e.Respects) == 0 {
		panic(fmt.Sprintf(
			"registry.Define(%s): the lift shape needs the Respects proof — the "+
				"obligation is the author's (R1)", e.Name))
	}
	mgr := GetConstMetaManager()
	resolve := func(name core.TermName) core.ConstTermMeta {
		if meta, ok := mgr.LoadConstMeta(name); ok {
			return meta
		}
		return core.ConstTermMeta{}
	}
	ld, err := proof.AnalyzeLiftDefinition(equations, defVar, resolve)
	if err != nil {
		panic(fmt.Sprintf("registry.Define(%s): %v", e.Name, err))
	}
	c, characterizing, err := proof.MintLiftDefinitionAs(mintEnv, ld, core.TermName(e.Const))
	if err != nil {
		panic(fmt.Sprintf("registry.Define(%s): %v", e.Name, err))
	}
	deps := e.Deps
	quotientDeps, err := quotientLiftDeps(ld.LiftQuotients())
	if err != nil {
		panic(fmt.Sprintf("registry.Define(%s): %v", e.Name, err))
	}
	for _, d := range quotientDeps {
		deps = withDep(deps, d)
	}
	respects := e.Respects
	return f.addDeclared(ProofEntry{
		Name:        e.Name,
		ServesAs:    e.ServesAs,
		Key:         e.ownKey(characterizing),
		Definition:  proof.DefinitionLift,
		defines:     []string{e.Const},
		notations:   notationsOf(e.Const, declaredSurface(e)),
		Deps:        deps,
		depsSpelled: true,
		stated:      characterizing,
		Build: bareDefinition(abbrev, func(env *proof.ProverEnv) (proof.Thm, *proof.Proof) {
			ctx := f.NewScript(env)
			sec := ctx.Section(characterizing)
			sec.Do(proof.DefineStep(c, proof.MakeCase(liftRespectsLabel, respects...)))
			if !sec.Proved() {
				panic(fmt.Sprintf(
					"registry.Define(%s): the lift definition section did not close — "+
						"are the quotient's Sound and Exact preloaded (Deps), and does the "+
						"Respects proof close the obligation?", e.Name))
			}
			return sec.PromisedThm(), &ctx.Proof
		}),
	})
}

// fullestEquation is the equation with the most leading ∀-binders — the
// first such. The declared syntax reads those binders POSITIONALLY, as
// the constant's arguments in order, which is the contract a single
// equation already carries. A recursion's base clause fixes the
// recursion argument to a constructor (`monoid_pow(op, e, x, 0) = e`)
// and binds one name fewer; its step clause binds the variable inside
// the constructor pattern in that argument's place
// (`∀op e x n. monoid_pow(op, e, x, suc(n)) = …`), so the step clause's
// binders line up with the arguments. A constructor carrying several
// variables would bind more names than there are arguments, and the
// notation check refuses it.
func fullestEquation(equations []core.Prop) core.Prop {
	best, bestCount := equations[0], -1
	for _, eq := range equations {
		count := 0
		for t := eq.Conclusion(); ; count++ {
			abs := ext.MatchesFORALL(t)
			if abs.IsZero() {
				break
			}
			t = abs.Body()
		}
		if count > bestCount {
			best, bestCount = eq, count
		}
	}
	return best
}

// constSyntaxOf reads a definition's Implicit, Notation, BigOp and
// Overload declarations against its fullest equation's ∀-binders and the
// constant's type into the syntax record the constant registers
// (dsl.ConstSyntax). Implicit must be the leading binders in order;
// Notation's holes must be exactly the remaining binders, each once;
// BigOp needs the type of a fold over a carrier; Overload a word that
// is no constant's name, on a constant without implicit arguments.
func constSyntaxOf(constName string, equation core.Prop, constType core.HolType, implicit []string, notation, bigOp, overload string, symbols map[string]string, coercion bool) (*dsl.ConstSyntax, error) {
	var binders []string
	var binderTypes []core.HolType
	t := equation.Conclusion()
	for abs := ext.MatchesFORALL(t); !abs.IsZero(); abs = ext.MatchesFORALL(t) {
		binders = append(binders, string(abs.Var().Name()))
		binderTypes = append(binderTypes, abs.Var().Type())
		t = abs.Body()
	}
	if len(binders) < len(implicit) {
		return nil, fmt.Errorf("Implicit: names %v exceed the equation's ∀-binders %v", implicit, binders)
	}
	for i, name := range implicit {
		if binders[i] != name {
			return nil, fmt.Errorf("Implicit: names %v must be the equation's leading ∀-binders in order; the equation binds %v",
				implicit, binders[:len(implicit)])
		}
	}
	syntax := &dsl.ConstSyntax{Implicit: append([]string(nil), implicit...)}
	if notation != "" {
		outfix, operator, err := parseNotation(notation, binders[len(implicit):])
		if err != nil {
			return nil, fmt.Errorf("Notation %q: %v", notation, err)
		}
		syntax.Outfix, syntax.Operator = outfix, operator
	}
	if bigOp != "" {
		b, err := bigOpOf(bigOp, constType)
		if err != nil {
			return nil, fmt.Errorf("BigOp %q: %v", bigOp, err)
		}
		syntax.BigOp = b
	}
	if len(symbols) > 0 {
		s, err := structureSyntaxOf(symbols, binders, binderTypes)
		if err != nil {
			return nil, fmt.Errorf("Symbols: %v", err)
		}
		syntax.Structure = s
	}
	if overload != "" {
		o, err := overloadOf(overload, constName, constType, implicit)
		if err != nil {
			return nil, fmt.Errorf("Overload %q: %v", overload, err)
		}
		syntax.Overload = o
	}
	if coercion {
		c, err := coercionOf(constType, implicit)
		if err != nil {
			return nil, fmt.Errorf("Coercion: %v", err)
		}
		syntax.Coercion = c
	}
	return syntax, nil
}

// coercionOf reads a Coercion declaration: the constant takes exactly
// one real, no implicit argument, and lands in a type other than real
// that takes no further argument — the codomain `&` lifts into.
func coercionOf(constType core.HolType, implicit []string) (*dsl.Coercion, error) {
	if len(implicit) > 0 {
		return nil, fmt.Errorf("a constant with implicit arguments %v declares no coercion", implicit)
	}
	dom, cod, ok := funTypeParts(constType)
	if !ok || !dom.Equals(dsl.RealType) {
		return nil, fmt.Errorf("the constant must take exactly a real (%s)", ext.FormatType(constType))
	}
	if _, _, more := funTypeParts(cod); more || cod.Equals(dsl.RealType) {
		return nil, fmt.Errorf("the codomain must be a type other than real that takes no further argument (%s)", ext.FormatType(constType))
	}
	return &dsl.Coercion{Into: cod}, nil
}

// overloadWordPattern is the shape of an overloaded word: a lowercase
// identifier in any script — `sum`, `dist`, and `π`, the word of a
// nullary constant, which is its symbol — read by the lexer as a name.
var overloadWordPattern = regexp.MustCompile(`^\p{Ll}[\p{Ll}\p{Nd}_]*$`)

// overloadOf reads an Overload declaration: a lowercase word other than
// the constant's own name, on a constant that takes arguments and no
// implicit ones — the word spells the constant's full application, and
// an implicit prefix would count arguments the text never writes.
func overloadOf(word, constName string, constType core.HolType, implicit []string) (*dsl.Overload, error) {
	if !overloadWordPattern.MatchString(word) {
		return nil, fmt.Errorf("a word is a lowercase identifier")
	}
	if word == constName {
		return nil, fmt.Errorf("the word is the constant's own name")
	}
	if len(implicit) > 0 {
		return nil, fmt.Errorf("a constant with implicit arguments %v declares no word", implicit)
	}
	arity := 0
	for t := constType; ; arity++ {
		_, cod, ok := funTypeParts(t)
		if !ok {
			break
		}
		t = cod
	}
	return &dsl.Overload{Word: word, Arity: arity, Type: constType}, nil
}

// structureSyntaxOf reads a structure's Symbols declaration against
// its components (the definition's ∀-binders, with their types): each
// named component carries its symbol at the arity its type gives it —
// an operation `A → A → A` an infix, a scalar action `A → B → B` an
// infix at a scalar and a vector, a map `A → A` a prefix — one
// component per symbol, arity and type.
func structureSyntaxOf(symbols map[string]string, components []string, types []core.HolType) (*dsl.StructureSyntax, error) {
	out := &dsl.StructureSyntax{Components: make([]dsl.StructureComponent, len(components))}
	claimed := map[string]string{}
	for name, symbol := range symbols {
		i := -1
		for j, c := range components {
			if c == name {
				i = j
			}
		}
		if i < 0 {
			return nil, fmt.Errorf("%s is not one of the structure's components %v", name, components)
		}
		arity := 0
		for ty := types[i]; ; arity++ {
			_, cod, ok := funTypeParts(ty)
			if !ok {
				break
			}
			ty = cod
		}
		if arity != 1 && arity != 2 {
			return nil, fmt.Errorf("%s: a symbol is carried by an operation or a map, not a component of type %s", name, ext.FormatType(types[i]))
		}
		if !dsl.OperatorSymbolOK(symbol, arity) {
			return nil, fmt.Errorf("%s ↦ %s: not a symbol the DSL parses at arity %d", name, symbol, arity)
		}
		// One symbol per operation at one signature: two components of
		// one type carrying one symbol are two structures at one
		// signature, which the parser refuses to tell apart. Two
		// signatures — a homomorphism's source and target additions, a
		// module's two additions and its scalar action — share a symbol,
		// and the parser reads each at its own operands.
		key := fmt.Sprintf("%s/%d/%s", symbol, arity, ext.FormatType(types[i]))
		if prev, dup := claimed[key]; dup {
			return nil, fmt.Errorf("%s and %s both carry %s at arity %d on %s", prev, name, symbol, arity, ext.FormatType(types[i]))
		}
		claimed[key] = name
		out.Components[i] = dsl.StructureComponent{Symbol: symbol, Arity: arity}
	}
	return out, nil
}

// bigOpOf reads a BigOp declaration against the constant's type, which
// must be a fold over a carrier: `(α → bool) → (α → β) → β` with β
// closed.
func bigOpOf(symbol string, constType core.HolType) (*dsl.BigOp, error) {
	if !dsl.BigOpSymbolOK(symbol) {
		return nil, fmt.Errorf("%s is not a big operator the DSL parses (Σ, Π)", symbol)
	}
	shape := fmt.Errorf("the constant's type %s is not a fold over a carrier, (α → bool) → (α → β) → β", ext.FormatType(constType))
	setTy, rest, ok := funTypeParts(constType)
	if !ok {
		return nil, shape
	}
	index, isSet, ok := funTypeParts(setTy)
	if !ok || !isSet.Equals(core.TypeBool()) {
		return nil, shape
	}
	termsTy, carrier, ok := funTypeParts(rest)
	if !ok {
		return nil, shape
	}
	index2, carrier2, ok := funTypeParts(termsTy)
	if !ok || !index.Equals(index2) || !carrier.Equals(carrier2) {
		return nil, shape
	}
	if len(carrier.TypeVars()) > 0 {
		return nil, fmt.Errorf("the carrier %s has type variables — a big operator is declared at one carrier", ext.FormatType(carrier))
	}
	return &dsl.BigOp{Symbol: symbol, Carrier: carrier}, nil
}

// funTypeParts splits a function type into its domain and codomain.
func funTypeParts(t core.HolType) (dom, cod core.HolType, ok bool) {
	c, isComposite := t.(core.CompositeType)
	if !isComposite || !c.Meta().Equals(core.MetaTypeFun()) {
		return nil, nil, false
	}
	return c.SubType(0), c.SubType(1), true
}

// parseNotation reads a notation pattern over the constant's explicit
// binders, in order — an outfix `<open> b₁, …, bₖ <close> [_ b]`, an
// infix `b₁ σ b₂`, or a prefix `-b` — and returns the record for the
// form it is, with the holes' argument positions.
func parseNotation(pattern string, explicit []string) (*dsl.Outfix, *dsl.Operator, error) {
	runes := []rune(strings.TrimSpace(pattern))
	if len(runes) == 0 {
		return nil, nil, fmt.Errorf("empty")
	}
	position := func(name string) (int, error) {
		for i, b := range explicit {
			if b == name {
				return i, nil
			}
		}
		return 0, fmt.Errorf("%s is not one of the constant's explicit binders %v", name, explicit)
	}
	used := map[string]bool{}
	hole := func(name string) (int, error) {
		name = strings.TrimSpace(name)
		if name == "" {
			return 0, fmt.Errorf("an empty hole")
		}
		pos, err := position(name)
		if err != nil {
			return 0, err
		}
		if used[name] {
			return 0, fmt.Errorf("%s is used twice", name)
		}
		used[name] = true
		return pos, nil
	}
	// The holes must be the constant's LEADING explicit binders, each
	// once: a definition stated pointwise binds the point after the
	// operation's own arguments (`vadd(add, u, v, i) = add(u(i), v(i))`),
	// and `u + v` is the operation, applied to a point or not.
	complete := func() error {
		for i := 0; i < len(used) && i < len(explicit); i++ {
			if !used[explicit[i]] {
				return fmt.Errorf("the notation must spell the constant's leading explicit binders %v exactly once (%s is missing)", explicit, explicit[i])
			}
		}
		if len(used) > len(explicit) {
			return fmt.Errorf("the notation spells more holes than the constant has explicit binders %v", explicit)
		}
		return nil
	}

	open := string(runes[0])
	if closes, isOutfix := dsl.OutfixCloses(open); isOutfix {
		// The notation closes at the first of open's closing delimiters
		// — the holes between are binder names, which spell none.
		rest := string(runes[1:])
		close, at := "", -1
		for _, c := range closes {
			if i := strings.Index(rest, c); i >= 0 && (at < 0 || i < at) {
				close, at = c, i
			}
		}
		if at < 0 {
			return nil, nil, fmt.Errorf("no closing %s", strings.Join(closes, " or "))
		}
		body, after := rest[:at], rest[at+len(close):]
		out := &dsl.Outfix{Open: open, Close: close, Sub: -1}
		for _, h := range strings.Split(body, ",") {
			pos, err := hole(h)
			if err != nil {
				if strings.HasPrefix(err.Error(), "an empty hole") {
					return nil, nil, fmt.Errorf("an empty hole between the delimiters")
				}
				return nil, nil, err
			}
			out.Body = append(out.Body, pos)
		}
		after = strings.TrimSpace(after)
		if after != "" {
			sub, isSub := strings.CutPrefix(after, "_")
			if !isSub || strings.TrimSpace(sub) == "" {
				return nil, nil, fmt.Errorf("after the closing %s only a `_binder` subscript may follow, got %q", close, after)
			}
			pos, err := hole(sub)
			if err != nil {
				return nil, nil, err
			}
			out.Sub = pos
		}
		return out, nil, complete()
	}

	// Prefix: the symbol before one hole.
	if open == "-" {
		pos, err := hole(string(runes[1:]))
		if err != nil {
			return nil, nil, err
		}
		return nil, &dsl.Operator{Symbol: "-", Args: []int{pos}}, complete()
	}

	// Infix: hole, symbol, hole — and the limit mixfix, the infix `⟶`
	// followed by its point clause `(at c)`, at arity three.
	fields := strings.Fields(string(runes))
	if len(fields) == 5 && fields[3] == "("+dsl.LimitPointClause && strings.HasSuffix(fields[4], ")") &&
		dsl.OperatorSymbolOK(fields[1], 3) {
		fn, err := hole(fields[0])
		if err != nil {
			return nil, nil, err
		}
		limit, err := hole(fields[2])
		if err != nil {
			return nil, nil, err
		}
		point, err := hole(strings.TrimSuffix(fields[4], ")"))
		if err != nil {
			return nil, nil, err
		}
		return nil, &dsl.Operator{Symbol: fields[1], Args: []int{fn, limit, point}}, complete()
	}
	if len(fields) != 3 || !dsl.OperatorSymbolOK(fields[1], 2) {
		return nil, nil, fmt.Errorf("a notation is an outfix (‖u‖_n, ⟪u, v⟫_n, ⁅x⁆, ⟦a, b⟭), an infix over a symbol the DSL parses (u + v, u - v, c • u, a ⟶ l, x ^ n; + - * / • ⟶ ^), the limit mixfix (f ⟶ l (at c)), or a prefix (-u)")
	}
	left, err := hole(fields[0])
	if err != nil {
		return nil, nil, err
	}
	right, err := hole(fields[2])
	if err != nil {
		return nil, nil, err
	}
	return nil, &dsl.Operator{Symbol: fields[1], Args: []int{left, right}}, complete()
}

// notationsOf is a single-constant door's notations table: the
// constant's declared surface, or no table when it is spelled by name.
func notationsOf(constName, surface string) map[string]string {
	if surface == "" {
		return nil
	}
	return map[string]string{constName: surface}
}

// declaredSurface is the one surface spelling a DefEntry declares for
// its constant — the Notation pattern, else the BigOp symbol, else the
// Overload word — kept on the entry for the corpus index.
func declaredSurface(e DefEntry) string {
	switch {
	case e.Notation != "":
		return e.Notation
	case e.BigOp != "":
		return e.BigOp
	case e.Coercion || e.NumeralCoercion:
		return "&"
	default:
		return e.Overload
	}
}

// oneLineTexts is texts each on one line (dsl.OneLine): a door's DSL
// texts as a chapter writes them, laid out over lines in its source,
// held and shown as the one string each reads as.
func oneLineTexts(texts []string) []string {
	if texts == nil {
		return nil
	}
	out := make([]string, len(texts))
	for i, text := range texts {
		out[i] = dsl.OneLine(text)
	}
	return out
}
