// vocabspec.go — the chapter vocabulary as DATA.
//
// A VocabSpec is the declarative form of a family's statement
// vocabulary: one row per name, consumed twice. The FRAMEWORK consumes
// it at script setup (Install runs as the family's vocab hook, so the
// elaborator reads the declaration directly), and the VOCAB GENERATOR
// (library/cmd/gen_family) consumes it to render the chapter's
// programmable-term surface — the ops struct whose *TermWrapper fields
// members build with — into zz_vocab_gen.go. The declaration is stated
// once and consumed, never narrated: the struct, the constructor, and
// the name-by-name restatement a hand-written vocab.go would carry are
// all derived from the rows (the theorem-citation wrappers'
// shape, applied to the constant half: a declaration consumed, not
// narrated).
//
// The division of knowledge is unchanged from the Alphabet contract:
// TYPES live in the domain's alphabet table (one spelling per domain),
// and WHICH names a chapter declares stays the chapter's own statement
// — the rows. A name outside the domain table spells its type in a
// Spelled row; everything a row cannot say goes through Custom, the
// escape hatch that keeps a chapter's odd genre hand-written without
// blocking the rest of its alphabet from being data.
//
// Every named row yields a handle. The old surface distinguished
// declared-only names from built names and spent prose justifying each
// handle's existence; here the handle is generated for every row and
// the distinction dissolves — an unused field costs nothing, and the
// prose that remains is about the mathematics. Nullary rows (Poly) are
// the one exception with teeth: their handles pin a ParseScope
// instance, so they are generated as build-site METHODS on the ops
// struct rather than constructor-time fields, preserving
// Alphabet.Pinned's timing discipline mechanically.
//
// The generated file addresses the spec through the package-level
// variable `vocab` — a naming convention WithVocabSpec documents and
// the compiler enforces (a differently-named spec leaves the generated
// file unable to resolve `vocab`, loudly).

package registry

import (
	"fmt"
	"strings"
	"unicode"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/proof"
)

// VocabSpec is one chapter's statement vocabulary as data. Construct
// with NewVocabSpec and the row builders at package-var time; register
// on the family with Family.WithVocabSpec.
type VocabSpec struct {
	alphabet *Alphabet
	opsName  string
	coerce   core.HolType
	rows     []*vocabRow
	byField  map[string]*vocabRow
}

type vocabRowKind int

const (
	rowTerm vocabRowKind = iota
	rowSpelled
	rowDefined
	rowPoly
	rowDeclare
	rowText
	rowBuilt
	rowFree
	rowEmbed
	rowCustom
)

// kindNames is the generator-facing spelling of each kind; RowInfos
// reports these and the renderer switches on them.
var kindNames = map[vocabRowKind]string{
	rowTerm: "term", rowSpelled: "spelled", rowDefined: "defined",
	rowPoly: "poly", rowDeclare: "declare", rowText: "text",
	rowBuilt: "built", rowFree: "free", rowEmbed: "embed",
	rowCustom: "custom",
}

type vocabRow struct {
	kind   vocabRowKind
	name   string // the constant's name (term/spelled/defined/poly); the free variable's (free)
	field  string // the generated Go surface name; "" only on declare/free/embed/custom rows
	names  []string
	typ    func() core.HolType
	text   string
	build  func(*proof.Script) *ext.TermWrapper
	fn     func(*proof.Script)
	bundle Bundle
}

// Bundle is a domain-owned builder a chapter embeds whole — the
// realvocab.Numerals shape: a struct of related handles whose
// construction the domain owns. Install runs at spec-install time (the
// bundle's declaration side effects must reach every statement door);
// the string fields tell the generator how to spell the embedded field
// and its constructor, since the registry cannot import the domain
// package that defines them.
type Bundle struct {
	// Path is the bundle package's import path; Pkg its package name.
	Path, Pkg string
	// Type is the embedded struct's name; New the constructor's, with
	// signature func(*proof.Script) Type.
	Type, New string
	// Install performs the bundle's declarations. The domain supplies
	// the constructor itself here (its handle result is discarded —
	// members reach handles through the generated embed).
	Install func(*proof.Script)
}

// NewVocabSpec starts a chapter vocabulary over the given domain
// alphabet. A chapter without a domain table passes nil and spells its
// types in Spelled rows.
func NewVocabSpec(alphabet *Alphabet) *VocabSpec {
	if alphabet == nil {
		// No domain table: every alphabet-routed row reads its type
		// off the constant's mint (alphabet.go's mintedEntry).
		alphabet = mintedAlphabet
	}
	return &VocabSpec{alphabet: alphabet, byField: map[string]*vocabRow{}}
}

// OpsName sets the generated ops struct's type name. The default,
// "vocabOps", serves a fresh chapter; a migrated chapter keeps its
// established name here so hand-written shorthand methods keep their
// receiver.
func (v *VocabSpec) OpsName(name string) *VocabSpec {
	v.opsName = name
	return v
}

// CoerceDomain declares the chapter's ambient numeric domain — an
// unanchored `&` in any member statement resolves to this domain's
// embedding by declaration, not by global default (ℝ, ℤ, or a type some
// constant is the declared coercion into — Family.WithCoerceDomain).
// Installed before any row.
func (v *VocabSpec) CoerceDomain(ty core.HolType) *VocabSpec {
	v.coerce = ty
	return v
}

// Term declares name through the domain alphabet — or, for a name the
// table does not carry, at the type its MINT registered — and yields
// its handle. The declaration is PINNED at one instance, which is what
// a chapter naming a constant beside its own type letters needs (`nil`
// in `dest_list(nil) = recspace_node(0, εv:A. ⊤, …)`); a chapter naming one
// at two instances at once declares it with Poly instead. The field
// name derives from the constant's own (int_add → IntAdd); As
// overrides.
func (v *VocabSpec) Term(name string) *VocabSpec {
	return v.add(vocabRow{kind: rowTerm, name: name, field: deriveField(name)})
}

// Spelled declares name at the given type — for the name whose type
// the domain table cannot carry (a pair-consuming int_gcd, a chapter
// with no table at all). typ is a func so every declaration mints
// fresh type-variable instances, the Alphabet convention.
func (v *VocabSpec) Spelled(name string, typ func() core.HolType) *VocabSpec {
	if typ == nil {
		panic(fmt.Sprintf("VocabSpec.Spelled(%q): nil type", name))
	}
	return v.add(vocabRow{kind: rowSpelled, name: name, field: deriveField(name), typ: typ})
}

// Defined declares a constant whose type is read off its registered
// meta — the row for a constant this chapter (or a sibling) MINTED, so
// its one authoritative type spelling is the mint itself. Refuses a
// polymorphic meta at install: a type with variables needs the author
// to choose the instance (Spelled) or keep it polymorphic (Poly).
func (v *VocabSpec) Defined(name string) *VocabSpec {
	return v.add(vocabRow{kind: rowDefined, name: name, field: deriveField(name)})
}

// Poly declares a name POLYMORPHICALLY (the ∅-class) through the domain
// alphabet: the chapter states it at more than one instance, so no
// constructor-time handle exists for it — a pinned instance in the
// ParseScope would fix the one instance every statement then reads —
// and the generator renders build-site methods instead
// (Alphabet.Pinned / PinnedAt semantics).
func (v *VocabSpec) Poly(name string) *VocabSpec {
	return v.add(vocabRow{kind: rowPoly, name: name, field: deriveField(name)})
}

// Declare registers names through the domain alphabet with no
// generated surface — for the name whose spelling cannot be a Go
// identifier and is never built (`,`). Everything else reads better as
// Term rows; this row is a syntactic necessity, not a chapter
// distinction.
func (v *VocabSpec) Declare(names ...string) *VocabSpec {
	return v.add(vocabRow{kind: rowDeclare, names: names})
}

// TermText yields a handle built by parsing text under the chapter
// scope at build time — the embedded-literal genre (`int_of_num(0)`).
// field names the handle; the text declares nothing, so every constant
// it mentions must have its own row above.
func (v *VocabSpec) TermText(field, text string) *VocabSpec {
	return v.add(vocabRow{kind: rowText, field: field, text: text})
}

// Built yields a handle a function constructs — the escape for a
// built term TermText cannot spell. The function runs at ops-build
// time, after Install.
func (v *VocabSpec) Built(field string, build func(*proof.Script) *ext.TermWrapper) *VocabSpec {
	if build == nil {
		panic(fmt.Sprintf("VocabSpec.Built(%q): nil builder", field))
	}
	return v.add(vocabRow{kind: rowBuilt, field: field, build: build})
}

// Free declares a chapter-standard free variable — the sequent-chapter
// genre, where every statement is written over the same frees.
func (v *VocabSpec) Free(name string, typ func() core.HolType) *VocabSpec {
	if typ == nil {
		panic(fmt.Sprintf("VocabSpec.Free(%q): nil type", name))
	}
	return v.add(vocabRow{kind: rowFree, name: name, typ: typ})
}

// Embed installs a domain-owned handle bundle and embeds it in the
// generated ops struct — see Bundle.
func (v *VocabSpec) Embed(b Bundle) *VocabSpec {
	if b.Install == nil || b.Path == "" || b.Pkg == "" || b.Type == "" || b.New == "" {
		panic("VocabSpec.Embed: incomplete Bundle — Path, Pkg, Type, New and Install are all required")
	}
	return v.add(vocabRow{kind: rowEmbed, bundle: b})
}

// Custom runs an arbitrary declaration closure at install — the
// escape hatch for what the rows do not model. Its one landed use is
// the mint file's initialization anchor: a closure naming the
// chapter's hand-minted metas, so Go initializes the mints before the
// family (the mint itself must NOT run at install — that would
// re-register per Script and trip the exclusive-registration guard).
// Handles for a Custom genre stay hand-written beside the spec.
func (v *VocabSpec) Custom(fn func(*proof.Script)) *VocabSpec {
	if fn == nil {
		panic("VocabSpec.Custom: nil closure")
	}
	return v.add(vocabRow{kind: rowCustom, fn: fn})
}

// As renames the previous row's generated surface — field name for a
// handle row, method name for a Poly row. Required where the derived
// name is not the one (`Term("int_add").As("Add")`) or cannot
// exist (`Term("+").As("Plus")`).
func (v *VocabSpec) As(field string) *VocabSpec {
	if len(v.rows) == 0 {
		panic("VocabSpec.As: no preceding row")
	}
	last := v.rows[len(v.rows)-1]
	switch last.kind {
	case rowTerm, rowSpelled, rowDefined, rowPoly, rowText, rowBuilt:
	default:
		panic(fmt.Sprintf("VocabSpec.As(%q): the preceding row (%s) has no generated surface to name", field, kindNames[last.kind]))
	}
	if v.byField[last.field] == last {
		delete(v.byField, last.field)
	}
	last.field = field
	v.claimField(last)
	return v
}

func (v *VocabSpec) add(r vocabRow) *VocabSpec {
	v.rows = append(v.rows, &r)
	last := v.rows[len(v.rows)-1]
	// An invalid derived name is not yet an error — the author's .As
	// may be the next call. finalize (run at WithVocabSpec) is what
	// demands every surface name be settled.
	if last.field != "" && validField(last.field) {
		v.claimField(last)
	}
	return v
}

func (v *VocabSpec) claimField(r *vocabRow) {
	if !validField(r.field) {
		panic(fmt.Sprintf("VocabSpec: %q derives no exported Go identifier (got %q) — name the surface with .As(…)", r.name, r.field))
	}
	if prev, dup := v.byField[r.field]; dup {
		panic(fmt.Sprintf("VocabSpec: rows %q and %q both claim surface name %s — rename one with .As(…)", prev.name, r.name, r.field))
	}
	v.byField[r.field] = r
}

// finalize demands every handle-bearing row settled on a valid
// surface name — the check add defers so `.As` can rescue a name the
// mechanical derivation cannot render (`Term("+").As("Plus")`).
func (v *VocabSpec) finalize() {
	for _, r := range v.rows {
		switch r.kind {
		case rowTerm, rowSpelled, rowDefined, rowPoly, rowText, rowBuilt:
			if v.byField[r.field] != r {
				panic(fmt.Sprintf("VocabSpec: %q derives no exported Go identifier (got %q) — name the surface with .As(…)", r.name, r.field))
			}
		}
	}
}

// deriveField is the mechanical name transform: strip nothing, split
// on '_', title-case each part (empty_set → Empty, int_add → IntAdd,
// bit1 → Bit1). A name it cannot render (operators, `_0`) yields an
// invalid identifier, which claimField converts into the .As demand.
func deriveField(name string) string {
	var b strings.Builder
	for _, part := range strings.Split(name, "_") {
		runes := []rune(part)
		for i, r := range runes {
			if i == 0 {
				b.WriteRune(unicode.ToUpper(r))
				continue
			}
			b.WriteRune(unicode.ToLower(r))
		}
	}
	return b.String()
}

func validField(f string) bool {
	for i, r := range f {
		switch {
		case i == 0 && !unicode.IsUpper(r):
			return false
		case !unicode.IsLetter(r) && !unicode.IsDigit(r):
			return false
		}
	}
	return f != ""
}

// ----- The framework half: Install -----------------------------------------

// Install declares the whole spec into ctx — the family vocab hook.
// Rows run in order, so a Custom closure may rely on the declarations
// above it.
func (v *VocabSpec) Install(ctx *proof.Script) {
	if v.coerce != nil {
		ctx.CoerceDomain(v.coerce)
	}
	for _, r := range v.rows {
		switch r.kind {
		case rowTerm:
			// A Term row is the chapter saying it names ONE instance:
			// pinned, nullary or not (Alphabet.Term says why the choice
			// is the chapter's and not the type's).
			v.alphabet.DeclarePinned(ctx, r.name)
		case rowPoly:
			v.alphabet.Declare(ctx, r.name)
		case rowSpelled:
			ctx.Const(r.name, r.typ())
		case rowDefined:
			ctx.Const(r.name, v.definedType(ctx, r.name))
		case rowDeclare:
			v.alphabet.Declare(ctx, r.names...)
		case rowFree:
			ctx.Var(r.name, r.typ())
		case rowEmbed:
			r.bundle.Install(ctx)
		case rowCustom:
			r.fn(ctx)
		case rowText, rowBuilt:
			// handle-only rows: nothing to declare
		}
	}
}

func (v *VocabSpec) definedType(ctx *proof.Script, name string) core.HolType {
	ty := ctx.ConstMeta(name).AbsType()
	if len(ty.TypeVars()) > 0 {
		panic(fmt.Sprintf(
			"VocabSpec.Defined(%q): the registered meta is polymorphic (%s) — choose the instance with Spelled, or keep it polymorphic with Poly",
			name, ext.FormatType(ty)))
	}
	return ty
}

// ----- The generated half's runtime: handles --------------------------------

// Handle builds the handle for the named surface field — the generated
// constructor's one verb. Field-keyed: the generated struct and this
// lookup share the spec's surface names, and the drift gate keeps the
// two in step.
func (v *VocabSpec) Handle(ctx *proof.Script, field string) *ext.TermWrapper {
	r := v.field(field)
	switch r.kind {
	case rowTerm:
		return v.alphabet.Term(ctx, r.name)
	case rowSpelled:
		return ctx.Const(r.name, r.typ())
	case rowDefined:
		return ctx.Const(r.name, v.definedType(ctx, r.name))
	case rowText:
		return ctx.TermText(r.text)
	case rowBuilt:
		return r.build(ctx)
	case rowPoly:
		panic(fmt.Sprintf("VocabSpec.Handle(%q): nullary — the generated build-site method routes through PinnedHandle", field))
	}
	panic(fmt.Sprintf("VocabSpec.Handle(%q): row kind %s has no handle", field, kindNames[r.kind]))
}

// PinnedHandle is a Poly row's build-site handle at the domain's
// generic instance — Alphabet.Pinned through the spec.
func (v *VocabSpec) PinnedHandle(ctx *proof.Script, field string) *ext.TermWrapper {
	return v.alphabet.Pinned(ctx, v.polyRow(field).name)
}

// PinnedHandleAt is PinnedHandle at a chosen element type —
// Alphabet.PinnedAt through the spec.
func (v *VocabSpec) PinnedHandleAt(ctx *proof.Script, field string, elem core.HolType) *ext.TermWrapper {
	return v.alphabet.PinnedAt(ctx, v.polyRow(field).name, elem)
}

func (v *VocabSpec) polyRow(field string) *vocabRow {
	r := v.field(field)
	if r.kind != rowPoly {
		panic(fmt.Sprintf("VocabSpec: %q is not a Poly row", field))
	}
	return r
}

func (v *VocabSpec) field(field string) *vocabRow {
	r, ok := v.byField[field]
	if !ok {
		known := make([]string, 0, len(v.byField))
		for f := range v.byField {
			known = append(known, f)
		}
		panic(fmt.Sprintf("VocabSpec: no row named %s — known surface names: %s (stale zz_vocab_gen.go? re-run go generate)",
			field, strings.Join(known, ", ")))
	}
	return r
}

// ----- The generator's read surface -----------------------------------------

// VocabRowInfo is one row as the generator and the drift gate see it.
type VocabRowInfo struct {
	Kind   string // a kindNames value
	Name   string
	Field  string
	Names  []string
	Text   string
	Bundle Bundle
}

// RowInfos snapshots the rows for rendering.
func (v *VocabSpec) RowInfos() []VocabRowInfo {
	out := make([]VocabRowInfo, 0, len(v.rows))
	for _, r := range v.rows {
		out = append(out, VocabRowInfo{Kind: kindNames[r.kind], Name: r.name, Field: r.field, Names: r.names, Text: r.text, Bundle: r.bundle})
	}
	return out
}

// OpsTypeName is the generated struct's type name.
func (v *VocabSpec) OpsTypeName() string {
	if v.opsName == "" {
		return "vocabOps"
	}
	return v.opsName
}

// ElemVar reports the domain alphabet's element type variable ("" when
// the domain has none, or there is no alphabet) — the generator emits
// a Poly row's …At method only when one exists.
func (v *VocabSpec) ElemVar() string {
	if v.alphabet == nil {
		return ""
	}
	return v.alphabet.elem
}
