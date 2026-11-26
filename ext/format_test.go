package ext

import (
	"fmt"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
)

func checkFormat[T any](t *testing.T, s T, f string) {
	assert.Equal(t, fmt.Sprint(s), f)
}

func checkLatex(t *testing.T, s Term, f string) {
	assert.Equal(t, FormatTerm(s, true), f)
}

func TestFormatType(t *testing.T) {
	Prod := core.MakeCompositeType(core.MakeMetaType("Prod", 2), TypeA, TypeInd)
	// Option D: every VarType is `var:<name>`; arity-0 composite is bare.
	assert.Equal(t, FormatType(Prod),
		"Prod(var:A,ind)")
	assert.Equal(t, FormatType(MakeFun(MakeFun(TypeBool, TypeA), TypeInd)),
		"((bool → var:A) → ind)")
	assert.Equal(t, FormatType(MakeFun(TypeBool, TypeA, TypeInd)),
		"((bool, var:A) → ind)")
}

func TestFormatTerm(t *testing.T) {
	x := WrapTerm(core.Var(utils.Subscript(utils.X_DOT, 0), TypeA))
	y := WrapTerm(Abs(x.AssertVar(), x).DeBruijn(0).(AbsTerm).Var())
	z := WrapTerm(core.Var(utils.Subscript(utils.AlphaStr, 1), TypeA))
	h := Var(utils.H_STROKE, TypeBool)
	f := Var(utils.F_HOOK+utils.PrimeStr, MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeBool, TypeBool))
	R := Var("R", MakeFun(TypeBool, TypeA, TypeBool))
	checkFormat(t, x.To(x.SuchThat(P.Apply(x))), "λẋ₀.(εẋ₀.P(ẋ₀))")
	checkFormat(t, x.SuchThat(P.Apply(x)).Eq(y), "(εẋ₀.P(ẋ₀)) = %1")
	checkFormat(t, x.To(P.Apply(x)).Apply(y), "(λẋ₀.P(ẋ₀))(%1)")
	checkFormat(t, P.Apply((x.To(x)).Apply(y)), "P((λẋ₀.ẋ₀)(%1))")
	checkFormat(t, x.To(y.To(h)).Apply(x), "(λẋ₀.λ%1.ħ)(ẋ₀)")
	checkFormat(t, x.To(y.To(h)).Apply(y, x), "(λẋ₀.λ%1.ħ)(%1, ẋ₀)")
	checkFormat(t, ForAll(x, y)(h), "∀ẋ₀.∀%1.ħ")
	checkFormat(t, ForAll(x)(Exists(y)(h)), "∀ẋ₀.∃%1.ħ")
	checkFormat(t, WrapTerm(x.SuchThat(P.Apply(x)).Core().(AppliedTerm).Fun()).Apply(P), "ε(P)")
	checkFormat(t, P.SuchThat(P.Apply(x)), "εP.P(ẋ₀)")
	checkFormat(t, P.SuchThat(P.Apply(x)).Apply(x), "(εP.P(ẋ₀))(ẋ₀)")
	checkFormat(t, P.SuchThat(h.Eq(P.Apply(x))).Apply(x), "(εP.(ħ ⇔ P(ẋ₀)))(ẋ₀)")
	checkFormat(t, R.SuchThat(R.Apply(h, x)).Apply(h, x), "(εR.R(ħ, ẋ₀))(ħ, ẋ₀)")
	checkFormat(t, Q.Apply(Q.Apply(h)), "Q(Q(ħ))")
	checkFormat(t, Q.Apply(h.And(Q.Apply(h))), "Q(ħ ∧ Q(ħ))")
	checkFormat(t, Not(h), "¬ħ")
	checkFormat(t, Not(P.Apply(x)), "¬P(ẋ₀)")
	checkFormat(t, Not(R.Apply(P.Apply(x), y)), "¬R(P(ẋ₀), %1)")
	checkFormat(t, Not(ForAll(x)(P.Apply(z))), "¬(∀ẋ₀.P(α₁))")
	checkFormat(t, R.Apply(h, y).Imply(Q.Apply(h)), "R(ħ, %1) ⇒ Q(ħ)")
	checkFormat(t, R.Apply(h, y).Xor(Q.Apply(h).Or(h)), "R(ħ, %1) ⊕ (Q(ħ) ∨ ħ)")
	checkFormat(t, R.Apply(h, y).And(h.Xor(h)), "R(ħ, %1) ∧ (ħ ⊕ ħ)")
	checkFormat(t, Not(R.Apply(h, y)).And(h.Eq(h)), "¬R(ħ, %1) ∧ (ħ ⇔ ħ)")
	checkFormat(t, Not(h.And(h)).Or(R.Apply(h, y)), "¬(ħ ∧ ħ) ∨ R(ħ, %1)")
	checkFormat(t, h.And(Not(Q.Apply(T))), "ħ ∧ ¬Q(⊤)")
	checkFormat(t, Not(h.And(Not(Q.Apply(T)))), "¬(ħ ∧ ¬Q(⊤))")
	checkFormat(t, Exists(f)(f.Apply(x).Eq(x)), "∃ƒʹ.(ƒʹ(ẋ₀) = ẋ₀)")
	checkFormat(t, P.To((Unique(h)(ForAll(x)(P.Apply(x).Imply(h)).Imply(h))).
		Or(Exists(x)(ForAll(y)((P.Apply(x)).And(P.Apply(y)).Imply(x.Neq(y)))))).Apply(P),
		"(λP.((∃!ħ.((∀ẋ₀.(P(ẋ₀) ⇒ ħ)) ⇒ ħ)) ∨ (∃ẋ₀.∀%1.((P(ẋ₀) ∧ P(%1)) ⇒ (ẋ₀ ≠ %1)))))(P)")
}

func TestTermlatex(t *testing.T) {
	x := Var(TermName(utils.Subscript(utils.X_DOT, 0)), TypeA)
	y := WrapTerm(Abs(x.AssertVar(), x).DeBruijn(0).(AbsTerm).Var())
	z := Var("α_1", TypeA)
	h := Var(utils.H_STROKE, TypeBool)
	f := Var(utils.F_HOOK+utils.PrimeStr, MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeBool, TypeBool))
	R := Var("R", MakeFun(TypeBool, TypeA, TypeBool))
	checkLatex(t, x.To(x.SuchThat(P.Apply(x))), "\\lambda{\\dot{x}_0}.\\left(\\varepsilon{\\dot{x}_0}.{P}\\left({\\dot{x}_0}\\right)\\right)")
	checkLatex(t, x.SuchThat(P.Apply(x)).Eq(y), "\\left(\\varepsilon{\\dot{x}_0}.{P}\\left({\\dot{x}_0}\\right)\\right)={\\%1}")
	checkLatex(t, x.To(P.Apply(x)).Apply(y), "\\left(\\lambda{\\dot{x}_0}.{P}\\left({\\dot{x}_0}\\right)\\right)\\left({\\%1}\\right)")
	checkLatex(t, P.Apply((x.To(x)).Apply(y)), "{P}\\left(\\left(\\lambda{\\dot{x}_0}.{\\dot{x}_0}\\right)\\left({\\%1}\\right)\\right)")
	checkLatex(t, x.To(y.To(h)).Apply(x), "\\left(\\lambda{\\dot{x}_0}.\\lambda{\\%1}.{\\hbar}\\right)\\left({\\dot{x}_0}\\right)")
	checkLatex(t, x.To(y.To(h)).Apply(y, x), "\\left(\\lambda{\\dot{x}_0}.\\lambda{\\%1}.{\\hbar}\\right)\\left({\\%1}, {\\dot{x}_0}\\right)")
	checkLatex(t, ForAll(x, y)(h), "\\forall{\\dot{x}_0}.\\forall{\\%1}.{\\hbar}")
	checkLatex(t, ForAll(x)(Exists(y)(h)), "\\forall{\\dot{x}_0}.\\exists{\\%1}.{\\hbar}")
	checkLatex(t, WrapTerm(x.SuchThat(P.Apply(x)).Core().(AppliedTerm).Fun()).Apply(P), "\\varepsilon\\left({P}\\right)")
	checkLatex(t, P.SuchThat(P.Apply(x)), "\\varepsilon{P}.{P}\\left({\\dot{x}_0}\\right)")
	checkLatex(t, P.SuchThat(P.Apply(x)).Apply(x), "\\left(\\varepsilon{P}.{P}\\left({\\dot{x}_0}\\right)\\right)\\left({\\dot{x}_0}\\right)")
	checkLatex(t, P.SuchThat(h.Eq(P.Apply(x))).Apply(x), "\\left(\\varepsilon{P}.\\left({\\hbar}\\iff{P}\\left({\\dot{x}_0}\\right)\\right)\\right)\\left({\\dot{x}_0}\\right)")
	checkLatex(t, R.SuchThat(R.Apply(h, x)).Apply(h, x), "\\left(\\varepsilon{R}.{R}\\left({\\hbar}, {\\dot{x}_0}\\right)\\right)\\left({\\hbar}, {\\dot{x}_0}\\right)")
	checkLatex(t, Q.Apply(Q.Apply(h)), "{Q}\\left({Q}\\left({\\hbar}\\right)\\right)")
	checkLatex(t, Q.Apply(h.And(Q.Apply(h))), "{Q}\\left({\\hbar}\\wedge{Q}\\left({\\hbar}\\right)\\right)")
	checkLatex(t, Not(h), "\\neg{\\hbar}")
	checkLatex(t, Not(P.Apply(x)), "\\neg{P}\\left({\\dot{x}_0}\\right)")
	checkLatex(t, Not(R.Apply(P.Apply(x), y)), "\\neg{R}\\left({P}\\left({\\dot{x}_0}\\right), {\\%1}\\right)")
	checkLatex(t, Not(ForAll(x)(P.Apply(z))), "\\neg\\left(\\forall{\\dot{x}_0}.{P}\\left({\\alpha_1}\\right)\\right)")
	checkLatex(t, R.Apply(h, y).Imply(Q.Apply(h)), "{R}\\left({\\hbar}, {\\%1}\\right)\\Rightarrow{Q}\\left({\\hbar}\\right)")
	checkLatex(t, R.Apply(h, y).Xor(Q.Apply(h).Or(h)), "{R}\\left({\\hbar}, {\\%1}\\right)\\oplus\\left({Q}\\left({\\hbar}\\right)\\vee{\\hbar}\\right)")
	checkLatex(t, R.Apply(h, y).And(h.Xor(h)), "{R}\\left({\\hbar}, {\\%1}\\right)\\wedge\\left({\\hbar}\\oplus{\\hbar}\\right)")
	checkLatex(t, Not(R.Apply(h, y)).And(h.Eq(h)), "\\neg{R}\\left({\\hbar}, {\\%1}\\right)\\wedge\\left({\\hbar}\\iff{\\hbar}\\right)")
	checkLatex(t, Not(h.And(h)).Or(R.Apply(h, y)), "\\neg\\left({\\hbar}\\wedge{\\hbar}\\right)\\vee{R}\\left({\\hbar}, {\\%1}\\right)")
	checkLatex(t, h.And(Not(Q.Apply(T))), "{\\hbar}\\wedge\\neg{Q}\\left(\\top\\right)")
	checkLatex(t, Not(h.And(Not(Q.Apply(T)))), "\\neg\\left({\\hbar}\\wedge\\neg{Q}\\left(\\top\\right)\\right)")
	checkLatex(t, Exists(f)(f.Apply(x).Eq(x)), "\\exists{\\mathsf{f}'}.\\left({\\mathsf{f}'}\\left({\\dot{x}_0}\\right)={\\dot{x}_0}\\right)")
	checkLatex(t, P.To((Unique(h)(ForAll(x)(P.Apply(x).Imply(h)).Imply(h))).
		Or(Exists(x)(ForAll(y)((P.Apply(x)).And(P.Apply(y)).Imply(x.Neq(y)))))).Apply(P),
		"\\left(\\lambda{P}.\\left(\\left(\\exists!{\\hbar}.\\left(\\left(\\forall{\\dot{x}_0}.\\left({P}\\left({\\dot{x}_0}\\right)"+
			"\\Rightarrow{\\hbar}\\right)\\right)\\Rightarrow{\\hbar}\\right)\\right)\\vee"+
			"\\left(\\exists{\\dot{x}_0}.\\forall{\\%1}.\\left(\\left({P}\\left({\\dot{x}_0}\\right)\\wedge{P}\\left({\\%1}\\right)\\right)"+
			"\\Rightarrow\\left({\\dot{x}_0}\\neq{\\%1}\\right)\\right)\\right)\\right)\\right)\\left({P}\\right)")
}

func TestExtraConsts(t *testing.T) {
	x := Var("x", TypeInd)
	y := Var("y", TypeInd)
	c0 := TestConst("<=", MakeFun(TypeInd, TypeInd, TypeBool))
	c1 := TestConst("<", MakeFun(TypeInd, TypeInd, TypeBool))
	c2 := TestConst("ID", MakeFun(TypeInd, TypeInd))
	c3 := TestConst("nat_div", MakeFun(TypeInd, TypeInd, TypeInd))
	// A unary const carrying a custom display format. Deliberately NOT
	// named after a numeral-alphabet const (_0/bit0/bit1): those
	// are reserved for num literals, and the printer's decimal-collapse
	// fold probes any such-named head against the canonical num-typed meta
	// — a same-named ind→ind impostor would (correctly) trip core's
	// "a name fixes a type" assertion.
	c4 := TestConst("UOP", MakeFun(TypeInd, TypeInd))

	addConstFmt("<=", defaultInfix("≤", "\\le"))
	addConstFmt("<", defaultInfix("<", "<"))
	addConstFmt("ID", _ConstTermFormat{Invisible: true})
	addConstFmt("nat_div", _ConstTermFormat{
		FmtTempl: FmtTemplate{
			2,
			func(s ...string) string { return fmt.Sprintf("%s/%s", s[0], s[1]) }},
		LatexTempl: FmtTemplate{
			2,
			func(s ...string) string { return fmt.Sprintf("\\frac{%s}{%s}", s[0], s[1]) }}})
	addConstFmt("UOP",
		_ConstTermFormat{Format: "B0", Latex: "\\textsf{B}_0"})

	checkFormat(t, c0.Apply(x, y), "x ≤ y")
	checkLatex(t, c0.Apply(x, y), "{x}\\le{y}")
	checkFormat(t, c1.Apply(x, y), "x < y")
	checkLatex(t, c1.Apply(x, y), "{x}<{y}")
	checkFormat(t, c2.Apply(x), "x")
	checkLatex(t, c2.Apply(x), "{x}")
	checkFormat(t, c3.Apply(c3.Apply(x, y), c3.Apply(y, x)),
		"(x/y)/(y/x)")
	checkLatex(t, c3.Apply(c3.Apply(x, y), c3.Apply(y, x)),
		"\\frac{\\left(\\frac{{x}}{{y}}\\right)}{\\left(\\frac{{y}}{{x}}\\right)}")
	checkFormat(t, c4.Apply(x), "B0(x)")
	checkLatex(t, c4.Apply(x), "{\\textsf{B}_0}\\left({x}\\right)")
}

// TestFormat_DisambiguateConstTypeConflict covers the printer contract that
// two structurally-distinct terms must never produce identical output strings.
// The motivating case is finiteness of a product universe — `finite(universe:(A#B)->bool) ⇔
// finite(universe:A->bool) ∧ finite(universe:B->bool)` — where default pretty-printing
// elides type annotations and lets both sides of the iff print as
// `finite(universe)`, misleading any reader (human or agent) into thinking the
// proposition is a tautology. The fix: when a polymorphic const appears in a
// term with more than one distinct holType, annotate every occurrence with
// its type instantiation.
func TestFormat_DisambiguateConstTypeConflict(t *testing.T) {
	// Build finite : (A→bool)→bool and universe : A→bool as polymorphic metas.
	finiteMeta := core.MakeConstMeta(
		core.TermName("finite"),
		MakeFun(MakeFun(TypeA, TypeBool), TypeBool))
	univMeta := core.MakeConstMeta(
		core.TermName("universe"),
		MakeFun(TypeA, TypeBool))

	// Two instantiations at distinct concrete types.
	finiteBool := Const(finiteMeta, MakeFun(MakeFun(TypeBool, TypeBool), TypeBool))
	univBool := Const(univMeta, MakeFun(TypeBool, TypeBool))
	finiteInd := Const(finiteMeta, MakeFun(MakeFun(TypeInd, TypeBool), TypeBool))
	univInd := Const(univMeta, MakeFun(TypeInd, TypeBool))

	lhs := finiteBool.Apply(univBool)
	rhs := finiteInd.Apply(univInd)

	// iff at type bool prints as ⇔.
	iff := lhs.Eq(rhs)

	// The LHS and RHS are structurally different ConstTerms (different
	// holTypes). Default pretty-printing without disambiguation would print
	// both sides identically as `finite(universe) ⇔ finite(universe)`. With
	// disambiguation, every finite and universe gets a type annotation suffix.
	got := FormatTerm(iff, false)
	assert.Equal(t,
		"finite⟨A:bool⟩(𝕌⟨A:bool⟩) ⇔ finite⟨A:ind⟩(𝕌⟨A:ind⟩)",
		got)

	// Printer contract: distinct subterms never produce identical output strings.
	// Split the output on ⇔ and verify the two sides are textually different.
	parts := splitOnIff(got)
	assert.Len(t, parts, 2)
	assert.NotEqual(t, parts[0], parts[1],
		"LHS and RHS of iff must print distinctly when structurally different")
}

// TestFormat_DisambiguateConstInProdType takes a statement over a product
// type: finite(universe:(A#B)->bool) ⇔
// finite(universe:A->bool) ∧ finite(universe:B->bool).
//
// Three distinct finite instantiations and three distinct universe instantiations
// appear in the term. Instantiated occurrences get ⟨A:...⟩ annotations from
// their TypeSubsts; the abstract-type occurrence (finite at its meta's
// abstract type (A→bool)→bool — empty TypeSubsts) gets EXPLICIT IDENTITY
// pairs (`finite⟨A:var:A⟩`) so the parser can pin the abstract instance
// instead of resolving the bare name against whatever single instance the
// scope holds (see formatConstTypeAnnotation). JSON is unchanged — it still
// omits `inst` for abstract instances.
func TestFormat_DisambiguateConstInProdType(t *testing.T) {
	finiteMeta := core.MakeConstMeta(
		core.TermName("finite"),
		MakeFun(MakeFun(TypeA, TypeBool), TypeBool))
	univMeta := core.MakeConstMeta(
		core.TermName("universe"),
		MakeFun(TypeA, TypeBool))

	prodAB := MakeProdType(TypeA, TypeB)

	// LHS: finite(universe : (A#B)→bool)
	finiteAB := Const(finiteMeta, MakeFun(MakeFun(prodAB, TypeBool), TypeBool))
	univAB := Const(univMeta, MakeFun(prodAB, TypeBool))
	lhs := finiteAB.Apply(univAB)

	// RHS conjunct 1: finite(universe : A→bool) — at abstract type, TypeSubsts empty.
	finiteA := Const(finiteMeta, MakeFun(MakeFun(TypeA, TypeBool), TypeBool))
	univA := Const(univMeta, MakeFun(TypeA, TypeBool))
	finiteUnivA := finiteA.Apply(univA)

	// RHS conjunct 2: finite(universe : B→bool) — subst A=B.
	finiteB := Const(finiteMeta, MakeFun(MakeFun(TypeB, TypeBool), TypeBool))
	univB := Const(univMeta, MakeFun(TypeB, TypeBool))
	finiteUnivB := finiteB.Apply(univB)

	rhs := finiteUnivA.And(finiteUnivB)
	iff := lhs.Eq(rhs)

	got := FormatTerm(iff, false)

	// Instantiated occurrences carry the inst-map annotation, matching the
	// keys/values the JSON marshaler would put in the `inst` map. Inner
	// VarTypes (A, B inside prod, or B itself) carry the Option D `var:`
	// prefix; the inst-map *key* (A) is the var name as a string, not a
	// FormatType output, so it stays bare.
	assertContainsAll(t, got,
		"finite⟨A:prod(var:A,var:B)⟩",
		"𝕌⟨A:prod(var:A,var:B)⟩",
		"finite⟨A:var:B⟩",
		"𝕌⟨A:var:B⟩",
	)
	// The abstract-type occurrence has empty TypeSubsts; under a conflict
	// it prints explicit identity pairs so the occurrence still names its
	// instance (JSON continues to omit the `inst` field for this case).
	assert.Contains(t, got, "finite⟨A:var:A⟩(𝕌⟨A:var:A⟩) ∧",
		"abstract-instance finite(universe) should carry identity annotation, got: %s", got)

	// Printer contract: both sides of the iff must be textually distinct.
	parts := splitOnIff(got)
	assert.Len(t, parts, 2)
	assert.NotEqual(t, parts[0], parts[1])
}

// TestFormat_UnrecoverableInstanceAnnotates pins the round-trip
// contract (the elaboration layer's printer leg): a polymorphic-const
// occurrence whose instance the printed term cannot re-derive
// annotates even with NO conflict in the prop — a lone `finite(𝕌)` at
// bool would otherwise re-parse at whatever instance the scope offers,
// silently a different theorem (identical print, distinct statements —
// the injectivity receipts). A grounded occurrence stays bare: a
// variable operand's printed type re-derives the instance.
func TestFormat_UnrecoverableInstanceAnnotates(t *testing.T) {
	finiteMeta := core.MakeConstMeta(
		core.TermName("finite"),
		MakeFun(MakeFun(TypeA, TypeBool), TypeBool))
	univMeta := core.MakeConstMeta(
		core.TermName("universe"),
		MakeFun(TypeA, TypeBool))

	// Single finite(universe) at one concrete type — no conflict, but
	// nothing in the printed term re-derives bool: both names pin.
	finiteBool := Const(finiteMeta, MakeFun(MakeFun(TypeBool, TypeBool), TypeBool))
	univBool := Const(univMeta, MakeFun(TypeBool, TypeBool))
	term := finiteBool.Apply(univBool)

	got := FormatTerm(term, false)
	assert.Contains(t, got, "finite⟨A:bool⟩")
	assert.Contains(t, got, "𝕌⟨A:bool⟩")

	// A variable operand grounds the instance — bare render preserved.
	s := core.Var(core.TermName("s"), MakeFun(TypeBool, TypeBool))
	assert.Equal(t, "finite(s)", FormatTerm(finiteBool.Apply(s), false))
}

// TestFormat_PolyBinderAnnotations covers the inspect-surface printer mode:
// polymorphic ∀/∃/∃!/λ binders gain a `:type` annotation; concrete binders
// stay bare; FormatTerm itself is unchanged.
//
// The motivating phenomenon is a polymorphic ∀-lemma whose binder types
// silently collapse across an `instantiate`: the residual hyp still carries a
// polymorphic binder (e.g. `∀f.…` where f : (A,B)→B), but the type-erased
// print hides the polymorphism, so the agent has no signal that the next
// `instantiate` witness must match a particular shape. Annotating polymorphic
// binders surfaces the constraint at the moment the agent is looking at the
// hyp, not five ministeps later when an instantiation fails.
func TestFormat_PolyBinderAnnotations(t *testing.T) {
	// Polymorphic binder: ∀f. f : (A,B)→B. We expect the inspect printer
	// to surface `(A,B)→B` (in parser-curry form).
	fPoly := Var("f", MakeFun(TypeA, TypeB, TypeB))
	bodyPoly := Var("b", TypeB)
	polyTerm := ForAll(fPoly)(bodyPoly.Eq(bodyPoly))

	gotInspect := PrintTermWithPolyBinders(polyTerm)
	assert.Equal(t, "∀f:(var:A → (var:B → var:B)).(b = b)", gotInspect,
		"polymorphic ∀-binder should print with `:type`")

	// Plain FormatTerm stays type-erased (the human-comment surface).
	gotPlain := PrintTerm(polyTerm)
	assert.Equal(t, "∀f.(b = b)", gotPlain,
		"plain FormatTerm must not annotate binders")

	// Concrete binder: ∀n. n : num. Annotation is suppressed even under
	// the poly mode — no information would be added.
	nConc := Var("n", TypeInd)
	concTerm := ForAll(nConc)(nConc.Eq(nConc))

	gotConcInspect := PrintTermWithPolyBinders(concTerm)
	assert.Equal(t, "∀n.(n = n)", gotConcInspect,
		"concrete ∀-binder should print exactly as PrintTerm")
	assert.Equal(t, gotConcInspect, PrintTerm(concTerm),
		"poly-binder printer must agree with PrintTerm on concrete binders")

	// λ-binder: same poly-only rule applies. The set_fold_stage-style residual hyp
	// has a λf : (A,B)→B inside; surfacing the binder type works the same.
	lamPoly := Abs(fPoly.AssertVar(), bodyPoly)
	gotLam := PrintTermWithPolyBinders(lamPoly)
	assert.Equal(t, "λf:(var:A → (var:B → var:B)).b", gotLam)

	// Mixed: one polymorphic binder + one concrete binder + one
	// polymorphic binder. Only the polymorphic ones get annotated, but the
	// shared multi-binder collapse still runs (∀f.∀n.∀g.…), so the output
	// pattern is `∀f:….∀n.∀g:….body`.
	gPoly := Var("g", MakeFun(TypeA, TypeA))
	multi := ForAll(fPoly, nConc, gPoly)(bodyPoly.Eq(bodyPoly))
	gotMulti := PrintTermWithPolyBinders(multi)
	assert.Contains(t, gotMulti, "∀f:(var:A → (var:B → var:B)).")
	assert.Contains(t, gotMulti, "∀n.") // concrete num stays bare
	assert.Contains(t, gotMulti, "∀g:(var:A → var:A).")
}

// TestFormat_PolyBinderForParser_Unchanged is a regression guard: the parser
// round-trip mode (FormatTermForParser) must keep annotating every binder
// regardless of shape — the new binderPoly mode is a separate axis from
// binderAll, and parser callers must not slip onto the new path.
func TestFormat_PolyBinderForParser_Unchanged(t *testing.T) {
	nConc := Var("n", TypeInd)
	concTerm := ForAll(nConc)(nConc.Eq(nConc))
	// FormatTermForParser still emits `:ind` on the concrete binder.
	assert.Equal(t, "∀n:ind.(n = n)", FormatTermForParser(concTerm))
}

// splitOnIff splits a string on the ⇔ delimiter, trimming whitespace around
// each part.
func splitOnIff(s string) []string {
	parts := strings.Split(s, "⇔")
	out := make([]string, len(parts))
	for i, p := range parts {
		out[i] = strings.TrimSpace(p)
	}
	return out
}

func assertContainsAll(t *testing.T, s string, subs ...string) {
	t.Helper()
	for _, sub := range subs {
		assert.Contains(t, s, sub,
			"expected output to contain %q, got: %s", sub, s)
	}
}
