// Tests for ParseScope.StrictResolution — the statement doors' strict
// name resolution (an undeclared name errors instead of freshening to a
// free variable), and the loose default the machine dialect keeps.
package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

func strictScope() *ParseScope { return &ParseScope{StrictResolution: true} }

func requireStrictError(t *testing.T, res ParseResult, name string) {
	t.Helper()
	if len(res.Errors) == 0 {
		t.Fatalf("expected a strict-resolution error naming %q, got a successful parse", name)
	}
	msg := res.Errors[0].Message
	if !strings.Contains(msg, "strict resolution") || !strings.Contains(msg, name) {
		t.Fatalf("expected a strict-resolution error naming %q, got: %s", name, msg)
	}
}

func requireParses(t *testing.T, res ParseResult) {
	t.Helper()
	if len(res.Errors) > 0 {
		t.Fatalf("expected a successful parse, got: %s", res.Errors[0].Message)
	}
	if res.Prop == nil {
		t.Fatal("expected a Prop")
	}
}

// A bare undeclared name in boolean context freshens as a bool variable
// under loose resolution — the class-1 signature. Strict rejects it,
// naming the name.
func TestStrictRejectsBareUndeclaredBoolAtom(t *testing.T) {
	requireStrictError(t, ParsePropTextInScope("∀m:num. m = m ∧ oops", strictScope()), "oops")
}

// An undeclared applied head whose result type is recoverable from
// context freshens as a function-typed variable under loose resolution.
// Strict rejects.
func TestStrictRejectsUndeclaredAppliedHead(t *testing.T) {
	requireStrictError(t, ParsePropTextInScope("∀n:num. foo(n) = n", strictScope()), "foo")
}

// An undeclared name typed by its equality partner freshens under loose
// resolution — the nullary-const shape (`𝕌`/`∅` receipts). Strict rejects.
func TestStrictRejectsEqualityPartnerFreshening(t *testing.T) {
	requireStrictError(t, ParsePropTextInScope("∀s:(A → bool). s = mystery", strictScope()), "mystery")
}

// Quantified names, in-text decls, and scope-declared Vars all resolve.
func TestStrictAcceptsDeclaredForms(t *testing.T) {
	requireParses(t, ParsePropTextInScope("∀m:num. m = m", strictScope()))
	requireParses(t, ParsePropTextInScope("x:bool ⊢ x ∨ ¬x", strictScope()))
	scope := &ParseScope{
		StrictResolution: true,
		Vars:             map[string]core.HolType{"x": core.TypeBool()},
	}
	requireParses(t, ParsePropTextInScope("x ∨ ¬x", scope))
}

// A name the const resolver supplies is a constant, not a freshening.
func TestStrictAcceptsResolverConst(t *testing.T) {
	scope := &ParseScope{
		StrictResolution: true,
		ConstResolver: func(name string) core.ConstTermMeta {
			if name == "predecessor" {
				return NatPreMeta
			}
			return core.ConstTermMeta{}
		},
	}
	requireParses(t, ParsePropTextInScope("∀n:num. predecessor(n) = predecessor(n)", scope))
	// Without the resolver, a use whose result type IS inferable (the
	// equality partner pins it) would have freshened — strict rejects
	// it. (predecessor is deliberately absent from the default nat scope; the
	// uninferable spelling `predecessor(n) = predecessor(n)` is already rejected by the
	// undeclared-head fail-fast, strict or not.)
	requireStrictError(t, ParsePropTextInScope("∀n:num. predecessor(n) = n", strictScope()), "predecessor")
}

// The DSL-side surface fallback (set-theory metas) still resolves under
// strict — P1a rejects FRESHENING; the def-less-fallback question is
// the resolver-precedence seam, deliberately unchanged here.
func TestStrictKeepsSurfaceFallback(t *testing.T) {
	requireParses(t, ParsePropTextInScope("∀s:(A → bool). ∅ ⊆ s", strictScope()))
}

// The machine dialect keeps the loose default: without the flag, an
// undeclared applied head freshens exactly as before.
func TestLooseDefaultStillFreshens(t *testing.T) {
	requireParses(t, ParsePropTextInScope("∀n:num. foo(n) = n", &ParseScope{}))
	requireParses(t, ParsePropText("∀n:num. foo(n) = n"))
}

// ----- StrictMint — the class-2 false-mint guard ---------------------

func strictMintScope() *ParseScope { return &ParseScope{StrictMint: true} }

func requireStrictMintError(t *testing.T, res ParseResult, needle string) {
	t.Helper()
	if len(res.Errors) == 0 {
		t.Fatalf("expected a strict-mint error naming %q, got a successful parse", needle)
	}
	msg := res.Errors[0].Message
	if !strings.Contains(msg, "strict mint") || !strings.Contains(msg, needle) {
		t.Fatalf("expected a strict-mint error naming %q, got: %s", needle, msg)
	}
}

// A bare polymorphic head freezes its own abstract letters — the
// class-2 false-mint shape. Rejected, with the tie spelling named.
func TestStrictMintRejectsBareHeads(t *testing.T) {
	requireStrictMintError(t,
		ParsePropTextInScope("∀n:num. subset(∅, ∅) ⇒ n = n", strictMintScope()), "subset")
	requireStrictMintError(t,
		ParsePropTextInScope("∅ = 𝕌", strictMintScope()), "empty_set")
	// The message spells the repair.
	res := ParsePropTextInScope("∅ = 𝕌", strictMintScope())
	if !strings.Contains(res.Errors[0].Message, "⟨") {
		t.Fatalf("strict-mint message must spell the ⟨⟩ tie, got: %s", res.Errors[0].Message)
	}
}

// A ⟨⟩ tie is authorial intent: a concrete pin erases the variable, a
// letter pin anchors it (the type-letter genre with ties written out —
// the pre-minting rule).
func TestStrictMintAcceptsTiedHeads(t *testing.T) {
	requireParses(t, ParsePropTextInScope("∀n:num. subset(∅⟨A:num⟩, ∅⟨A:num⟩) ⇒ n = n", strictMintScope()))
	requireParses(t, ParsePropTextInScope("subset⟨A:B⟩(∅⟨A:B⟩, ∅⟨A:B⟩)", strictMintScope()))
}

// A binder whose type mentions the variable anchors it — ordinary
// polymorphic statements stay bare.
func TestStrictMintAcceptsBinderAnchored(t *testing.T) {
	requireParses(t, ParsePropTextInScope("∀s:(A → bool). ∅ ⊆ s", strictMintScope()))
}

// Loose default unchanged: the same bare heads still parse.
func TestStrictMintLooseDefault(t *testing.T) {
	requireParses(t, ParsePropTextInScope("∅ = 𝕌", &ParseScope{}))
}

// ----- CoerceDomain — the class-3 ambient-domain policy ---------------

func intDomainScope() *ParseScope { return &ParseScope{CoerceDomain: IntType} }

func conclConstNames(t *testing.T, p core.Prop) map[string]bool {
	t.Helper()
	consts := map[core.TermKey]core.ConstTerm{}
	ext.CollectConstTerms(p.Conclusion(), consts)
	out := map[string]bool{}
	for _, c := range consts {
		out[string(c.Name())] = true
	}
	return out
}

// The receipt's silent shape — no anchor, both sides coerced: the
// declared domain decides; the loose default stays ℝ.
func TestCoerceDomainDecidesUnanchored(t *testing.T) {
	text := "∀m:num. ∀n:num. (&m = &n) ⇔ (m = n)"
	res := ParsePropTextInScope(text, intDomainScope())
	requireParses(t, res)
	names := conclConstNames(t, res.Prop)
	if !names["int_of_num"] || names["real_of_num"] {
		t.Fatalf("declared int domain must lower & to int_of_num, got consts %v", names)
	}
	loose := ParsePropTextInScope(text, &ParseScope{})
	requireParses(t, loose)
	if !conclConstNames(t, loose.Prop)["real_of_num"] {
		t.Fatal("loose scope must keep the legacy real default")
	}
}

// Anchors beat the declaration, in both directions — an operand type
// the author spelled is intent, so bridge statements cost nothing.
func TestCoerceDomainYieldsToAnchors(t *testing.T) {
	res := ParsePropTextInScope("∀x:int. x + &2 = x", &ParseScope{CoerceDomain: RealType})
	requireParses(t, res)
	if !conclConstNames(t, res.Prop)["int_of_num"] {
		t.Fatal("an int-typed partner must anchor & to int_of_num even under a real declaration")
	}
	res2 := ParsePropTextInScope("∀x:real. x + &2 = x", intDomainScope())
	requireParses(t, res2)
	if !conclConstNames(t, res2.Prop)["real_of_num"] {
		t.Fatal("a real-typed partner must anchor & to real_of_num even under an int declaration")
	}
}

// The COND boundary from the receipts dissolves under a declaration:
// no anchor reaches inside a conditional, so the domain decides.
func TestCoerceDomainReachesUnderCOND(t *testing.T) {
	res := ParsePropTextInScope("∀m:num. COND(m = m, &m, &0) = &1", intDomainScope())
	requireParses(t, res)
	names := conclConstNames(t, res.Prop)
	if !names["int_of_num"] || names["real_of_num"] {
		t.Fatalf("declared domain must reach under COND, got consts %v", names)
	}
}

// Strict doors reject a SURVIVING pure-default coercion, naming the
// repairs; one the reconcile retargets is anchored and still parses,
// and a declared domain removes the default entirely.
func TestStrictRejectsUnanchoredDefaultCoerce(t *testing.T) {
	res := ParsePropTextInScope("∀m:num. ∀n:num. (&m = &n) ⇔ (m = n)", strictScope())
	if len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "unanchored") {
		t.Fatalf("expected the unanchored-& strict error, got %v", res.Errors)
	}
	requireParses(t, ParsePropTextInScope("∀x:int. x + &2 = x", strictScope()))
	requireParses(t, ParsePropTextInScope("∀m:num. ∀n:num. (&m = &n) ⇔ (m = n)",
		&ParseScope{StrictResolution: true, CoerceDomain: IntType}))
	// A same-domain partner exonerates: the default agreed with an
	// author-typed real neighbour (`&0 + x`, `real_inv(&0) = &0`).
	requireParses(t, ParsePropTextInScope("∀x:real. &0 + x = x", strictScope()))
	requireParses(t, ParsePropTextInScope("∀x:real. x ≠ &0 ⇒ x * x ≠ &0", strictScope()))
	// Both-sides-coerced stays flagged — the silent-ℝ receipt shape.
	res2 := ParsePropTextInScope("∀m:num. ∀n:num. &(m + n) = &m + &n", strictScope())
	if len(res2.Errors) == 0 || !strings.Contains(res2.Errors[0].Message, "unanchored") {
		t.Fatalf("expected the unanchored-& strict error for the both-coerced shape, got %v", res2.Errors)
	}
}

// The declared domain flows into TERM texts — the nothing-but-a-
// coercion receipt bites bodies (`&(val(w))` as a witness has no
// operator application to anchor it).
func TestCoerceDomainAppliesToTerms(t *testing.T) {
	res := ParseTermTextInScope("&(m)", map[string]core.HolType{"m": NumType}, intDomainScope(), nil)
	if len(res.Errors) > 0 {
		t.Fatalf("term parse failed: %s", res.Errors[0].Message)
	}
	consts := map[core.TermKey]core.ConstTerm{}
	ext.CollectConstTerms(res.Term, consts)
	for _, c := range consts {
		if string(c.Name()) == "int_of_num" {
			return
		}
	}
	t.Fatal("declared int domain must lower a bare term-text & to int_of_num")
}

// The guard on `&` stands by itself. A claim door resolves names
// loosely at the parse (it reports an undeclared name itself, after)
// and must still refuse an `&` nothing anchors where no domain is
// declared: read without the guard, `&m < &n` is silently a statement
// about ℝ. A declared domain answers it, and so does an anchor.
func TestStrictCoercionAlone(t *testing.T) {
	vars := func() map[string]core.HolType {
		return map[string]core.HolType{"m": NumType, "n": NumType, "x": RealType}
	}
	refused := ParsePropTextInScope("&m < &n", &ParseScope{Vars: vars(), StrictCoercion: true})
	if len(refused.Errors) == 0 || !strings.Contains(refused.Errors[0].Message, "unanchored") {
		t.Fatalf("expected the unanchored-& error under the guard alone, got %v", refused.Errors)
	}

	declared := ParsePropTextInScope("&m < &n", &ParseScope{Vars: vars(), StrictCoercion: true, CoerceDomain: IntType})
	requireParses(t, declared)
	if names := conclConstNames(t, declared.Prop); !names["int_of_num"] || names["real_of_num"] {
		t.Fatalf("the declared domain must decide, got consts %v", names)
	}

	anchored := ParsePropTextInScope("x < &n", &ParseScope{Vars: vars(), StrictCoercion: true})
	requireParses(t, anchored)

	// Names stay loose: the guard is the `&` half of strict resolution
	// and no more of it.
	loose := ParsePropTextInScope("x < &n ∧ undeclared", &ParseScope{Vars: vars(), StrictCoercion: true})
	requireParses(t, loose)
	strict := ParsePropTextInScope("x < &n ∧ undeclared", &ParseScope{Vars: vars(), StrictResolution: true})
	if len(strict.Errors) == 0 {
		t.Fatal("strict resolution refuses the undeclared name")
	}

	// Without the guard and without a domain the legacy default stands.
	silent := ParsePropTextInScope("&m < &n", &ParseScope{Vars: vars()})
	requireParses(t, silent)
}
