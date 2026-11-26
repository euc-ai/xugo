// Arithmetic constants and numeric-literal lowering for the text DSL.
//
// The text parser recognizes nat-domain infix operators (+, -, *, <,
// ≤, >, ≥, ≠) and numeric literals (0, 1, 42, …). They lower to
// applications of the const metas defined here.
//
// The metas are constructed name+absType-locally; alpha-key equality
// with the registry's metas for the same consts holds whenever the
// (name, absType) pair matches (ConstTerm.AlphaKey hashes only name +
// instantiated type, not meta identity — see core/const_term.go).
// Drift between these and the registry manifests as test failures in
// the corpus round-trip suite.
//
// Polymorphic-instance support (the same `+` at type real, etc.) is
// deferred: the operator table dispatches by symbol only, always to
// the nat instance. The natOperator switch is structured so that
// adding a (symbol, domain) layer later is a local change.

package dsl

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// NumMetaType / NumType are the meta-level and HOL `num` types. The
// canonical definitions, the BIT-tower alphabet, and the big.Int
// conversion helpers live in the shared bridge ext/numeral.go; these
// are re-exports, so every `dsl.NumType` / `dsl.ZeroMeta` callsite (and
// every emitted proof) resolves to the single instance there.
var NumMetaType = ext.NumMetaType

// NumType is the HOL `num` type.
var NumType = ext.NumType

// Nat-domain arithmetic const metas. Each meta's (name, absType)
// must match the chapter mint of the same name (peano, arith,
// nat_order, nat_monus, nat_div_mod, nat_parity) — round-trip tests
// verify this. All are monomorphic, so meta.Term() returns a non-nil
// canonical ConstTerm.
var (
	NatPlusMeta  = core.MakeConstMeta("+", core.MakeFun(NumType, NumType, NumType))
	NatMinusMeta = core.MakeConstMeta("-", core.MakeFun(NumType, NumType, NumType))
	NatStarMeta  = core.MakeConstMeta("*", core.MakeFun(NumType, NumType, NumType))
	NatDivMeta   = core.MakeConstMeta("nat_div", core.MakeFun(NumType, NumType, NumType))
	NatModMeta   = core.MakeConstMeta("nat_mod", core.MakeFun(NumType, NumType, NumType))
	NatMaxMeta   = core.MakeConstMeta("nat_max", core.MakeFun(NumType, NumType, NumType))
	NatMinMeta   = core.MakeConstMeta("nat_min", core.MakeFun(NumType, NumType, NumType))
	NatPreMeta   = core.MakeConstMeta("predecessor", core.MakeFun(NumType, NumType))
	NatExpMeta   = core.MakeConstMeta("nat_pow", core.MakeFun(NumType, NumType, NumType))
	// factorial n = n! (a recursive definition). Like predecessor/nat_even/nat_odd it is NOT a
	// default-scope const (corpus proofs bind `factorial` as the recursion's ∃-var);
	// omega builds/matches it via this meta and folds a LITERAL factorial(c) to its
	// numeral value (omega's factSimp).
	NatFactMeta = core.MakeConstMeta("factorial", core.MakeFun(NumType, NumType))
	// nat_dist(m,n) = (m-n)+(n-m) is the num distance (|m-n|), the foundation of the
	// nat→real lift. Its argument is a PAIR: nat_dist : num#num → num. Defined by
	// a plain definition (no ∃nat_dist binding in any proof), so — unlike predecessor/nat_even/nat_odd —
	// it is safe in the default scope, alongside nat_max/nat_min/nat_div/nat_mod. omega bridges it
	// into the monus layer (omega's nat_sub.go).
	NatDistMeta = core.MakeConstMeta("nat_dist", core.MakeFun(ext.MakeProdType(NumType, NumType), NumType))
	// nat_even/nat_odd are num→bool predicates (recursive definitions). Like predecessor they
	// are NOT default-scope consts (corpus proofs bind `nat_even`/`nat_odd` as the
	// recursion's ∃-vars); omega builds/matches them via these metas directly, and
	// the parity bridge routes them into the nat_mod-2 layer (omega/nat_sub.go).
	NatEvenMeta   = core.MakeConstMeta("nat_even", core.MakeFun(NumType, core.TypeBool()))
	NatOddMeta    = core.MakeConstMeta("nat_odd", core.MakeFun(NumType, core.TypeBool()))
	NatLtMeta     = core.MakeConstMeta("<", core.MakeFun(NumType, NumType, core.TypeBool()))
	NatLeMeta     = core.MakeConstMeta("<=", core.MakeFun(NumType, NumType, core.TypeBool()))
	NatGtMeta     = core.MakeConstMeta(">", core.MakeFun(NumType, NumType, core.TypeBool()))
	NatGeMeta     = core.MakeConstMeta(">=", core.MakeFun(NumType, NumType, core.TypeBool()))
	NatNumsegMeta = core.MakeConstMeta("..", core.MakeFun(NumType, NumType, NumType, core.TypeBool()))
	// NatDividesMeta: `nat_divides d n` — d divides n, defined inside ℕ
	// (proofs/nat_num/nat_divides). The infix surface is `d ∣ n`
	// (U+2223, NOT the ASCII set-builder pipe), dispatched by operand
	// type alongside int_divides — see arithOperator.
	NatDividesMeta = core.MakeConstMeta("nat_divides", core.MakeFun(NumType, NumType, core.TypeBool()))

	// _0/bit0/bit1 encode natural-number literals (a literal n is the
	// BIT-tower over these; see ext/numeral.go). Re-exported from the
	// shared bridge so the parser, omega, and the library all build/read
	// numerals through one big.Int-backed path.
	ZeroMeta = ext.ZeroMeta
	Bit0Meta = ext.Bit0Meta
	Bit1Meta = ext.Bit1Meta

	// suc is included with the nat literal encoders: it has no infix
	// surface and every induction over num states it, so the parser
	// resolves it as a well-known const and a text needs no declaration
	// for it (which is also why peano's SucDef spells its definiendum by
	// a stand-in).
	SUCMeta = core.MakeConstMeta("suc", core.MakeFun(NumType, NumType))
)

// natOperator returns the const meta for a recognized nat-arith
// operator symbol, or nil. Keyed by the operator's lex form (ASCII
// for +-*<>, and the normalized Unicode ≤/≥ for those).
func natOperator(op string) core.ConstTermMeta {
	switch op {
	case "+":
		return NatPlusMeta
	case "-":
		return NatMinusMeta
	case "*":
		return NatStarMeta
	case "<":
		return NatLtMeta
	case "≤":
		return NatLeMeta
	case ">":
		return NatGtMeta
	case "≥":
		return NatGeMeta
	case "∣":
		return NatDividesMeta
	case "..":
		return NatNumsegMeta
	}
	return core.ConstTermMeta{}
}

// defaultNatScopeConsts is the const-table every typeEnv seeds at
// construction time, exposed via env.scopeConsts. These are the
// foundational constants the DSL must always be able to resolve by name
// without the caller supplying a scope:
//
//   - _0, bit0, bit1 — the irreducible alphabet for binary numeric
//     literals (`42` = `bit0(bit1(bit0(bit1(bit1(_0)))))`). Cannot
//     write any numeral without these three.
//   - suc — no infix syntax, foundational to every nat induction.
//     Structurally identical to predecessor/nat_mod/nat_div/SUB/nat_max/nat_min; included by
//     convention as a frequently-used non-infix const. Add others here
//     when the convention warrants.
//
// Polymorphic foundational consts (the pair constructor `,`) live only
// in defaultNatScopeConstMetas — they have no single fixed instance, so
// there is no entry here. buildApp's meta-only branch instantiates them
// per use-site.
//
// MEMBERSHIP RULE — read before adding a name. A constant belongs in
// the default scope iff NO corpus proof BINDS a variable of that name.
// In practice that tracks how the constant is introduced:
//
//	a plain definition       → eligible.  nat_max, nat_min, nat_div, nat_mod, nat_dist:
//	                           nothing ever binds them, so a default
//	                           const shadows nothing.
//	a recursive definition   → NOT eligible. The recursion's existence
//	                           proof reads `∃f. …`, so the corpus binds
//	                           a VARIABLE of that name (nat_pow's own seed:
//	                           `⊢ (∀x.∃nat_pow.P(x, nat_pow)) ⇔ (∃nat_pow.∀x.P(x,
//	                           nat_pow(x)))`). A default const of that name
//	                           shadows the bound var and breaks the
//	                           parse — which is why predecessor, factorial, nat_even, nat_odd
//	                           and nat_pow are absent, each noted at its
//	                           declaration below.
//
// The trap this rule exists to stop: the METAS are declared side by
// side (NatExpMeta sits between NatPreMeta and NatFactMeta, all built
// by MakeConstMeta exactly like NatMaxMeta), because omega must build
// and match every one of these terms. Scope membership answers a
// different question, and inferring it from the declarations (adding
// nat_pow to "fix the ragged list") would break every proof that binds a
// variable named nat_pow. A name kept out is reached
// through ParseScope.ConstResolver instead, which resolves to the
// registry's DEF-CARRYING meta — strictly safer than a default entry
// would be, since a default entry's meta here is DEF-LESS and
// identity-distinct from the ConstMetaManager's.
//
// To extend the default set, satisfy the rule above, then add an entry
// here and in defaultNatScopeConstMetas. Caller-supplied scope
// (ParseScope.Consts) merges on top, with the default winning on
// collision: a well-known name beats caller scope.
var defaultNatScopeConsts = map[string]core.ConstTerm{
	"_0":       ZeroMeta.Term(),
	"bit0":     Bit0Meta.Term(),
	"bit1":     Bit1Meta.Term(),
	"suc":      SUCMeta.Term(),
	"nat_max":  NatMaxMeta.Term(), // non-infix, like suc (a case-split client of omega's nat_sub.go)
	"nat_min":  NatMinMeta.Term(),
	"nat_div":  NatDivMeta.Term(), // non-infix; nat_div/nat_mod layer (omega's nat_divmod.go)
	"nat_mod":  NatModMeta.Term(),
	"nat_dist": NatDistMeta.Term(), // num distance; bridges to monus (omega's nat_sub.go)
	// NOTE: predecessor is deliberately NOT a default-scope const. It is defined by
	// a recursive definition, so corpus proofs bind a variable named `predecessor` (the
	// recursion's `∃predecessor. …`); a default const `predecessor` shadows that bound var and
	// breaks their parse. omega builds/matches predecessor via NatPreMeta directly; tests
	// that need to parse `predecessor(n)` pass it through ParsePropTextInScope.
	// real_of_num: the `&` real-literal embedding. Always
	// available so every `&n` (which parser.go desugars to real_of_num(n))
	// resolves without a caller-supplied scope, like the nat encoders.
	"real_of_num": RealOfNumMeta.Term(),
	// int_of_num: the int-literal embedding (num→int). The PRINTED form of an
	// int literal (`int_of_num(n)`, the round-trip-safe alternative to `&n`,
	// which defaults to real), so it must resolve by name in the default scope
	// for the print→reparse loop, exactly like real_of_num.
	"int_of_num": IntOfNumMeta.Term(),
}

// defaultNatScopeConstMetas mirrors defaultNatScopeConsts at the meta
// level, used by buildApp's polymorphic-instantiation fallback when a
// scopeConsts entry's fixed instance doesn't match an application's
// arg types. For monomorphic nat encoders this fallback never fires,
// but populating both keeps the channels symmetric.
//
// The pair constructor `,` is registered here (and intentionally NOT in
// defaultNatScopeConsts — it is polymorphic A → B → prod(A, B), no
// single fixed instance) so parseAtom's tokComma branch resolves
// `,(a, b)` through the meta-only branch of buildApp. Without this,
// the printer-emitted form for pair applications (e.g. `,(qʹ, pʹ)`)
// would not round-trip back through the parser even after the
// grammar accepts the syntax.
//
// COND is the same shape: polymorphic bool → A → A → A, no single fixed
// instance, so it lives meta-only. The text printer emits applied COND as
// `COND(p, x, y)` (ext.FormatTermForParser), but without this registration
// the parser treats `COND` as an undeclared head and builds a free *var*
// named "COND" instead of the ext.COND const — so ext.MatchesCond (and the
// omega trivialCondRewrite cascade that depends on it) never fires on any
// text-DSL goal containing a conditional. Registering the meta routes
// `COND(...)` through buildAppViaMeta, instantiating at the branch type.
var defaultNatScopeConstMetas = map[string]core.ConstTermMeta{
	"_0":       ZeroMeta,
	"bit0":     Bit0Meta,
	"bit1":     Bit1Meta,
	"suc":      SUCMeta,
	"nat_max":  NatMaxMeta,
	"nat_min":  NatMinMeta,
	"nat_div":  NatDivMeta,
	"nat_mod":  NatModMeta,
	"nat_dist": NatDistMeta,
	// predecessor omitted on purpose — see defaultNatScopeConsts.
	"real_of_num": RealOfNumMeta, // `&` embedding
	"int_of_num":  IntOfNumMeta,  // int-literal embedding (printed form; see above)
	",":           ext.CommaConstMeta,
	"COND":        ext.COND.Meta(), // polymorphic if-then-else; see note above
	// `..` segment: prefix-call form `..(m, n)` / `..(m, n, p)` resolves
	// through the meta-only branch of buildApp, exactly like `,` and COND.
	// The infix form `m..n` reaches NatNumsegMeta via the arithOperator
	// path in buildBinOp; this entry is what lets the prefix form (and
	// any agent-asserted text DSL that pre-dates the infix lex) build
	// the same const-applied term.
	"..": NatNumsegMeta,
}

// RealMetaType is the meta-level "real" type (the reals; 0-ary
// type constant). Structurally equal to what resolveType produces for the
// bare type name "real", so `x:real` declarations resolve to RealType.
var RealMetaType = core.MakeMetaType("real", 0)

// RealType is the HOL `real` type.
var RealType core.HolType = core.MakeCompositeType(RealMetaType)

// Real is `:real` as a phantom of the typed term surface
// (ext.TypePhantom), declared beside the metatype it reifies per the
// vocabulary's decentralization rule (ext/holtype_phantom.go).
type Real struct{}

func (Real) Reify() ext.HolType { return RealType }

// Real-domain arithmetic const metas, NAMED AS THE REGISTRY NAMES THEM
// (real_add/real_mul/…): every recorded key and every chapter statement
// lives in that vocabulary — so the metas must share it for AlphaKeys to
// match (the same reason the nat metas reuse the registry's `+`/`<`).
//
// The OVERLOADED-SYMBOL surface survives unchanged: the agent still writes
// `x + y` / `x < y` at real operands — realOperator/arithOperator dispatch on
// the LEX SYMBOL + operand type, never on the const name — and the printer
// renders these consts back as infix symbols (ext/format.go's name map). A
// side benefit: no same-name-different-type `+`/`<` metas, which the
// name-keyed LoadConstMeta layer could not represent.
var (
	RealPlusMeta = core.MakeConstMeta("real_add", core.MakeFun(RealType, RealType, RealType))
	RealStarMeta = core.MakeConstMeta("real_mul", core.MakeFun(RealType, RealType, RealType))
	RealSubMeta  = core.MakeConstMeta("real_sub", core.MakeFun(RealType, RealType, RealType))
	RealNegMeta  = core.MakeConstMeta("real_neg", core.MakeFun(RealType, RealType))
	RealLtMeta   = core.MakeConstMeta("real_lt", core.MakeFun(RealType, RealType, core.TypeBool()))
	RealLeMeta   = core.MakeConstMeta("real_le", core.MakeFun(RealType, RealType, core.TypeBool()))
	RealGtMeta   = core.MakeConstMeta("real_gt", core.MakeFun(RealType, RealType, core.TypeBool()))
	RealGeMeta   = core.MakeConstMeta("real_ge", core.MakeFun(RealType, RealType, core.TypeBool()))

	// RealAbsMeta is `real_abs : real → real`
	// (`abs x = COND(&0 ≤ x, x, −x)`); RealMaxMeta / RealMinMeta are
	// `real_max`/`real_min : real → real → real` (piecewise by `x ≤ y`); RealSgnMeta
	// is `real_sgn : real → real` (the three-way sign, a nested COND). All four are
	// piecewise-by-comparison, eliminated by the real case split (omega/real_ops.go) —
	// the real twins of the int int_abs/int_max/int_min/int_sgn handlers.
	RealAbsMeta = core.MakeConstMeta("real_abs", core.MakeFun(RealType, RealType))
	RealMaxMeta = core.MakeConstMeta("real_max", core.MakeFun(RealType, RealType, RealType))
	RealMinMeta = core.MakeConstMeta("real_min", core.MakeFun(RealType, RealType, RealType))
	RealSgnMeta = core.MakeConstMeta("real_sgn", core.MakeFun(RealType, RealType))
	// RealPowMeta is `real_pow : real → num → real` (the exponent is num).
	// A literal exponent unfolds to a product chain (omega's realPowUnfold), the real twin
	// of int_pow / num nat_pow.
	RealPowMeta = core.MakeConstMeta("real_pow", core.MakeFun(RealType, NumType, RealType))
	// RealDivMeta / RealInvMeta are `real_div : real → real → real`
	// (`x / y = x · inv y`) and `real_inv : real → real` (multiplicative inverse).
	// omega's field layer clears denominators / cancels inverses; it has
	// no int twin (ℤ has Euclidean int_div/int_rem instead).
	RealDivMeta = core.MakeConstMeta("real_div", core.MakeFun(RealType, RealType, RealType))
	RealInvMeta = core.MakeConstMeta("real_inv", core.MakeFun(RealType, RealType))

	// RealOfNumMeta is the `&` coercion num→real. The agent never writes
	// the name (it writes `&n`); it is the desugar target and the head of
	// every real literal.
	RealOfNumMeta = core.MakeConstMeta("real_of_num", core.MakeFun(NumType, RealType))
)

// realOperator returns the real-domain const meta for an overloaded
// arith/comparison operator symbol, or nil if the symbol has no real
// instance. Keyed by the same canonical lex forms as natOperator
// (ASCII + - * < >, normalized Unicode ≤/≥). `-` is `real_sub` (TOTAL
// subtraction, unlike num's truncated monus).
func realOperator(op string) core.ConstTermMeta {
	switch op {
	case "+":
		return RealPlusMeta
	case "-":
		return RealSubMeta
	case "*":
		return RealStarMeta
	case "/":
		return RealDivMeta
	case "<":
		return RealLtMeta
	case "≤":
		return RealLeMeta
	case ">":
		return RealGtMeta
	case "≥":
		return RealGeMeta
	}
	return core.ConstTermMeta{}
}

// intOperator returns the int-domain const meta for an overloaded
// arith/comparison operator symbol, or nil if the symbol has no int
// instance. Same canonical lex forms; `-` is `int_sub` (TOTAL). The int
// analog of realOperator — the agent surface dispatches `+ - * < ≤ > ≥` to
// int when both operands are int-typed.
func intOperator(op string) core.ConstTermMeta {
	switch op {
	case "+":
		return IntPlusMeta
	case "-":
		return IntSubMeta
	case "*":
		return IntStarMeta
	case "<":
		return IntLtMeta
	case "≤":
		return IntLeMeta
	case ">":
		return IntGtMeta
	case "≥":
		return IntGeMeta
	case "∣":
		return IntDividesMeta
	}
	return core.ConstTermMeta{}
}

// isArithOperator reports whether `op` is one of the overloaded
// arith/comparison symbols (+ - * / < ≤ > ≥ ∣ ..). Membership is the union
// over the arith domains, not the num layer alone: `/` is real division and
// has no num or int instance, because ℕ's truncated and ℤ's Euclidean
// division keep an applied spelling (the overloaded words `div(m, n)` and
// `rem(m, n)`) rather than acquiring a second notation for a different
// operation.
// (Every other overloaded symbol is still num-anchored, and the other domains
// only add instances for symbols num already spells.) Callers that need the
// per-domain instance use arithDomainOperator; a symbol with no instance at
// the operand's domain is reported there, which is what turns `m / n` at num
// into "operator / has no instance for operand type num" rather than a parse
// error about an unknown character.
func isArithOperator(op string) bool {
	for _, table := range []func(string) core.ConstTermMeta{
		natOperator, realOperator, intOperator,
		hrealOperator, naddOperator, trealOperator,
	} {
		if !table(op).IsZero() {
			return true
		}
	}
	return false
}

// NativeConstNames is the set of constant names the parser builds
// WITHOUT resolving them through a scope or a registry: the default
// nat-scope constants (numerals, suc, nat_div, the embeddings `&` and
// the int literal, `,`, COND, `..`), every operator's constant at every
// arithmetic domain (`+` at num, real_add at real, hreal_add at hreal,
// …) and the three powers. A text spelling one of these parses whether
// or not the chapter that mints it has initialized, so nothing need
// order that mint before the text — which is what the definition
// gate (library/integrity/gates) asks of every other constant a
// definition's equation spells.
func NativeConstNames() map[string]bool {
	out := map[string]bool{}
	for name := range defaultNatScopeConstMetas {
		out[name] = true
	}
	for _, table := range []func(string) core.ConstTermMeta{
		natOperator, realOperator, intOperator, hrealOperator, naddOperator, trealOperator,
	} {
		for _, op := range []string{"+", "-", "*", "/", "<", "≤", ">", "≥", "∣", ".."} {
			if m := table(op); !m.IsZero() {
				out[string(m.Name())] = true
			}
		}
	}
	for _, m := range []core.ConstTermMeta{NatExpMeta, RealPowMeta, IntPowMeta} {
		out[string(m.Name())] = true
	}
	return out
}

// arithDomainOperator returns the const meta for overloaded operator `op` at
// operand domain `ty`, or nil when `ty` is not an arith domain or `op` has no
// instance there (`-` over hreal, say, which the tower does not define).
//
// This is the operator-table dispatch arith.go's header anticipated, keyed by
// (symbol, operand type) rather than by const name — which is what lets one
// surface symbol serve six domains whose consts are named entirely differently
// (`+` is `+` at num, `real_add` at real, `hreal_add` at hreal, …).
func arithDomainOperator(op string, ty core.HolType) core.ConstTermMeta {
	switch {
	case ty.Equals(NumType):
		return natOperator(op)
	case ty.Equals(RealType):
		return realOperator(op)
	case ty.Equals(IntType):
		return intOperator(op)
	case ty.Equals(HrealType):
		return hrealOperator(op)
	case ty.Equals(NaddType):
		return naddOperator(op)
	case ty.Equals(TrealType):
		return trealOperator(op)
	}
	return core.ConstTermMeta{}
}

// powDomainOperator returns the power constant the BASE's domain picks
// for `x ^ n` — nat_pow at num, real_pow at real, int_pow at int, the
// exponent num in each — or nil when the base is in none of them: a
// type variable, ℂ, the tower layers. The power is the one overloaded
// symbol whose two operands do not share a domain, so it has its own
// table rather than a row in the per-domain ones; the build asks it
// first and, where it answers nil, the constant declaring `^` at that
// arity (operator.go — comm_monoid's monoid_pow under a bound
// operation).
func powDomainOperator(base core.HolType) core.ConstTermMeta {
	switch {
	case base.Equals(NumType):
		return NatExpMeta
	case base.Equals(RealType):
		return RealPowMeta
	case base.Equals(IntType):
		return IntPowMeta
	}
	return core.ConstTermMeta{}
}

// arithDomainNames lists the arith domains in dispatch order, for error
// messages. Kept beside arithDomainOperator so the two cannot drift.
const arithDomainNames = "num, real, int, hreal, nadd, or treal (hreal × hreal)"

// IntMetaType is the meta-level "int" type (the integers; 0-ary type
// constant). Structurally equal to what resolveType produces for the bare type
// name "int", so `x:int` declarations resolve to IntType.
var IntMetaType = core.MakeMetaType("int", 0)

// IntType is the HOL `int` type.
var IntType core.HolType = core.MakeCompositeType(IntMetaType)

// Int is `:int` as a phantom of the typed term surface, beside its
// metatype exactly as Real is beside RealMetaType.
type Int struct{}

func (Int) Reify() ext.HolType { return IntType }

// Integer-domain arithmetic const metas, NAMED AS THE REGISTRY NAMES THEM
// (int_add/int_mul/…), exactly as the real metas are (`int_<op> :
// int→int→bool` / `int→int→int`). The metas must share the names +
// absTypes so ConstTerm.AlphaKeys match the registered metas — the same
// discipline the nat/real metas follow.
//
// The int layer is a subtype of real (int_le x y ⇔ real_of_int x ≤ real_of_int
// y, etc.), but omega's int decision layer treats int as its own Domain (the
// `Domain` seam) with int-native order lemmas — the int order theorems are the
// real ones lifted through real_of_int, but in XuGo
// they are standalone library theorems, so the layer is self-contained and needs
// no real_of_int bridge. Subtraction (int_sub) and negation (int_neg) are
// declared for vocabulary completeness but have no omega consumer yet (the
// uint64-coefficient linForm carries no sign — the positive `+ * < ≤` fragment
// only, matching where the real twin stopped).
var (
	IntPlusMeta = core.MakeConstMeta("int_add", core.MakeFun(IntType, IntType, IntType))
	IntStarMeta = core.MakeConstMeta("int_mul", core.MakeFun(IntType, IntType, IntType))
	IntSubMeta  = core.MakeConstMeta("int_sub", core.MakeFun(IntType, IntType, IntType))
	IntNegMeta  = core.MakeConstMeta("int_neg", core.MakeFun(IntType, IntType))
	// IntAbsMeta is `int_abs : int → int`
	// (`int_abs x = if &0 <= x then x else --x`). omega treats it as a
	// piecewise-by-`&0 ≤ x` operator the int case split eliminates
	// (int_split.go), exactly as nat_max/nat_min are handled over num.
	IntAbsMeta = core.MakeConstMeta("int_abs", core.MakeFun(IntType, IntType))
	// IntMaxMeta / IntMinMeta are `int_max`/`int_min : int → int → int`
	// (piecewise by `x ≤ y`, the int twin of num nat_max/nat_min); IntSgnMeta is
	// `int_sgn : int → int` (the three-way sign, a nested COND). All eliminated
	// by the int case split (int_split.go).
	IntMaxMeta = core.MakeConstMeta("int_max", core.MakeFun(IntType, IntType, IntType))
	IntMinMeta = core.MakeConstMeta("int_min", core.MakeFun(IntType, IntType, IntType))
	IntSgnMeta = core.MakeConstMeta("int_sgn", core.MakeFun(IntType, IntType))
	// IntPowMeta is `int_pow : int → num → int` (the exponent is num).
	// A literal exponent unfolds to a product chain (omega/int.go), the int twin
	// of num nat_pow.
	IntPowMeta = core.MakeConstMeta("int_pow", core.MakeFun(IntType, NumType, IntType))
	IntLtMeta  = core.MakeConstMeta("int_lt", core.MakeFun(IntType, IntType, core.TypeBool()))
	IntLeMeta  = core.MakeConstMeta("int_le", core.MakeFun(IntType, IntType, core.TypeBool()))
	IntGtMeta  = core.MakeConstMeta("int_gt", core.MakeFun(IntType, IntType, core.TypeBool()))
	IntGeMeta  = core.MakeConstMeta("int_ge", core.MakeFun(IntType, IntType, core.TypeBool()))
	// IntDividesMeta: `int_divides d e` — d divides e (∃z. e = d·z). The agent
	// surface is deferred (built through the production builder, like the rest of
	// the int layer); this meta gives omega's divisibility handler its vocabulary.
	IntDividesMeta = core.MakeConstMeta("int_divides", core.MakeFun(IntType, IntType, core.TypeBool()))

	// IntDivMeta / IntRemMeta are ℤ's Euclidean division `int_div`/`int_rem :
	// int → int → int`. int_div_rem.DivisionIdentity gives the
	// unconditional identity `m = int_div(m,n)·n + int_rem(m,n)`, and DivisionAlgorithm the
	// bounds `&0 ≤ int_rem(m,n) ∧ int_rem(m,n) < int_abs(n)` for `n ≠ &0`. omega treats
	// them as bounded atoms — the int twin of num's nat_div/nat_mod enrichment
	// (omega/nat_divmod.go). NOTE: the const names are `int_div`/`int_rem`,
	// distinct from num's `nat_div`/`nat_mod` (NatDivMeta/NatModMeta).
	IntDivMeta = core.MakeConstMeta("int_div", core.MakeFun(IntType, IntType, IntType))
	IntRemMeta = core.MakeConstMeta("int_rem", core.MakeFun(IntType, IntType, IntType))

	// IntOfNumMeta is the `&` coercion num→int (`int_of_num`). The head of
	// every int literal `&n = int_of_num(<bit-tree n>)`, the int analog of
	// RealOfNumMeta. The agent-facing `&` is type-directed (build.go): this meta
	// when its context is int, real_of_num otherwise.
	IntOfNumMeta = core.MakeConstMeta("int_of_num", core.MakeFun(NumType, IntType))

	// RealOfIntMeta is `real_of_int : int → real` — the homomorphism that
	// embeds ℤ into ℝ (the int type is a subtype of real, cut out by `integer`).
	// It is NOT part of omega's int DECISION layer (which stays real_of_int-free);
	// it is the material omega.IntOfRealThm consumes to DERIVE theorems
	// over ℤ from the proven ones over ℝ (omega/int_lemmas.go).
	RealOfIntMeta = core.MakeConstMeta("real_of_int", core.MakeFun(IntType, RealType))
)

// The integer-domain operator-table dispatch (intOperator above) and the
// type-directed `&` coercion (build.go astCoerce) are now wired into
// arithOperator/buildBinOp — the agent surface dispatches `+ - * < ≤ > ≥` to
// int on int-typed operands, the unary `-` builds int_neg, and `&n` resolves
// to int_of_num when its context is int (real otherwise). On OUTPUT int
// literals print explicitly as `int_of_num(n)` (NOT `&n`): `&` defaults to
// real on re-parse, so an explicit int_of_num head keeps the round-trip
// unambiguous, while the operator infix (`+`/`≤`/…) re-resolves to int by
// operand type. The printer infix lives in ext/format.go.

// ---------------------------------------------------------------------------
// The real-construction tower: nadd → hreal → treal.
//
// ℝ is built in three quotient steps, and each step carries its OWN
// addition, multiplication and order:
//
//	nadd   near-additive functions num→num (the "almost-homomorphisms")
//	hreal  the non-negative reals, nadd quotiented by nadd_eq
//	treal  signed pairs hreal × hreal, before the final treal_eq quotient
//
// Arithmetically these layers are ordinary semirings, so their statements read
// far better infix (`x·(y + z) ≤ x·y + x·z`) than as nested prefix calls. They
// get the same treatment the real and int layers already get: the CONST NAMES
// stay the registry's (hreal_add, nadd_mul, treal_le, …) so every stored
// AlphaKey / normalized key / recorded CNF trajectory is untouched, and only
// the SURFACE is infix — dispatched by operand type
// through arithDomainOperator, printed back by the name map in ext/format.go.
// Parsing `x + y` at hreal operands yields the byte-identical term the prefix
// spelling `hreal_add(x, y)` yields; nothing below the surface moves.
//
// NOT given infix, deliberately: the two EQUIVALENCE relations `nadd_eq` and
// `treal_eq`. They are not overloads of a symbol the surface already spells —
// giving them one would mean inventing new notation (a `~` family) rather than
// extending an existing dispatch, and that is a vocabulary decision, not a
// notation-floor fix. They stay prefix.
//
// Also left prefix for the same reason: the num embeddings hreal_of_num /
// nadd_of_num / treal_of_num (no `&`-style symbol is established for them),
// the inverses hreal_inv / nadd_inv / treal_inv, and treal_neg.

// HrealMetaType / HrealType are `hreal` (the non-negative reals;
// a 0-ary type constant). Structurally equal to what resolveType produces for
// the bare type name "hreal", so `x:hreal` declarations resolve to HrealType.
var HrealMetaType = core.MakeMetaType("hreal", 0)

// HrealType is the HOL `hreal` type.
var HrealType core.HolType = core.MakeCompositeType(HrealMetaType)

// NaddMetaType / NaddType are `nadd` (near-additive functions
// num→num), the tower's bottom layer, likewise a 0-ary type constant.
var NaddMetaType = core.MakeMetaType("nadd", 0)

// NaddType is the HOL `nadd` type.
var NaddType core.HolType = core.MakeCompositeType(NaddMetaType)

// TrealType is `hreal × hreal` — the tower's signed layer. Unlike the other
// five arith domains it is a COMPOSITE type, not a 0-ary constant: a treal is
// literally a pair `(positive part, negative part)`, and the corpus spells it
// `prod(hreal, hreal)`. arithDomainOperator matches it structurally, so
// `x + y` at two `prod(hreal, hreal)` operands dispatches to treal_add.
var TrealType = ext.MakeProdType(HrealType, HrealType)

// Tower arithmetic const metas, NAMED AS THE REGISTRY NAMES THEM — the same
// discipline as the real/int metas above, and for the same reason: the
// registered metas, the chapter statements and the recorded CNF proofs are all
// in this vocabulary, so a symbol-NAMED meta here would silently fail to
// α-match them.
var (
	HrealPlusMeta = core.MakeConstMeta("hreal_add", core.MakeFun(HrealType, HrealType, HrealType))
	HrealStarMeta = core.MakeConstMeta("hreal_mul", core.MakeFun(HrealType, HrealType, HrealType))
	HrealLeMeta   = core.MakeConstMeta("hreal_le", core.MakeFun(HrealType, HrealType, core.TypeBool()))

	NaddPlusMeta = core.MakeConstMeta("nadd_add", core.MakeFun(NaddType, NaddType, NaddType))
	NaddStarMeta = core.MakeConstMeta("nadd_mul", core.MakeFun(NaddType, NaddType, NaddType))
	NaddLeMeta   = core.MakeConstMeta("nadd_le", core.MakeFun(NaddType, NaddType, core.TypeBool()))

	TrealPlusMeta = core.MakeConstMeta("treal_add", core.MakeFun(TrealType, TrealType, TrealType))
	TrealStarMeta = core.MakeConstMeta("treal_mul", core.MakeFun(TrealType, TrealType, TrealType))
	TrealLeMeta   = core.MakeConstMeta("treal_le", core.MakeFun(TrealType, TrealType, core.TypeBool()))
)

// hrealOperator returns the hreal-domain const meta for an overloaded operator
// symbol, or nil. Only `+ * ≤` have hreal instances: the layer is the
// NON-NEGATIVE reals, so there is no subtraction and no negation, and the
// strict order `<` is not part of its imported vocabulary.
func hrealOperator(op string) core.ConstTermMeta {
	switch op {
	case "+":
		return HrealPlusMeta
	case "*":
		return HrealStarMeta
	case "≤":
		return HrealLeMeta
	}
	return core.ConstTermMeta{}
}

// naddOperator is the nadd-layer twin of hrealOperator — same three symbols,
// same absence of subtraction (nadd functions are num→num).
func naddOperator(op string) core.ConstTermMeta {
	switch op {
	case "+":
		return NaddPlusMeta
	case "*":
		return NaddStarMeta
	case "≤":
		return NaddLeMeta
	}
	return core.ConstTermMeta{}
}

// trealOperator is the treal-layer twin. treal DOES have a negation
// (treal_neg), but no binary `-` const — treal subtraction is spelled as
// `treal_add(x, treal_neg(y))` — so `-` is deliberately absent here rather
// than silently mapped to something the corpus does not have.
func trealOperator(op string) core.ConstTermMeta {
	switch op {
	case "+":
		return TrealPlusMeta
	case "*":
		return TrealStarMeta
	case "≤":
		return TrealLeMeta
	}
	return core.ConstTermMeta{}
}
