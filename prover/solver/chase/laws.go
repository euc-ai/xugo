package chase

// laws.go — the general laws the chase closer's certificates read, each
// in its STATED form, installed by library/serve from the algebra and
// set chapters (InstallChaseBundle), as omega's structure ring has its
// table. The closer never imports a chapter: a structure fact is
// recognized by its head constant's NAME, and the laws about it come
// from this table. Each law is the CARRIER form of its chapter — a
// structure law `∀S. S_on(S) ⇒ ∀xs. xs ∈ S.carrier ⇒ body`, a
// definition clause a plain `∀…` — and a law's guard is discharged at
// every instance from the memberships the closer has derived (the
// manual's Design rules, "A structure is read on its carrier").

import (
	"fmt"
	"slices"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/omega"
)

// The structure and vocabulary constants, by the names the chapters
// mint them under.
const (
	moduleOnName        = "module_on"
	homomorphismName    = "module_homomorphism"
	exactAtName         = "exact_at"
	submoduleName       = "submodule"
	imageName           = "image"
	kernelName          = "group_kernel"
	leftCosetName       = "left_coset"
	subgroupName        = "subgroup"
	groupOnName         = "group_on"
	abelianGroupOnName  = "abelian_group_on"
	subsetName          = "is_subset"
	injectiveOnName     = "injective_on"
	moduleOnArity       = 2
	homomorphismArity   = 4
	exactAtArity        = 5
	submoduleArity      = 3
	imageArity          = 2
	kernelArity         = 3
	leftCosetArity      = 3
	subgroupArity       = 2
	groupOnArity        = 1
	abelianGroupOnArity = 1
	subsetArity         = 2
	injectiveOnArity    = 2
)

// ScalarLaws are the module action laws and the explicit ring
// normalizer's table, read when a module's scalars are chased. The
// table is all or none: a zero table keeps the additive-only reading,
// and a partial one is refused at install.
type ScalarLaws struct {
	// ── module_on(R, M) ⇒ …
	RingOn       *prop.PropWrapper // comm_ring_on(R)
	SmulAddLeft  *prop.PropWrapper // ∀c u v. c ∈ R.carrier ∧ u ∈ M.carrier ∧ v ∈ M.carrier ⇒ c • (u + v) = c • u + c • v
	SmulAddRight *prop.PropWrapper // ∀c d u. c ∈ R.carrier ∧ d ∈ R.carrier ∧ u ∈ M.carrier ⇒ (c + d) • u = c • u + d • u
	SmulMul      *prop.PropWrapper // ∀c d u. c ∈ R.carrier ∧ d ∈ R.carrier ∧ u ∈ M.carrier ⇒ (c * d) • u = c • (d • u)
	SmulOne      *prop.PropWrapper // ∀u. u ∈ M.carrier ⇒ R.one • u = u
	ZeroSmul     *prop.PropWrapper // ∀u. u ∈ M.carrier ⇒ R.zero • u = M.zero
	SmulZero     *prop.PropWrapper // ∀c. c ∈ R.carrier ⇒ c • M.zero = M.zero
	// ── module_homomorphism(R, M, N, f) ⇒ …
	HomSmul *prop.PropWrapper // ∀c u. c ∈ R.carrier ∧ u ∈ M.carrier ⇒ f(c • u) = c • f(u)
	// Ring is the ring normalizer's table (omega.InstalledStructureRingLaws),
	// bound per scalar ring to the memberships the leaf states.
	Ring omega.StructureRingLaws
}

// fields names every law of the scalar table, for the install check.
func (s *ScalarLaws) fields() map[string]*prop.PropWrapper {
	return map[string]*prop.PropWrapper{
		"RingOn": s.RingOn, "SmulAddLeft": s.SmulAddLeft, "SmulAddRight": s.SmulAddRight,
		"SmulMul": s.SmulMul, "SmulOne": s.SmulOne, "ZeroSmul": s.ZeroSmul, "SmulZero": s.SmulZero,
		"HomSmul": s.HomSmul,
	}
}

// installed reports whether the scalar table is set: any law is.
func (s *ScalarLaws) installed() bool {
	for _, law := range s.fields() {
		if law != nil {
			return true
		}
	}
	return false
}

// Laws is the installed table. The carrier laws are required; Rewrites holds
// the supplied record definitions that may be normalized in a diagram.
type Laws struct {
	Scalars ScalarLaws
	// ── module_on(R, M) ⇒ …, at the record projections
	AddGroupOn *prop.PropWrapper // group_on(module_additive_group(M))
	AddComm    *prop.PropWrapper // ∀u v. u ∈ M.carrier ∧ v ∈ M.carrier ⇒ u + v = v + u
	SmulIn     *prop.PropWrapper // ∀c u. c ∈ R.carrier ∧ u ∈ M.carrier ⇒ c • u ∈ M.carrier
	Rewrites   RecordRewrites
	// NormalizeWith computes record projections as the shared instance
	// normal form does, without its β: the reading computes the
	// applications itself, every one in the leaf and all but a law's own
	// in the law's instance (Laws.reading). Each equation is read through
	// read — a proof's own read of its theorem (omega.LibraryReader), nil
	// for the fallback library/serve installs.
	NormalizeWith func(read omega.LibraryRead) prop.Rewrite
	// ── abelian_group_on(G) ⇔ group_on(G) ∧ commutativity on G.carrier
	AbelianGroupOnDef *prop.PropWrapper
	// ── abelian_group_on(G) ⇒ …
	NegAdd *prop.PropWrapper // ∀x y. x ∈ c ∧ y ∈ c ⇒ neg(add(x, y)) = add(neg(x), neg(y))
	// ── group_on(G) ⇒ …
	OneIn           *prop.PropWrapper // one ∈ c
	MulIn           *prop.PropWrapper // ∀x y. x ∈ c ∧ y ∈ c ⇒ mul(x, y) ∈ c
	InvIn           *prop.PropWrapper // ∀x. x ∈ c ⇒ inv(x) ∈ c
	Assoc           *prop.PropWrapper // ∀x y z. x ∈ c ∧ y ∈ c ∧ z ∈ c ⇒ mul(x, mul(y, z)) = mul(mul(x, y), z)
	LeftIdentity    *prop.PropWrapper // ∀x. x ∈ c ⇒ mul(one, x) = x
	RightIdentity   *prop.PropWrapper // ∀x. x ∈ c ⇒ mul(x, one) = x
	LeftInverse     *prop.PropWrapper // ∀x. x ∈ c ⇒ mul(inv(x), x) = one
	RightInverse    *prop.PropWrapper // ∀x. x ∈ c ⇒ mul(x, inv(x)) = one
	InvInv          *prop.PropWrapper // ∀x. x ∈ c ⇒ inv(inv(x)) = x
	InvOne          *prop.PropWrapper // inv(one) = one
	IdempotentIsOne *prop.PropWrapper // ∀e. e ∈ c ⇒ (mul(e, e) = e ⇒ e = one)
	InvUnique       *prop.PropWrapper // ∀x y. x ∈ c ∧ y ∈ c ⇒ (mul(x, y) = one ⇔ x = inv(y))
	LeftCosetEq     *prop.PropWrapper // ∀x y h. x ∈ c ∧ y ∈ c ∧ subgroup(G, h) ⇒ (left_coset(mul, x, h) = left_coset(mul, y, h) ⇔ mul(inv(x), y) ∈ h)
	// ── module_homomorphism(R, M, N, f) ⇒ …
	HomSource *prop.PropWrapper // module_on(R, M)
	HomTarget *prop.PropWrapper // module_on(R, N)
	HomIn     *prop.PropWrapper // ∀u. u ∈ M.carrier ⇒ f(u) ∈ N.carrier
	HomAdd    *prop.PropWrapper // ∀u v. u ∈ M.carrier ∧ v ∈ M.carrier ⇒ f(M.add(u, v)) = N.add(f(u), f(v))
	// ── the vocabulary's definitions and their membership readings
	ExactAtDef        *prop.PropWrapper // ∀e M M' f g. exact_at(e, M, M', f, g) ⇔ image(f, M) = group_kernel(e, M', g)
	InImage           *prop.PropWrapper // ∀f s y. y ∈ image(f, s) ⇔ ∃x. y = f(x) ∧ x ∈ s
	InKernel          *prop.PropWrapper // ∀one' c f x. x ∈ group_kernel(one', c, f) ⇔ x ∈ c ∧ f(x) = one'
	SubmoduleSubgroup *prop.PropWrapper // ∀R M N. submodule(R, M, N) ⇒ subgroup(module_additive_group(M), N)
	SubgroupSubset    *prop.PropWrapper // ∀G h. subgroup(G, h) ⇒ is_subset(h, G.carrier)
	SubsetDef         *prop.PropWrapper // ∀s t. is_subset(s, t) ⇔ ∀x. x ∈ s ⇒ x ∈ t
	InjectiveOnDef    *prop.PropWrapper // ∀s f. injective_on(s, f) ⇔ ∀x y. x ∈ s ∧ y ∈ s ∧ f(x) = f(y) ⇒ x = y
	Extension         *prop.PropWrapper // ∀s t. s = t ⇔ ∀x. x ∈ s ⇔ x ∈ t

	// member is the membership constant `∈`, read off InImage at
	// install (SetLaws).
	member        core.ConstTermMeta
	recordRewrite prop.Rewrite
}

var (
	lawsMu         sync.Mutex
	installedLaws  *Laws
	foundationKeys map[core.PropKey]bool
)

// SetLaws installs the table (nil uninstalls). Every carrier law must be
// set, and the scalar table whole or empty; optional record equations
// become proved rewrites, and the membership constant is read off
// InImage.
func SetLaws(l *Laws) {
	if l != nil {
		if l.Scalars.installed() {
			for name, law := range l.Scalars.fields() {
				if law == nil {
					panic(fmt.Sprintf("chase.SetLaws: the scalar law %s is not installed (the scalar table is all or none)", name))
				}
			}
			if l.Scalars.Ring.PowZeroClause == nil || l.Scalars.Ring.MulMonoid == nil {
				panic("chase.SetLaws: the scalar table's ring normalizer laws are not installed (omega.InstalledStructureRingLaws)")
			}
		}
		for name, law := range l.fields() {
			if law == nil {
				panic(fmt.Sprintf("chase.SetLaws: the law %s is not installed", name))
			}
		}
		body, _ := l.InImage.StripConclForAll()
		lhs, _, ok := ext.MatchesIFF(body.Conclusion())
		if !ok {
			panic("chase.SetLaws: InImage is not an ⇔")
		}
		head, args := ext.MatchesApply(lhs)
		c, isConst := head.AsConst()
		if !isConst || len(args) != 2 {
			panic("chase.SetLaws: InImage's left side is not a membership `y ∈ image(f, s)`")
		}
		l.member = c.Meta()
		l.recordRewrite = l.Rewrites.rewrite()
	}
	lawsMu.Lock()
	installedLaws = l
	lawsMu.Unlock()
}

// fields names every law of the table, for the install check.
func (l *Laws) fields() map[string]*prop.PropWrapper {
	return map[string]*prop.PropWrapper{
		"AddGroupOn": l.AddGroupOn, "AddComm": l.AddComm, "SmulIn": l.SmulIn,
		"AbelianGroupOnDef": l.AbelianGroupOnDef, "NegAdd": l.NegAdd,
		"OneIn": l.OneIn, "MulIn": l.MulIn, "InvIn": l.InvIn, "Assoc": l.Assoc,
		"LeftIdentity": l.LeftIdentity, "RightIdentity": l.RightIdentity,
		"LeftInverse": l.LeftInverse, "RightInverse": l.RightInverse,
		"InvInv": l.InvInv, "InvOne": l.InvOne, "IdempotentIsOne": l.IdempotentIsOne,
		"InvUnique": l.InvUnique, "LeftCosetEq": l.LeftCosetEq,
		"HomSource": l.HomSource, "HomTarget": l.HomTarget,
		"HomIn": l.HomIn, "HomAdd": l.HomAdd,
		"ExactAtDef": l.ExactAtDef, "InImage": l.InImage, "InKernel": l.InKernel,
		"SubmoduleSubgroup": l.SubmoduleSubgroup, "SubgroupSubset": l.SubgroupSubset, "SubsetDef": l.SubsetDef,
		"InjectiveOnDef": l.InjectiveOnDef, "Extension": l.Extension,
	}
}

// Installed is the installed table, nil when none is.
func Installed() *Laws {
	lawsMu.Lock()
	defer lawsMu.Unlock()
	return installedLaws
}

// Enabled reports whether the closer is live: its laws are installed.
func Enabled() bool { return Installed() != nil }

// SetFoundation installs the laws' capability foundation closure —
// every entry the table rests on — for the scope-less gate.
func SetFoundation(keys map[core.PropKey]bool) {
	lawsMu.Lock()
	foundationKeys = keys
	lawsMu.Unlock()
}

// AllowsTarget reports whether a proof of target may use the closer: a
// member the laws rest on may not.
func AllowsTarget(target core.PropKey) bool {
	if target == "" {
		return true
	}
	lawsMu.Lock()
	defer lawsMu.Unlock()
	return !foundationKeys[target]
}

// lawAt instantiates a stated law at its records or definition parameters,
// discharges the structure hypothesis from fact when the law has one,
// and instantiates the body's own leading binders at args. A law stated
// in the standard form is read through the telescope the fact picks
// (prop.LawTelescopeAt): its hypothesis stating fact's predicate first,
// over the binders it mentions, the other hypotheses one guard ahead of
// the body. The law's
// type variables are instantiated by matching each leading binder's
// type against the lead term's. A membership guard the law states
// ahead of its body is left in place: the caller discharges it
// (memberships). Definition reductions retain the goal's spelling here;
// at computes projections for a structure-law reading.
func lawAt(law *prop.PropWrapper, lead []core.Term, fact *prop.PropWrapper, args ...core.Term) *prop.PropWrapper {
	if law == nil {
		panic("chase: a law the certificates read is not installed")
	}
	w := law
	if fact != nil {
		w = prop.WrapProp(prop.LawTelescopeAt(law, fact.Conclusion()))
	}
	if len(lead) > 0 {
		var env []core.TypeSubst
		body := w.Conclusion()
		for i, t := range lead {
			abs := ext.MatchesFORALL(body)
			if abs.IsZero() {
				panic(fmt.Sprintf("chase: a law has fewer leading binders than the %d components: %s", len(lead), ext.PrintTerm(w.Conclusion())))
			}
			if !core.MatchTypeInto(abs.Var().Type(), t.Type(), func(core.VarType) bool { return true }, &env) {
				panic(fmt.Sprintf("chase: a law's binder %s does not type-match the component %s (position %d)",
					ext.PrintTerm(abs.Var()), ext.PrintTerm(t), i))
			}
			body = abs.Body()
		}
		env = slices.DeleteFunc(env, func(s core.TypeSubst) bool { return s.HolType.Equals(s.VarType) })
		if len(env) > 0 {
			w = w.TypeInst(env...)
		}
		w = w.ConclForAllInsts(lead...)
	}
	if fact != nil {
		w = w.DemoteHyp().DeriveHypFrom(fact)
	}
	if len(args) > 0 {
		w = w.ConclForAllInsts(args...)
	}
	return w
}

// _Reading is the closer's normal form as one reader reads it: the
// supplied record definitions (recordRewrite), the instance normal
// form's record step computed through the reader's read, and every
// application of a λ computed, `(λv. b)(a)` to `b[a/v]`. It is the form
// the other closers read a leaf in, and the closer compares carriers,
// maps and elements in it alone: a packed complex holds its terms and
// its differentials as λs over its degrees, and what such a λ gives at a
// degree and the term a membership spells out are one term in it.
//
// A homomorphism's value is told in that form by its map, not by an
// application left standing (images): the head of a named map, the body
// of a map given by a λ.
type _Reading struct {
	// steps are the record definitions and the record step; without an
	// installed normal form the record step is left out.
	steps []prop.Rewrite
	// leaf is the normal form itself.
	leaf prop.Rewrite
}

func (l *Laws) reading(reader *omega.LibraryReader) *_Reading {
	steps := []prop.Rewrite{l.recordRewrite}
	if l.NormalizeWith != nil {
		var read omega.LibraryRead
		if reader != nil {
			read = reader.Read
		}
		steps = append(steps, l.NormalizeWith(read))
	}
	return &_Reading{steps: steps, leaf: toFixpoint(prop.ChainRewrites(append(slices.Clone(steps), prop.DeepBeta)...))}
}

// instance is the normal form of a law's instance, the applications of
// the λs in kept left as the instance states them (applied): the laws
// of a homomorphism given by a λ are instantiated at the λ and state it
// applied to an element, the certificates compose them in that spelling
// (homAdd, homZero, homNeg, pushHom) and instantiate the laws of the
// target at such applications, and a value leaves the spelling through
// its β bridge (pushHom, images). The λs kept are in the normal form
// already, being parts of facts read in it, so the rewrites change
// nothing under them; one that is not would have its application
// computed a round later, and panics here.
func (r *_Reading) instance(kept []core.Term) prop.Rewrite {
	if len(kept) == 0 {
		return r.leaf
	}
	for _, f := range kept {
		if r.leaf(f) != nil {
			panic("chase: a law is instantiated at a λ that is not in the normal form (engine invariant): " + ext.PrintTerm(f))
		}
	}
	rest := prop.DeepRewrite(func(t core.Term) *prop.PropWrapper {
		app, ok := t.AsAppliedTerm()
		if !ok {
			return nil
		}
		if _, isAbs := app.Fun().AsAbsTerm(); !isAbs || slices.ContainsFunc(kept, app.Fun().AlphaEquals) {
			return nil
		}
		return prop.BetaRewrite(t)
	})
	return toFixpoint(prop.ChainRewrites(append(slices.Clone(r.steps), rest)...))
}

// toFixpoint is step taken until it changes nothing; nil where its
// first run changes nothing.
func toFixpoint(step prop.Rewrite) prop.Rewrite {
	return func(t core.Term) *prop.PropWrapper {
		var result *prop.PropWrapper
		for {
			next := step(t)
			if next == nil {
				return result
			}
			if result == nil {
				result = next
			} else {
				result = result.EqTrans(next)
			}
			t = prop.Rhs(next)
		}
	}
}

// applied are the λs a law's instance states applied, given the terms
// the law is instantiated at: each of the terms that is a λ, which the
// law applies, and each λ one of them spells applied already, a value
// in the certificates' spelling.
func applied(lead, args []core.Term) []core.Term {
	var out []core.Term
	spelled := prop.DeepRewrite(func(t core.Term) *prop.PropWrapper {
		if app, ok := t.AsAppliedTerm(); ok {
			if _, isAbs := app.Fun().AsAbsTerm(); isAbs {
				out = append(out, app.Fun())
			}
		}
		return nil
	})
	for _, t := range slices.Concat(lead, args) {
		if _, isAbs := t.AsAbsTerm(); isAbs {
			out = append(out, t)
		}
		spelled(t)
	}
	return out
}

// closureComponent reads an operation and its carrier from a closure law
// instantiated at a structure fact: the law concludes `op(x̄) ∈ carrier`
// at its own variables, and op is what stands applied to them in the
// normal form. An operation the record gives by a λ has its application
// computed there and leaves no such term; the closer writes sums, and
// reads them, as one operation applied to its elements, and refuses the
// structure by name.
func (d *_Diagram) closureComponent(law *prop.PropWrapper, record core.Term, fact *prop.PropWrapper, arity int) (core.Term, core.Term, error) {
	// The variables the law applies the operation to, by their place
	// among its binders, read off the law as stated.
	stated, _, binders := closureConclusion(d, lawAt(law, []core.Term{record}, fact).Conclusion())
	places := make([]int, arity)
	for i := arity - 1; i >= 0; i-- {
		app, ok := stated.AsAppliedTerm()
		if !ok {
			panic("chase: a closure law applies its operation to too few arguments")
		}
		places[i] = slices.IndexFunc(binders, func(v core.VarTerm) bool { return app.Arg().Equals(v) })
		if places[i] < 0 {
			panic("chase: a closure law applies its operation to a term that is none of its variables")
		}
		stated = app.Fun()
	}
	element, set, binders := closureConclusion(d, d.canonicalAt(law, []core.Term{record}, fact).Conclusion())
	op := element
	for i := arity - 1; i >= 0; i-- {
		app, ok := op.AsAppliedTerm()
		if !ok || !app.Arg().Equals(binders[places[i]]) {
			return nil, nil, lambdaOperation(record, element)
		}
		op = app.Fun()
	}
	if slices.ContainsFunc(binders, op.HasFree) {
		return nil, nil, lambdaOperation(record, element)
	}
	return op, set, nil
}

// closureConclusion is the membership a closure law concludes under its
// binders and guards: the element, the set and the binders.
func closureConclusion(d *_Diagram, body core.Term) (element, set core.Term, binders []core.VarTerm) {
	for {
		if abs := ext.MatchesFORALL(body); !abs.IsZero() {
			binders = append(binders, abs.Var())
			body = abs.Body()
		} else if _, next, ok := ext.MatchesIMPLY(body); ok {
			body = next
		} else {
			break
		}
	}
	element, set, ok := d.matchMembership(body)
	if !ok {
		panic("chase: a closure law does not conclude a membership")
	}
	return element, set, binders
}

// lambdaOperation is the refusal of a structure one of whose operations
// is no term applied to its elements.
func lambdaOperation(record, value core.Term) error {
	return fmt.Errorf("the structure %s gives an operation by a λ — at the law's variables it is %s, no one term applied to them — and the chase closer reads an operation as a term applied to its elements; name the operation, or state the step outside the chase",
		ext.PrintTerm(record), ext.PrintTerm(value))
}
