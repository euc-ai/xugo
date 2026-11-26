package chase

// image.go — a homomorphism's value read in the closer's normal form.
// Nothing in a leaf read in that form is an application left standing
// (Laws.reading), so the value of a map given by a λ is no application
// of the map: it is the map's body with the argument where the binder
// stood, and it is read back against that body.

import (
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// _Image is an element read as h's value at arg. eq is Γ ⊢ fn(arg) = t,
// fn(arg) the application as h's laws spell it; nil where t is that
// application as written.
type _Image struct {
	h   *_Hom
	arg core.Term
	eq  *prop.PropWrapper
}

// images are the readings of t as the value of a homomorphism into dst
// (into any module where dst is nil), in the order the homomorphisms
// were read. A map applied as written — a named map, or a λ in a law's
// instance — is told by the head. A value of a map given by a λ is told
// by the body (argumentOf), and the reading is the kernel's: β of the λ
// applied to the argument found is t, or the reading is dropped.
func (d *_Diagram) images(t core.Term, dst *_Node) []_Image {
	var out []_Image
	app, applied := t.AsAppliedTerm()
	for _, h := range d.homs {
		if dst != nil && h.dst != dst {
			continue
		}
		if applied && app.Fun().AlphaEquals(h.fn) {
			out = append(out, _Image{h: h, arg: app.Arg()})
			continue
		}
		fn, isAbs := h.fn.AsAbsTerm()
		if !isAbs {
			continue
		}
		arg, ok := argumentOf(fn, t)
		if !ok {
			continue
		}
		if beta := prop.DeepBeta(ext.Apply(h.fn, arg)); beta != nil && prop.Rhs(beta).AlphaEquals(t) {
			out = append(out, _Image{h: h, arg: arg, eq: beta})
		}
	}
	return out
}

// valued reports whether t is h's value at u, u a variable the term
// binds: the map applied to u as written, or, of a map given by a λ,
// its body at u.
func (d *_Diagram) valued(h *_Hom, t, u core.Term) bool {
	return d.apply(h, u).AlphaEquals(t) || ext.Apply(h.fn, u).AlphaEquals(t)
}

// valuedAt is the homomorphism out of src whose value at u is t, the
// first read where several are.
func (d *_Diagram) valuedAt(t, u core.Term, src *_Node) *_Hom {
	for _, h := range d.homs {
		if h.src == src && d.valued(h, t, u) {
			return h
		}
	}
	return nil
}

// valuedAtBoth is the homomorphism out of src whose values at u and at
// v are l and r, in either order.
func (d *_Diagram) valuedAtBoth(l, r, u, v core.Term, src *_Node) *_Hom {
	for _, h := range d.homs {
		if h.src == src && (d.valued(h, l, u) && d.valued(h, r, v) || d.valued(h, l, v) && d.valued(h, r, u)) {
			return h
		}
	}
	return nil
}

// of is Γ ⊢ t = r from w : Γ ⊢ fn(arg) = r.
func (im _Image) of(w *prop.PropWrapper) *prop.PropWrapper {
	if im.eq == nil {
		return w
	}
	return im.eq.EqSym().EqTrans(w)
}

// member is Γ ⊢ t ∈ set from w : Γ ⊢ fn(arg) ∈ set.
func (im _Image) member(d *_Diagram, w *prop.PropWrapper, set core.Term) *prop.PropWrapper {
	if im.eq == nil {
		return w
	}
	return im.eq.LeftApply(d.memberConst(prop.Lhs(im.eq), set)).RightApply(set).EqMP(w)
}

// argumentOf is the a with body[a/v] = t for fn = `λv. body`, read off
// t: where body spells v, t spells a. ok is false where body does not
// spell v, where two places of v hold two terms, where a would name a
// variable body binds, and where t is not body elsewhere. The reading
// is first-order: where body applies v, or takes a part of it that
// computes at a, the value is not undone.
func argumentOf(fn core.AbsTerm, t core.Term) (core.Term, bool) {
	v, body := fn.Var(), fn.Body()
	if !body.Type().Equals(t.Type()) || !body.HasFree(v) {
		return nil, false
	}
	var arg core.Term
	var match func(p, q core.Term, env []core.VarPair) bool
	match = func(p, q core.Term, env []core.VarPair) bool {
		if !p.HasFree(v) {
			return p.AlphaEqualsWithEnv(q, env)
		}
		switch p := p.Core().(type) {
		case core.VarTerm:
			if !p.Type().Equals(q.Type()) || slices.ContainsFunc(env, func(b core.VarPair) bool { return q.HasFree(b.V1) }) {
				return false
			}
			if arg == nil {
				arg = q
				return true
			}
			return arg.AlphaEquals(q)
		case core.AppliedTerm:
			q, ok := q.AsAppliedTerm()
			return ok && match(p.Fun(), q.Fun(), env) && match(p.Arg(), q.Arg(), env)
		case core.AbsTerm:
			q, ok := q.AsAbsTerm()
			return ok && p.Var().Type().Equals(q.Var().Type()) &&
				match(p.Body(), q.Body(), append(slices.Clone(env), core.VarPair{V0: p.Var(), V1: q.Var()}))
		}
		return false
	}
	if !match(body, t, nil) || arg == nil {
		return nil, false
	}
	return arg, true
}
