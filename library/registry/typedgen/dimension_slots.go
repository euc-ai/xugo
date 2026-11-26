// dimension_slots.go — the dimension refinement of a wrapper's witness
// slots.
//
// A term-level vector chapter's operations declare their dimension
// argument (registry.DefEntry.Dim → registry.DimSlot). For a statement
// this reads, per vector binder, the dimension it is read at: every
// application of a Dim-declared constant that takes the binder as a
// vector argument pairs it with that application's dimension argument.
// A binder paired with exactly one dimension, itself a num binder of
// the statement, becomes a dimtypes.Vec parameter at that dimension's
// phantom; the dimension binder is then written off its vectors and
// leaves the parameter list. A vector binder whose membership is one of
// the statement's antecedents — `vec⟨m⟩(zero, x) ∧ vec⟨m⟩(zero, y) ⇒ …`,
// the conjuncts of the one ⇒ under the prefix — arrives as a
// proof.Inhabited, and the generated cite bundles the evidence. A
// binder read at two different dimensions, or at a dimension that is
// not a binder, keeps its plain slot: nothing is elided that the
// statement does not determine.
//
// The same refinement reads a structure law for its READING: a point
// whose membership in a component set is one of the reading's guards —
// `x ∈ M ∧ y ∈ M ⇒ d(x, y) = d(y, x)` under `metric_space(M, d)`, or
// a guard with a second antecedent below it, `x ∈ c ⇒ x ≠ zero ⇒ …` —
// arrives as a proof.Member, its evidence bundled the same way. A plain
// theorem's `x ∈ s` is not one: the set must be a component of the
// structure the law is read at.
//
// A MATRIX is the same reading at two dimensions. Its constants declare
// the pair (RowDim/ColumnDim → registry.MatrixDimSlots), a binder paired
// with one row binder and one column binder becomes a dimtypes.Mat at
// both phantoms, both dimension binders leave the parameter list, and a
// membership antecedent makes it a proof.InhabitedMat. The two
// refinements do not compete for a binder: a vector carrier is `num → τ`
// and a matrix carrier `num → num → τ`, and ext.MatchesFun flattens the
// arrow spine, so the length test alone separates them.
//
// A MAP between two vector spaces is the third carrier,
// `(num → τ) → num → τ`, read at two dimensions like a matrix: its
// constants declare the pair (SourceDim/TargetDim →
// registry.VecFunDimSlots), a binder paired with one source binder and one
// target binder becomes a dimtypes.VecFun at both phantoms, and both
// dimension binders leave the parameter list. The two may be one binder
// — a map of a space into itself — and the VecFun then spells one phantom
// twice. Its first argument is an arrow where a matrix's is num, so no
// binder is both.

package typedgen

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/library/registry"
)

// paramType is the slot's Go parameter type.
func (s witnessSlot) paramType() string {
	switch {
	case s.member:
		carrier := s.carrier
		if carrier == "" {
			carrier = "on.Any"
		}
		return fmt.Sprintf("*proof.Member[%s, %s]", s.phantom, carrier)
	case s.inhabited && s.matRows != "":
		return fmt.Sprintf("*proof.InhabitedMat[%s, Dim%s, Dim%s]", s.elem, dimParamName(s.matRows), dimParamName(s.matCols))
	case s.matRows != "":
		return fmt.Sprintf("*dimtypes.Mat[%s, Dim%s, Dim%s]", s.elem, dimParamName(s.matRows), dimParamName(s.matCols))
	case s.vecFunSource != "":
		return fmt.Sprintf("*dimtypes.VecFun[%s, Dim%s, Dim%s]", s.elem, dimParamName(s.vecFunSource), dimParamName(s.vecFunTarget))
	case s.inhabited:
		return fmt.Sprintf("*proof.Inhabited[%s, Dim%s]", s.elem, dimParamName(s.vecDim))
	case s.vecDim != "":
		return fmt.Sprintf("*dimtypes.Vec[%s, Dim%s]", s.elem, dimParamName(s.vecDim))
	}
	return fmt.Sprintf("ext.Typed[%s]", s.phantom)
}

// dimParamName spells the method type parameter for a dimension
// binder: Dim + the binder's name, capitalized (`n` → DimN).
func dimParamName(binder string) string {
	if binder == "" {
		return ""
	}
	return string([]rune(binder)[0]-'a'+'A') + binder[1:]
}

// refineDimensionSlots pairs the statement's vector, matrix and map
// binders with their dimensions and marks the slots.
func refineDimensionSlots(p core.Prop, slots []witnessSlot, letterParam map[string]string, usedTypedefs map[string]bool) error {
	byBinder := map[string]*witnessSlot{}
	for i := range slots {
		byBinder[slots[i].binder] = &slots[i]
	}
	// pairs: vector binder → the set of dimension terms it is read at.
	// rowPairs / colPairs: the same for a matrix binder's two dimensions.
	// sourcePairs / targetPairs: the same for a map binder's two.
	pairs := map[string][]core.Term{}
	rowPairs, colPairs := map[string][]core.Term{}, map[string][]core.Term{}
	sourcePairs, targetPairs := map[string][]core.Term{}, map[string][]core.Term{}
	var walk func(t core.Term)
	walk = func(t core.Term) {
		switch tt := t.Core().(type) {
		case core.AppliedTerm:
			head, args := spine(tt)
			if c, ok := head.AsConst(); ok {
				if pos, declared := registry.DimSlot(string(c.Name())); declared && pos < len(args) {
					dim := args[pos]
					for _, arg := range args {
						v, isVar := arg.AsVar()
						if !isVar {
							continue
						}
						if s, isBinder := byBinder[string(v.Name())]; isBinder && isVectorType(s.typ) {
							pairs[s.binder] = append(pairs[s.binder], dim)
						}
					}
				}
				rowPos, colPos, declared := registry.MatrixDimSlots(string(c.Name()))
				if declared && rowPos < len(args) && colPos < len(args) {
					rows, cols := args[rowPos], args[colPos]
					for _, arg := range args {
						v, isVar := arg.AsVar()
						if !isVar {
							continue
						}
						if s, isBinder := byBinder[string(v.Name())]; isBinder && isMatrixType(s.typ) {
							rowPairs[s.binder] = append(rowPairs[s.binder], rows)
							colPairs[s.binder] = append(colPairs[s.binder], cols)
						}
					}
				}
				sourcePos, targetPos, declared := registry.VecFunDimSlots(string(c.Name()))
				if declared && sourcePos < len(args) && targetPos < len(args) {
					source, target := args[sourcePos], args[targetPos]
					for _, arg := range args {
						v, isVar := arg.AsVar()
						if !isVar {
							continue
						}
						if s, isBinder := byBinder[string(v.Name())]; isBinder && registry.IsVecFunType(s.typ) {
							sourcePairs[s.binder] = append(sourcePairs[s.binder], source)
							targetPairs[s.binder] = append(targetPairs[s.binder], target)
						}
					}
				}
			}
			walk(tt.Fun())
			walk(tt.Arg())
		case core.AbsTerm:
			walk(tt.Body())
		}
	}
	walk(p.Conclusion())

	for binder, dims := range pairs {
		s := byBinder[binder]
		dimBinder := resolveDimensionBinder(dims, byBinder)
		if dimBinder == "" {
			continue
		}
		elem, err := renderPhantom(ext.MatchesFun(s.typ)[1], letterParam, usedTypedefs)
		if err != nil {
			return err
		}
		s.elem, s.vecDim = elem, dimBinder
		byBinder[dimBinder].elided = true
	}
	for binder, rows := range rowPairs {
		s := byBinder[binder]
		rowBinder := resolveDimensionBinder(rows, byBinder)
		colBinder := resolveDimensionBinder(colPairs[binder], byBinder)
		if rowBinder == "" || colBinder == "" {
			continue
		}
		elem, err := renderPhantom(ext.MatchesFun(s.typ)[2], letterParam, usedTypedefs)
		if err != nil {
			return err
		}
		s.elem, s.matRows, s.matCols = elem, rowBinder, colBinder
		byBinder[rowBinder].elided = true
		byBinder[colBinder].elided = true
	}
	for binder, sources := range sourcePairs {
		s := byBinder[binder]
		sourceBinder := resolveDimensionBinder(sources, byBinder)
		targetBinder := resolveDimensionBinder(targetPairs[binder], byBinder)
		if sourceBinder == "" || targetBinder == "" {
			continue
		}
		elem, err := renderPhantom(ext.MatchesFun(s.typ)[2], letterParam, usedTypedefs)
		if err != nil {
			return err
		}
		s.elem, s.vecFunSource, s.vecFunTarget = elem, sourceBinder, targetBinder
		byBinder[sourceBinder].elided = true
		byBinder[targetBinder].elided = true
	}
	// The statement's own antecedents, each read for a vector or matrix
	// membership. A law's statement has one antecedent, the structure
	// predicate, with the body's below it: its own At keeps plain
	// slots, and the reading's are refined in buildWrappers.
	markMemberships(slots, antecedentConjuncts(p.Conclusion()))
	return nil
}

// keepUnanchoredDimensions gives its parameter back to each dimension
// binder none of the slots anchors. A reading drops the law's
// components, and a vector, matrix or map among them takes its
// dimension's anchor with it; the reading still binds that dimension,
// and with no carrier left to write it off, the caller writes it.
func keepUnanchoredDimensions(slots []witnessSlot) {
	anchored := map[string]bool{}
	for _, s := range slots {
		for _, dim := range []string{s.vecDim, s.matRows, s.matCols, s.vecFunSource, s.vecFunTarget} {
			if dim != "" {
				anchored[dim] = true
			}
		}
	}
	for i := range slots {
		if slots[i].elided && !anchored[slots[i].binder] {
			slots[i].elided = false
		}
	}
}

// resolveDimensionBinder is the dimension the terms all name, when they
// name ONE num binder of the statement; "" when they disagree, or name
// something that is not a binder. Read at two dimensions, or at one that
// is not a binder, a carrier keeps its plain slot.
func resolveDimensionBinder(dims []core.Term, byBinder map[string]*witnessSlot) string {
	dimBinder := ""
	for _, d := range dims {
		v, ok := d.AsVar()
		if !ok {
			return ""
		}
		ds, isBinder := byBinder[string(v.Name())]
		if !isBinder || !ds.typ.Equals(ext.NumType) || (dimBinder != "" && dimBinder != ds.binder) {
			return ""
		}
		dimBinder = ds.binder
	}
	return dimBinder
}

// markMemberships marks, for each antecedent that is a membership of a
// vector or matrix binder at its own dimension binders, that binder's
// slot (Inhabited / InhabitedMat). The cite then bundles the evidence;
// what the antecedents say beyond the memberships stays with the caller.
func markMemberships(slots []witnessSlot, antecedents []core.Term) {
	for _, a := range antecedents {
		markVectorMembership(slots, a)
	}
}

// markMembers marks, for each guard that is a point's membership in a
// COMPONENT set of the structure a law is read at — `x ∈ M` with M
// among components, or `x ∈ M.carrier` with M a component record and
// carrier one of its fields — the point's slot a Member, and the cite
// bundles the evidence. The guards are every antecedent along the
// reading's telescope, a second ⇒ below the first included: a Member
// embeds its term and so passes to an ext.Typed slot, where its
// evidence would be dropped without a word. A vector slot is a
// concrete *Vec, to which an Inhabited does not pass, so
// markMemberships keeps to the one antecedent.
func markMembers(slots []witnessSlot, guards []core.Term, components map[string]bool) {
	for _, a := range guards {
		head, args := spine(a)
		c, ok := head.AsConst()
		if !ok || string(c.Name()) != "set_member" || len(args) != 2 {
			continue
		}
		x, xIsVar := args[0].AsVar()
		if !xIsVar || !componentSet(args[1], components) {
			continue
		}
		for i := range slots {
			s := &slots[i]
			if s.binder == string(x.Name()) && s.vecDim == "" && s.matRows == "" && s.vecFunSource == "" && !s.elided {
				s.member, s.inhabited = true, true
			}
		}
	}
}

// componentSet reports whether set is a component of the structure, or a
// field of a component record: the record's projection applied to the
// component (`mod_carrier(M)`, which the text spells `M.carrier`).
func componentSet(set core.Term, components map[string]bool) bool {
	if v, ok := set.AsVar(); ok {
		return components[string(v.Name())]
	}
	head, args := spine(set)
	c, isConst := head.AsConst()
	if !isConst || len(args) != 1 {
		return false
	}
	v, ok := args[0].AsVar()
	if !ok || !components[string(v.Name())] {
		return false
	}
	record, ok := v.Type().(core.CompositeType)
	if !ok {
		return false
	}
	syntax := registry.GetConstMetaManager().StructSyntax(string(record.Meta().Name()))
	if syntax == nil {
		return false
	}
	for _, f := range syntax.Fields {
		if f.Const == string(c.Name()) {
			return true
		}
	}
	return false
}

// antecedentConjuncts returns the conjuncts of the one ⇒-antecedent
// under the term's ∀-prefix: nil where there is no antecedent, or where
// a second antecedent sits below the first (the wrapper would have to
// bundle facts by position across two levels).
func antecedentConjuncts(t core.Term) []core.Term {
	for abs := ext.MatchesFORALL(t); !abs.IsZero(); abs = ext.MatchesFORALL(t) {
		t = abs.Body()
	}
	ante, concl, ok := ext.MatchesIMPLY(t)
	if !ok {
		return nil
	}
	for abs := ext.MatchesFORALL(concl); !abs.IsZero(); abs = ext.MatchesFORALL(concl) {
		concl = abs.Body()
	}
	if _, _, again := ext.MatchesIMPLY(concl); again {
		return nil
	}
	return conjuncts(ante)
}

// guardConjuncts returns the conjuncts of every ⇒-antecedent along the
// term's ∀/⇒ telescope, in order — a reading's guards, wherever they
// sit: `x ∈ c ∧ y ∈ c ⇒ x * y = one ⇒ …` gives x ∈ c, y ∈ c and
// x * y = one, and `x ∈ c ⇒ ∀y. y ∈ c ⇒ …` gives both memberships.
func guardConjuncts(t core.Term) []core.Term {
	var out []core.Term
	for {
		if abs := ext.MatchesFORALL(t); !abs.IsZero() {
			t = abs.Body()
			continue
		}
		ante, concl, ok := ext.MatchesIMPLY(t)
		if !ok {
			return out
		}
		out = append(out, conjuncts(ante)...)
		t = concl
	}
}

// conjuncts flattens a ∧-tree into its leaves, in order.
func conjuncts(t core.Term) []core.Term {
	if l, r, isConj := ext.MatchesBinaryOp(ext.AND)(t); isConj {
		return append(conjuncts(l), conjuncts(r)...)
	}
	return []core.Term{t}
}

// markVectorMembership marks the vector or matrix slot whose membership
// at its own dimension binders is the antecedent `membership`: its
// parameter becomes an Inhabited / InhabitedMat and the cite bundles the
// evidence. The membership predicate must spell its dimensions and then
// its subject as its LAST arguments — which is what proof.Inhabit checks
// at run time, so the two agree by construction.
func markVectorMembership(slots []witnessSlot, membership core.Term) {
	head, args := spine(membership)
	c, ok := head.AsConst()
	if !ok {
		return
	}
	last, ok := args[len(args)-1].AsVar()
	if !ok {
		return
	}
	if pos, declared := registry.DimSlot(string(c.Name())); declared && len(args) >= 2 && pos == len(args)-2 {
		dv, isVar := args[pos].AsVar()
		if !isVar {
			return
		}
		for i := range slots {
			s := &slots[i]
			if s.vecDim != "" && string(last.Name()) == s.binder && string(dv.Name()) == s.vecDim {
				s.inhabited = true
			}
		}
		return
	}
	rowPos, colPos, declared := registry.MatrixDimSlots(string(c.Name()))
	if !declared || len(args) < 3 || rowPos != len(args)-3 || colPos != len(args)-2 {
		return
	}
	rv, rowIsVar := args[rowPos].AsVar()
	cv, colIsVar := args[colPos].AsVar()
	if !rowIsVar || !colIsVar {
		return
	}
	for i := range slots {
		s := &slots[i]
		if s.matRows != "" && string(last.Name()) == s.binder &&
			string(rv.Name()) == s.matRows && string(cv.Name()) == s.matCols {
			s.inhabited = true
		}
	}
}

// readingBody is a structure law's body once its components and
// hypothesis are gone: what a reading at an instance states, whose
// antecedents decide the reading's Inhabited and Member slots.
func readingBody(p core.Prop) core.Term {
	t := p.Conclusion()
	for abs := ext.MatchesFORALL(t); !abs.IsZero(); abs = ext.MatchesFORALL(t) {
		t = abs.Body()
	}
	_, body, _ := ext.MatchesIMPLY(t)
	return body
}

// isVectorType reports whether t is a carrier `num → τ`. MatchesFun
// flattens the whole arrow spine, so a matrix carrier — three parts —
// fails this test rather than passing it as a sequence of sequences.
func isVectorType(t core.HolType) bool {
	if !ext.IsFunType(t) {
		return false
	}
	parts := ext.MatchesFun(t)
	return len(parts) == 2 && parts[0].Equals(ext.NumType)
}

// isMatrixType reports whether t is a carrier `num → num → τ`.
func isMatrixType(t core.HolType) bool {
	if !ext.IsFunType(t) {
		return false
	}
	parts := ext.MatchesFun(t)
	return len(parts) == 3 && parts[0].Equals(ext.NumType) && parts[1].Equals(ext.NumType)
}

// spine splits an application into its head and arguments.
func spine(t core.Term) (head core.Term, args []core.Term) {
	head = t
	for {
		app, ok := head.AsAppliedTerm()
		if !ok {
			return head, args
		}
		args = append([]core.Term{app.Arg()}, args...)
		head = app.Fun()
	}
}

// renderWitnesses spells At's argument list: a plain slot by
// name, an elided dimension binder as the one dimension the carriers
// that fixed it are anchored at — a vector's Dim, a matrix's Rows or
// Cols, a map's Source or Target, and SameDimension asserts they agree.
// An elided binder has such a carrier among the slots: the statement's
// own list by construction, a reading's by keepUnanchoredDimensions.
func renderWitnesses(slots []witnessSlot) string {
	var out []string
	for _, s := range slots {
		if !s.elided {
			out = append(out, s.name)
			continue
		}
		var anchors []string
		for _, v := range slots {
			if v.vecDim == s.binder {
				anchors = append(anchors, v.name+".Dim()")
			}
			if v.matRows == s.binder {
				anchors = append(anchors, v.name+".Rows()")
			}
			if v.matCols == s.binder {
				anchors = append(anchors, v.name+".Cols()")
			}
			if v.vecFunSource == s.binder {
				anchors = append(anchors, v.name+".Source()")
			}
			if v.vecFunTarget == s.binder {
				anchors = append(anchors, v.name+".Target()")
			}
		}
		if len(anchors) == 0 {
			panic(fmt.Sprintf("typedgen: the dimension binder %s is elided and no slot of the list anchors it", s.binder))
		}
		out = append(out, "proof.SameDimension("+joinComma(anchors)+")")
	}
	return joinComma(out)
}

func joinComma(parts []string) string {
	out := ""
	for i, p := range parts {
		if i > 0 {
			out += ", "
		}
		out += p
	}
	return out
}

// dimensionTypeParams spells the method's dimension type parameters, one
// per dimension binder its vectors, matrices and maps are read at, and
// reports whether an Inhabited or Member parameter is present.
func dimensionTypeParams(slots []witnessSlot) (string, bool) {
	seen := map[string]bool{}
	var names []string
	hasInhabited := false
	add := func(binder string) {
		if binder != "" && !seen[binder] {
			seen[binder] = true
			names = append(names, "Dim"+dimParamName(binder))
		}
	}
	for _, s := range slots {
		add(s.vecDim)
		add(s.matRows)
		add(s.matCols)
		add(s.vecFunSource)
		add(s.vecFunTarget)
		if s.inhabited {
			hasInhabited = true
		}
	}
	if len(names) == 0 {
		return "", hasInhabited
	}
	return ", " + joinComma(names) + " dimtypes.DimPhantom", hasInhabited
}
