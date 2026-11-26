// dimslot.go — which argument of a chapter's constant is its DIMENSION.
//
// A term-level vector chapter reads its vectors at a num argument:
// `vec⟨n⟩(zero, u)` is membership in dimension n, `dot⟨n⟩(add, mul, u,
// v)` folds the first n products, `vec_norm⟨n⟩(u)` reads n coordinates.
// The kernel term carries n as an ordinary argument; the Go surface can
// carry it as a phantom on the vector (ext/dimtypes.Vec[Elem, DimN]) and
// write it off the vector at the cite — but only once it knows which
// argument the dimension IS. DefEntry.Dim declares that, and this table
// is what the typed wrapper generator reads (library/cmd/gen_family):
// for each application of a Dim-declared constant in a statement, the
// vector binders it applies to are paired with the dimension argument.
//
// A MATRIX reads at two — `matrix⟨n, m⟩(zero, A)` is membership in the
// n×m matrices — so its constant declares the pair (DefEntry.RowDim,
// DefEntry.ColumnDim) and the generator refines its matrix binders to
// dimtypes.Mat[Elem, R, C]. The two tables are separate because the
// kinds are: a constant reads its VECTOR arguments at one dimension and
// its MATRIX arguments at two, and `matrix_act⟨k⟩(add, mul, A, x)` does
// both at once — k is the vector x's dimension and the matrix A's
// column count, and A's row count is not in the term at all. Which
// arguments a declaration governs is decided by their carrier shape,
// never by position: `num → τ` is a vector, `num → num → τ` a matrix.
//
// A MAP between two vector spaces reads at two as well —
// `vec_op_norm⟨n, m⟩(L)` reads L on n-vectors and its values as
// m-vectors — and its constant declares that pair (DefEntry.SourceDim,
// DefEntry.TargetDim), a third table: the generator refines the
// constant's map arguments, the carrier `(num → τ) → num → τ`, to
// dimtypes.VecFun[Elem, Source, Target]. A constant of maps of a space into
// itself has one dimension to name for both, `vec_inverse_on⟨n⟩(L, K)`.
//
// A dimension may govern no argument: `smooth_manifold_map⟨n, m⟩(T, 𝒜,
// S, ℬ, f)` reads a map between manifolds of dimensions n and m, and no
// argument of it is a sequence read at either. Its constant names them
// in DefEntry.Dimensions, which fills no table here: the binders reach
// the ⟨…⟩ through declaredDimensions alone, and the wrappers keep them
// as ordinary parameters.

package registry

import (
	"fmt"
	"slices"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

var (
	dimSlotsMu sync.RWMutex
	dimSlots   = map[string]int{}

	matrixDimSlotsMu sync.RWMutex
	matrixDimSlots   = map[string][2]int{}

	vecFunDimSlotsMu sync.RWMutex
	vecFunDimSlots   = map[string][2]int{}
)

// registerDimSlot records that the constant's argument named dim (a
// ∀-binder of its first equation, of type num) is its dimension slot,
// by position.
func registerDimSlot(constName string, equation core.Prop, dim string) error {
	t := equation.Conclusion()
	pos := 0
	for abs := ext.MatchesFORALL(t); !abs.IsZero(); abs = ext.MatchesFORALL(t) {
		if string(abs.Var().Name()) == dim {
			if !abs.Var().Type().Equals(ext.NumType) {
				return fmt.Errorf("%s is bound at %s, not num", dim, ext.FormatType(abs.Var().Type()))
			}
			dimSlotsMu.Lock()
			defer dimSlotsMu.Unlock()
			if prev, dup := dimSlots[constName]; dup {
				return fmt.Errorf("%s already declares argument %d as its dimension", constName, prev)
			}
			dimSlots[constName] = pos
			return nil
		}
		t = abs.Body()
		pos++
	}
	return fmt.Errorf("%s is not a ∀-binder of the equation", dim)
}

// DimSlot returns the argument position (0-based, over the constant's
// full application) that constName declared as its dimension, and
// whether it declared one.
func DimSlot(constName string) (int, bool) {
	dimSlotsMu.RLock()
	defer dimSlotsMu.RUnlock()
	pos, ok := dimSlots[constName]
	return pos, ok
}

// registerMatrixDimSlots records the constant's row and column dimension
// arguments by position — registerDimSlot at two binders, both required.
func registerMatrixDimSlots(constName string, equation core.Prop, rowDim, columnDim string) error {
	if rowDim == "" || columnDim == "" {
		return fmt.Errorf("a matrix dimension declaration needs both RowDim and ColumnDim")
	}
	if rowDim == columnDim {
		return fmt.Errorf("RowDim and ColumnDim are both %s — a square matrix still binds its two dimensions separately", rowDim)
	}
	positions := map[string]int{}
	t := equation.Conclusion()
	pos := 0
	for abs := ext.MatchesFORALL(t); !abs.IsZero(); abs = ext.MatchesFORALL(t) {
		name := string(abs.Var().Name())
		if name == rowDim || name == columnDim {
			if !abs.Var().Type().Equals(ext.NumType) {
				return fmt.Errorf("%s is bound at %s, not num", name, ext.FormatType(abs.Var().Type()))
			}
			positions[name] = pos
		}
		t = abs.Body()
		pos++
	}
	for _, name := range []string{rowDim, columnDim} {
		if _, found := positions[name]; !found {
			return fmt.Errorf("%s is not a ∀-binder of the equation", name)
		}
	}
	matrixDimSlotsMu.Lock()
	defer matrixDimSlotsMu.Unlock()
	if prev, dup := matrixDimSlots[constName]; dup {
		return fmt.Errorf("%s already declares arguments %d and %d as its dimensions", constName, prev[0], prev[1])
	}
	matrixDimSlots[constName] = [2]int{positions[rowDim], positions[columnDim]}
	return nil
}

// MatrixDimSlots returns the argument positions (0-based, over the
// constant's full application) that constName declared as its row and
// column dimensions, and whether it declared them.
func MatrixDimSlots(constName string) (rows, columns int, ok bool) {
	matrixDimSlotsMu.RLock()
	defer matrixDimSlotsMu.RUnlock()
	pair, found := matrixDimSlots[constName]
	return pair[0], pair[1], found
}

// registerVecFunDimSlots records the constant's source and target dimension
// arguments by position, both required. The two may be one binder: a
// constant of maps of a space into itself carries one dimension. The
// equation must bind an argument of the map carrier, or the declaration
// would govern nothing.
func registerVecFunDimSlots(constName string, equation core.Prop, sourceDim, targetDim string) error {
	if sourceDim == "" || targetDim == "" {
		return fmt.Errorf("a map dimension declaration needs both SourceDim and TargetDim")
	}
	positions := map[string]int{}
	hasVecFun := false
	t := equation.Conclusion()
	pos := 0
	for abs := ext.MatchesFORALL(t); !abs.IsZero(); abs = ext.MatchesFORALL(t) {
		name := string(abs.Var().Name())
		if name == sourceDim || name == targetDim {
			if !abs.Var().Type().Equals(ext.NumType) {
				return fmt.Errorf("%s is bound at %s, not num", name, ext.FormatType(abs.Var().Type()))
			}
			positions[name] = pos
		}
		if IsVecFunType(abs.Var().Type()) {
			hasVecFun = true
		}
		t = abs.Body()
		pos++
	}
	for _, name := range []string{sourceDim, targetDim} {
		if _, found := positions[name]; !found {
			return fmt.Errorf("%s is not a ∀-binder of the equation", name)
		}
	}
	if !hasVecFun {
		return fmt.Errorf("the equation binds no map between vector spaces, an argument of type (num → τ) → num → τ, for the declaration to govern")
	}
	vecFunDimSlotsMu.Lock()
	defer vecFunDimSlotsMu.Unlock()
	if prev, dup := vecFunDimSlots[constName]; dup {
		return fmt.Errorf("%s already declares arguments %d and %d as its maps' dimensions", constName, prev[0], prev[1])
	}
	vecFunDimSlots[constName] = [2]int{positions[sourceDim], positions[targetDim]}
	return nil
}

// VecFunDimSlots returns the argument positions (0-based, over the
// constant's full application) that constName declared as the source and
// target dimensions of its map arguments, and whether it declared them.
func VecFunDimSlots(constName string) (source, target int, ok bool) {
	vecFunDimSlotsMu.RLock()
	defer vecFunDimSlotsMu.RUnlock()
	pair, found := vecFunDimSlots[constName]
	return pair[0], pair[1], found
}

// IsVecFunType reports whether t is the carrier of a map between two
// term-level vector spaces over one element, `(num → τ) → num → τ`.
// ext.MatchesFun flattens the arrow spine to the right and leaves the
// first argument whole, so the shape is three parts: a vector carrier,
// num, and that carrier's element.
func IsVecFunType(t core.HolType) bool {
	if !ext.IsFunType(t) {
		return false
	}
	parts := ext.MatchesFun(t)
	if len(parts) != 3 || !parts[1].Equals(ext.NumType) || !ext.IsFunType(parts[0]) {
		return false
	}
	source := ext.MatchesFun(parts[0])
	return len(source) == 2 && source[0].Equals(ext.NumType) && source[1].Equals(parts[2])
}

// declaredDimensions is the binder names an entry declares as
// dimensions — Dim, RowDim and ColumnDim, SourceDim and TargetDim,
// then Dimensions — each once, in that order: the arguments its text
// writes in the ⟨…⟩ after the constant's name (ext/dsl/dimension.go).
func declaredDimensions(e DefEntry) []string {
	var names []string
	for _, name := range append([]string{e.Dim, e.RowDim, e.ColumnDim, e.SourceDim, e.TargetDim}, e.Dimensions...) {
		if name != "" && !slices.Contains(names, name) {
			names = append(names, name)
		}
	}
	return names
}

// checkDimensionsField refuses a DefEntry.Dimensions list that names a
// binder twice, names none, or names one another dimension declaration
// already names: a dimension binder has one declaration, and a binder
// a vector, matrix or map is read at declares itself there.
func checkDimensionsField(e DefEntry) error {
	other := []struct{ field, name string }{
		{"Dim", e.Dim}, {"RowDim", e.RowDim}, {"ColumnDim", e.ColumnDim},
		{"SourceDim", e.SourceDim}, {"TargetDim", e.TargetDim},
	}
	for i, name := range e.Dimensions {
		if name == "" {
			return fmt.Errorf("entry %d is empty", i)
		}
		if slices.Contains(e.Dimensions[:i], name) {
			return fmt.Errorf("%s is named twice", name)
		}
		for _, o := range other {
			if o.name == name {
				return fmt.Errorf("%s is already declared by %s", name, o.field)
			}
		}
	}
	return nil
}

// checkNumBinders holds each name to a ∀-binder of the equation bound at
// num, the outermost binder of that name.
func checkNumBinders(equation core.Prop, names []string) error {
	bound := map[string]core.HolType{}
	t := equation.Conclusion()
	for abs := ext.MatchesFORALL(t); !abs.IsZero(); abs = ext.MatchesFORALL(t) {
		name := string(abs.Var().Name())
		if _, outer := bound[name]; !outer {
			bound[name] = abs.Var().Type()
		}
		t = abs.Body()
	}
	for _, name := range names {
		typ, found := bound[name]
		if !found {
			return fmt.Errorf("%s is not a ∀-binder of the equation", name)
		}
		if !typ.Equals(ext.NumType) {
			return fmt.Errorf("%s is bound at %s, not num", name, ext.FormatType(typ))
		}
	}
	return nil
}

// checkLeadingDimensions holds an entry's declared dimensions to the
// equation's binders right after its implicit prefix, which is where
// the ⟨…⟩ form reads them from: dims of them, in any order among
// themselves.
func checkLeadingDimensions(equation core.Prop, implicit int, dims []string) error {
	var binders []string
	t := equation.Conclusion()
	for abs := ext.MatchesFORALL(t); !abs.IsZero(); abs = ext.MatchesFORALL(t) {
		binders = append(binders, string(abs.Var().Name()))
		t = abs.Body()
	}
	if len(binders) < implicit+len(dims) {
		return fmt.Errorf("the declared dimensions %v exceed the equation's binders %v after its %d implicit one(s)", dims, binders, implicit)
	}
	leading := binders[implicit : implicit+len(dims)]
	for _, name := range dims {
		if !slices.Contains(leading, name) {
			return fmt.Errorf("the declared dimensions %v must be the equation's binders right after its implicit prefix — the arguments the text writes in ⟨…⟩ — and those are %v", dims, leading)
		}
	}
	return nil
}
