// definitions.go — the chapter's definitional layer: the loops at a
// point, the class of a path under homotopy with its ends held, the
// operations on classes that joining and reversing induce, the
// fundamental group as a group record, the map of classes a continuous
// map induces, and simply connected spaces.
//
// The operations on classes name no base point and choose no
// representative: the join of two classes is every path homotopic to the
// join of a member of the first with a member of the second, which is
// the class of that join when the two meet end to start. So one pair of
// operations serves loops at a point and paths between points alike. On
// classes that do not meet the join reads joins that are not paths, and
// no statement uses it there.

package fundamental_group

import (
	"github.com/euc-ai/xugo/library/registry"
)

// LoopsAtDef — `loops_at(T, x)`: the paths that begin and end at x.
var LoopsAtDef = loopsAtDefThm{family.Define(registry.DefEntry{
	Name:     "LoopsAtDef",
	Key:      "prop_5fe64a171138708d",
	Const:    "loops_at",
	Type:     "set(set(A)) → A → set(real → A)",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀x:A. loops_at(T, x) = {g:(real → A) | path_in(T, g) ∧ g(&0) = x ∧ g(&1) = x}",
	},
})}

// PathClassDef — `path_class(T, g)`: the paths homotopic to g with the
// ends held.
var PathClassDef = pathClassDefThm{family.Define(registry.DefEntry{
	Name:     "PathClassDef",
	Key:      "prop_8b4558d853c0e01a",
	Const:    "path_class",
	Type:     "set(set(A)) → (real → A) → set(real → A)",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀g:(real → A). path_class(T, g) = {k:(real → A) | path_homotopic(T, g, k)}",
	},
})}

// PathClassJoinDef — `path_class_join(T, C, D)`: the paths homotopic to
// the join of a member of C with a member of D.
var PathClassJoinDef = pathClassJoinDefThm{family.Define(registry.DefEntry{
	Name:     "PathClassJoinDef",
	Key:      "prop_99817427ead20669",
	Const:    "path_class_join",
	Type:     "set(set(A)) → set(real → A) → set(real → A) → set(real → A)",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀C D:set(real → A). " +
			"    path_class_join(T, C, D) = " +
			"    {k:(real → A) | ∃g h:(real → A). g ∈ C ∧ h ∈ D ∧ path_homotopic(T, k, path_join(g, h))}",
	},
})}

// PathClassReverseDef — `path_class_reverse(T, C)`: the paths homotopic to
// the reverse of a member of C.
var PathClassReverseDef = pathClassReverseDefThm{family.Define(registry.DefEntry{
	Name:     "PathClassReverseDef",
	Key:      "prop_487e752d73446180",
	Const:    "path_class_reverse",
	Type:     "set(set(A)) → set(real → A) → set(real → A)",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀C:set(real → A). " +
			"    path_class_reverse(T, C) = " +
			"    {k:(real → A) | ∃g:(real → A). g ∈ C ∧ path_homotopic(T, k, path_reverse(g))}",
	},
})}

// FundamentalGroupDef — `fundamental_group(T, x)`: the group record whose
// carrier is the classes of the loops at x, multiplied by joining, with
// the class of the constant loop for unit and reversal for inverse.
var FundamentalGroupDef = fundamentalGroupDefThm{family.Define(registry.DefEntry{
	Name:     "FundamentalGroupDef",
	Key:      "prop_b918043054846ad0",
	Const:    "fundamental_group",
	Type:     "set(set(A)) → A → group_ops(set(real → A))",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀x:A. " +
			"    fundamental_group(T, x) = " +
			"    mk_group(path_class_join(T), " +
			"        path_class(T, λt:real. x), " +
			"        path_class_reverse(T), " +
			"        quotient_on(loops_at(T, x), path_homotopic(T)))",
	},
	Reading: "At a point outside the space there are no loops and the " +
		"carrier is empty; the group laws are stated at a point of the space.",
	Deps: []registry.EntryLike{LoopsAtDef, PathClassDef, PathClassJoinDef, PathClassReverseDef},
})}

// FundamentalMapDef — `fundamental_map(S, f, C)`: the paths of S
// homotopic to f after a member of C — the class a continuous map carries
// a class of paths to.
var FundamentalMapDef = fundamentalMapDefThm{family.Define(registry.DefEntry{
	Name:     "FundamentalMapDef",
	Key:      "prop_c08a5b5492983660",
	Const:    "fundamental_map",
	Type:     "set(set(B)) → (A → B) → set(real → A) → set(real → B)",
	Implicit: []string{"S"},
	Equations: []string{
		"∀S:set(set(B)). ∀f:(A → B). ∀C:set(real → A). " +
			"    fundamental_map(S, f, C) = " +
			"    {k:(real → B) | ∃g:(real → A). g ∈ C ∧ path_homotopic(S, k, f ∘ g)}",
	},
})}

// SimplyConnectedSpaceDef — `simply_connected_space(T)`: the space is
// path-connected and every loop is homotopic, with its ends held, to the
// constant loop at its base point.
var SimplyConnectedSpaceDef = simplyConnectedSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "SimplyConnectedSpaceDef",
	Key:   "prop_4a2f7fcf3041ae7e",
	Const: "simply_connected_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    simply_connected_space(T) ⇔ " +
			"    path_connected_in(T, ⋃T) ∧ " +
			"    ∀x:A. ∀g:(real → A). g ∈ loops_at(T, x) ⇒ path_homotopic(T, g, λt:real. x)",
	},
	Reading: "The empty space is simply connected, as it is " +
		"path-connected: there is no point and no loop to ask about.",
	Deps: []registry.EntryLike{LoopsAtDef},
})}
