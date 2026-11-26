/** File: disjunction_branches.go
 *
 * The named branches of a disjunctive-hypothesis split.
 *
 *   A ∨ B ⊢ C   →   A ⊢ C   and   B ⊢ C
 *
 * The tactic hands the two children back in the disjunction's order,
 * and a surface taking `cases ...Case` reads them positionally — so the
 * author says in prose which disjunct a branch assumes, and the prose is
 * unchecked. Each branch gets a name and its own TYPE instead: LeftHolds
 * and RightHolds cannot be passed in each other's slot, and the verb —
 * not the author — places each where the tactic wants it. The same
 * discipline as the ⇔ split's halves (iff_direction.go); the Cases /
 * Induct / Iff verbs claim their branches by name already, and a
 * disjunction's were the one split left to position.
 *
 * The positional forms survive one layer down (SplitDisjCases,
 * SplitDisjAtCases): emit renders a split whose children did not become
 * a Case block as a bare caseless step, and the dismiss combinators
 * (hyp_handle.go) split first and discharge one side afterwards. A
 * chapter body never authors them — TestLintNoPositionalBranchCases.
 */

package proof

// DisjLeftHolds carries the branch on which the LEFT disjunct of a
// disjunctive hypothesis is resident. It is a distinct type from
// DisjRightHolds so the two cannot be swapped.
type DisjLeftHolds struct{ c Case }

// DisjRightHolds carries the branch on which the RIGHT disjunct is
// resident.
type DisjRightHolds struct{ c Case }

// LeftHolds is the branch of a disjunctive-hypothesis split on which the
// left disjunct holds. label says what that branch proves, in
// mathematics; the constructor says which disjunct it assumes.
func LeftHolds(label string, body ...Action) DisjLeftHolds {
	return DisjLeftHolds{c: MakeCase(label, body...)}
}

// RightHolds is the branch on which the right disjunct holds.
func RightHolds(label string, body ...Action) DisjRightHolds {
	return DisjRightHolds{c: MakeCase(label, body...)}
}

// SplitDisj splits the first ∨-shaped hypothesis into its two branches,
// each claimed by the disjunct it assumes.
func SplitDisj(left DisjLeftHolds, right DisjRightHolds) Step {
	return SplitDisjCases(left.c, right.c)
}

// SplitDisjAt is SplitDisj on the hypothesis at hypIdx.
func SplitDisjAt(hypIdx int, left DisjLeftHolds, right DisjRightHolds) Step {
	return SplitDisjAtCases(hypIdx, left.c, right.c)
}
