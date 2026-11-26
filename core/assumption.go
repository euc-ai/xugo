package core

import "sync"

// An AssumptionDoor names the door a statement entered a certificate by
// without a rule deriving it.
type AssumptionDoor uint8

const (
	// AxiomDoor is NewAxiom: the library's postulate and its cards.
	AxiomDoor AssumptionDoor = iota + 1
	// BoundaryDoor is ForceWithBoundary: a promise cell settled from its
	// statement because the caller's predicate trusted it.
	BoundaryDoor
	// TestDoor is TestThm.
	TestDoor
)

func (d AssumptionDoor) String() string {
	switch d {
	case AxiomDoor:
		return "NewAxiom"
	case BoundaryDoor:
		return "ForceWithBoundary"
	case TestDoor:
		return "TestThm"
	default:
		return "no door"
	}
}

// An Assumption is one statement a certificate stands on that no rule
// derived, with the door it came in by.
type Assumption struct {
	Statement Prop
	Door      AssumptionDoor
}

// _Assumption is one assumption, made once per statement and door: two
// mints of α-equal statements through one door are one assumption.
type _Assumption struct {
	id        uint32
	statement *_Statement
	door      AssumptionDoor
	// alone is the set holding this assumption and no other.
	alone *_Assumptions
}

// _Assumptions is a set of assumptions, ordered by id and never written
// after it is made. The empty set is nil.
type _Assumptions struct{ members []*_Assumption }

type _AssumptionKey struct {
	statement PropKey
	door      AssumptionDoor
}

// assumptionTable holds every assumption the process has made. Under a
// statement's key and a door it lists the assumptions made of the
// statements having that key: one, unless two statements that are not
// α-equal share the key (PropKey). number counts the assumptions made.
var assumptionTable = struct {
	mu     sync.Mutex
	made   map[_AssumptionKey][]*_Assumption
	number uint32
}{made: map[_AssumptionKey][]*_Assumption{}}

// assumed is the set holding the one assumption of s through door. The
// assumption is found by comparing statements: the key says which to
// compare s against and decides nothing, so a certificate lists the
// statement it was minted over whatever shares that statement's key.
func assumed(s _Statement, door AssumptionDoor) *_Assumptions {
	key := _AssumptionKey{s.AlphaKey(), door}
	assumptionTable.mu.Lock()
	defer assumptionTable.mu.Unlock()
	sharing := assumptionTable.made[key]
	for _, a := range sharing {
		if a.statement.alphaEquals(&s) {
			return a.alone
		}
	}
	assumptionTable.number++
	a := &_Assumption{
		id:        assumptionTable.number,
		statement: &_Statement{conclusion: s.conclusion, hyps: s.hyps},
		door:      door,
	}
	a.alone = &_Assumptions{members: []*_Assumption{a}}
	assumptionTable.made[key] = append(sharing, a)
	return a.alone
}

// union is the set of the assumptions in a or in b. It is a or b itself
// when one holds the other, so a derivation that keeps drawing on the
// same assumptions allocates nothing.
func (a *_Assumptions) union(b *_Assumptions) *_Assumptions {
	if a == b || b == nil {
		return a
	}
	if a == nil {
		return b
	}
	x, y := a.members, b.members
	// Count first: the union is one of the two far more often than not.
	n, i, j := 0, 0, 0
	for i < len(x) && j < len(y) {
		switch {
		case x[i].id == y[j].id:
			i, j = i+1, j+1
		case x[i].id < y[j].id:
			i++
		default:
			j++
		}
		n++
	}
	n += len(x) - i + len(y) - j
	switch n {
	case len(x):
		return a
	case len(y):
		return b
	}
	merged := make([]*_Assumption, 0, n)
	i, j = 0, 0
	for i < len(x) && j < len(y) {
		switch {
		case x[i].id == y[j].id:
			merged = append(merged, x[i])
			i, j = i+1, j+1
		case x[i].id < y[j].id:
			merged = append(merged, x[i])
			i++
		default:
			merged = append(merged, y[j])
			j++
		}
	}
	return &_Assumptions{members: append(append(merged, x[i:]...), y[j:]...)}
}

// list is the set as a caller may keep it.
func (a *_Assumptions) list() []Assumption {
	if a == nil {
		return nil
	}
	out := make([]Assumption, len(a.members))
	for i, m := range a.members {
		out[i] = Assumption{Statement: _Proposition{m.statement}, Door: m.door}
	}
	return out
}
