package refuter

import (
	"maps"
	"slices"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/clause"
	"github.com/euc-ai/xugo/utils"
)

type (
	Term      = core.Term
	VarTerm   = core.VarTerm
	Prop      = core.Prop
	Thm       = core.ThmCert
	PropKey   = core.PropKey
	Clause    = clause.Clause
	ClauseKey = clause.ClauseKey
	ClauseThm = clause.ClauseThm
	ClauseMap = clause.ClauseMap
)

var (
	Assert = utils.Assert
	OneOf  = utils.OneOf
)

const (
	_CLAUSE_DEDUCE_BUFFER_SIZE = 32
	_CLAUSE_SIZE_LIMIT         = 128
	_CONTRADICT_WORKERS        = 8
	// Maximum concurrent (c, ci) resolve goroutines per processNewClause
	// pick. The outer fan-out across all (c, ci) pairs is otherwise
	// O(active), which under heavy load (large active set × many parallel
	// outer refutations) creates enough scheduler-driven non-determinism
	// to push the saturation into a divergent search trajectory. Bounding
	// the live count keeps the inner Resolve unification work parallel
	// without thrashing the goroutine scheduler. Each running task here
	// also fans out internally inside c.Resolve, so we leave headroom by
	// keeping this lower than _CONTRADICT_WORKERS.
	_RESOLVE_FANOUT = 4
)

func searchOrderedClauses(clauses []*Clause, c *Clause) (int, bool) {
	return slices.BinarySearchFunc(clauses, c, clause.CompareClauses)
}

type _KeyPair struct{ k0, k1 ClauseKey }

type _AttemptRecords struct{ utils.Map[_KeyPair, struct{}] }

func (r *_AttemptRecords) clone() *_AttemptRecords {
	newRecords := &_AttemptRecords{}
	r.Copy(&newRecords.Map)
	return newRecords
}

func (r *_AttemptRecords) loadOrStoreFactor(c *Clause) bool {
	if _, ok := r.LoadOrStore(_KeyPair{c.Key(), ""}, struct{}{}); ok {
		return true
	}
	return false
}

func (r *_AttemptRecords) loadOrStoreResolve(c0, c1 *Clause) bool {
	if _, ok := r.LoadOrStore(_KeyPair{c0.Key(), c1.Key()}, struct{}{}); ok {
		return true
	}
	return false
}

type _RefuteCache struct {
	// for contradicts between clause pairs
	contradicts utils.Map[_KeyPair, *ClauseThm]
	// for proofs
	proof utils.Map[PropKey, *_ProofDAG]
}

func (c *_RefuteCache) loadContradict(c0, c1 *Clause) *ClauseThm {
	t, _ := c.contradicts.Load(_KeyPair{c0.Key(), c1.Key()})
	return t
}

func (c *_RefuteCache) storeContradict(c0, c1 *Clause, t *ClauseThm) {
	Assert(t != nil && t.NumHyps() <= 2 && t.HasHypClause(c0) && t.HasHypClause(c1))
	c.contradicts.LoadOrStore(_KeyPair{c0.Key(), c1.Key()}, t)
	if c0.Key() != c1.Key() {
		c.contradicts.LoadOrStore(_KeyPair{c1.Key(), c0.Key()}, t)
	}
}

func (c *_RefuteCache) loadOrStoreProof(key PropKey, proof *_ProofDAG) {
	c.proof.LoadOrStore(key, proof)
}

type _ActiveSet struct {
	// The ordered active clauses
	clauses []*Clause
	m       ClauseMap
	sync.RWMutex
}

func (c *_ActiveSet) has(clause *Clause) bool {
	c.RLock()
	defer c.RUnlock()
	_, ok := c.m[clause.Key()]
	return ok
}

func (c *_ActiveSet) snapshot() []*Clause {
	c.RLock()
	defer c.RUnlock()
	return utils.Clone(c.clauses)
}

func (c *_ActiveSet) clone() *_ActiveSet {
	c.RLock()
	defer c.RUnlock()
	return &_ActiveSet{
		clauses: utils.Clone(c.clauses),
		m:       maps.Clone(c.m)}
}

func (c *_ActiveSet) insert(newClause *Clause) bool {
	c.Lock()
	defer c.Unlock()

	if len(c.clauses) == 0 {
		c.clauses, c.m[newClause.Key()] = []*Clause{newClause}, newClause
		return true
	}

	if _, ok := c.m[newClause.Key()]; ok {
		return false
	}

	insertPos, found := searchOrderedClauses(c.clauses, newClause)
	Assert(!found)

	// If some existing clause divides the new clause, no need to add it.
	for _, c := range c.clauses[:insertPos] {
		if c.TriviallySubsumes(newClause) {
			return false
		}
	}

	newClauses := make([]*Clause, 0, len(c.clauses)+1)
	newClauses = append(newClauses, c.clauses[:insertPos]...)
	newClauses = append(newClauses, newClause)
	c.m[newClause.Key()] = newClause

	// If the new clause divides some existing clause, remove the existing one.
	for _, clause := range c.clauses[insertPos:] {
		if newClause.TriviallySubsumes(clause) {
			delete(c.m, clause.Key())
		} else {
			newClauses = append(newClauses, clause)
		}
	}
	c.clauses = newClauses
	Assert(len(c.clauses) == len(c.m))
	return true
}

func (c *_ActiveSet) reset() {
	c.Lock()
	defer c.Unlock()
	c.clauses = nil
	clear(c.m)
}

// remove takes clause out of the set; a clause outside it is left alone.
func (c *_ActiveSet) remove(clause *Clause) {
	c.Lock()
	defer c.Unlock()
	if _, ok := c.m[clause.Key()]; !ok {
		return
	}
	delete(c.m, clause.Key())
	i, found := searchOrderedClauses(c.clauses, clause)
	Assert(found)
	c.clauses = slices.Delete(c.clauses, i, i+1)
	Assert(len(c.clauses) == len(c.m))
}

type _DeductionRecords struct {
	records map[ClauseKey]*_DeduceStep
	// The ordered conclusion clauses for all steps for convenient access.
	clauses []*Clause
	sync.RWMutex
}

func emptyDeductRecord() *_DeductionRecords {
	return &_DeductionRecords{records: make(map[ClauseKey]*_DeduceStep)}
}

func (d *_DeductionRecords) empty() bool {
	d.RLock()
	defer d.RUnlock()
	return len(d.clauses) == 0
}

func (d *_DeductionRecords) has(c *Clause) bool {
	d.RLock()
	defer d.RUnlock()
	_, ok := d.records[c.Key()]
	return ok
}

func (d *_DeductionRecords) lookup(c *Clause) *_DeduceStep {
	d.RLock()
	defer d.RUnlock()
	if record, ok := d.records[c.Key()]; ok {
		return record
	}
	return nil
}

// Returns true if write to the records, false if it's already there.
func (d *_DeductionRecords) write(clauseThm *ClauseThm) bool {
	d.Lock()
	defer d.Unlock()
	conclusion := clauseThm.ConclClause()
	_, ok := d.records[conclusion.Key()]
	if ok {
		return false
	}

	d.records[conclusion.Key()] = makeDeduceStep(clauseThm)
	insertPos, found := searchOrderedClauses(d.clauses, conclusion)
	Assert(!found)
	d.clauses = slices.Insert(d.clauses, insertPos, conclusion)
	return true
}

func (d *_DeductionRecords) clone() *_DeductionRecords {
	d.RLock()
	defer d.RUnlock()
	new := emptyDeductRecord()
	new.records = maps.Clone(d.records)
	new.clauses = utils.Clone(d.clauses)
	return new
}

type _PassiveSet struct {
	// The ordered useful clauses
	clauses     []*Clause
	uselessness utils.Set[ClauseKey]
	// Set once the search over this set is saturated: every producer has
	// returned and nothing is selectable. A clause added after that would
	// never be selected, so add refuses it.
	sealed bool
	sync.RWMutex
}

func emptyPassiveSet() *_PassiveSet {
	return &_PassiveSet{uselessness: utils.EmptySet[ClauseKey]()}
}

func (s *_PassiveSet) snapshot() []*Clause {
	s.RLock()
	defer s.RUnlock()
	return utils.Clone(s.clauses)
}

func (s *_PassiveSet) has(c *Clause) bool {
	s.RLock()
	defer s.RUnlock()
	_, found := searchOrderedClauses(s.clauses, c)
	return found
}

func (s *_PassiveSet) add(c *Clause) {
	s.Lock()
	defer s.Unlock()
	Assert(!s.sealed)
	if s.uselessness.Has(c.Key()) {
		return
	}
	insertPos, found := searchOrderedClauses(s.clauses, c)
	Assert(!found)
	s.clauses = slices.Insert(s.clauses, insertPos, c)
}

func (s *_PassiveSet) clone() *_PassiveSet {
	s.RLock()
	defer s.RUnlock()
	return &_PassiveSet{
		clauses:     utils.Clone(s.clauses),
		uselessness: s.uselessness.Clone(),
	}
}

// seal records that the search over this set is saturated; a later add panics.
func (s *_PassiveSet) seal() {
	s.Lock()
	defer s.Unlock()
	s.sealed = true
}

func (s *_PassiveSet) checkUselessness(c *Clause) bool {
	s.RLock()
	defer s.RUnlock()
	return s.uselessness.Has(c.Key())
}

func (s *_PassiveSet) markUseless(c *Clause) {
	s.Lock()
	defer s.Unlock()

	if s.uselessness.Has(c.Key()) {
		return
	}
	s.uselessness.Add(c.Key())
	ind, found := searchOrderedClauses(s.clauses, c)
	Assert(found)
	s.clauses = slices.Delete(s.clauses, ind, ind+1)
}
