package bridge

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/reify"
	"github.com/euc-ai/xugo/utils"
)

// The lemmas the embedding mode cites, as family.Member.
const (
	lemmaEncodeFamilyCarrier = "polynomial_encoding.EncodePolynomialsInCarrier"
	lemmaDecodeEncodeFamily  = "polynomial_encoding.DecodeEncodePolynomials"
	lemmaEncodeFamilyOutside = "polynomial_encoding.EncodePolynomialsOutside"
	lemmaEncodeCarrier       = "polynomial_encoding.EncodeInCarrier"
	lemmaDecodeEncode        = "polynomial_encoding.DecodeEncode"
	lemmaEncodeDef           = "polynomial_encoding.EncodePolynomialDef"
	lemmaEmbedding           = "algebraically_closed_field_transfer.EmbeddingElementary"
	lemmaOrderedEmbedding    = "real_closed_field_transfer.EmbeddingElementary"
	lemmaHomomorphismDef     = "ring_homomorphism.RingHomomorphism"
	lemmaDecodeImage         = "polynomial_encoding.DecodeImage"
	lemmaDecodeTupleImage    = "polynomial_encoding.DecodeTupleImage"
)

// _Embedding is an embedding-mode call read off its goal and facts: the
// homomorphism fact names i from F into G; the goal is Φ(F, params) ⇔
// Φ(G, i(params)) in either order; the closed-field facts make the
// theory, and in the ordered theory name F's order and G's.
type _Embedding struct {
	F, G, i   core.Term
	ltF, ltG  core.Term
	theory    Theory
	hom       *prop.PropWrapper
	sideF     core.Term
	sideG     core.Term
	fFirst    bool
	params    []reify.Parameter
	images    []reify.Parameter
	envF      core.Term
	rho       core.VarTerm
	represent []core.Term
	bF        *_Builder
	resF      *reify.Result
}

// embedding proves the iff goal along the embedding: both sides read as
// one formula φ with the parameters F's side names, F's bridge at an
// environment ρ representing them and G's at λv. i(ρ(v)), which
// represents their images; EmbeddingElementary joins the two
// evaluations. The theorem holds under the environment's facts: ρ
// carrier-valued and each parameter represented in it.
func (x *_Executor) embedding(e *_Embedding) (*prop.PropWrapper, error) {
	inF := reify.Input{Structure: reify.Structure{Field: e.F, Order: e.ltF}, Proposition: e.sideF, Parameters: e.params, Unfold: DefinitionUnfolder(), Arithmetic: _Arithmetic{x.lib}, Vocabulary: x.vocabulary}
	resF, err := reify.Reify(inF)
	if err != nil {
		return nil, err
	}
	inG := reify.Input{Structure: reify.Structure{Field: e.G, Order: e.ltG}, Proposition: e.sideG, Parameters: e.images, Unfold: DefinitionUnfolder(), Arithmetic: _Arithmetic{x.lib}, Vocabulary: x.vocabulary}
	resG, err := reify.Reify(inG)
	if err != nil {
		return nil, err
	}
	if !resF.Formula.AlphaEquals(resG.Formula) {
		return nil, refuse("the two sides of the embedding read as two formulas:\n  over %s: %s\n  over %s: %s", ext.PrintTerm(e.F), ext.PrintTerm(resF.Formula), ext.PrintTerm(e.G), ext.PrintTerm(resG.Formula))
	}
	bF := newBuilder(inF, resF, x.lib)
	bridgeF, rho := bF.parameterized()
	bG := newBuilder(inG, resG, x.lib)
	bridgeG, rhoG := bG.parameterized()
	v := bF.fresh("v", ext.NumType)
	image := core.Abs(v, core.Apply(e.i, core.Apply(rho, v)))
	bridgeG = bridgeG.TermInst(core.MakeTermSubst(rhoG, image))

	e.rho, e.bF, e.resF = rho, bF, resF
	e.envF = bF.call("fo_env_ok", bF.carrier, x.universe(), rho)
	envF := assume(e.envF)
	c := &_Context{sigma: rho, envOK: envF}

	// G's environment and its representations, from F's through i.
	opened := bF.instance(lemmaHomomorphismDef, bF.ring, bG.ring, e.i).EqMP(e.hom)
	inCarrier := opened.DeriveTrans(conjunctionPieces(opened.Conclusion())[2])
	bridgeG = x.imageEnvironment(bF, bG, envF, inCarrier, image).DeriveTrans(bridgeG)
	blocksF, blocksG := parameterBlocks(resF), parameterBlocks(resG)
	for k, block := range blocksF {
		rep := bF.representation(block, bF.blockValue(block), rho)
		e.represent = append(e.represent, rep)
		target := bG.representation(blocksG[k], bG.blockValue(blocksG[k]), image)
		derived := x.imageRepresentation(bF, bG, e, block, assume(rep), image, target)
		if bridgeG.HasHyp(target) {
			bridgeG = derived.DeriveTrans(bridgeG)
		}
	}
	sideF, sideG := _Structure{F: e.F, lt: e.ltF}, _Structure{F: e.G, lt: e.ltG}
	bridgeG = wrap(x.structureFrom(bG, sideG).MaybeDeriveTrans(bridgeG))
	bridgeF = x.structureFrom(bF, sideF).DeriveTrans(bridgeF)

	// EmbeddingElementary at ρ and φ, the theory's.
	wf, _ := bF.support(resF.Formula, resF.Names.Frontier, &_Context{})
	valid := bF.instance(lemmaFormulaValidDef, resF.Formula).EqSym().EqMP(wf)
	given := c.with(x.closedFact(bF, sideF), x.closedFact(bG, sideG), e.hom, valid)
	var elementary *prop.PropWrapper
	if e.theory == RealClosedTheory {
		elementary = bF.use(lemmaOrderedEmbedding, given, e.F, e.ltF, e.G, e.ltG, e.i, rho, resF.Formula)
	} else {
		elementary = bF.use(lemmaEmbedding, given, e.F, e.G, e.i, rho, resF.Formula)
	}
	iff := bridgeF.EqTrans(elementary).EqTrans(bridgeG.EqSym())
	if !e.fFirst {
		iff = iff.EqSym()
	}
	sameConclusion(iff, x.call.Goal, "the embedding's iff")
	return iff, nil
}

func (x *_Executor) universe() core.Term {
	return core.MakeConstTerm(x.lib.Constant("universe"), ext.MakeFun(ext.NumType, core.TypeBool()))
}

func parameterBlocks(res *reify.Result) []*reify.Block {
	var out []*reify.Block
	for _, b := range res.Names.Blocks {
		if b.Parameter {
			out = append(out, b)
		}
	}
	return out
}

// imageEnvironment is fo_env_ok(F.carrier, 𝕌, ρ) ⊢ fo_env_ok(G.carrier,
// 𝕌, λv. i(ρ(v))): every value of ρ lies in F's carrier, and i carries
// F's carrier into G's.
func (x *_Executor) imageEnvironment(bF, bG *_Builder, envF, inCarrier *prop.PropWrapper, image core.Term) *prop.PropWrapper {
	defF := bF.instance(lemmaEnvOKDef, bF.carrier, x.universe(), envArg(envF.Conclusion()))
	defG := bG.instance(lemmaEnvOKDef, bG.carrier, x.universe(), image)
	everyF := defF.EqMP(envF)
	_, everyG, _ := core.MatchesEQ(defG.Conclusion())
	all := ext.MatchesFORALL(everyG)
	v := all.Var()
	inUniverse, _, _ := ext.MatchesIMPLY(all.Body())
	valueF := modusPonens(everyF.ConclForAllInst(v), assume(inUniverse))
	_, member := ext.MatchesApply(valueF.Conclusion())
	mapped := modusPonens(inCarrier.ConclForAllInst(member[0]), valueF)
	return defG.EqSym().EqMP(mapped.PromoteHyp(inUniverse).ConclForAll(v))
}

func envArg(env core.Term) core.Term {
	_, args := ext.MatchesApply(env)
	return args[2]
}

// imageRepresentation derives a parameter's image represented in
// λv. i(ρ(v)) from the parameter represented in ρ: decoding commutes
// with i (DecodeImage, DecodeTupleImage), and a scalar's value is
// i(ρ(s)).
func (x *_Executor) imageRepresentation(bF, bG *_Builder, e *_Embedding, block *reify.Block, rep *prop.PropWrapper, image, target core.Term) *prop.PropWrapper {
	rho := e.rho
	var derived *prop.PropWrapper
	switch block.Kind {
	case reify.ScalarBlock:
		at, _, _ := core.MatchesEQ(target)
		derived = prop.BetaRewrite(at).EqTrans(unary(core.Apply(e.i, core.Apply(rho, block.Start)), rep))
	case reify.TupleBlock:
		commute := modusPonens(bF.instance(lemmaDecodeTupleImage, bF.ring, bG.ring, e.i, block.Dimension, block.Start, rho), e.hom)
		derived = commute.EqTrans(replace(rightOf(commute), rep))
	case reify.PolynomialBlock:
		commute := modusPonens(bF.instance(lemmaDecodeImage, bF.ring, bG.ring, e.i, block.Dimension, block.Degree, block.Start, rho), e.hom)
		derived = commute.EqTrans(replace(rightOf(commute), rep))
	case reify.FamilyBlock:
		all := ext.MatchesFORALL(target)
		j := all.Var()
		below, member, _ := ext.MatchesIMPLY(all.Body())
		repAt := modusPonens(rep.ConclForAllInst(j), assume(below))
		openG := bG.instance(lemmaDecodeFamilyDef, bG.ring, block.Dimension, block.Degree, block.Start, image, j)
		_, decodeArgs := ext.MatchesApply(rightOf(openG))
		start := decodeArgs[3]
		openF := bF.instance(lemmaDecodeFamilyDef, bF.ring, block.Dimension, block.Degree, block.Start, rho, j)
		commute := modusPonens(bF.instance(lemmaDecodeImage, bF.ring, bG.ring, e.i, block.Dimension, block.Degree, start, rho), e.hom)
		decoded := openF.EqSym().EqTrans(repAt)
		_, value, _ := core.MatchesEQ(member)
		derived = openG.EqTrans(commute).EqTrans(replace(rightOf(commute), decoded))
		if redex, isRedex := value.AsAppliedTerm(); isRedex {
			if _, isAbs := redex.Fun().AsAbsTerm(); isAbs {
				derived = derived.EqTrans(prop.BetaRewrite(value).EqSym())
			}
		}
		sameConclusion(derived, member, "a family member's image representation")
		return discharge(derived, below).ConclForAll(j)
	}
	sameConclusion(derived, target, "a parameter's image representation")
	return derived
}

func rightOf(eq *prop.PropWrapper) core.Term {
	_, r, _ := core.MatchesEQ(eq.Conclusion())
	return r
}

// readEmbedding reads an embedding-mode call: the goal is an iff, a
// fact ring_homomorphism(field_ring(F), field_ring(G), i) names the
// embedding, the side where G is not free is F's, and F's side's
// variables other than F and its numeric data are the parameters, each
// with the fact bounding it (a family's and a polynomial's degree
// bound, a tuple's ring_tuple guard), and its image on G's side.
func (x *_Executor) readEmbedding() (*_Embedding, error) {
	l, r, ok := core.MatchesEQ(x.call.Goal)
	if !ok || !l.Type().Equals(core.TypeBool()) {
		return nil, refuse("a call with no source proves an iff along an embedding, Φ(F, params) ⇔ Φ(G, i(params)); the goal is %s", ext.PrintTerm(x.call.Goal))
	}
	var e *_Embedding
	for _, f := range x.facts {
		if !isApplicationOf(f.Conclusion(), "ring_homomorphism") {
			continue
		}
		_, args := ext.MatchesApply(f.Conclusion())
		if len(args) != 3 || !isApplicationOf(args[0], "field_ring") || !isApplicationOf(args[1], "field_ring") {
			continue
		}
		_, fs := ext.MatchesApply(args[0])
		_, gs := ext.MatchesApply(args[1])
		if !freeIn(fs[0], x.call.Goal) || !freeIn(gs[0], x.call.Goal) {
			continue
		}
		if e != nil {
			return nil, refuse("the facts name two embeddings of the goal's fields")
		}
		e = &_Embedding{F: fs[0], G: gs[0], i: args[2], hom: f}
	}
	if e == nil {
		return nil, refuse("the embedding mode reads its embedding off a fact ring_homomorphism(field_ring(F), field_ring(G), i); none is among the facts")
	}
	switch {
	case !freeIn(e.G, l) && freeIn(e.G, r):
		e.sideF, e.sideG, e.fFirst = l, r, true
	case freeIn(e.G, l) && !freeIn(e.G, r):
		e.sideF, e.sideG = r, l
	default:
		return nil, refuse("the iff's sides are not one about %s and one about %s", ext.PrintTerm(e.F), ext.PrintTerm(e.G))
	}
	if err := x.embeddingTheory(e); err != nil {
		return nil, err
	}
	element := constantCall(x.lib, "field_zero", e.F).Type()
	monomial := ext.MakeFun(ext.NumType, ext.NumType)
	ring := constantCall(x.lib, "field_ring", e.F)
	for _, free := range e.sideF.Frees(nil) {
		v, ok := free.AsVar()
		if !ok || v.Equals(e.F) || (e.ltF != nil && v.Equals(e.ltF)) || v.Type().Equals(ext.NumType) {
			continue
		}
		p := reify.Parameter{Name: string(v.Name()), Term: v}
		image := reify.Parameter{Name: string(v.Name())}
		j := core.Var("j", ext.NumType).RenameToAvoid(v, e.i)
		m := core.Var("m", monomial).RenameToAvoid(v, e.i)
		switch {
		case v.Type().Equals(element):
			p.Kind = reify.ScalarBlock
			image.Term = core.Apply(e.i, v)
		case v.Type().Equals(ext.MakeFun(ext.NumType, element)):
			p.Kind = reify.TupleBlock
			image.Term = core.Abs(j, core.Apply(e.i, core.Apply(v, j)))
		case v.Type().Equals(ext.MakeFun(monomial, element)):
			p.Kind = reify.PolynomialBlock
			image.Term = core.Abs(m, core.Apply(e.i, core.Apply(v, m)))
		case v.Type().Equals(ext.MakeFun(ext.NumType, monomial, element)):
			p.Kind = reify.FamilyBlock
			image.Term = core.Abs(j, core.Abs(m, core.Apply(e.i, ext.Apply(v, j, m))))
		default:
			return nil, refuse("the free variable %s of type %s is no parameter the formulas speak of", v.Name(), ext.FormatType(v.Type()))
		}
		if err := x.bounds(&p, ring); err != nil {
			if !x.boundFromMembership(&p, ring) {
				return nil, err
			}
		}
		image.Kind, image.Dimension, image.Degree, image.Count = p.Kind, p.Dimension, p.Degree, p.Count
		e.params = append(e.params, p)
		e.images = append(e.images, image)
	}
	return e, nil
}

// bounds reads a parameter's bounds off its fact: ring_tuple(R, n, x)
// for a tuple, polynomial_bound(R, n, d, p) for a polynomial,
// ∀j. j < k ⇒ polynomial_bound(R, n, d, P(j)) for a family.
func (x *_Executor) bounds(p *reify.Parameter, ring core.Term) error {
	v := p.Term
	for _, f := range x.facts {
		t := f.Conclusion()
		switch p.Kind {
		case reify.ScalarBlock:
			return nil
		case reify.TupleBlock:
			if isApplicationOf(t, "ring_tuple") {
				if _, args := ext.MatchesApply(t); len(args) == 3 && args[0].AlphaEquals(ring) && args[2].AlphaEquals(v) {
					p.Dimension = args[1]
					return nil
				}
			}
		case reify.PolynomialBlock:
			if isApplicationOf(t, "polynomial_bound") {
				if _, args := ext.MatchesApply(t); len(args) == 4 && args[0].AlphaEquals(ring) && args[3].AlphaEquals(v) {
					p.Dimension, p.Degree = args[1], args[2]
					return nil
				}
			}
		case reify.FamilyBlock:
			all := ext.MatchesFORALL(t)
			if all.IsZero() {
				continue
			}
			below, bound, ok := ext.MatchesIMPLY(all.Body())
			if !ok || !isApplicationOf(below, "<") || !isApplicationOf(bound, "polynomial_bound") {
				continue
			}
			_, lt := ext.MatchesApply(below)
			_, args := ext.MatchesApply(bound)
			if len(lt) == 2 && len(args) == 4 && lt[0].AlphaEquals(all.Var()) && args[0].AlphaEquals(ring) &&
				args[3].AlphaEquals(core.Apply(v, all.Var())) && !lt[1].HasFree(all.Var()) {
				p.Dimension, p.Degree, p.Count = args[1], args[2], lt[1]
				return nil
			}
		}
	}
	shape := map[reify.BlockKind]string{
		reify.TupleBlock:      "ring_tuple(field_ring(F), n, %s)",
		reify.PolynomialBlock: "polynomial_bound(field_ring(F), n, d, %s)",
		reify.FamilyBlock:     "∀j. j < k ⇒ polynomial_bound(field_ring(F), n, d, %s(j))",
	}[p.Kind]
	return refuse("no fact bounds the parameter %s; the embedding mode reads it off "+shape, p.Name, p.Name)
}

// embed carries out an embedding-mode call, in the theory its
// closed-field facts make.
func (x *_Executor) embed() (*prop.PropWrapper, Theory, error) {
	e, err := x.readEmbedding()
	if err != nil {
		return nil, 0, err
	}
	iff, err := x.embedding(e)
	if err != nil {
		return nil, 0, err
	}
	iff, err = x.environment(e, iff)
	if err != nil {
		return nil, 0, err
	}
	return x.dischargeBounds(iff), e.theory, nil
}

// embeddingTheory reads the theory off the closed-field facts of F and
// G: both algebraically closed, or both real closed, each with its
// order.
func (x *_Executor) embeddingTheory(e *_Embedding) error {
	closed := func(structure core.Term) (Theory, core.Term, bool) {
		if x.fact(constantCall(x.lib, "algebraically_closed_field_on", structure)) != nil {
			return AlgebraicallyClosedTheory, nil, true
		}
		for _, f := range x.facts {
			if _, args := ext.MatchesApply(f.Conclusion()); isApplicationOf(f.Conclusion(), "real_closed_field") && len(args) == 2 && args[0].AlphaEquals(structure) {
				return RealClosedTheory, args[1], true
			}
		}
		return 0, nil, false
	}
	theoryF, ltF, okF := closed(e.F)
	theoryG, ltG, okG := closed(e.G)
	switch {
	case !okF:
		return refuse("no fact names %s an algebraically closed or a real closed field", ext.PrintTerm(e.F))
	case !okG:
		return refuse("no fact names %s an algebraically closed or a real closed field", ext.PrintTerm(e.G))
	case theoryF != theoryG:
		return refuse("the facts name one of %s and %s an algebraically closed field and the other a real closed one; the embedding mode reads both in one theory", ext.PrintTerm(e.F), ext.PrintTerm(e.G))
	}
	e.theory, e.ltF, e.ltG = theoryF, ltF, ltG
	return nil
}

// boundFromMembership reads a polynomial's or a family's degree bound,
// where no fact states one, off its membership in the polynomial
// algebra, as .At does: p ∈ polynomial_algebra(R, {i | i < n}), or a
// family's ∀j. j < k ⇒ P(j) ∈ …, gives CommonDegreeBound's ∃d. B(d);
// the call is proved at a fresh d under B(d) (the bound fact then
// among the call's facts, derived from it) and the ∃ discharges it
// (dischargeBounds). False where no membership fact names the
// parameter.
func (x *_Executor) boundFromMembership(p *reify.Parameter, ring core.Term) bool {
	v := p.Term
	var g _DegreeGuard
	for _, f := range x.facts {
		t := f.Conclusion()
		switch p.Kind {
		case reify.PolynomialBlock:
			if n, ok := algebraMembership(t, ring, v); ok {
				j := core.Var("j", ext.NumType).RenameToAvoid(v)
				g = _DegreeGuard{ring: ring, dimension: n, count: numeral(1), family: core.Abs(j, v), scalar: true}
			}
		case reify.FamilyBlock:
			all := ext.MatchesFORALL(t)
			if all.IsZero() {
				continue
			}
			below, member, ok := ext.MatchesIMPLY(all.Body())
			_, lt := ext.MatchesApply(below)
			if !ok || !isApplicationOf(below, "<") || len(lt) != 2 || !lt[0].AlphaEquals(all.Var()) || lt[1].HasFree(all.Var()) {
				continue
			}
			if n, ok := algebraMembership(member, ring, core.Apply(v, all.Var())); ok && !n.HasFree(all.Var()) {
				g = _DegreeGuard{ring: ring, dimension: n, count: lt[1], family: v}
			}
		}
		if g.ring != nil {
			break
		}
	}
	if g.ring == nil {
		return false
	}
	w, err := x.commonBound(g, x.bounded)
	if err != nil {
		return false
	}
	var bound *prop.PropWrapper
	if g.scalar {
		zero := numeral(0)
		below := derivedArith(x.lib, constantCall(x.lib, "<", zero, numeral(1)), nil)
		bound = modusPonens(assume(w.body).ConclForAllInst(zero), below)
	} else {
		bound = assume(w.body)
	}
	x.bounded = append(x.bounded, w)
	x.facts = append(x.facts, bound)
	return x.bounds(p, ring) == nil
}

// algebraMembership reads t as member ∈ polynomial_algebra(ring, {i |
// i < n}) and returns n.
func algebraMembership(t, ring, member core.Term) (core.Term, bool) {
	if !isApplicationOf(t, "set_member") {
		return nil, false
	}
	_, args := ext.MatchesApply(t)
	if len(args) != 2 || !args[0].AlphaEquals(member) || !isApplicationOf(args[1], "polynomial_algebra") {
		return nil, false
	}
	_, alg := ext.MatchesApply(args[1])
	if len(alg) != 2 || !alg[0].AlphaEquals(ring) {
		return nil, false
	}
	return belowBound(alg[1])
}

// belowBound reads the set-builder {i | i < n} as the text parser lowers
// it, set_comprehension(λv. ∃i. comprehension_spec(v, i < n, i)), and
// returns n.
func belowBound(S core.Term) (core.Term, bool) {
	_, args := ext.MatchesApply(S)
	if !isApplicationOf(S, "set_comprehension") || len(args) != 1 {
		return nil, false
	}
	generator, isAbs := args[0].AsAbsTerm()
	if !isAbs {
		return nil, false
	}
	existential := ext.MatchesEXISTS(generator.Body())
	if existential.IsZero() || !isApplicationOf(existential.Body(), "comprehension_spec") {
		return nil, false
	}
	_, spec := ext.MatchesApply(existential.Body())
	if len(spec) != 3 || !spec[0].Equals(generator.Var()) || !spec[2].Equals(existential.Var()) || !isApplicationOf(spec[1], "<") {
		return nil, false
	}
	_, less := ext.MatchesApply(spec[1])
	if len(less) != 2 || !less[0].Equals(existential.Var()) || less[1].HasFree(existential.Var()) || less[1].HasFree(generator.Var()) {
		return nil, false
	}
	return less[1], true
}

// dischargeBounds discharges each degree bound boundFromMembership took
// by its ∃, the latest first.
func (x *_Executor) dischargeBounds(t *prop.PropWrapper) *prop.PropWrapper {
	for i := len(x.bounded) - 1; i >= 0; i-- {
		w := x.bounded[i]
		if t.HasHyp(w.body) {
			t = w.exists.DeriveTrans(t.HypExists(w.bound, w.body))
		}
	}
	return t
}

// environment instantiates the iff's environment at the parameters'
// encoding and discharges its facts. From the zero environment λv.
// F.zero each parameter's block is written in turn — encode_polynomials
// for a family, encode_polynomial for a polynomial — the values stay in
// the carrier (EncodePolynomialsInCarrier, EncodeInCarrier), the
// parameter is decoded back from its block (DecodeEncodePolynomials,
// DecodeEncode), and the write keeps every name below its block, so an
// earlier parameter is still decoded from its own (EncodePolynomialsOutside
// or the encoding's definition, then the decoding's congruence).
func (x *_Executor) environment(e *_Embedding, iff *prop.PropWrapper) (*prop.PropWrapper, error) {
	b := e.bF
	z := b.fresh("v", ext.NumType)
	var rho core.Term = core.Abs(z, b.call("field_zero", b.F))
	w := b.fresh("w", ext.NumType)
	carrierAt := b.use(lemmaZeroIn, nil, b.ring)
	var done []*_Binder
	for k, block := range parameterBlocks(e.resF) {
		p := e.params[k]
		var next core.Term
		var rep, agree *prop.PropWrapper
		switch block.Kind {
		case reify.FamilyBlock:
			members, support := b.familyHalves(block, p.Term, x.facts)
			next = b.call("encode_polynomials", block.Dimension, block.Degree, block.Start, block.Count, p.Term, rho)
			carrierAt = b.use(lemmaEncodeFamilyCarrier, (&_Context{}).with(members, carrierAt), b.ring, block.Dimension, block.Degree, block.Start, block.Count, p.Term, rho, w)
			rep = b.decodedFamily(block, p.Term, rho, support)
			outside := b.instance(lemmaEncodeFamilyOutside, block.Dimension, block.Degree, block.Start, block.Count, p.Term, rho, w)
			h, _, _ := ext.MatchesIMPLY(outside.Conclusion())
			l, r, _ := ext.MatchesOR(h)
			agree = modusPonens(outside, wrap(prop.ConclOR0(l, r)))
		case reify.PolynomialBlock:
			member, support := b.polynomialHalves(block, p.Term, x.facts)
			next = b.call("encode_polynomial", block.Dimension, block.Degree, block.Start, p.Term, rho)
			carrierAt = b.use(lemmaEncodeCarrier, (&_Context{}).with(member, carrierAt), b.ring, block.Dimension, block.Degree, block.Start, p.Term, rho, w)
			rep = b.use(lemmaDecodeEncode, (&_Context{}).with(support), b.ring, block.Dimension, block.Degree, block.Start, p.Term, rho)
			agree = b.keptBelow(block, p.Term, rho, w)
		default:
			return nil, refuse("the embedding mode encodes families and polynomials; the parameter %s is a %s", p.Name, block.Kind)
		}
		below := b.call("<", w, block.Start)
		agreement := &_Agreement{fact: agree.PromoteHyp(below).ConclForAll(w), tau: next, sig: rho, start: block.Start}
		step := &_Context{agree: []*_Agreement{agreement}}
		for i, bd := range done {
			done[i] = &_Binder{block: bd.block, value: bd.value, rep: b.transport(bd, step)}
		}
		sameConclusion(rep, b.representation(block, p.Term, next), "a parameter's representation in its encoding")
		done = append(done, &_Binder{block: block, value: p.Term, rep: rep})
		rho = next
	}
	iff = iff.TermInst(core.MakeTermSubst(e.rho, rho))
	envDef := b.instance(lemmaEnvOKDef, b.carrier, x.universe(), rho)
	_, every, _ := core.MatchesEQ(envDef.Conclusion())
	all := ext.MatchesFORALL(every)
	inUniverse, _, _ := ext.MatchesIMPLY(all.Body())
	at := carrierAt.TermInst(core.MakeTermSubst(w, all.Var()))
	if len(done) == 0 {
		at = b.use(lemmaZeroIn, nil, b.ring)
	}
	env := envDef.EqSym().EqMP(wrap(at.PromoteHyp(inUniverse).ConclForAll(all.Var())))
	iff = wrap(env.MaybeDeriveTrans(iff))
	for _, bd := range done {
		iff = wrap(bd.rep.MaybeDeriveTrans(iff))
	}
	return wrap(x.structureFrom(b, _Structure{F: e.F, lt: e.ltF}).MaybeDeriveTrans(iff)), nil
}

// familyHalves is a family's bound fact read as its two halves under
// the index: ∀j. j < k ⇒ P(j) ∈ polynomial_algebra(R, {i | i < n}) and
// ∀j. j < k ⇒ fun_support(R.zero, P(j)) ⊆ bounded_monomials(n, d).
func (b *_Builder) familyHalves(block *reify.Block, P core.Term, facts []*prop.PropWrapper) (members, support *prop.PropWrapper) {
	bound := b.guard(&reify.Block{Kind: block.Kind, Dimension: block.Dimension, Degree: block.Degree, Count: block.Count, Owner: block.Owner, Variable: varOf(P)})
	var fact *prop.PropWrapper
	for _, f := range facts {
		if f.Conclusion().AlphaEquals(bound) {
			fact = f
		}
	}
	utils.Assert(fact != nil)
	all := ext.MatchesFORALL(fact.Conclusion())
	j := all.Var()
	below, _, _ := ext.MatchesIMPLY(all.Body())
	at := modusPonens(fact.ConclForAllInst(j), assume(below))
	def := b.instance(lemmaBoundDef, b.ring, block.Dimension, block.Degree, core.Apply(P, j))
	opened := def.EqMP(at)
	l, r := conjuncts(def)
	members = discharge(opened.DeriveTrans(prop.HypAND0(l, r)), below).ConclForAll(j)
	support = discharge(opened.DeriveTrans(prop.HypAND1(l, r)), below).ConclForAll(j)
	return members, support
}

// decodedFamily is ⊢ ∀j. j < k ⇒ decode_polynomials(R, n, d, s,
// encode_polynomials(n, d, s, k, P, ρ), j) = P(j): DecodeEncodePolynomials
// at each index below the count, from the family's support half.
func (b *_Builder) decodedFamily(block *reify.Block, P, rho core.Term, support *prop.PropWrapper) *prop.PropWrapper {
	j := b.fresh("j", ext.NumType)
	below := assume(b.call("<", j, block.Count))
	at := b.use(lemmaDecodeEncodeFamily, (&_Context{}).with(support, below), b.ring, block.Dimension, block.Degree, block.Start, block.Count, P, rho, j)
	return discharge(at, below.Conclusion()).ConclForAll(j)
}

// polynomialHalves is a polynomial's bound fact read as its two halves:
// p ∈ polynomial_algebra(R, {i | i < n}) and fun_support(R.zero, p) ⊆
// bounded_monomials(n, d).
func (b *_Builder) polynomialHalves(block *reify.Block, p core.Term, facts []*prop.PropWrapper) (member, support *prop.PropWrapper) {
	bound := b.call("polynomial_bound", b.ring, block.Dimension, block.Degree, p)
	var fact *prop.PropWrapper
	for _, f := range facts {
		if f.Conclusion().AlphaEquals(bound) {
			fact = f
		}
	}
	utils.Assert(fact != nil)
	def := b.instance(lemmaBoundDef, b.ring, block.Dimension, block.Degree, p)
	opened := def.EqMP(fact)
	l, r := conjuncts(def)
	return opened.DeriveTrans(prop.HypAND0(l, r)), opened.DeriveTrans(prop.HypAND1(l, r))
}

// keptBelow is w < s ⊢ encode_polynomial(n, d, s, p, ρ, w) = ρ(w): below
// the block the encoding's definition keeps the value.
func (b *_Builder) keptBelow(block *reify.Block, p, rho core.Term, w core.VarTerm) *prop.PropWrapper {
	def := wrap(instantiate(wrap(b.lib.Theorem(lemmaEncodeDef)), block.Dimension, block.Degree, block.Start, p, rho, w))
	_, rhs, _ := core.MatchesEQ(def.Conclusion())
	guard, _, _, _ := ext.MatchesCond(rhs)
	off := ext.Not(guard).Core()
	below := b.call("<", w, block.Start)
	offBlock := modusPonens(b.arith(ext.WrapTerm(below).Imply(off).Core(), nil), assume(below))
	kept := prop.CondDecideByHyps(func(match func(core.Term) bool) bool { return match(off) })(rhs)
	return offBlock.DeriveTrans(def.EqTrans(kept))
}

func varOf(t core.Term) core.VarTerm {
	v, _ := t.AsVar()
	return v
}

// EmbeddingBridge is an embedding-mode call's iff at an environment ρ,
// returned beside it: Φ(F, params) ⇔ Φ(G, i(params)) under
// fo_env_ok(F.carrier, 𝕌, ρ), each parameter represented in ρ, and the
// call's facts.
func EmbeddingBridge(call Call, vocabulary *reify.Vocabulary, lib Library) (core.Prop, core.VarTerm, error) {
	x := &_Executor{call: call, vocabulary: vocabulary, lib: lib}
	x.readFacts()
	e, err := x.readEmbedding()
	if err != nil {
		return nil, core.VarTerm{}, err
	}
	iff, err := x.embedding(e)
	if err != nil {
		return nil, core.VarTerm{}, err
	}
	return iff.Core(), e.rho, nil
}
