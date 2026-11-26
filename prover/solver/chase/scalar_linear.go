package chase

// scalar_linear.go — the polynomial linear algebra at a scalar node: a
// vector over the node's atoms read as a polynomial vector over its
// base atoms, the relations as polynomial rows, and the decisions on
// them — a combination of the relations, a homomorphism's image and its
// kernel modulo the target's relations — each returned over the node's
// atoms, so the integer certificate path spells it. Where neither the
// vectors nor the rows carry a monomial, the integer Hermite-form
// decision stands.

import (
	"math/big"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// polynomial reads v over the node's atoms as a vector over its base
// atoms: a scaled atom's coefficient goes to its base at its monomial.
func (n *_Node) polynomial(v _Vector) _PolynomialVector {
	out := _PolynomialVector{}
	for i, c := range v {
		a := n.atoms[i]
		t := _PolynomialTerm{pos: i}
		if a.scalarBase != nil {
			t.pos = a.scalarBase.index
			t.mono = a.scalarMono
		}
		if old := out[t]; old != nil {
			c = new(big.Int).Add(old, c)
		}
		if c.Sign() == 0 {
			delete(out, t)
		} else {
			out[t] = new(big.Int).Set(c)
		}
	}
	return out
}

// vector reads p back over the node's atoms, introducing the scaled
// atoms it names in decreasing term order.
func (n *_Node) vector(p _PolynomialVector) _Vector {
	out := _Vector{}
	for _, t := range p.terms() {
		a := n.scaledAtom(n.atoms[t.pos], t.mono)
		if old := out[a.index]; old != nil {
			out[a.index] = new(big.Int).Add(old, p[t])
		} else {
			out[a.index] = new(big.Int).Set(p[t])
		}
		if out[a.index].Sign() == 0 {
			delete(out, a.index)
		}
	}
	return out
}

// baseAtoms are the node's unscaled atoms.
func (n *_Node) baseAtoms() []*_Atom {
	var out []*_Atom
	for _, a := range n.atoms {
		if a.scalarBase == nil {
			out = append(out, a)
		}
	}
	return out
}

// polynomialRelations are the node's supplied relations as polynomial
// rows, the relations beside them; the derived multiples scalarExpress
// records are left out, being consequences.
func (n *_Node) polynomialRelations() ([]_PolynomialVector, []*_Relation) {
	var rows []_PolynomialVector
	var rels []*_Relation
	for _, rel := range n.relations {
		if !rel.derived {
			rows = append(rows, n.polynomial(rel.v))
			rels = append(rels, rel)
		}
	}
	return rows, rels
}

// scalarExpress is inLattice at a scalar node: v as a combination of
// the relations, the coefficients over n.relations. A polynomial
// coefficient q·m on a supplied relation l = r is realized by the
// derived relation m • l = m • r, recorded at the node once and counted
// q times, so the certificate's integer combination spells it. The
// basis is cached until a relation or an atom arrives.
func (d *_Diagram) scalarExpress(n *_Node, v _Vector) ([]*big.Int, bool) {
	if v.isZero() {
		return zeroRow(len(n.relations)), true
	}
	rows, rels := n.polynomialRelations()
	integer := n.polynomial(v).constants()
	for _, r := range rows {
		integer = integer && r.constants()
	}
	if integer {
		e := buildEchelon(n.relationRows(), len(n.atoms))
		c, _, ok := e.express(v.dense(len(n.atoms)))
		return c, ok
	}
	if n.scalarBasis == nil || n.scalarBasisVersion != len(rels) || n.scalarBasisAtoms != len(n.atoms) {
		n.scalarBasis = buildPolynomialBasis(rows)
		n.scalarBasisVersion = len(rels)
		n.scalarBasisAtoms = len(n.atoms)
	}
	coefficients, ok := n.scalarBasis.express(n.polynomial(v))
	if !ok {
		return nil, false
	}
	counts := map[int]*big.Int{}
	for _, t := range coefficients.terms() {
		rel := rels[t.pos]
		l, r, proof := rel.l, rel.r, rel.proof
		if t.mono != "" {
			c := n.scalar.monoTerm(t.mono)
			l, r = ext.Apply(n.smul, c, l), ext.Apply(n.smul, c, r)
			proof = proof.LeftApply(ext.Apply(n.smul, c))
		}
		before := len(n.relations)
		if err := d.addRelation(l, r, proof); err != nil {
			panic("chase: a polynomial relation multiplier lost its membership: " + err.Error())
		}
		if len(n.relations) > before {
			n.relations[len(n.relations)-1].derived = true
		}
		for i, known := range n.relations {
			if known.l.AlphaEquals(l) && known.r.AlphaEquals(r) {
				if counts[i] == nil {
					counts[i] = new(big.Int)
				}
				counts[i].Add(counts[i], coefficients[t])
				break
			}
		}
	}
	out := zeroRow(len(n.relations))
	for i, c := range counts {
		out[i] = c
	}
	return out, true
}

// scalarHomVector is the image of the atom a under h over the target's
// atoms; the atoms its normalization introduces inherit a's schema
// provenance.
func (d *_Diagram) scalarHomVector(h *_Hom, a *_Atom) _Vector {
	first := len(h.dst.atoms)
	d.rememberBetaImage(h, a.term)
	v, _, err := d.vecOf(d.apply(h, a.term), h.dst)
	if err != nil {
		panic(err)
	}
	if a.schemaGenerated {
		for _, image := range h.dst.atoms[first:] {
			image.schemaGenerated = true
		}
	}
	return v
}

// scalarHomRows are h's base atoms and their images as polynomial rows
// over the target's base atoms.
func (d *_Diagram) scalarHomRows(h *_Hom) ([]*_Atom, []_PolynomialVector) {
	bases := h.src.baseAtoms()
	rows := make([]_PolynomialVector, len(bases))
	for i, a := range bases {
		rows[i] = h.dst.polynomial(d.scalarHomVector(h, a))
	}
	return bases, rows
}

// scalarImage is imageCoefficients at a scalar source: u over the
// source's atoms with h(u) − v in the target's relations, the
// combination over the image rows and the relations by the integer
// echelon when every row is constant and by the polynomial basis
// otherwise; only the image rows' coefficients are read back.
func (d *_Diagram) scalarImage(h *_Hom, v _Vector) (_Vector, bool) {
	bases, rows := d.scalarHomRows(h)
	relations, _ := h.dst.polynomialRelations()
	input := append(rows, relations...)
	target := h.dst.polynomial(v)
	integer := target.constants()
	for _, row := range input {
		integer = integer && row.constants()
	}
	var coeffs _PolynomialVector
	var ok bool
	if integer {
		matrix := make([][]*big.Int, len(input))
		for i, row := range input {
			matrix[i] = zeroRow(len(h.dst.atoms))
			for t, c := range row {
				matrix[i][t.pos].Set(c)
			}
		}
		wanted := zeroRow(len(h.dst.atoms))
		for t, c := range target {
			wanted[t.pos].Set(c)
		}
		combination, _, found := buildEchelon(matrix, len(h.dst.atoms)).express(wanted)
		ok = found
		coeffs = _PolynomialVector{}
		if found {
			for i, c := range combination {
				if c.Sign() != 0 {
					coeffs[_PolynomialTerm{pos: i}] = c
				}
			}
		}
	} else {
		coeffs, ok = buildPolynomialBasis(input).express(target)
	}
	if !ok {
		return nil, false
	}
	out := _PolynomialVector{}
	for t, c := range coeffs {
		if t.pos < len(bases) {
			t.pos = bases[t.pos].index
			out[t] = new(big.Int).Set(c)
		}
	}
	return h.src.vector(out), true
}

// scalarKernel is kernelVectors at a scalar source: a generating set of
// the elements h provably sends to zero, the preimage of the target's
// relations, by the integer lattice when every row is constant and by
// elimination from the graph of h otherwise.
func (d *_Diagram) scalarKernel(h *_Hom) []_Vector {
	bases, rows := d.scalarHomRows(h)
	relations, _ := h.dst.polynomialRelations()
	integer := true
	for _, r := range rows {
		integer = integer && r.constants()
	}
	for _, r := range relations {
		integer = integer && r.constants()
	}
	var kernel []_PolynomialVector
	if integer {
		f := make([][]*big.Int, len(rows))
		rs := make([][]*big.Int, len(relations))
		dense := func(p _PolynomialVector) []*big.Int {
			r := zeroRow(len(h.dst.atoms))
			for t, c := range p {
				r[t.pos].Set(c)
			}
			return r
		}
		for i, r := range rows {
			f[i] = dense(r)
		}
		for i, r := range relations {
			rs[i] = dense(r)
		}
		for _, row := range preimageLattice(f, len(bases), len(h.dst.atoms), rs) {
			p := _PolynomialVector{}
			for i, c := range row {
				if c.Sign() != 0 {
					p[_PolynomialTerm{pos: i}] = c
				}
			}
			kernel = append(kernel, p)
		}
	} else {
		kernel = polynomialPreimage(rows, relations, len(bases))
	}
	var out []_Vector
	for _, p := range kernel {
		shifted := _PolynomialVector{}
		for t, c := range p {
			t.pos = bases[t.pos].index
			shifted[t] = c
		}
		v := h.src.vector(shifted)
		if !v.isZero() {
			out = append(out, v)
		}
	}
	return out
}

// readScalarEquation records l = r as a scalar equation of every ring
// both sides are members of, once each; false when they are members of
// no ring.
func (d *_Diagram) readScalarEquation(l, r core.Term, proof *prop.PropWrapper) bool {
	read := false
	for _, s := range d.scalarRings {
		if _, ok := s.member(l); !ok {
			continue
		}
		if _, ok := s.member(r); !ok {
			continue
		}
		seen := false
		for _, old := range s.equations {
			if old.Conclusion().AlphaEquals(proof.Conclusion()) {
				seen = true
				break
			}
		}
		if !seen {
			s.equations = append(s.equations, proof)
		}
		read = true
	}
	return read
}

// installScalarRelations records, at every base atom a of a scalar
// node, the relation l • a = r • a for every scalar equation l = r of
// its ring, once each; true when a relation was added.
func (d *_Diagram) installScalarRelations() bool {
	if d.scalarRelationSeen == nil {
		d.scalarRelationSeen = map[string]bool{}
	}
	grew := false
	for _, n := range d.nodes {
		if n.scalar != nil {
			for _, a := range n.baseAtoms() {
				for _, eq := range n.scalar.equations {
					key := scalarKey(a.term, eq.Conclusion()) + "|" + string(n.set.AlphaKey())
					if d.scalarRelationSeen[key] {
						continue
					}
					d.scalarRelationSeen[key] = true
					l, r, _ := core.MatchesEQ(eq.Conclusion())
					proof := eq.LeftApply(n.smul).RightApply(a.term)
					before := len(n.relations)
					if err := d.addRelation(ext.Apply(n.smul, l, a.term), ext.Apply(n.smul, r, a.term), proof); err != nil {
						panic(err)
					}
					grew = grew || len(n.relations) > before
				}
			}
		}
	}
	return grew
}
