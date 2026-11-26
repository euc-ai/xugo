# ideal_colength — quotients of ideals multiplied by an invertible fractional ideal: simple layers, finite quotients and colengths

Multiplying a nonzero simple ideal quotient I/J by an invertible
fractional ideal M of a subring S of a field L gives an S-linear
isomorphism I/J ≅ IM/JM. A single product x · f, with x ∈ M and
f ∈ (S : M), outside the annihilator of the layer, inverted modulo it,
selects mutually inverse multiplication maps on that layer. In
particular, M/mM is a line over the actual residue field S/m at every
maximal ideal m, with no embedding of S/m into S required.

Peeling one simple layer at a time then gives two outputs from one
argument: finite quotients retain their cardinality, and
finite-dimensional quotients over a subfield k of S retain their
dimension. Dividing an invertible N by an invertible ideal I therefore
enlarges it by the colength of I, dim((S : I) · N / N) = dim(S/I), and
the n-th power of the ideal of a k-rational point has colength n. This
is the arithmetic a curve's line bundles are made of when the curve is
held by the coordinate rings of its charts inside its function field:
twisting at a point changes each chart's colength by the point's.
Finiteness of colength passes from principal ideals to every nonzero
ideal: a nonzero ideal I holds a nonzero f, and f · S ⊆ I ⊆ S makes S/I
a quotient of S/f · S.

Every statement is read under the bundle `∀L:field_on(A)`, with S a
subring of L, `subring(field_ring(L), S)`. Dimensions use either a
subfield k of S or the residue field S/m, as stated.

## Members

### Simple layers and finite quotients

| Member | Statement |
|---|---|
| `ScaleQuotientHom` | multiplication by a field element descends between quotient modules when it carries numerator into numerator and denominator into denominator |
| `InvertibleSimpleLayer` | I/J ≅ IM/JM as S-modules when I covers J (`ideal_cover`) and M is invertible |
| `InvertibleIdealResidueLine` | M/mM (`ideal_quotient_module`) is one-dimensional over S/m for M invertible and every maximal ideal m |
| `InvertibleQuotientCardinality` | multiplication by an invertible fractional ideal preserves finite ideal quotient cardinality |
| `IdealIndexMultiplicative` | [S : IJ] = [S : I]·[S : J] for ideals I, J of finite index with J invertible |

### Colengths over a subfield k

| Member | Statement |
|---|---|
| `ScaleQuotientDim` | dim(aM/aN) = dim(M/N) for fractional ideals N ⊆ M and a ≠ zero |
| `InvertibleQuotientDim` | dim(IM/JM) = dim(I/J) for M invertible and ideals J ⊆ I with I/J finite-dimensional |
| `InvertibleResidueLineOverSubfield` | dim(M/mM) = 1 over k for M invertible at the ideal m of a k-rational point of S |
| `RationalPowerColength` | dim(S/pⁿ) = n for the invertible ideal p of a k-rational point of S, so a member of pⁿ has dim(S/aS) ≥ n |
| `InvertibleFractionalQuotientDim` | dim(IM/JM) = dim(I/J) for fractional ideals J ⊆ I with I and M invertible, L the fraction field of S and I/J finite-dimensional |
| `NonzeroIdealQuotientFinite` | S/I is finite-dimensional over k for every nonzero ideal I of S, when k ⊆ S is a subfield and S/a · S is finite-dimensional for every nonzero a ∈ S |
| `InvertibleMeetQuotientsFinite` | when L is the field of fractions of S, k ⊆ S a subfield and S/a · S finite-dimensional for every nonzero a ∈ S, an invertible J has S/(J ∩ S) and J/(J ∩ S) finite-dimensional |
| `InvertibleColengthQuotient` | dim((S : I) · N / N) = dim(S/I) for invertible N and an invertible ideal I |
