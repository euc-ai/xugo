# polynomial_sign_table — ordered sign tables of polynomial lists and the cells of increasing cuts

The input is a finite list of integer polynomials in parameter names U and one eliminated name v. Ordered tables retain the order of roots and intervening cells; the realizable sign vectors are their projection. Zero polynomials, specialized degree drops, multiple roots and empty input lists are included. The cuts of a table, r(0) < r(1) < … < r(k − 1), lie in the carrier in increasing order: ordered_field's predicate increasing_cuts. Their cells are read at an index: an even cell is an open interval and an odd one a cut, every cell holds a point, and an open cell is infinite and convex, so a polynomial over a real closed field without a root in one keeps one sign on it. A table of a family of polynomials over the field gives each cell the sign of each member; parametric_sign_table builds such tables uniformly in the parameters, and uniform_sign_table proves that every family has one.

| Member | Statement |
|---|---|
| `SignsDef` | Evaluate the polynomials and retain their signs in list order. |
| `RealizableSignsDef` | All sign vectors obtained by varying the eliminated variable over the carrier. |
| `SignCellDef` | Odd cells are the successive cuts and even cells the open intervals between them, including the two rays. |
| `SignTableDef` | A finite ordered partition into nonempty cells on each of which the entire sign vector is constant. |
| `SignTableExists` | Every specialized polynomial list has a finite ordered sign table. |
| `SignCellsCover` | The cells of increasing cuts in an ordered field cover its carrier. |
| `SignCellInCarrier` | Every point of a cell of cuts lies in the carrier. |
| `OpenCellMember` | An even cell is the open interval between its two cuts. |
| `CutCellMember` | An odd cell is its single cut. |
| `SignCellsNonempty` | Every cell of increasing cuts holds a point. |
| `OpenCellConvex` | An open cell holds every point between two of its points. |
| `OpenCellInfinite` | An open cell of increasing cuts is infinite. |
| `PolynomialFamilySignTableDef` | A sign table of m polynomials: increasing cuts in the carrier, nonempty cells, and the sign t(j, i) of the i-th polynomial throughout cell j. |
| `VanishingOnOpenCell` | A polynomial member of a sign table with sign zero on an open cell is the zero polynomial. |
| `RootFreeCellSign` | A polynomial with no root in an open cell has one sign on it. |
