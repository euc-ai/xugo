# curve_valuation — pole order at the origin

The pole space L(nO) is the module of sections of O(nO). Pole order is
minimal n for a nonzero member of the affine structure ring; its value at
zero is fixed to zero. All cards assume a finite smooth Weierstrass datum.
The pole spaces are the one-point pole spaces of scheme/regular_point at
the origin, and the pole order of a nonzero affine function is minus its
order there (`OriginPoleData`); the order law, the filtration increment
and the extreme-term argument the cards below use are that chapter's and
algebra/field/valuation_order's, read at the origin.

## Definitions

| Member | Meaning |
|---|---|
| `poleSpaceDef` | `elliptic_pole_space` |
| `poleOrderDef` | `elliptic_pole_order` |
| `poleOrderBasisDef` | `elliptic_pole_basis` |

## Theorems

| Member | Statement |
|---|---|
| `StructureRingHasPoleAtOrigin` | Every affine regular function belongs to some L(nO). — card |
| `OriginPoleData` | L(nO) is the one-point pole space of the origin, and pole_O(g) = −ord_O(g) for nonzero affine g. — card |
| `PoleSpaceMembership` | For nonzero affine g, g∈L(nO) exactly when pole_O(g)≤n. — card |
| `PoleOrderAdditive` | The pole order of a nonzero affine product is the sum of pole orders. — card |
| `PoleOrderFiltrationStep` | The finite pole-space dimension rises by zero or one at each step. — card |
| `PoleOrderBasisExists` | L(nO) has a finite basis with pairwise distinct pole orders. — card |
| `PoleSpacePolynomialForm` | L(nO) consists of p(x)+q(x)y with respective nonzero weights 2 deg p and 2 deg q+3 at most n. — card |
| `PoleSpaceDimension` | For n≥1, L(nO) is finite-dimensional of dimension n. — card |
