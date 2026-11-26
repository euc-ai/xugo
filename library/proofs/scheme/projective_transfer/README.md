# projective_transfer — projective equation curves carried along an embedding of algebraically closed fields

A projective equation curve is given by finitely many forms E over a subfield k of a field M; its geometric conditions — a prime ideal, a point, the Jacobian rank — are read over M. A ring homomorphism ι of M into a second field N carries k onto the subfield ι(k) and each form P onto «carried»(P), the form whose coefficients are the images of P's. What reads only k survives any such ι: the Hilbert function, and so the genus, are computed over the isomorphic fields k and ι(k); the curve's points over a set of values l go one to one onto the carried curve's over ι(l), and with M closed and k finite the points over the field of q^m elements onto those over N's field of q^m elements, so every count is kept. What reads M needs both fields algebraically closed, and is carried by elementarity (`ByElementarity`, through algebraically_closed_field_transfer.EmbeddingElementary): each condition is first restated, at one field, as a first-order statement about the listed equations — normalized zeros for a point (projective_curve.PointsAsNormalizedZeros), a kernel of dimension two at every normalized zero for the Jacobian rank (JacobianKernelCriterion), and degree-bounded pointwise ideal membership for primality (homogeneous_polynomial.FormIdealPrimeCriterion, carried by polynomial_system_descent.FormIdealPrimeDescent). CarriedSmoothCurve assembles the nine conditions: E cuts out a smooth projective equation curve over M exactly when the carried forms cut one out over N.

## The Hilbert function and the genus

| Member | Statement |
|---|---|
| `CarriedPolynomials` | ι is an isomorphism of k onto ι(k), and «carried» one of the polynomials over k onto those over ι(k), keeping the forms of each degree |
| `CarriedIdealFormsDimension` | the ideal's forms of degree d over k and the carried ideal's over ι(k) have one dimension |
| `CarriedHilbertFunction` | carried along ι, a set of equations over k keeps its Hilbert function at every degree, and so its genus |

## Points

| Member | Statement |
|---|---|
| `CarriedEvaluation` | a polynomial over k carried along ι takes at the carried point the image under ι of its value at the point |
| `CarriedPoints` | ι carries the points of the curve over l one to one onto the points of the carried curve over ι(l) |
| `CarriedPointCount` | carried along ι, the curve keeps the size of its field of constants and its number of points over the field of q^m elements for every m > 0 |
| `CarriedPointExists` | along ι between algebraically closed fields, a curve given by finitely many polynomials over M has a point over M exactly when the carried curve has one over N |

## The Jacobian condition

| Member | Statement |
|---|---|
| `JacobianKernelCriterion` | the gradients of a listed family P(0), …, P(r − 1) span n − 1 dimensions at every point of its curve exactly when, at every normalized zero x, the tuples the partials Q(j·(n+1)+c) = ∂_c P(j) kill at x form a plane: two with only the trivial relation, and any three with a nontrivial one |
| `CarriedSmoothness` | along ι between algebraically closed fields, a curve given by finitely many equations over k meets the Jacobian condition (the gradients span n − 1 dimensions at every point) over M exactly when the carried curve meets it over N |

## The smooth curve

| Member | Statement |
|---|---|
| `CarriedSmoothCurve` | along ι between algebraically closed fields, a set of forms over k cuts out a smooth projective equation curve over M exactly when the carried forms cut one out over N |
