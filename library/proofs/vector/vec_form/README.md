# vec_form — smooth differential forms on Euclidean open sets

A form reads a point x and a matrix P whose columns are its vector
arguments. All dimensions and degrees share the host type
`(num → real) → (num → num → real) → real`. The predicate
`vec_form_on⟨n⟩(U, k, ω)` fixes the ambient dimension n, open domain U
and degree k. It requires zero values off U, ignores matrix entries
outside the n×k block, and gives literal function equality for form laws.
Normalization does not assert smoothness across the boundary of U.

`FormLocal` tests this predicate on open neighbourhoods of each point.
Each local test normalizes to that neighbourhood, and its conclusion
normalizes to U. The original function may have arbitrary values off U;
local smoothness imposes no condition there. This criterion lets
compatible chart data construct forms on whole coordinate images.

The definition uses the increasing-coordinate expansion

$$
\omega(x, P) = \sum_a \omega(x, E_a) \det(P[a, :]) \quad (x \in U).
$$

Here a lists k distinct increasing indices below n and has zero tail,
so the indexing set is finite. E_a has coordinate vector $e_{a(j)}$ in
column j, and P[a, :] is the k×k minor with those rows. The coefficient
functions x ↦ ω(x, E_a) are smooth on U. The determinant expansion
encodes alternation and multilinearity while retaining an evaluation
on arbitrary, possibly unpadded, matrix arguments. In degree zero
there is one empty frame and its minor determinant is one: forms are
smooth functions on U, normalized to zero outside it. For k > n the
indexing set is empty, so the only form is zero. In top degree the
coefficient at the identity matrix multiplies det(P).

`vec_form_module⟨n⟩(U, k)` restricts an iterated real function module
to this carrier. Addition and scalar multiplication are pointwise and
are the same operations in every degree. The wedge product is the
signed shuffle sum, counting each split into two ordered blocks once.
Its unit is one on U and zero outside U; associativity and the sign
$(-1)^{pq}$ give the graded algebra laws.

`vec_exterior_derivative⟨n⟩(U, k, ω)` has degree k+1. Its formula
differentiates the coefficient obtained by fixing all input columns
except one, takes the directional derivative along that column, and
sums with the sign of the omitted position. Mixed partial symmetry
gives d² = 0 and the product rule gives the graded Leibniz law. The
input degree is explicit, with no subtraction at degree zero.

`vec_form_pullback⟨n, m⟩(U, k, f, ω)` evaluates ω at f(x) on the
columns obtained by applying the m×n Jacobian of f. Its laws require
f smooth on the open source and mapping it into the target form's
open domain. Pullback is linear and contravariant, and commutes with
wedge and exterior derivative. These conditions also justify the
local differentiation of the normalized expressions.

Matrices of forms carry connection and curvature identities. The ring of even
forms connects the algebraic Pfaffian to smooth two-form matrices, with
pullback, frame-change and closedness laws for curvature Pfaffians.

## Members

| Member | Statement |
|---|---|
| `FormIndicesDef` | `vec_form_indices(n, k)`: increasing coordinate lists with zero tail |
| `formBasisDef` | `vec_form_basis⟨n, k⟩(a)`: the coordinate frame indexed by a |
| `FormOnDef` | `vec_form_on⟨n⟩(U, k, ω)`: a normalized smooth k-form on U |
| `FormModuleDef` | `vec_form_module⟨n⟩(U, k)`: the form carrier with pointwise real module operations |
| `WedgeDef` | `vec_form_wedge⟨n⟩(U, p, q, α, β)`: the signed shuffle product |
| `ExteriorDerivativeDef` | `vec_exterior_derivative⟨n⟩(U, k, ω)`: the degree-raising alternating derivative |
| `PullbackDef` | `vec_form_pullback⟨n, m⟩(U, k, f, ω)`: Jacobian pullback, normalized on U |
| `FormLocal` | Locally normalized forms give a form after normalization to the open domain — card |
| `FormModule` | Forms of each degree on an open set form a real module — card |
| `FormZeroDegree` | Zero-forms are matrix-independent smooth scalar coefficients, normalized off U |
| `FormAboveDimension` | A form of degree greater than the ambient dimension is zero — card |
| `TopDegreeDeterminant` | A top-degree form is its identity-frame coefficient times the determinant — card |
| `FormRestrict` | Normalized restriction to an open subset preserves forms — card |
| `WedgeForm` | Wedge takes degrees p and q to degree p+q — card |
| `WedgeBilinear` | Wedge is a bilinear map of the degree modules — card |
| `WedgeAssociative` | Wedge is associative — card |
| `WedgeGradedCommutative` | Interchanging degrees p and q contributes $(-1)^{pq}$ — card |
| `WedgeUnit` | The normalized constant one is a zero-form and a two-sided wedge unit — card |
| `ExteriorDerivativeForm` | Exterior derivative raises the degree by one — card |
| `ExteriorDerivativeLinear` | Exterior derivative is a homomorphism of the degree modules — card |
| `ExteriorDerivativeSquareZero` | d² = 0 as equality of normalized forms — card |
| `ExteriorDerivativeLeibniz` | d(α∧β) = dα∧β + (-1)^p α∧dβ — card |
| `PullbackForm` | Smooth pullback preserves the degree carrier — card |
| `PullbackLinear` | Pullback is a homomorphism between the degree modules — card |
| `PullbackIdentity` | Identity pullback fixes each form — card |
| `PullbackCompose` | f* g* = (g ∘ f)* — card |
| `PullbackWedge` | Pullback preserves wedge — card |
| `PullbackExteriorDerivative` | Pullback commutes with exterior derivative — card |

## Integration of the time component (homotopy.go)

The point `(x, t)` is encoded by appending t at coordinate n of an
n-vector. The homotopy operator inserts that time vector in the first
column, then the k input vectors with zero time component, and integrates
from 0 to 1. Thus `vec_form_homotopy⟨n⟩(U, k, ω)` has output degree k
and takes an input of degree k+1 in dimension n+1. This convention gives

$$
dK\omega + Kd\omega = j_1^{\ast} \omega - j_0^{\ast} \omega.
$$

The input form is defined on an open neighbourhood W of U×[0,1].
Openness gives a tube about each compact parameter segment, so smooth
parameter integration is local in x and needs no compact-support
assumption or uniform global tube. In input degree zero the formula is
`Kdω = j₁*ω − j₀*ω`; there is no negative-degree form or dK term.

| Member | Statement |
|---|---|
| `HomotopyDef` | `vec_form_homotopy⟨n⟩(U, k, ω)`: integral of the first-slot time contraction |
| `HomotopyForm` | K takes smooth (k+1)-forms near U×[0,1] to smooth k-forms on U — card |
| `HomotopyLinear` | K is a homomorphism between the corresponding real form modules — card |
| `HomotopyOperator` | dK + Kd = j₁* − j₀* in positive input degrees — card |
| `HomotopyOperatorZeroDegree` | Kd = j₁* − j₀* in input degree zero — card |

## Matrices of forms (matrix_definitions.go, matrix.go, curvature.go)

A matrix entry is a scalar form on the same open set. Ambient dimension,
form degree, row count and column count are separate parameters.
`vec_form_matrix_on⟨n⟩(U, k, r, s, A)` requires openness even for an empty
matrix shape, and requires every inactive entry to be the whole zero form.
The product contracts matrix indices and wedges entries; it is generally
not commutative. Exterior derivative and pullback act entrywise.

Transposition and cyclic exchange under the trace both contribute the
degree sign $(-1)^{pq}$. For a skew matrix A of one-forms, this makes A∧A
skew as well. Curvature is F = dA+A∧A, a matrix of two-forms. It is skew
when A is skew, while the Bianchi identity

$$
dF + A \wedge F - F \wedge A = 0
$$

holds without the skew assumption. Its proof keeps the matrix factors in
order and cancels by the graded Leibniz rule and associativity.

| Member | Statement |
|---|---|
| `FormMatrixOnDef` | `vec_form_matrix_on⟨n⟩(U, k, r, s, A)`: a rectangular matrix of homogeneous forms |
| `FormMatrixProductDef` | `vec_form_matrix_product⟨n⟩(U, p, q, r, s, t, A, B)`: matrix contraction using wedge |
| `FormMatrixDerivativeDef` | `vec_form_matrix_derivative⟨n⟩(U, k, r, s, A)`: entrywise exterior derivative |
| `FormMatrixPullbackDef` | `vec_form_matrix_pullback⟨n, m⟩(U, k, r, s, f, A)`: entrywise pullback |
| `formMatrixTraceDef` | `vec_form_matrix_trace(r, A)`: sum of the diagonal form entries |
| `FormSkewMatrixOnDef` | `vec_form_skew_matrix_on⟨n⟩(U, k, r, A)`: square homogeneous form matrix with Aᵀ = −A |
| `FormCurvatureDef` | `vec_form_curvature⟨n⟩(U, r, A)`: dA+A∧A for one-form entries |
| `MatrixProductForm` | Matrix wedge multiplication adds entry degrees and preserves the output shape — card |
| `MatrixProductAssociative` | Matrix wedge multiplication is associative — card |
| `MatrixDerivativeForm` | Entrywise exterior derivative raises the entry degree by one — card |
| `MatrixDerivativeSquareZero` | The entrywise exterior derivative squares to zero — card |
| `MatrixDerivativeLeibniz` | d(AB) = (dA)B + (-1)^p A(dB) for degree-p entries of A — card |
| `MatrixPullbackForm` | Entrywise pullback preserves degree and shape — card |
| `MatrixPullbackProduct` | Pullback preserves matrix wedge multiplication — card |
| `MatrixPullbackDerivative` | Pullback commutes with entrywise exterior derivative — card |
| `MatrixTraceForm` | The trace is a scalar form of the entry degree — card |
| `MatrixTraceCyclic` | $\operatorname{tr}(AB) = (-1)^{pq} \operatorname{tr}(BA)$, including rectangular factors — card |
| `MatrixTraceDerivative` | d tr(A) = tr(dA) — card |
| `MatrixTransposeProduct` | $(AB)^T = (-1)^{pq} B^T A^T$ — card |
| `CurvatureForm` | A one-form matrix has curvature of degree two — card |
| `CurvatureSkew` | A skew one-form matrix has skew curvature — card |
| `CurvatureBianchi` | dF + A∧F − F∧A = 0 for every one-form matrix — card |
| `CurvaturePullback` | Curvature commutes with smooth pullback — card |

## Even forms and Pfaffians

An inhomogeneous even form is a sequence indexed by its actual degree.
`vec_even_form_on⟨n⟩(U, α)` requires each component to be a normalized
smooth form, and each odd component to vanish. Components above n
vanish by the homogeneous form predicate, so no separate finite-support
choice is needed. `vec_even_form_ring⟨n⟩(U)` uses componentwise addition
and finite convolution by wedge. It is a commutative ring on this
carrier; its unit has the normalized constant one in degree zero.
On the empty open set this is the zero ring.

`vec_form_degree_term(k, ω)` inserts a homogeneous form in degree k.
For even degrees this respects wedge and places form matrices in the
existing algebraic matrix carrier. Real skew symmetry forces the
original diagonal to vanish, so lifting a skew matrix gives an
alternating matrix over the even-form ring despite its zero divisors.

For an r by r matrix B of two-forms, `vec_form_pfaffian⟨n⟩(U, r, B)`
takes the degree-r component of the existing algebraic Pfaffian after
inserting each entry into degree two. Each matching product has r/2
factors, so all other components vanish. Order zero gives the
normalized unit and odd orders give zero.
No skew symmetry is required for the form-degree, pullback or scaling
laws. In order 2m, constant scaling by t multiplies the Pfaffian by
$t^m$; this supplies the normalization by $2\pi$ for Euler forms.

Congruence by a smooth zero-form matrix H multiplies the Pfaffian of
a skew two-form matrix by the pointwise real determinant of H. The
identity does not require invertibility. Determinant one gives
invariance; positive determinant alone still rescales it. A unit
zero-form vector in the kernel forces the Pfaffian to vanish by the
algebraic unimodular-kernel theorem. The unit-length hypothesis
provides the dual pairing one, which a merely nonzero vector would
not provide over this ring.

| Member | Statement |
|---|---|
| `evenFormOnDef` | `vec_even_form_on⟨n⟩(U, α)`: normalized forms in each actual degree, zero in odd degrees |
| `formDegreeTermDef` | `vec_form_degree_term(k, ω)`: insertion in degree k |
| `evenFormRingDef` | `vec_even_form_ring⟨n⟩(U)`: pointwise addition and wedge convolution on the even carrier |
| `FormPfaffianDef` | `vec_form_pfaffian⟨n⟩(U, r, B)`: degree-r component of the algebraic Pfaffian of lifted two-form entries |
| `EvenFormRing` | The even-form carrier on an open set is a commutative ring — card |
| `EvenFormTerm` | An even-degree form inserts into the ring carrier — card |
| `EvenFormTermProduct` | Multiplication of insertions is insertion of their wedge — card |
| `EvenFormMatrixLift` | An even-degree square form matrix lifts to an algebraic matrix over the ring — card |
| `EvenFormSkewMatrixLift` | A skew even-degree form matrix lifts to an alternating algebraic matrix — card |
| `PfaffianHomogeneous` | The lifted Pfaffian is concentrated in degree r — card |
| `PfaffianForm` | The Pfaffian of an r by r matrix of two-forms is an r-form — card |
| `PfaffianEmpty` | The order-zero Pfaffian is the normalized unit zero-form — card |
| `PfaffianOdd` | Every odd-order Pfaffian is zero — card |
| `PfaffianPullback` | Pfaffian commutes with smooth pullback — card |
| `PfaffianScale` | Scaling all entries by t scales the order-2m Pfaffian by $t^m$ — card |
| `PfaffianCongruence` | Congruence by H contributes its pointwise determinant — card |
| `PfaffianOrientedFrame` | Determinant-one frame changes preserve the Pfaffian — card |
| `PfaffianUnitKernel` | A smooth unit zero-form vector in the kernel forces the Pfaffian to vanish — card |

## Gauge changes and closed curvature Pfaffians

`vec_form_matrix_conjugate⟨n⟩(U, k, r, H, B)` is the congruence by H,
with H in degree zero and B in degree k. Orthogonality is expressed by
`vec_form_orthogonal_on⟨n⟩(U, r, H)`: the entries are normalized smooth
zero-forms, and their real matrix at every point of U is orthogonal.
The matrix rank r is independent of the base dimension n.

The connection convention is

$$
A^H = H^{\mathrm{T}} A H + H^{\mathrm{T}} dH.
$$

`vec_form_gauge_connection⟨n⟩(U, r, H, A)` defines this expression.
Orthogonal H preserves skew one-form connections, and the curvature
transforms by congruence. Adding determinant one therefore preserves
the curvature Pfaffian. All equalities hold as normalized functions,
including outside U; no smoothness across its boundary is required.

`PfaffianCurvatureClosed` asserts closedness for every smooth skew
one-form matrix on an open Euclidean domain. Differentiating the
matching polynomial and substituting Bianchi gives cancellation by
the infinitesimal skew-congruence identity. The calculation is in the
full graded algebra: connection entries have degree one and the
curvature derivative has degree three. The commutative ring of even
forms supplies the algebraic Pfaffian identities but does not contain
the exterior derivative of every even form. Odd rank, zero rank and
rank exceeding the base dimension are included in the statement.

| Member | Statement |
|---|---|
| `FormMatrixConjugateDef` | `vec_form_matrix_conjugate⟨n⟩(U, k, r, H, B)`: congruence by a zero-form matrix |
| `FormOrthogonalOnDef` | `vec_form_orthogonal_on⟨n⟩(U, r, H)`: a normalized smooth orthogonal zero-form matrix |
| `FormGaugeConnectionDef` | `vec_form_gauge_connection⟨n⟩(U, r, H, A)`: the connection after an orthogonal frame change |
| `GaugeConnectionSkew` | Orthogonal gauge change preserves skew one-form connections — card |
| `CurvatureGauge` | Curvature transforms by orthogonal congruence — card |
| `PfaffianCurvatureGauge` | Determinant-one orthogonal gauge changes preserve the curvature Pfaffian — card |
| `PfaffianCurvatureClosed` | The Pfaffian of the curvature of any smooth skew connection is closed — card |

The `manifold/riemannian` chapter constructs the skew torsion-free connection
in a positive orthonormal frame and applies this gauge calculus to compare
connections, curvatures and Pfaffians under frame and coordinate changes.
Its normalized Pfaffians on positive charts define the global Euler form.
