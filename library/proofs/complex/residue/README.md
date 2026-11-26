# residue — the winding index of a path, the residue at an isolated singularity, and the orders of zeros and poles

The winding index of a path γ about a point w off it is
$\frac{1}{2\pi i} \cdot \int_\gamma \frac{dz}{z-w}$, `winding_index(γ, γ', a, b, w)`. The residue of
f at c, `complex_residue(f, c)`, is $\frac{1}{2\pi i}$ times the integral of f round
the circle of half the radius of a punctured disc about c on which f is
holomorphic, chosen among such discs. The orders of a zero and of a
pole, `complex_zero_order(f, c)` and `complex_pole_order(f, c)`, are the
powers of z − c that f, or 1/f, carries as a factor near c, with a
holomorphic cofactor not vanishing at c.

Each is the standard notion where its hypotheses hold — a closed
piecewise smooth path missing w with γ' its velocity, an isolated
singularity, f holomorphic near c and not vanishing on a disc about it,
f with a pole at c or agreeing near c with a holomorphic function not
zero at c — and elsewhere a number with no such meaning or an
unspecified value; the definitions' readings say which. In particular the
pole order is not 0 at a zero of f: the zero order is the one read there.

The chapter reads cauchy_integral's table, and through it
path_integral's: «circleInt», «closedPathIn», «convex», «disc» and «coef».
Its own table names the punctured disc `«punctured»(c, r)`,
`{z | 0 < |z − c| < r}`, and `«circleIndex»(c, r, w)`, the winding index
about w of the circle about c of radius r, run once round on ⟦0, 2π⟧. It
names how a function can look near a point.
`«meromorphicAt»(f, p)`: on a punctured disc about p, f is $\frac{g(z)}{(z-p)^{m+1}}$
with g holomorphic on the disc. This is *at most* a pole: g(p) may vanish,
so a removable point also counts. `«poleFactor»(f, c, m)`: on a punctured
disc about c, f is $\frac{g(z)}{(z-c)^m}$ with g holomorphic on the disc and
g(c) ≠ 0. `«zeroFactor»(f, c, m)`: on a disc about c, f is (z − c)ᵐ·g(z)
with g holomorphic there and g(c) ≠ 0. A pole is a pole factor of positive
order, `«properPole»(f, p)` = `∃m. «poleFactor»(f, p, m + 1)`.

## The definitions (definitions.go)

| constant | reading |
|---|---|
| `winding_index(γ, γ', a, b, w)` | `path_integral(λz. 1/(z − w), γ, γ', a, b) / (2πi)` |
| `complex_residue(f, c)` | `εw. ∃r. 0 < r ∧ holomorphic_on(«punctured»(c, r), f) ∧ «circleInt»(f, c, r / 2) = 2πi·w`: the w with ∮ f = 2πi·w round the circle of half the radius of a punctured disc about c where f is holomorphic |
| `complex_zero_order(f, c)` | `εm. «zeroFactor»(f, c, m)`: the m with f(z) = (z − c)ᵐ·g(z) near c, g holomorphic, g(c) ≠ 0 |
| `complex_pole_order(f, c)` | `εm. «poleFactor»(f, c, m)`: the m with $f(z) = \frac{g(z)}{(z-c)^m}$ off c near c, g holomorphic, g(c) ≠ 0 |

## The winding index (winding.go)

The winding index divides an integral by 2πi, which is not 0
(`path_integral.TwoPiINonzero`). So the integral of $\frac{1}{z-p}$ along a
path is 2πi times the index (`WindingIntegral`); every later residue
argument reads the index this way. Round a circle the integral of
$\frac{1}{z-w}$ is 2πi for every w inside it
(`cauchy_integral.CircleWindingInside`), so the circle winds once about
each point inside. A closed path in a convex open set does not wind about
a point outside the set: $\frac{1}{z-w}$ is holomorphic on the set, so by
Cauchy's theorem (`cauchy_integral.CauchyConvex`) it integrates to 0
round the path. A circle does not wind about a point w outside it: it
stays in the disc about c of radius |w − c|, which is open and convex
and misses w. So round a circle, which winds once about each point
inside and not about one outside, an index-weighted sum over points off
the circle is the plain sum of the weights inside; and a circle of
radius r ≥ 0 is a closed path in any set holding the points at distance
r from its centre. The higher
powers need no Cauchy theorem: off p, $\frac{1}{(z-p)^{n+1}}$ has derivative
$-\frac{n+1}{(z-p)^{n+2}}$, by the reciprocal rule over the power of a
translate, so $\frac{1}{(z-p)^{k+2}}$ is the derivative of $-\frac{1}{(k+1)(z-p)^{k+1}}$,
and its integral round a closed path missing p is the change of that
primitive between the path's ends, which agree: 0. $\frac{1}{(z-p)^n}$ is
holomorphic on any set that misses p, being the reciprocal of a power of
z − p, which is not 0 there. Round a closed path missing p, a principal
part integrates term by term: every term but the last has exponent at
least 2 and integrates to 0, and the last, $\frac{c(m)}{z-p}$, gives 2πi times
the winding index times c(m).

| member | statement |
|---|---|
| `WindingIntegral` | `path_integral(λz. complex_inv(z − p), γ, γ', a, b) = &(&2 * pi) * complex_i * winding_index(γ, γ', a, b, p)` |
| `WindingCircleInside` | `\|w − c\| < r ⇒ «circleIndex»(c, r, w) = &1` |
| `WindingCircleOutside` | `\|r\| < \|w − c\| ⇒ «circleIndex»(c, r, w) = &0` |
| `WindingOutsideConvex` | `S ∈ complex_topology ∧ «convex»(S) ∧ «closedPathIn»(S, γ, γ', a, b) ∧ w ∉ S ⇒ winding_index(γ, γ', a, b, w) = &0` |
| `WindingCircleCount` | `&0 ≤ r ∧ finite(Z) ∧ (∀z. z ∈ Z ⇒ \|z − c\| ≠ r) ⇒ Σ_{z∈Z} «circleIndex»(c, r, z) * &(&(k(z))) = &(&(Σ_{z∈Z ∩ «disc»(c, r)} k(z)))` |
| `CircleClosedPathIn` | `&0 ≤ r ∧ (∀z. \|z − c\| = r ⇒ z ∈ X) ⇒ «closedPathIn»(X, circle_path(c, r), λt. complex_i * &r * exp(complex_i * &t), &0, &2 * pi)` |
| `InversePowerDerivative` | `z ≠ p ⇒ complex_derivative_at(λu. complex_inv((u − p) ^ (n + 1)), z, −(&(n + 1) * complex_inv((z − p) ^ (n + 2))))` |
| `InversePowerIntegralZero` | `«closedPathIn»(𝕌 ∖ {p}, γ, γ', a, b) ⇒ path_integral(λz. complex_inv((z − p) ^ (k + 2)), γ, γ', a, b) = &0` |
| `InversePowerHolomorphic` | `p ∉ s ⇒ holomorphic_on(s, λz. complex_inv((z − p) ^ n))` |
| `PrincipalPartIntegral` | `«closedPathIn»(𝕌 ∖ {p}, γ, γ', a, b) ⇒ path_integral(λz. Σ_{k∈0 .. m} c(k) * complex_inv((z − p) ^ (m + 1 − k)), γ, γ', a, b) = &(&2 * pi) * complex_i * winding_index(γ, γ', a, b, p) * c(m)` |

## Poles (poles.go)

Let f be $\frac{g}{(z-c)^{m+1}}$ off c near c, with g the sum of
Σ b(n)(z − c)ⁿ on the disc of radius r. The residue chooses among the
radii ρ on whose punctured disc f is holomorphic. For each such ρ, the
function G equal to g(c) at c and to f(z)(z − c)ᵐ⁺¹ elsewhere is
holomorphic on the disc of radius ρ: near c it is g, and near any other
point it is the product. So G is the sum of the power series whose
coefficients are read off the circle of radius ρ/2, and these are b's,
the two series having one sum near c. Round that circle f is
$\frac{G}{(z-c)^{m+1}}$, whose integral is 2πi times the m-th coefficient: every
radius gives 2πi·b(m), and the residue is b(m). Dropping the first
m + 1 terms of g's series and dividing by (z − c)ᵐ⁺¹ leaves the tail
Σ b(n + m + 1)(z − c)ⁿ, whose sum is holomorphic on the disc; dividing
the dropped terms by (z − c)ᵐ⁺¹ term by term gives the principal part.
A function continuous at c that is, off c, (z − c)ᵏ⁺¹ times a function
continuous at c vanishes at c. So $\frac{g}{(z-c)^m} = \frac{h}{(z-c)^n}$ near c with
g(c), h(c) ≠ 0 forces m = n, the side with the larger exponent having a
numerator vanishing at c; the pole order is the exponent such a
representation gives. Dividing f by (z − c)ᵐ⁺ʲ turns two zero factors, of
orders m and j, into pole factors of orders j and m of one function, so
the zero order is the exponent its representation gives too. At a pole, the coefficients of g's
power series give both the principal part and the residue; a principal
part is holomorphic off its pole, being a finite sum of constants times
inverse powers.

A function that is $\frac{G(z)}{z-c}$ off c near c, with G holomorphic on a
disc about c, has at most a pole at c, and its residue is G(c): the
constant term of G's power series is G's value at the centre. A
logarithmic derivative has this form near a zero and near a pole. Where
f is φ·h off c near c, with h holomorphic and not 0 on a disc about c and
$\frac{\varphi'}{\varphi} = \frac{k}{z-c}$ — φ behaving as (z − c)ᵏ — the product rule gives
$\frac{f'}{f} = \frac{k}{z-c} + \frac{h'}{h}$, which is $\frac{G}{z-c}$ with G = k + (z − c)·h′/h,
so f′/f has residue k. At a zero of order m, f is (z − c)ᵐ·h with
h(c) ≠ 0, h has no zero on the disc since f has none off c, and k = m. At
a pole of order m + 1, f is $\frac{1}{(z-c)^{m+1}} \cdot g$ with g(c) ≠ 0, g has no zero
near c, being continuous at c, and k = −(m + 1), minus the pole order.

A function grows without bound at a proper pole: off p it is
$\frac{g}{(z-p)^{m+1}}$ with g(p) ≠ 0, so |g| stays above |g(p)|/2 near p while
|z − p|ᵐ⁺¹ ≤ |z − p| falls below any bound. So no proper pole lies near a
point where f is continuous, f staying within 1 of its value there; and f
is holomorphic on a punctured disc about a proper pole, being a quotient
there of functions holomorphic on it. Together these isolate the poles of
a function holomorphic on a disc off its proper poles: about each point
of the disc lies a disc holding no other pole, so the poles in a smaller
closed disc, which is compact, have no limit point and are finitely many.
The zeros off the poles are finitely many there too, unless f vanishes
throughout the disc off them. Where its zeros accumulate at a point of
the disc, that point is no pole, f having no zero near a pole; so f is
holomorphic on a disc about it and vanishes there by the identity
theorem. The points about which f vanishes on a disc then form a set
open in the plane that holds each point of the disc it comes near, and
the disc is connected (`cauchy_integral.DiscConnected`), so that set
holds all of the disc or none of it.

| member | statement |
|---|---|
| `ResidueAtPole` | `&0 < r ∧ (∀z. \|z − c\| < r ⇒ complex_sums(λn. b(n) * (z − c) ^ n, g(z))) ∧ (∀z. z ∈ «punctured»(c, r) ⇒ f(z) = g(z) / (z − c) ^ (m + 1)) ⇒ complex_residue(f, c) = b(m)` |
| `PrincipalPart` | the same hypotheses `⇒ ∃h. holomorphic_on(«disc»(c, r), h) ∧ ∀z. z ∈ «punctured»(c, r) ⇒ f(z) = Σ_{k∈0 .. m} b(k) * complex_inv((z − c) ^ (m + 1 − k)) + h(z)` |
| `PrincipalPartAtPole` | `«meromorphicAt»(f, p) ⇒ ∃r m c h. &0 < r ∧ holomorphic_on(«disc»(p, r), h) ∧ (∀z. z ∈ «punctured»(p, r) ⇒ f(z) = Σ_{k∈0 .. m} c(k) * complex_inv((z − p) ^ (m + 1 − k)) + h(z)) ∧ complex_residue(f, p) = c(m)` |
| `PrincipalPartHolomorphic` | `p ∉ s ⇒ holomorphic_on(s, λz. Σ_{k∈0 .. m} c(k) * complex_inv((z − p) ^ (m + 1 − k)))` |
| `VanishesAtCentre` | `&0 < ρ ∧ complex_continuous_at(g, c) ∧ complex_continuous_at(h, c) ∧ (∀z. z ∈ «punctured»(c, ρ) ⇒ h(z) = (z − c) ^ (k + 1) * g(z)) ⇒ h(c) = &0` |
| `PoleFactorUnique` | `&0 < ρ ∧` g, h continuous at c `∧ g(c) ≠ &0 ∧ h(c) ≠ &0 ∧ (∀z. z ∈ «punctured»(c, ρ) ⇒ g(z) / (z − c) ^ m = h(z) / (z − c) ^ n) ⇒ m = n` |
| `PoleOrderUnique` | `«poleFactor»(f, c, m) ⇒ complex_pole_order(f, c) = m` |
| `ZeroOrderUnique` | `«zeroFactor»(f, c, m) ⇒ complex_zero_order(f, c) = m` |
| `SimplePoleResidue` | `&0 < r ∧ holomorphic_on(«disc»(c, r), G) ∧ (∀z. z ∈ «punctured»(c, r) ⇒ F(z) = G(z) / (z − c)) ⇒ «meromorphicAt»(F, c) ∧ complex_residue(F, c) = G(c)` |
| `LogDerivativeResidue` | `&0 < r ∧ holomorphic_on(«disc»(c, r), h) ∧ (∀z. z ∈ «disc»(c, r) ⇒ h(z) ≠ &0) ∧ (∀z. z ∈ «punctured»(c, r) ⇒ φ(z) ≠ &0 ∧ complex_derivative_at(φ, z, k * φ(z) / (z − c))) ∧ (∀z. z ∈ «punctured»(c, r) ⇒ f(z) = φ(z) * h(z)) ∧ (∀z. z ∈ «punctured»(c, r) ⇒ complex_derivative_at(f, z, f'(z))) ⇒ «meromorphicAt»(λz. f'(z) / f(z), c) ∧ complex_residue(λz. f'(z) / f(z), c) = k` |
| `LogDerivativeAtZero` | `&0 < r ∧ holomorphic_on(«disc»(c, r), f) ∧ (∀z. z ∈ «punctured»(c, r) ⇒ f(z) ≠ &0) ∧ (∀z. z ∈ «punctured»(c, r) ⇒ complex_derivative_at(f, z, f'(z))) ⇒ «meromorphicAt»(λz. f'(z) / f(z), c) ∧ complex_residue(λz. f'(z) / f(z), c) = &(&(complex_zero_order(f, c)))` |
| `LogDerivativeAtPole` | `«properPole»(f, c) ∧ &0 < r ∧ (∀z. z ∈ «punctured»(c, r) ⇒ complex_derivative_at(f, z, f'(z))) ⇒ «meromorphicAt»(λz. f'(z) / f(z), c) ∧ complex_residue(λz. f'(z) / f(z), c) = −&(&(complex_pole_order(f, c)))` |
| `PoleUnbounded` | `«properPole»(f, p) ⇒ ∃δ. &0 < δ ∧ ∀z. z ∈ «punctured»(p, δ) ⇒ M < \|f(z)\|` |
| `NoPoleNearContinuity` | `complex_continuous_at(f, q) ⇒ ∃δ. &0 < δ ∧ ∀p. «properPole»(f, p) ⇒ δ ≤ \|p − q\|` |
| `PolePuncturedHolomorphic` | `«properPole»(f, p) ⇒ ∃ρ. &0 < ρ ∧ holomorphic_on(«punctured»(p, ρ), f)` |
| `PolesFiniteInClosedDisc` | `holomorphic_on(«disc»(c, R) ∖ P, f) ∧ (∀p. p ∈ P ⇒ «properPole»(f, p)) ∧ r < R ⇒ finite({p \| p ∈ P ∧ \|p − c\| ≤ r})` |
| `ZerosFiniteOffPoles` | `holomorphic_on(«disc»(c, R) ∖ P, f) ∧ (∀p. p ∈ P ⇒ «properPole»(f, p)) ∧ r < R ∧ ¬(∀z. z ∈ «disc»(c, R) ∖ P ⇒ f(z) = &0) ⇒ finite({z \| \|z − c\| ≤ r ∧ z ∉ P ∧ f(z) = &0})` |

## The residue theorem (theorem.go)

Let f be holomorphic on a convex open set S except at the finitely
many points P, each at most a pole of f. At each pole p, f is its
principal part plus a function H(p) holomorphic on a disc about p, and
the residue is the principal part's coefficient of $\frac{1}{z-p}$. Subtract
all the principal parts from f, and at each pole p give the difference Q
the value H(p) less the other principal parts. Then Q is holomorphic on
S: off the poles it is f less finitely many functions holomorphic there,
and near p, where no other pole lies, it is H(p) less the other
principal parts. So by Cauchy's theorem Q integrates to 0 round a closed
path in S ∖ P; on the path f is Q plus the principal parts, and each
principal part integrates to 2πi times the winding index times its
residue.

| member | statement |
|---|---|
| `ResidueTheorem` | `S ∈ complex_topology ∧ «convex»(S) ∧ finite(P) ∧ holomorphic_on(S ∖ P, f) ∧ (∀p. p ∈ P ⇒ «meromorphicAt»(f, p)) ∧ «closedPathIn»(S ∖ P, γ, γ', a, b) ⇒ path_integral(f, γ, γ', a, b) = &(&2 * pi) * complex_i * Σ_{p∈P} winding_index(γ, γ', a, b, p) * complex_residue(f, p)` |

## The argument principle and Rouché (argument.go)

For the argument principle, let f have a derivative f′ on a convex open
set S off a finite set P of genuine poles, and let f have finitely many
zeros in S ∖ P. S ∖ P is open, P being finite
(`complex_topology.OpenDiffFinite`), so f′ is holomorphic there; f′/f is holomorphic on S off the zeros and the poles
in S, and at each of these it has at most a pole, with residue the
zero's order or minus the pole's. The residue theorem therefore gives
the integral of f′/f round a closed path in S ∖ P on which f has no zero
as 2πi times the index-weighted sum of these orders; a pole outside S counts
nothing. For Rouché, suppose |f − g| < |f| along the path: neither f nor
g is 0 there, and g/f lies within 1 of 1, so in the slit plane
(`complex_log.SlitPlaneNearOne`), where log has derivative 1/w. So log(g/f) is a primitive of g′/g − f′/f along
the path, its integral round the closed path is 0, and the two
index-weighted zero counts agree. On the circle of radius r about c,
inside a disc of radius R > r, nothing need be assumed finite. Where
|f − g| < |f| on the circle neither f nor g is 0 there, so neither
vanishes throughout the disc, and each has finitely many zeros in the
closed disc of radius $\rho = \frac{r+R}{2}$ (`cauchy_integral.ZerosFiniteInClosedDisc`);
for the argument principle f is not 0 on the circle, and the poles and
the zeros off them are finitely many there (`PolesFiniteInClosedDisc`,
`ZerosFiniteOffPoles`). Both theorems then apply on the open disc of
radius ρ, round the circle as a closed path in it, and the index-weighted
sums are plain sums inside (`WindingCircleCount`): f and g have as many
zeros inside the circle, counted with order, and the integral of f′/f
round the circle is 2πi times the zeros less the poles inside.

| member | statement |
|---|---|
| `ArgumentPrinciple` | `S ∈ complex_topology ∧ «convex»(S) ∧ finite(P) ∧ (∀z. z ∈ S ∖ P ⇒ complex_derivative_at(f, z, f'(z))) ∧ (∀p. p ∈ P ⇒ «properPole»(f, p)) ∧ finite({z \| z ∈ S ∖ P ∧ f(z) = &0}) ∧ «closedPathIn»(S ∖ P, γ, γ', a, b) ∧ (∀t. a ≤ t ∧ t ≤ b ⇒ f(γ(t)) ≠ &0) ⇒ path_integral(λz. f'(z) / f(z), γ, γ', a, b) = &(&2 * pi) * complex_i * (Σ_{z∈{z \| z ∈ S ∖ P ∧ f(z) = &0}} winding_index(γ, γ', a, b, z) * &(&(complex_zero_order(f, z))) − Σ_{p∈P} winding_index(γ, γ', a, b, p) * &(&(complex_pole_order(f, p))))` |
| `ArgumentPrincipleHolomorphic` | `S ∈ complex_topology ∧ «convex»(S) ∧ (∀z. z ∈ S ⇒ complex_derivative_at(f, z, f'(z))) ∧ finite({z \| z ∈ S ∧ f(z) = &0}) ∧ «closedPathIn»(S, γ, γ', a, b) ∧ (∀t. a ≤ t ∧ t ≤ b ⇒ f(γ(t)) ≠ &0) ⇒ path_integral(λz. f'(z) / f(z), γ, γ', a, b) = &(&2 * pi) * complex_i * Σ_{z∈{z \| z ∈ S ∧ f(z) = &0}} winding_index(γ, γ', a, b, z) * &(&(complex_zero_order(f, z)))` |
| `Rouche` | `S ∈ complex_topology ∧ «convex»(S) ∧ holomorphic_on(S, f) ∧ holomorphic_on(S, g) ∧ finite({z \| z ∈ S ∧ f(z) = &0}) ∧ finite({z \| z ∈ S ∧ g(z) = &0}) ∧ «closedPathIn»(S, γ, γ', a, b) ∧ (∀t. a ≤ t ∧ t ≤ b ⇒ \|f(γ(t)) − g(γ(t))\| < \|f(γ(t))\|) ⇒ Σ_{z∈{z \| z ∈ S ∧ f(z) = &0}} winding_index(γ, γ', a, b, z) * &(&(complex_zero_order(f, z))) = Σ_{z∈{z \| z ∈ S ∧ g(z) = &0}} winding_index(γ, γ', a, b, z) * &(&(complex_zero_order(g, z)))` |
| `RoucheCircle` | `holomorphic_on(«disc»(c, R), f) ∧ holomorphic_on(«disc»(c, R), g) ∧ r < R ∧ (∀z. \|z − c\| = r ⇒ \|f(z) − g(z)\| < \|f(z)\|) ⇒ Σ_{z∈{z \| z ∈ «disc»(c, r) ∧ f(z) = &0}} complex_zero_order(f, z) = Σ_{z∈{z \| z ∈ «disc»(c, r) ∧ g(z) = &0}} complex_zero_order(g, z)` |
| `ArgumentPrincipleCircle` | `&0 ≤ r ∧ r < R ∧ (∀z. z ∈ «disc»(c, R) ∖ P ⇒ complex_derivative_at(f, z, f'(z))) ∧ (∀p. p ∈ P ⇒ «properPole»(f, p)) ∧ (∀z. \|z − c\| = r ⇒ z ∉ P ∧ f(z) ≠ &0) ⇒ «circleInt»(λz. f'(z) / f(z), c, r) = &(&2 * pi) * complex_i * (&(&(Σ_{z∈{z \| z ∈ «disc»(c, r) ∖ P ∧ f(z) = &0}} complex_zero_order(f, z))) − &(&(Σ_{p∈P ∩ «disc»(c, r)} complex_pole_order(f, p))))` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
