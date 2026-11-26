# complex_log — the argument of a complex number and the principal logarithm

Every nonzero complex number is `|z|·exp(it)` for exactly one angle `t`
in ⟬−π, π⟧, its principal argument `complex_arg(z)`; the principal
logarithm is `log(z) = log|z| + i·arg z`, the one logarithm of `z`
whose imaginary part lies in ⟬−π, π⟧. The argument is defined by
choice, as the line's inverse functions are (`real_arctan`,
`real_arcsin`), and the half-angle formula $\arg z = 2 \cdot \arctan\left(\frac{y}{\lvert z \rvert + x}\right)$
off the closed negative half-line is a theorem: it is what makes the
argument continuous there, and with it the logarithm. That plane slit
along the closed negative half-line, `slit_plane`, the complex numbers
that are not a real ≤ 0, is where the argument and the logarithm are
continuous; there log is the inverse of exp, and its derivative is 1/z.

## The definitions (definitions.go)

| constant | reading |
|---|---|
| `complex_arg(z)` | `εt. −π < t ∧ t ≤ π ∧ z = \|z\|·exp(i·t)` |
| `complex_log(z)`, written `log(z)` | `log\|z\| + i·complex_arg(z)` |
| `slit_plane` | `{z \| ¬(re(z) ≤ &0 ∧ im(z) = &0)}` |

## The argument (arg.go)

Every complex number is |z|·exp(it) for an angle t in ⟬−π, π⟧: at 0 any
angle serves; otherwise z/|z| lies on the unit circle, so its
reflection (−re, im) is (cos s, sin s) for some s in ⟦0, 2π⟭, and π − s
is such an angle. The argument is chosen among these angles
(`ArgSpec`). z = r·exp(it) exactly when z's parts are r·cos t and
r·sin t, and two angles in ⟬−π, π⟧ with the same cosine and sine differ
by an integer multiple of 2π smaller than 2π in size, so they are equal
(`real_trigonometry.CosSinInjective`).
Hence the argument of a nonzero z is its only polar angle there: 0 on
the positive reals, π on the negative ones. Off the closed negative
half-line, which is where |z| + re z > 0 (and so |z| > 0,
`SlitPlaneAbsPos`; the disc of radius 1 about 1 lies there, its real parts
being positive, `SlitPlaneNearOne`), half the argument h lies in
⟬−π/2, π/2⟭; from |z| + re z = 2|z|cos²h and im z = 2|z|·sin h·cos h the
quotient $\frac{\operatorname{im} z}{\lvert z \rvert + \operatorname{re} z}$ is $\tan h$, the half-angle formula. It makes
the argument continuous there: on a disc about z the argument equals
the formula, a continuous real function of the continuous half-angle
tangent $\frac{\operatorname{im} w}{\lvert w \rvert + \operatorname{re} w}$ (`complex_topology.ContinuousAtRealCompose`,
`complex_topology.ContinuousAtLocal`).

| member | statement |
|---|---|
| `PolarFormExists` | `∃t. −π < t ∧ t ≤ π ∧ z = &\|z\| * exp(complex_i * &t)` |
| `ArgSpec` | `−π < complex_arg(z) ∧ complex_arg(z) ≤ π ∧ z = &\|z\| * exp(complex_i * &complex_arg(z))` |
| `ArgBounds` | `−π < complex_arg(z) ∧ complex_arg(z) ≤ π` |
| `ArgPolar` | `z = &\|z\| * exp(complex_i * &complex_arg(z))` |
| `PolarParts` | `z = &r * exp(complex_i * &t) ⇔ re(z) = r · cos(t) ∧ im(z) = r · sin(t)` |
| `ArgUnique` | `z ≠ &0 ∧ −π < t ∧ t ≤ π ∧ z = &\|z\| * exp(complex_i * &t) ⇒ complex_arg(z) = t` |
| `ArgPositiveReal` | `&0 < x ⇒ complex_arg(&x) = &0` |
| `ArgNegativeReal` | `x < &0 ⇒ complex_arg(&x) = π` |
| `SlitPlaneIff` | `z ∈ slit_plane ⇔ &0 < \|z\| + re(z)` |
| `SlitPlaneAbsPos` | `z ∈ slit_plane ⇒ &0 < \|z\|` |
| `SlitPlaneNearOne` | `\|w − &1\| < &1 ⇒ w ∈ slit_plane` |
| `ArgHalfAngle` | `z ∈ slit_plane ⇒ complex_arg(z) = &2 · arctan(im(z) / (\|z\| + re(z)))` |
| `ArgContinuous` | `z ∈ slit_plane ⇒ complex_continuous_at(λw. &complex_arg(w), z)` |

## The logarithm (log.go)

The parts of log z = log|z| + i·arg z are log|z| and arg z. On the
positive reals |x| = x and arg x = 0, so the principal logarithm is ℝ's.
Off the half-line, log|w| is the continuous real logarithm of the
continuous modulus (|z| > 0 there), and the argument is continuous
there, so the logarithm is continuous. exp undoes log away from 0:
exp(log z) = exp(log|z|)·exp(i·arg z) = |z|·exp(i·arg z) = z. log undoes
exp on the strip −π < im z ≤ π: exp(z) = exp(re z)·exp(i·im z), so
|exp z| = exp(re z) (`complex_power_series.AbsExp`) and arg exp(z) = im z. On the slit plane log is
continuous and undone by exp on the disc of radius |z| about z, and exp
has derivative exp(log z) = z ≠ 0 at log z, so the derivative of the
inverse is 1/z (`complex_derivative.DerivativeInverse`).

| member | statement |
|---|---|
| `LogParts` | `re(log(z)) = log(\|z\|) ∧ im(log(z)) = complex_arg(z)` |
| `LogPositiveReal` | `&0 < x ⇒ log(&x) = &(log(x))` |
| `ExpLog` | `z ≠ &0 ⇒ exp(log(z)) = z` |
| `LogExp` | `−π < im(z) ∧ im(z) ≤ π ⇒ log(exp(z)) = z` |
| `LogContinuous` | `z ∈ slit_plane ⇒ complex_continuous_at(complex_log, z)` |
| `LogDerivative` | `z ∈ slit_plane ⇒ complex_derivative_at(complex_log, z, complex_inv(z))` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
