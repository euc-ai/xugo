# projective_form_pair — two forms of one degree without a common zero on a projective equation curve

Over a finite field no two linear forms need miss every point of the curve, so the two forms are found in a higher degree, and this chapter supplies what finds them: the zeros on the curve of a form over k outside the ideal lie in one finite field, and a form over k built from the q^s-th power map has no zero over that field. `projective_presentation.SmoothProjectiveBiaffinePresentation` builds the pair from them: F = Xⱼʳ, and G = H or H + F with H that form. Two forms without a common zero generate every form of large degree modulo the ideal — a graded Nullstellensatz proved by the bounded Hilbert function of a hyperplane section, with no Noetherian hypothesis.

## Rational zeros and an anisotropic form

| Member | Statement |
|---|---|
| `FormValuesBound` | at a zero on the curve of a form of degree r ≤ d over k outside the ideal, the values of the forms of degree d span a k-subspace of M of dimension at most h(d) − h(d − r) |
| `FormZerosRational` | the zeros on the curve of a form over k outside the ideal have their coordinates in one finite subfield of M |
| `AnisotropicForm` | over a finite subfield k of a field M, for every s > 0 some form over k of positive degree has no zero at a nonzero point over the field of qˢ elements |

## The graded Nullstellensatz

| Member | Statement |
|---|---|
| `VariablePowersGenerate` | subspaces of the forms over k closed under the variables, in which every variable has a power, hold every form of large degree |
| `GeneratedIdealForms` | subspaces of the forms over k, closed under the variables from N₀ on, are from N₀ on the forms of their degree in the ideal they generate |
| `CommonZeroWithoutPower` | subspaces of the forms over k closed under the variables and of bounded codimension, in which some variable has no power, have a common zero in projective space over a closed M |
| `GradedNullstellensatz` | subspaces of the forms over k, closed under the variables, of bounded codimension and with no common zero in projective space over a closed M, hold every form of large degree |

## Two forms generate

| Member | Statement |
|---|---|
| `CoprimeFormsGenerate` | over a closed M, two forms F and G of one degree r over k without a common zero on the curve write every form of large degree d + r as F·P₀ + G·P₁ + W, with P₀ and P₁ forms of degree d and W in the ideal of the curve |
| `CoprimeValuesGenerate` | over a closed M, at a point x of the curve, two forms of one degree r without a common zero write the value of every form of large degree d + r as F(x)·p + G(x)·q, p and q values of forms of degree d |
