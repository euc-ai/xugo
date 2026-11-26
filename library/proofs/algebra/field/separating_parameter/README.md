# separating_parameter — separating parameters, integral primitive elements and Galois closures over k(t)

Over a perfect field k, a finitely generated extension K of transcendence
degree one has a separating parameter: an element t transcendental over k with
K finite and separable over k(t) (`SeparatingParameterExists`). In
characteristic p a transcendental element lies outside the rational functions
of its p-th power, a finite extension of k(t) has degree at most p over its
p-th powers, an element outside them separates, and the separating parameter
comes by descent on the degree (`separating.go`). Over k(t) a finite separable
extension then has a primitive element whose minimal polynomial is monic of the
full degree with coefficients in k[t], and inside an algebraically closed field
a Galois closure in which K is the fixed field of its own automorphisms
(`parameters.go`). None of this asks for regularity: these are the
presentations a regular function field (function_field) is read through.

## Members

| Member | Statement |
|---|---|
| `TranscendentalOutsidePowerAdjoin` | An element transcendental over k does not lie in k(t ^ p), for p at least two |
| `PowerSubfieldIndexBound` | A finite extension L of k(t), with k equal to its own p-th powers, has degree at most p over its p-th powers |
| `SeparableOffPowerSubfield` | An element t of K outside the p-th powers of K separates: over k(t), with K finite and k its own p-th powers, every element of K is separable |
| `SeparatingParameterExists` | A finite type extension of transcendence degree one over a perfect field has a separating transcendence basis |
| `IntegralPrimitiveElement` | A finite separable extension K of k(t), t transcendental over k, has a primitive element whose minimal polynomial over k(t) is monic of degree [K : k(t)], separable, with coefficients in k[t] |
| `FiniteGaloisClosureExists` | A finite separable extension K of k(t) in an algebraically closed field lies in a Galois extension L of k(t) in which the minimal polynomial of every element of K splits, and K is the fixed field of the automorphisms of L fixing K |
