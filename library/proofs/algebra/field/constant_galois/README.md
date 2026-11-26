# constant_galois — the Galois theory of a function field's composite with a finite field of constants

Let K be regular over a finite field k of q elements inside an algebraically
closed M, and l the subfield of q^r elements. The composite K(l) is Galois over
K (`ConstantCompositeGalois`), and a basis of l dual for the sum of conjugates
recovers the coordinates of an element as sums of its conjugates' multiples
(`ConstantTraceDual`). A finite sum of elements integral over a subring is
integral (`integral_element.IntegralModuleSum`), so the coordinates of an
element integral over the chart of a ring S, generated over S by a k-basis of l
(`constant_field_extension.ConstantChartFinite`), are integral over S: this is
what makes the chart of a normal ring normal. The sum of the conjugates itself
— fixed by the group, nonzero, integral when its argument is
(field_automorphism), a K-linear form into K on a Galois extension
(`galois_correspondence.GaloisTraceLinear`) — and the form y ↦ T(b * y)
(`field_extension.ProductFormLinear`) are the algebra's.

Enlarging the finite constants keeps the geometric Galois group
(`GeometricGaloisBaseChange`): for L Galois over k(t), the composite of L with
the field of q^R elements, R a multiple of the degree of L's constants, is
Galois over the rational functions of those constants, with the same group and
the corresponding fixed composita. It is a centerpiece and stands alone in
`galois.go`: its fourteen lemmas — the tensor transport, the extension and
realization of automorphisms, the count — serve it and nothing else.

## Normality

| Member | Statement |
|---|---|
| `ConstantCompositeData` | The field l of q^r constants is a finite extension of k inside the subfield K(l), and k is closed in K |
| `ConstantCompositeGalois` | The composite K(l) of a regular function field with the field of q^r constants is Galois over K |
| `ConstantTraceForm` | K(l) is Galois over K, and the sum of the conjugates is K-linear there and a k-linear form on l |
| `ConstantTraceDual` | A k-basis E of l has a dual family d in l for which T(d(e) * x) is the K-coordinate of x at e |

## The geometric Galois group

| Member | Statement |
|---|---|
| `GeometricGaloisBaseChange` | Enlarging finite constants preserves the geometric Galois group, its degree, and the corresponding intermediate fixed composita |
