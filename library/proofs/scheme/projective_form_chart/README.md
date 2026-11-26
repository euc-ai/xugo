# projective_form_chart — the two charts of a pair of forms: a curve finite over the projective line

The two charts are the curve's own: the rings of the open sets where a form F and a form G of one degree r over k do not vanish, glued along $t = \frac{G(x)}{F(x)}$. When F and G have no common zero on the curve, each chart is finite free over its polynomial ring and the two meet in k: together they are a curve over the line. Each chart is also integrally closed, as the affine pieces of the smooth curve are.

## The charts

| Member | Statement |
|---|---|
| `ChartQuotientsGenerate` | the quotients $\frac{x(i)^r}{F(x)}$ lie in the chart of F and generate its unit ideal |
| `ChartPieceAways` | the chart of F and the affine piece where x(j) ≠ 0 each lie in the other with one element inverted, $h = \frac{F(x)}{x(j)^r}$ and its inverse g |
| `FormChartIntegrallyClosed` | the ring of the open set where a form over k outside the ideal does not vanish is integrally closed in the generic field |
| `ChartInOtherAway` | the chart of F lies in the chart of G with $\frac{F(x)}{G(x)}$ inverted |
| `ParameterInChart` | $t = \frac{G(x)}{F(x)}$ lies in the chart of F |
| `ParameterInverse` | the inverse of $t = \frac{G(x)}{F(x)}$ is $\frac{F(x)}{G(x)}$ |
| `ChartsBiaffine` | glued along the overlap, the charts of F and G are a biaffine datum with $t = \frac{G(x)}{F(x)}$ and 1/t |
| `ChartFractionField` | K is the field of fractions of the chart of F |
| `FormsOverSubspace` | the forms of degree r·j over F(x)ʲ are the values of degree r·j times $F(x)^{-j}$, a k-subspace of M of dimension h(r·j) |
| `ChartsMeetInConstants` | the charts of F and G meet in k |
| `ParameterTranscendental` | $t = \frac{G(x)}{F(x)}$ is transcendental over k |
| `ChartFinitelyGenerated` | the chart of F is finitely generated over k[t] |
| `ChartFreeOverLine` | the chart of F is free of finite rank over k[t] |
| `FormChartsAreCurve` | the charts of two forms of one degree without a common zero, glued along $t = \frac{G(x)}{F(x)}$, are a curve over the line |
