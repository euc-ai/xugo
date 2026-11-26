# chern_thom — Chern–Thom comparison with the fixed Koszul convention

The Koszul complex uses Lambda E, even to odd, and on a line its map is z. With ch=tr exp(-F/(2 pi i)), its fibre character is $(-1)^r\operatorname{Td}(E^{\ast})^{-1}$. The formula below is supported correctly: on a noncompact base it applies to the Thom image of a compact K class, not to the bare Koszul triple.

The line calculation uses an angular form and a compact radial cutoff. Higher rank follows by projective pullback injection, the actual tautological splitting, multiplicativity and base change of fibre integration. This comparison is independent of both analytic and topological numerical indices.

## Members

| Member | Statement or role |
|---|---|
| `DualDef` | Definition of `projection_dual` |
| `InverseToddDef` | Definition of `inverse_todd_class` |
| `InverseTodd` | The inverse Todd class satisfies the graded convolution identity — card |
| `correctedCharacterDef` | Definition of `thom_corrected_character` |
| `LineKoszulCharacter` | The line Koszul character has the negative dual-Todd correction — card |
| `ChernThom` | The rank-r Koszul Thom character has correction (-1)^r Td(E*) inverse — card |
