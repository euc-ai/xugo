# residue_points — the points of a ring over a finite field with finite residues, in an algebraically closed field

Inside an algebraically closed M, a maximal ideal m of a subring S over a
finite field k, of residue degree d, is the kernel of exactly d points of S in
M, each with image the subfield of q^d elements: the points are a torsor under
its automorphisms over k. A point in a subfield of M is a point in M with
values there, so the points of S in the subfield of q^n elements with kernel m
are none unless d divides n, and then d. The subfields of q^d elements, their
inclusions and their automorphisms over k are finite_field's
(`finite_field.FiniteConstantsContained`,
`finite_field.FiniteConstantsAutomorphisms`).

## Members

| Member | Statement |
|---|---|
| `ResidueModuleOn` | Over a subfield k of M inside a subring S, S modulo an ideal is a k-module |
| `PointKernelMaximal` | A point of S in a finite subfield has maximal kernel with finite residues over k |
| `PointResidueField` | φ: S → M with S/ker φ finite over a finite k ⇒ ker φ maximal and φ(S) a subfield of q^d elements |
| `ResidueSize` | S modulo a maximal ideal of finite dimension d over the finite field k has q^d classes, and d is positive |
| `PointTwist` | An automorphism of the image of a point carries it to a point with the same kernel |
| `ResiduePointExists` | A maximal ideal of finite residue dimension over a finite field is the kernel of a point in a closed field |
| `ResiduePointImage` | A point with kernel m has image the subfield of M with q^d elements |
| `PointFactorsThroughAutomorphism` | Two points of one kernel and one image differ by an automorphism of that image over k |
| `ResiduePoints` | Exactly d points of S in M have kernel m, and each has image the subfield of M with q^d elements |
| `PointsInSubfield` | A point of S in a subfield is a point of S in M with values in that subfield |
| `ConstantPointsWithKernel` | The points of S in the subfield with q^n elements with kernel m, of residue degree d, are none unless d divides n, and then d |
