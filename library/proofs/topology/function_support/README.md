# function_support — carrier-relative closed support

`function_support(T, z, f)` is the closure in T of the carrier points
where f differs from the distinguished value z. The value type can be
arbitrary: z need not be the zero of a ring, and f need not be continuous.
The carrier guard is essential. Closure of a set with points outside
its space need not lie in that space, whereas this nonzero locus always
does. Values of f outside the carrier play no role.

On an open subspace U the support is U intersected with the ambient
support. Openness matters: restriction to a singleton can erase the
nonzero values that accumulate there. Extension by z from U preserves
support when the subspace support is closed in the ambient space.
Closedness only in U does not prevent new boundary support. In a
Hausdorff space, compact support in U supplies ambient closedness.

A pointwise operation in which either input being distinguished forces
the output to be distinguished has support in the intersection of the
input supports. Continuous pullback has support in the carrier-relative
preimage of the target support; a homeomorphism gives equality. These
statements also cover empty carriers and empty support.

| Member | Statement |
|---|---|
| `SupportDef` | `function_support(T, z, f)`: closure of the guarded nonzero locus |
| `SupportClosed` | Support is closed in a topological space — card |
| `SupportEmpty` | Empty support means the function equals z on the carrier — card |
| `SupportCongruence` | Carrier agreement gives equal supports — card |
| `SupportOutside` | A carrier point outside support has value z — card |
| `SupportClosedBound` | A closed set outside which f equals z bounds support — card |
| `SupportRestrictOpen` | Open restriction intersects support with the open subset — card |
| `SupportExtendZero` | Ambient closedness prevents extension from adding boundary support — card |
| `SupportProduct` | An operation annihilated by either distinguished input has intersection support — card |
| `SupportPullback` | Continuous pullback has support in the preimage of target support — card |
| `SupportHomeomorphism` | A homeomorphism gives equality in the pullback support formula — card |
