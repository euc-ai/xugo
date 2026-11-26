# scheme — schemes, the locally ringed spaces covered by spectra of their rings of sections

A scheme is a locally ringed space every point of which lies in an open
set `U` isomorphic, as a locally ringed space, to the spectrum of the ring
of its own sections `F(U)`. If `U` is isomorphic to the spectrum of any
ring, that ring is isomorphic to `F(U)`, so the definition asks no more
than the textbook's; and it names the ring without quantifying over a
type of rings. The spectrum of `F(U)` has points of the type `set(B)` and
sections of the type `set(B) → set(prod(B, B))`, fixed by the type `B` of
the sections, so the definition is a formula like any other.

| member | statement |
|---|---|
| `Scheme` | `scheme(…)` ⇔ a locally ringed space, every point in an open `U` isomorphic to the spectrum of `F(U)` |
| `LocallyRinged` | the axiom |
| `SpecScheme` | the prime spectrum of a ring is a scheme — card |
