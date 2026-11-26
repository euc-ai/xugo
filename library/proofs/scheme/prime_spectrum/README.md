# prime_spectrum — the prime spectrum of a ring on a set and its Zariski topology

The points of the spectrum of the ring record `R` are its prime ideals:
`prime_spectrum(R)`, a set of sets. `zariski_closed(R, I)` is `V(I)`, the
primes holding `I`; `zariski_open(R, f)` is `D(f)`, the primes missing `f`;
the Zariski topology is the family of the complements of the `V(I)`. The
basic open sets `D(f)` are a base of compact open sets, and `D(f)` is
covered by the `D(h)`, `h ∈ H`, exactly when a power of `f` lies in the
ideal `H` generates — the one place `PrimeAvoidingPowers` enters (an ideal
holding no power of `f` lies in a prime missing `f`).

## The definitions

| member | statement |
|---|---|
| `PrimeSpectrumDef` | `prime_spectrum(R)` = the prime ideals of `R` |
| `ZariskiClosedDef` | `zariski_closed(R, I)` = the primes holding `I` |
| `ZariskiOpenDef` | `zariski_open(R, f)` = the primes missing `f` |
| `ZariskiTopologyDef` | `zariski_topology(R)` = the complements of the `V(I)` |

## The topology and its basic open sets

| member | statement |
|---|---|
| `OpenOfBasicNeighbourhoods` | a set each of whose points lies in a `D(f)` inside it is open |
| `ZariskiIsTopology` | `is_topology(zariski_topology(R))` |
| `ZariskiSpace` | `⋃zariski_topology(R) = prime_spectrum(R)` |
| `ZariskiOpenOpen` | `f ∈ R.carrier ⇒ zariski_open(R, f)` is open |
| `ZariskiOpenMember` | a prime lies in `D(f)` exactly when it misses `f` |
| `ZariskiOpenMul` | `D(f) ∩ D(g) = D(f * g)` |
| `ZariskiOpenBase` | each point of an open set lies in a `D(f)` inside it |
| `ZariskiBase` | the basic open sets `D(f)`, `f ∈ R.carrier`, are a base of the Zariski topology |
| `ZariskiOpenCover` | `D(f) ⊆ ⋃{D(h) \| h ∈ H}` ⇔ a power of `f` lies in `ideal_span(R, H)` |
| `ZariskiOpenCompact` | `D(f)` is compact |
