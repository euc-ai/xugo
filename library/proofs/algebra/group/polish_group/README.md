# polish_group — Polish abelian groups, Polishable subgroups and homomorphisms with Borel lifts

A covered group is a Polish abelian group together with a Polishable subgroup, retaining the coset carrier even when the subgroup is not closed. A morphism is a quotient homomorphism with a Borel lift; its lift need not be a homomorphism.

Two theorems about a continuous homomorphism of Polish groups are stated apart. `ContinuousSurjectionBorelSection` gives a homomorphism onto a Polish group a Borel section, by the open mapping theorem and a Borel transversal of the closed cosets of the kernel; this is what the inversion and connecting-map arguments use. `ContinuousHomImagePolishable` makes the image of any continuous homomorphism a Polishable Borel subgroup: the quotient by the closed kernel is a Polish group by `ClosedSubgroupQuotientPolish`, its topology is transported to the image, and polish_space's `LusinSouslin` makes the image and the transported Borel sets Borel; this is what the Polishable clause of a cohomology cover uses.

`ContinuousLiftBijectiveIso` is the inversion statement the cohomology mechanism needs: a quotient map lifted by a continuous homomorphism, bijective on the quotient carriers, whose target denominator is the continuous image of a Polish group, has an inverse with a Borel lift. The inverse lift is the first coordinate of a Borel section of (x, p) ↦ f(x)·q(p), and BorelLiftModuloSubgroup descends it. The inverse property of groups with a Polish cover for merely Borel lifts, [Bergfalk, Lupini and Panagiotopoulos, Lemma 2.4 and Remark 3.3](https://londmathsoc.onlinelibrary.wiley.com/doi/full/10.1112/plms.12631), needs a uniformization theorem and is not stated. `DiscreteProductGroupPolish` makes a countable product of countable discrete abelian groups, with pointwise operations on the normalized carrier, a Polish abelian group; the based-dual and Čech cochain groups are its instances.

A left translate of an open set is open (`LeftTranslateOpen`, translates.go): it is the preimage of the set under x ↦ g⁻¹x, continuous because multiplication is. Cosets of an open subgroup are such translates, which is what [borel_subgroup](../borel_subgroup/README.md) reads.

## Members

| Member | Status | Statement and purpose |
|---|---|---|
| `PolishAbelianGroupDef` | definition | The topology has exactly the group carrier, with continuous multiplication and inverse. |
| `PolishableSubgroupDef` | definition | The subgroup admits a Polish group topology with the ambient trace Borel sets. |
| `PolishCoverOnDef` | definition | The covered quotient has underlying carrier left_cosets(G.mul, G.carrier, N). |
| `BorelCoverMapDef` | definition | A quotient homomorphism with a Borel lift; the lift may be additive only modulo the target subgroup. |
| `BorelCoverIsoDef` | definition | Both directions have Borel lifts; their inverse equations are guarded by quotient membership. |
| `LeftTranslateOpen` | theorem | A left translate of an open set of a Polish group is open: it is the preimage of the set under x ↦ g⁻¹x. |
| `ContinuousSurjectionBorelSection` | card | A continuous homomorphism onto a Polish group has a Borel section; the image is closed, so no Borel-image theorem enters. |
| `ContinuousHomImagePolishable` | card | The image need not be closed or Polish in its subspace topology; its Polish topology is transported from the quotient by the kernel. |
| `ClosedSubgroupPolish` | card | Restrict the continuous operations to the closed subgroup and apply ClosedSubspacePolish. |
| `ClosedSubgroupQuotientPolish` | card | The quotient of a Polish abelian group by a closed subgroup is a Polish abelian group in the quotient topology. |
| `BorelLiftModuloSubgroup` | card | The lift need only be additive modulo M and send N into M; no homomorphism lift or quotient selector is required. |
| `ContinuousLiftBijectiveIso` | card | A continuous homomorphic lift bijective on quotient carriers, with a presented target denominator, has an inverse with a Borel lift. |
| `DiscreteProductGroupPolish` | card | Pointwise operations on a countable product of countable discrete abelian groups give a Polish abelian group for the discrete product topology. |

## Polish models and applications

ProductGroupPolish uses the supplied Polish factor topologies and their continuous operations; it does not discretize uncountable factors.

| Member | Status | Statement and purpose |
|---|---|---|
| `ProductGroupPolish` | card | CountableProductPolish supplies the space. — card |
