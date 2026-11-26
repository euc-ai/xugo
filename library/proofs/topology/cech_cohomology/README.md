# cech_cohomology — countable-cover Čech complexes of module-valued presheaves and their Polish covers

A cover is indexed by natural numbers, with repetitions and empty opens allowed. A tuple is a pair of its degree and a sequence of indices, zero after that degree. All degrees use this one tuple host. A cochain is normalized to the coordinate zero outside the active degree, while addition and scalar multiplication are read at the section module of each tuple intersection.

Sections on finite intersections are countable discrete modules. The product cochain topology is Polish and restrictions induce continuous maps. Refinement maps give the usual Čech pullback; different refinement index maps are cochain homotopic. A refinement yields an isomorphism of covers only when its actual ordinary cohomology map is an isomorphism. No claim identifies an arbitrary single-cover cohomology with space or sheaf cohomology; that requires a separate comparison hypothesis. Taking the scalar ring to be the integers gives the abelian-group case.

The section carrier varies with the tuple intersection, so these are products of varying discrete factors with prescribed inactive coordinates. `polish_space.FiniteCoordinateContinuous` supplies continuity in each degree: an output of the differential reads the finitely many deleted-tuple coordinates, and an output of a refinement map reads one old tuple coordinate before applying a restriction. In each application, the algebraic carrier conditions ensure that the map lands in the target normalized cochain carrier. Countability enters separately: `polish_group.DiscreteProductGroupPolish` makes each degree a Polish abelian group. All theorem members here remain cards.

## Members

| Member | Status | Statement and purpose |
|---|---|---|
| `cechIndicesDef` | definition | A degree-n tuple has n+1 active entries and zero tail. |
| `cechMeetDef` | definition | The intersection over the nonempty finite tuple of cover indices. |
| `cechDeleteDef` | definition | Delete one tuple entry, reducing its degree and normalizing the tail; read only in positive degree with i at most the degree. |
| `cechRefineTupleDef` | definition | Apply the refinement index map to active tuple entries only. |
| `modulePresheafDef` | definition | The existing set-valued presheaf has module sections and linear restriction maps. |
| `cechDatumDef` | definition | All finite-intersection section groups are countable; the ambient section type need not be countable. |
| `cechZeroDef` | definition | The zero cochain is the section zero at each tuple intersection. |
| `cechTermsDef` | definition | The degree carrier consists of section assignments on its tuples, with coordinate zero outside that degree. |
| `cechDifferentialDef` | definition | The alternating restriction sum has n+2 terms and is normalized outside the target degree. |
| `CechComplexDef` | definition | One complex record holds every degree on the normalized tuple-function host. |
| `cechTopologiesDef` | definition | A countable product of discrete section groups, with prescribed inactive coordinates. |
| `cechRefinementMapDef` | definition | A refined output coordinate reads one old coordinate and restricts it to the refined intersection. |
| `CechIndicesCountable` | card | The zero-tail tuples are the image of finite sequences of natural numbers of length n+1. |
| `CountableCoverCechPolishModel` | card | DiscreteProductGroupPolish gives Polish terms and FiniteCoordinateContinuous applies to the finite alternating restriction sum. Tuples are nonempty in every degree and inactive values use the coordinate-dependent zero. |
| `CechRefinementContinuous` | card | FiniteCoordinateContinuous applies because each active output reads one old coordinate; refinement commutes with the alternating restriction differential. |
| `CechRefinementHomotopy` | card | Tuple deletion is used in positive degree at valid positions. Refinement choices need only yield algebraic homotopies to induce identical maps on cohomology. |
| `CechRefinementDefinableIso` | card | A refinement alone does not force equality of cover cohomology, and an unrelated abstract group isomorphism is not the required hypothesis. |
| `CechCountableOrContinuum` | card | Countable-cover Čech cohomology with countable sections is countable or has at least continuum many classes. |

## Polish models and applications

Polish section groups and continuous restriction maps give Polish Cech models with their supplied topologies. Refinement maps are continuous; algebraic prism homotopies suffice. The finite-intersection diagram interface uses strictly increasing zero-tail tuples and supports the affine-cover application without constructing a topological space. Repeated copies of a finite cover reduce by the prism homotopy; arbitrary cover-independence is not asserted.

| Member | Status | Statement and purpose |
|---|---|---|
| `FiniteRepeatedCoverVanishing` | card | This is reduction of repeated copies of one finite cover; it does not assert invariance for arbitrary refinements. — card |
| `IntersectionIndicesDef` | definition | Finite nonempty sets of chart indices. |
| `OrderedCechIndicesDef` | definition | Strictly increasing tuples with a zero tail, representing oriented finite intersections. |
| `CechSupportDef` | definition | The nonempty finite set underlying a Cech tuple. |
| `IntersectionModuleDatumDef` | definition | A strict module diagram on finite intersections, with restriction in the direction of inclusion of index sets. |
| `IntersectionCechComplexDef` | definition | The alternating Cech complex on increasing tuples, with the same zero-tail and deletion conventions as cech_complex. |
| `IntersectionCechTopologiesDef` | definition | Actual factor topologies on all finite intersections. |
| `IntersectionCechCochain` | card | Deleting two coordinates in opposite orders gives the same restriction by strict composition. — card |
| `IntersectionCechPolishModel` | card | Ordered tuple sets are subsets of the countable zero-tail tuples. — card |
| `polishCechDatumDef` | definition | A module presheaf of Polish additive groups with continuous restrictions. |
| `polishCechTopologiesDef` | definition | The existing Cech complex carries the supplied factor topologies, without discretizing its section groups. |
| `PolishCechModel` | card | The tuple sets are countable, and each differential coordinate is a finite alternating sum of continuous restrictions. — card |
| `PolishCechRefinementContinuous` | card | The existing refinement formula reads one input coordinate and applies one continuous restriction. — card |
| `PolishCechRefinementHomotopy` | card | Use the alternating prism of the two index maps. — card |
