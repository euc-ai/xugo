# borel_subgroup — Borel subgroups of Polish abelian groups: open or meager, countable or continuum index

Baire category read into a Polish abelian group. Pettis's lemma gives a non-meager set with the Baire property an identity neighbourhood inside its difference set; so a non-meager Borel subgroup is open, hence also closed, and an open subgroup has countable index by separability. In the other direction a meager subgroup has at least continuum many cosets, by Mycielski's theorem applied to the coset relation, which is the preimage of the subgroup under the open map (x, y) ↦ x·y⁻¹. Together: a Borel subgroup of a Polish abelian group has countable index exactly when it is open, and otherwise continuum many cosets; a Borel subgroup that is not closed is meager and has continuum many cosets.

The continuum is spelled as the subsets of ℕ, `card_le(𝕌⟨A:set(num)⟩, …)`, as real_cardinality spells the size of the line. Closedness is read in the group's topology; a closed subgroup of uncountable index exists, so only meagerness decides the dichotomy. [polish_cohomology](../../module/polish_cohomology/README.md) reads these cards at the coboundaries inside the cocycles.

`subgroup_index.go` holds the countable index of an open subgroup (`OpenSubgroupCountableIndex`). To read their exact statements and dependencies, run `xugo query family algebra/group/borel_subgroup`.

## Members

| Member | Status | Statement and purpose |
|---|---|---|
| `PettisLemma` | card | A non-meager set with the Baire property has an open identity neighbourhood inside s·s⁻¹. |
| `NonmeagerBorelSubgroupOpen` | card | A non-meager Borel subgroup is open and closed. |
| `OpenSubgroupCountableIndex` | theorem | An open subgroup of a Polish group has countably many cosets, by separability. |
| `CountableIndexBorelSubgroupClopen` | card | A Borel subgroup of countable index is open and closed, since the carrier is not meager. |
| `MeagerSubgroupContinuumIndex` | card | A meager subgroup has at least continuum many cosets, by Mycielski's theorem on the coset relation. |
| `NonclosedBorelSubgroupContinuumIndex` | card | A Borel subgroup that is not closed is meager and has at least continuum many cosets. |
| `BorelSubgroupIndexDichotomy` | card | A Borel subgroup has countably many cosets or at least continuum many. |

## Polish models and applications

For a Polish cover, countability of the quotient is equivalent to openness of the actual denominator. A closed denominator gives a Polish quotient group. A nonclosed denominator is meager in its closure and admits a continuous Cantor family of pairwise inequivalent representatives.

| Member | Status | Statement and purpose |
|---|---|---|
| `PolishCoverCountableIffOpen` | card | A Polishable subgroup is Borel. — card |
| `ClosedCoverQuotientPolish` | card | The quotient of a Polish group by a closed subgroup is Polish. — card |
| `NonclosedCoverCantorRepresentatives` | card | The continuous Cantor parametrization is an additional conclusion beyond the existing cardinal-only Mycielski card; its finite-cylinder fusion proof must establish continuity explicitly. — card |
