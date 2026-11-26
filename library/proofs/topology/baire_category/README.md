# baire_category — nowhere dense and meager sets, the Baire property and Baire spaces

A set is nowhere dense when its closure has no interior point, meager when it lies in a countable union of nowhere dense sets, and has the Baire property when it differs from an open set by a meager set; all three are read inside one space, so the set lies in the carrier, and they declare the topology implicit, as `closed_in` and `closure` do. A Baire space has no nonempty meager open set. Every notion is stated on a topology, with no metric; metric and completeness arguments enter only for Polish spaces.

Polish spaces are Baire spaces, by `complete_metric.BaireCategory` read through a compatible complete metric. The Borel sets have the Baire property, because the sets with that property form a sigma algebra containing the open sets. A continuous open map pulls meager sets back to meager sets. Mycielski's theorem (`MycielskiIndependentCantorSet`) gives continuum many pairwise independent points for a meager relation on a nonempty Polish space without isolated points, the continuum spelled as the subsets of ℕ and the Cantor branches indexed by binary words (`word_of_bits`). These are what [borel_subgroup](../../algebra/group/borel_subgroup/README.md) reads into Polish groups.

`definitions.go` holds the four definitions; `nowhere_dense.go` holds what they give: the union of two nowhere dense sets is nowhere dense (`NowhereDenseUnion`), a closed set is nowhere dense exactly when its interior is empty (`ClosedNowhereDenseIffEmptyInterior`), the closure of a nowhere dense set is nowhere dense (`ClosureNowhereDense`), the complement of a closed nowhere dense set is open and dense (`ClosedNowhereDenseComplement`), a meager set lies in the union of an increasing sequence of closed nowhere dense sets (`MeagerClosedCover`), a continuous open map pulls a meager set back to a meager set (`OpenMapMeagerPreimage`), and the diagonal of a Hausdorff space without isolated points is closed and nowhere dense in its square (`DiagonalClosedNowhereDense`); `baire_space.go` holds that a Polish space is a Baire space (`PolishBaire`); `cards.go` holds the cards; and `mycielski.go` holds Mycielski's theorem alone, a self-contained centrepiece whose sections — the pairing of one more ball, against balls already shrunk, off a closed nowhere dense set of the square, the shrinking of finitely many balls off it, the Cantor scheme of balls and the limits of its branches — are steps of that one proof and are cited nowhere else.

To read exact statements and dependencies, run `xugo query family topology/baire_category`.

## Members

| Member | Status | Statement and purpose |
|---|---|---|
| `NowhereDenseDef` | definition | A subset of the carrier whose closure has empty interior. |
| `MeagerDef` | definition | A subset of a countable union of nowhere dense sets. |
| `BairePropertyDef` | definition | Differs from an open set by a meager set. |
| `BaireSpaceDef` | definition | No nonempty open set is meager. |
| `NowhereDenseUnion` | theorem | The union of two nowhere dense sets in a topology is nowhere dense. |
| `ClosedNowhereDenseIffEmptyInterior` | theorem | A closed set is nowhere dense exactly when its interior is empty. |
| `ClosureNowhereDense` | theorem | The closure of a nowhere dense set is nowhere dense. |
| `ClosedNowhereDenseComplement` | theorem | The complement of a closed nowhere dense set is open and dense. |
| `MeagerClosedCover` | theorem | A meager set lies in the union of an increasing sequence of closed nowhere dense sets. |
| `OpenMapMeagerPreimage` | theorem | A continuous open map pulls a meager set back to a meager set; no surjectivity is needed. |
| `DiagonalClosedNowhereDense` | theorem | In a Hausdorff space without isolated points, the diagonal is closed and nowhere dense in the square. |
| `PolishBaire` | theorem | A Polish space is a Baire space, by BaireCategory in a compatible complete metric. |
| `MeagerCountableUnion` | card | A countable union of meager sets is meager; no hypothesis on the space. |
| `BorelBaireProperty` | card | The sets with the Baire property form a sigma algebra containing the open sets. |
| `MycielskiIndependentCantorSet` | theorem | A meager relation on a nonempty Polish space without isolated points has continuum many pairwise independent points. |
