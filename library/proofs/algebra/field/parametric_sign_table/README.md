# parametric_sign_table — parametric sign tables, uniform in the parameters: the notion, its combinators and the Cohen–Hörmander step

A family of polynomials in one variable over the parameter ring has a uniform table under a condition when one fixed list of parameter polynomials, read at the model, gives the size of the table and the sign of each member on each cell, in every real closed field and environment meeting the condition. The parameter polynomials and branch rules are chosen before the real closed field and the parameter environment. Such tables survive splitting on the sign of a parameter polynomial, a stronger condition and a change of members that keeps their signs, and a family of constants has one. The step adds a polynomial p of fixed degree and leading sign to a family: the table of the others, of p′ and of the remainders of p by each of them is coarsened to the cuts where one of the others or p′ vanishes without being the zero polynomial, and each open cell of the coarse table, where p′ keeps one sign, is split at one point, the root of p there when it has one.

| Member | Statement |
|---|---|
| `ParametricSignTableDef` | Polynomials over the parameter ring whose sign table, in every real closed field and environment meeting a condition, is given by the signs of one fixed list of parameter polynomials. |
| `ModelSpecialization` | A model of a condition is an ordered field, so a field, with the parameters assigned points of its carrier, and specialization there is a ring homomorphism from the parameter polynomials that keeps zero. |
| `SignTableByCases` | A family whose table is uniform under each sign of a parameter polynomial has a uniform table. |
| `SignTableByAgreement` | A family whose members take, point by point, the signs of chosen members of a family with a uniform table has one too. |
| `ConstantFamilySignTable` | A family of constants has a uniform table with one cell. |
| `SignTableUnderStrongerCondition` | A table under a condition is a table under every condition that implies it in each model. |
| `SignTableBySigns` | A family whose table is uniform under every assignment of signs to finitely many parameter polynomials has a uniform table. |
| `VanishingCutsTable` | The cuts where a nonzero one of the first members vanishes carry a table of those members. |
| `GapSplit` | Where a polynomial's derivative keeps one sign, one point splits the interval into parts of known sign, the polynomial vanishing there exactly when the end signs are opposite. |
| `MonotoneRefinement` | A table of a family ending in p′ refines, by one split point in each open cell, the root of p there when it has one, to a table of p and the others. |
| `DerivativeRemainderStep` | The Cohen–Hörmander step: the table of a family whose first member has a fixed degree and leading sign follows from the table of the others, its derivative, and its remainders by each of them. |
