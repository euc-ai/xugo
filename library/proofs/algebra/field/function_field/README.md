# function_field — regular function fields of one variable

A regular function field K over k, inside a field M, is finitely generated over
a perfect field k (perfect_field), of transcendence degree one, with exactly k
as its algebraic constants (`RegularFunctionFieldDef`). The ambient field is
kept separate from the function field so finite constant extensions and
splitting fields have room to exist. Regularity reads the same in M and in the
restriction of M to a subfield holding K, in both directions (`ambient_field.go`);
the ring and regular module of a restricted field, its polynomial images and its
algebraicity read as M's (`field.RestrictFieldRecords`,
`algebraic_element.RestrictFieldReadings`). Over a finite base the algebraic
constants of a finite extension of k(t) form a finite exact constant field
(`constants.go`), and a function field of one variable embeds into an
algebraically closed field along any embedding of its base field
(`embedding.go`: through k₀[s] (algebraic_element), its field of fractions
k₀(s) (ring_localization) and the finitely many algebraic generators
(algebraic_closure)).

The chapters above this one: rational_function_field (k(t) and plane equations
over it), constant_composite (the composite with a finite extension of the
constants), constant_field_extension (its charts), constant_galois and
constant_splitting. separating_parameter presents a function field over k(t)
without asking for regularity.

## Definitions

| Member | Statement |
|---|---|
| `RegularFunctionFieldDef` | `regular_function_field`: field_ops(A) → set(A) → set(A) → bool |

## Members

| Member | Statement |
|---|---|
| `RegularFunctionFieldInAmbient` | A function field regular over k read in the restriction of M to a subfield K is regular over k read in M |
| `RegularFunctionFieldInRestriction` | A function field regular over k in M stays regular read inside its own carrier |
| `ExactConstantFieldFinite` | Over a finite base k, the algebraic constants in a finite extension of k(t) form a finite exact constant field, of positive degree r and cardinality card(k)^r |
| `FunctionFieldEmbedding` | a finitely generated field of one variable embeds into an algebraically closed field along any embedding of the base field k₀, its transcendental sent to any transcendental |
