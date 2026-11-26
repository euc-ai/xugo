# constant_twist — the fixed constant twists of a finite Galois function field

Let L be a regular function field over a finite field k, Galois over k(t), and s an automorphism of L over k(t) of order e. On the composite of L with the field l of |k|^e elements, the lift of s that fixes l, after the lift of the |k|-th power on l that fixes L, is the twist automorphism of s, and its fixed field is the twist field. The twist acts as s on L and as the |k|-th power on the constants, with order e, and the twist field is regular over k, of degree |G| over k(t), with the same composite with the constants as L (`CyclicConstantTwistDescent`). Counting the points of the twist fields over a good open is scheme/fixed_twist_models.

## Definitions

| Member | Statement |
|---|---|
| `constantFrobeniusLiftDef` | `constant_frobenius_lift`: field_ops(A) → set(A) → set(A) → permutation(A) → permutation(A) |
| `constantAutomorphismLiftDef` | `constant_automorphism_lift`: field_ops(A) → set(A) → set(A) → permutation(A) → permutation(A) |
| `ConstantTwistAutomorphismDef` | `constant_twist_automorphism`: field_ops(A) → set(A) → set(A) → permutation(A) → permutation(A) |
| `ConstantTwistFieldDef` | `constant_twist_field`: field_ops(A) → set(A) → set(A) → permutation(A) → set(A) |

## Descent to the twist field

| Member | Statement |
|---|---|
| `ConstantAutomorphismExtends` | An automorphism of the constants extends to the composite over L |
| `ConstantAutomorphismLiftExists` | An automorphism of L over k(t) extends to the composite fixing the constants |
| `ConstantTwistOrder` | An automorphism acting as s on L and as the q-power on the constants has order e |
| `ConstantTwistActs` | The twist acts as s on L and as the q-power on the constants, and fixes its fixed field |
| `ConstantTwistFieldData` | The twisted field lies over k(t) inside the composite with index e |
| `TwistedFieldConstants` | The elements of the twisted field algebraic over k are k |
| `CyclicConstantTwistDescent` | The twisted field is regular over k, of degree \|G\| over k(t), with the same composite with the constants as L |
