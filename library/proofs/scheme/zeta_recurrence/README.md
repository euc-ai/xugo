# zeta_recurrence — the trace and Lucas sequences of the elliptic zeta numerator

The integer sequences s_n(a, q) and u_n(a, q) solve the two-term recurrence
$x_{n+1} = a \cdot x_n - q \cdot x_{n-1}$ from (2, a) and (0, 1): the power sums and the
Lucas sequence of the two roots of 1 − aT + qT², written without taking a
root. Every identity is one of integer sequences, with no power-series
type and no extension field of constants.

## Definitions

| Member | Meaning |
|---|---|
| `traceStateDef` | `elliptic_trace_state` |
| `traceSequenceDef` | `elliptic_trace_sequence` |
| `lucasSequenceDef` | `elliptic_lucas_sequence` |

## Sequences

| Member | Statement |
|---|---|
| `TraceSequenceSign` | s_n(−a,q)=(−1)^n s_n(a,q). — card |
| `LucasDeterminant` | u_{n+1}²−a·u_{n+1}·u_n+q·u_n²=q^n. |
| `TraceFromLucas` | s_n=2u_{n+1}−a·u_n. |
| `LucasIdentity` | s_n²−4q^n=(a²−4q)u_n². |
