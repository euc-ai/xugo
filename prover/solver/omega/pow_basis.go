package omega

// The pow basis: `real_pow(t, c)` and `int_pow(t, c)` with a literal exponent
// read as the monomial t^c, so a power and a written-out product meet as one
// unknown in the linear layer instead of standing as two unrelated atoms.
//
// A literal exponent auto-unfolds only up to c ≤ 1 in the simp step
// (real_ops.go realPowSimp, int.go intPowSimp): a complex base to a high power
// explodes the TERM, and the corpus wants `real_pow(x, 2)` left as written.
// Reading it in the basis costs no term growth at all — only the linear form
// expands — so the pow handlers (sign, base and exponent monotonicity, the
// of_num bridge) go on meeting the spelling the author wrote, while linarith
// stops seeing `real_pow(x, 2) ≤ y` and `x * x ≤ y` as facts about different
// things.
//
// The lockstep is the CHAIN (domain.go powChain): each domain's unfold proves
// `pow(m, c) = m·(m·(…·1))`, the untrusted extraction reads that same chain,
// and ring.go's normalizeProof asserts the unfold's right-hand side against
// it — so a drift in either half is a loud panic, never a silent divergence
// between the model and the certificate.
//
// num reads `nat_pow(t, c)` the same way, through its own chain unfold
// (nat_exp.go natPowChainUnfold): `expUnfold`, the simp step's unfold, shortcuts
// c=1 and c=2 to their own shapes (`m` and `m·m`) rather than the uniform
// chain, so the basis takes a separate unfold that proves the chain for every
// c. The bounded-variable enumeration (nat_exp.go) keys on a comparison whose
// side is nonlinear, which a product monomial still is, so `x·x ≤ 4` under
// `x ≤ 2` is enumerated as before.
//
// The wiring is an init rather than a struct literal because each ring names
// its own domain: naming the ring back inside the domain's literal would be an
// initialization cycle (the same reason polyMul is wired here-style).
func init() {
	natRing.powUnfold = natPowChainUnfold
	realRing.powUnfold = realPowUnfold
	intRing.powUnfold = intPowUnfold
}
