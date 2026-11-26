// proof_policy.go — startup hook for the canonical proof-policy table.
//
// InstallProofPolicy hands library/integrity/policy's generated table to
// proof.NewStaticProofScope's query API. Sibling to InstallNatBundle /
// InstallRealBundle: the table is corpus content, its consumer is tent
// machinery, and the tent never imports library/ — so it is installed,
// not imported.
//
// Callers: the engine's initEngine, and the TestMains of the replay
// harnesses. NOT manifest.Build — that is the path policy_gen itself
// runs to COMPUTE the table, and it must work with none installed.

package serve

import "github.com/euc-ai/xugo/library/integrity/policy"

// InstallProofPolicy installs the canonical proof-policy table. Idempotent.
func InstallProofPolicy() { policy.Install() }
