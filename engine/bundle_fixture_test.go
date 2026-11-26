package engine

import (
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/solver/omega"
)

// The engine tests run serially. A corpus bundle stays installed across
// fixtures until a test replaces it through the matching setter below.
// This shares immutable theorem bindings, not session caches or state.
var testNatBundleInstalled, testRealBundleInstalled bool

func installTestNatBundle() {
	if !testNatBundleInstalled {
		serve.InstallNatBundle()
		testNatBundleInstalled = true
	}
}

func setTestNatBundle(bundle *omega.NatLemmaBundle) {
	testNatBundleInstalled = false
	omega.SetNatLemmaBundle(bundle)
}

func installTestRealBundle() {
	if !testRealBundleInstalled {
		serve.InstallRealBundle()
		testRealBundleInstalled = true
	}
}

func setTestRealBundle(bundle *omega.RealLemmaBundle) {
	testRealBundleInstalled = false
	omega.SetRealLemmaBundle(bundle)
}
