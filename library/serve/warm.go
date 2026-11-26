// Bundle warm-up: settling every installed bundle field's root promise
// under a trust frontier before any proof's force runs.
//
// Each bundle field is a promise (PromiseForGeneral's, EntryThm's, or a
// derivation over them), unforced in a fresh process until some proof's
// final force reaches it. core.deriveProp makes a derivation lazy the
// moment one of its dependencies is an unforced promise, and everything
// derived from it inherits that; so the first arithmetic-heavy proof in a
// process builds its whole proof as a lazy DAG, retained until its force —
// measured on eudoxus_slope.Mul: 569,651 derived cells forced, a 1.4 GB live heap
// pinned at the harness's memory limit, 4.4 s and 20 CPU-s, against
// 107,132 cells, 200 MB, 1.3 s and 3 CPU-s once any earlier proof had
// settled the eight fields it reads. Settling the fields first, under the
// corpus trust frontier the harness already forces under, makes every
// proof in the process derive eagerly.
//
// The frontier is the harness's: a field's root entries settle from their
// statements, each verified by its own replay, and every certificate that
// comes to stand on such a settle lists it (core's ThmCert.Assumes) —
// what a replay holds a member's certificates to. A warm-up must not hide
// a field no corpus theorem backs: a builder that panics fails the
// warm-up by name, where an unconsumed field would otherwise never be
// forced (two int fields stood unbuildable that way).

package serve

import (
	"context"
	"errors"
	"fmt"
	"reflect"
	"sort"
	"sync"

	"github.com/euc-ai/xugo/core"
)

// installedBundle is one installed bundle struct with the provenance
// table its install declared (computeBundleCapability's overrides).
type installedBundle struct {
	name      string
	bundle    any
	overrides map[string][]core.PropKey
}

var (
	installedMu      sync.Mutex
	installedBundles = map[string]installedBundle{}
)

// noteInstalledBundle records b, keyed by its type, replacing an earlier
// install of the same bundle: the bundle a warm-up reads is the one
// omega reads.
func noteInstalledBundle(b any, overrides map[string][]core.PropKey) {
	name := reflect.TypeOf(b).Elem().Name()
	installedMu.Lock()
	defer installedMu.Unlock()
	installedBundles[name] = installedBundle{name: name, bundle: b, overrides: overrides}
}

// WarmReport says what a warm-up did, for a harness log line.
type WarmReport struct {
	Forced  int // fields settled by this call
	Settled int // fields already settled (a certificate, or forced earlier)
}

// WarmBundles forces every installed bundle field under the trust
// frontier `trusted`. A field whose builder panics (no corpus theorem
// backs it, or its reconstruction does not deliver its statement) is an
// error naming the field, "<Bundle>.<Field>"; the other fields are still
// warmed, and the errors are joined. Idempotent: a settled field is
// counted, not forced again.
func WarmBundles(ctx context.Context, trusted core.PropPredicate) (WarmReport, error) {
	installedMu.Lock()
	bundles := make([]installedBundle, 0, len(installedBundles))
	for _, b := range installedBundles {
		bundles = append(bundles, b)
	}
	installedMu.Unlock()
	sort.Slice(bundles, func(i, j int) bool { return bundles[i].name < bundles[j].name })

	var report WarmReport
	var errs []error
	for _, b := range bundles {
		for _, f := range bundleFields(b.bundle, b.overrides) {
			promise, isPromise := f.wrapper.Core().(core.ThmPromise)
			if !isPromise || promise.Proved() {
				report.Settled++
				continue
			}
			if err := forceField(ctx, b.name+"."+f.field, promise, trusted); err != nil {
				errs = append(errs, err)
				continue
			}
			report.Forced++
		}
	}
	return report, errors.Join(errs...)
}

// forceField settles one field under the frontier. A panic on the way —
// a field no corpus theorem backs, a reconstruction that does not
// deliver its statement — is reported as the field's.
func forceField(ctx context.Context, field string, promise core.ThmPromise, trusted core.PropPredicate) (err error) {
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("bundle warm-up: field %s: %v", field, r)
		}
	}()
	core.ForceWithBoundary(ctx, promise, trusted)
	return nil
}

// String renders a report for a log line.
func (r WarmReport) String() string {
	return fmt.Sprintf("%d fields forced, %d already settled", r.Forced, r.Settled)
}
