// Package utils is the general-purpose helpers the rest of the module
// shares: slices, maps, sets, iterators, predicates and function
// combinators, name and string helpers, and the concurrency helpers —
// a worker pool and the channel and context utilities.
package utils

import (
	"fmt"
	"path/filepath"
	"reflect"
	"runtime"
	"slices"
	"strings"
	"sync"
)

// AssertionFailed is the text every failed Assert panics with, followed
// by the site of the Assert call.
const AssertionFailed = "Should not happen."

// Assert panics when assertion is false. The panic value names the
// caller's function and file:line, so a reader who meets the failure
// through a recover that prints the value alone can locate it.
func Assert(assertion bool) {
	if !assertion {
		panic(AssertionFailed + " " + assertionSite(2))
	}
}

// IsAssertionFailure reports whether a recovered panic value is a
// failed assertion: Assert's value, or the bare AssertionFailed text
// an invariant check in ext panics with. A recover that reads a panic
// as an ordinary failure raises one of these again, since a success
// after it would hide the breach.
func IsAssertionFailure(r any) bool {
	s, ok := r.(string)
	return ok && strings.HasPrefix(s, AssertionFailed)
}

// assertionSite names the frame skip levels above it as
// "(at <file>:<line> in <function>)".
func assertionSite(skip int) string {
	pc, file, line, ok := runtime.Caller(skip)
	if !ok {
		return "(at an unknown site)"
	}
	function := "an unknown function"
	if f := runtime.FuncForPC(pc); f != nil {
		function = f.Name()
	}
	return fmt.Sprintf("(at %s:%d in %s)", filepath.Base(file), line, function)
}

// thisPackage is the import path of this package, as the runtime
// spells it in a function's name.
var thisPackage = strings.TrimSuffix(
	runtime.FuncForPC(reflect.ValueOf(Assert).Pointer()).Name(), ".Assert")

// PanicSite names the frame a panic in flight was raised from, for the
// deferred function that recovers it: "<file>:<line> in <function>" of
// the frame under runtime.gopanic that belongs neither to the runtime
// nor to this package (an Assert names its own caller). A recover on the
// way that raised the panic again is not where it came from: among the
// raises still on the stack the site is the first one's.
func PanicSite() string {
	pc := make([]uintptr, 256)
	frames := runtime.CallersFrames(pc[:runtime.Callers(1, pc)])
	site := "an unknown site"
	underPanic := false
	for {
		f, more := frames.Next()
		switch {
		case f.Function == "runtime.gopanic":
			underPanic = true
		case underPanic && !strings.HasPrefix(f.Function, "runtime.") && !strings.HasPrefix(f.Function, thisPackage+"."):
			site = fmt.Sprintf("%s:%d in %s", filepath.Base(f.File), f.Line, f.Function)
			underPanic = false
		}
		if !more {
			return site
		}
	}
}

func OneOf(v ...bool) bool {
	Assert(len(v) > 1)
	if len(v) == 2 {
		return v[0] != v[1]
	}
	if v[0] {
		return !slices.Contains(v[1:], true)
	}
	return OneOf(v[1:]...)
}

type Lazy[T any] struct {
	val T
	sync.Once
}

func (l *Lazy[T]) InitOrLoad(val func() T) T {
	l.Once.Do(func() { l.val = val() })
	return l.val
}

func SubIndices(n, lenThres int) (res [][]int) {
	if lenThres > n {
		return
	}
	subIndicesRecur(0, n, lenThres, nil, &res)
	return res
}

func subIndicesRecur(start, n, lenThres int, current []int, res *[][]int) {
	if len(current) >= lenThres {
		// Add the current slice to results
		*res = append(*res, Clone(current))
	}

	for i := start; i < n; i++ {
		// Include the current element and generate further combinations
		subIndicesRecur(i+1, n, lenThres, append(current, i), res)
	}
}
