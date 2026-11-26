// fan_out_test.go — the corpus-wide gates' questions asked on every
// processor.
//
// A gate that asks one question of every member — a normalization, a
// parse, a spelling — asks it once per member, and the answers do not
// depend on one another. fanOut asks them on every
// processor and hands the answers back in the members' order, so the
// gate reports the same lines in the same order it would report asking
// them one at a time.
package gates

import (
	"runtime"
	"sync"
)

// fanOut applies f to every item on every processor and returns the
// results in the items' order. f runs on a goroutine of its own: it
// returns what the gate reports and calls nothing on the *testing.T.
func fanOut[T, R any](items []T, f func(T) R) []R {
	out := make([]R, len(items))
	next := make(chan int)
	var wg sync.WaitGroup
	for range runtime.GOMAXPROCS(0) {
		wg.Go(func() {
			for i := range next {
				out[i] = f(items[i])
			}
		})
	}
	for i := range items {
		next <- i
	}
	close(next)
	wg.Wait()
	return out
}
