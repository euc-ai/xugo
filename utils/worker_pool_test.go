package utils

import (
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

func TestBasicWorkerPool(t *testing.T) {
	defer goleak.VerifyNone(t)
	numWorkers := 4
	pool := NewWorkerPool(numWorkers)

	for i := range numWorkers {
		pool.Go(func() { time.Sleep(time.Duration(i) * 100 * time.Millisecond) })
	}
	start := time.Now()

	// extra job
	done := make(chan struct{})
	pool.Go(func() { close(done) })

	assert.Equal(t, <-done, struct{}{})

	// Wait can be called multiple times.
	pool.Wait()
	pool.Wait()

	// Trying to add a task after Wait() should not panic and not run.
	assert.NotPanics(t, func() { pool.Go(func() { panic("") }) })

	// The longest job took numWorkers-1 seconds.
	assert.Greater(t, time.Since(start), 100*time.Millisecond*time.Duration(numWorkers-1))
	assert.Less(t, time.Since(start), 100*time.Millisecond*time.Duration(numWorkers))
}

func TestWorkerPoolWithResChan(t *testing.T) {
	defer goleak.VerifyNone(t)
	numWorkers := 4
	results := make(chan int, 10)
	pool := NewWorkerPoolWithResChan(numWorkers, results)

	// Submit tasks that produce results
	for i := range numWorkers {
		taskID := i
		pool.Go(func() {
			time.Sleep(time.Duration(taskID) * 100 * time.Millisecond)
			results <- taskID
		})
	}
	start := time.Now()

	// extra job with result
	pool.Go(func() { results <- 999 })

	pool.CloseAsync()

	// Collect all results after CloseAsync() is called
	var collectedResults []int
	for result := range results {
		collectedResults = append(collectedResults, result)
	}

	// Check that we got all expected results
	assert.Len(t, collectedResults, numWorkers+1)
	assert.Contains(t, collectedResults, 999) // extra job result

	// Trying to add a task after CloseAsync() should not panic and not run.
	assert.NotPanics(t, func() { pool.Go(func() { panic("") }) })

	// The longest job took numWorkers-1 seconds.
	assert.Greater(t, time.Since(start), 100*time.Millisecond*time.Duration(numWorkers-1))
	assert.Less(t, time.Since(start), 100*time.Millisecond*time.Duration(numWorkers))

	// Channel should be closed after CloseAsync()
	select {
	case _, ok := <-results:
		assert.False(t, ok, "Result channel should be closed")
	default:
		t.Fatal("Result channel should be closed and readable")
	}
}

func TestTaskExecution(t *testing.T) {
	defer goleak.VerifyNone(t)

	const numWorkers = 3
	const numTasks = 10
	pool := NewWorkerPool(numWorkers)
	defer pool.Wait()

	var counter int64

	// Add multiple tasks
	for range numTasks {
		pool.Go(func() {
			atomic.AddInt64(&counter, 1)
			time.Sleep(10 * time.Millisecond) // Simulate work
		})
	}
	pool.Wait()
	assert.Equal(t, int64(numTasks), atomic.LoadInt64(&counter))
}

func TestTaskAddedBeforeWait(t *testing.T) {
	defer goleak.VerifyNone(t)

	pool := NewWorkerPool(1)
	var counter int64

	// task 1 to block the queue for a while.
	pool.Go(func() {
		atomic.AddInt64(&counter, 1)
		time.Sleep(100 * time.Millisecond)
	})

	// task 2 to be executed
	pool.Go(func() { atomic.AddInt64(&counter, 1) })

	time.Sleep(10 * time.Millisecond)

	// close the pool after the 2nd task is added
	// but before the 2nd task is executed
	assert.Equal(t, int64(1), atomic.LoadInt64(&counter))
	pool.Wait()

	// the 2nd task should be executed
	assert.Equal(t, int64(2), atomic.LoadInt64(&counter))
}

func TestConcurrentAddTask(t *testing.T) {
	defer goleak.VerifyNone(t)

	const numWorkers = 5
	const numGoroutines = 10
	const tasksPerGoroutine = 50

	pool := NewWorkerPool(numWorkers)

	var counter int64
	var wg sync.WaitGroup

	// Launch multiple goroutines that add tasks concurrently
	for range numGoroutines {
		wg.Go(func() {
			for range tasksPerGoroutine {
				pool.Go(func() { atomic.AddInt64(&counter, 1) })
			}
		})
	}

	// Wait for all task submitters to finish
	wg.Wait()
	// Close pool after all tasks are submitted and completed
	pool.Wait()

	expectedTasks := int64(numGoroutines * tasksPerGoroutine)
	assert.Equal(t, expectedTasks, atomic.LoadInt64(&counter))
}

func TestZeroWorkers(t *testing.T) {
	defer goleak.VerifyNone(t)

	pool := NewWorkerPool(0)
	defer pool.Wait()

	// Adding a task to a pool with 0 workers should not deadlock
	// but the task should never execute
	var executed bool

	done := make(chan struct{})
	go func() {
		pool.Go(func() { executed = true })
		close(done)
	}()

	select {
	case <-done:
		// Task was added successfully
	case <-time.After(100 * time.Millisecond):
		t.Fatal("AddTask should not block with 0 workers")
	}

	time.Sleep(50 * time.Millisecond)
	assert.False(t, executed, "Task should not execute with 0 workers")
}

func TestSingleWorker(t *testing.T) {
	defer goleak.VerifyNone(t)

	pool := NewWorkerPool(1)
	defer pool.Wait()

	var order []int
	var mu sync.Mutex

	for i := range 5 {
		taskID := i
		pool.Go(func() {
			mu.Lock()
			order = append(order, taskID)
			mu.Unlock()
			time.Sleep(10 * time.Millisecond)
		})
	}

	pool.Wait()
	assert.Len(t, order, 5)
	// With single worker, tasks should execute in order
	assert.Equal(t, []int{0, 1, 2, 3, 4}, order)
}

// Benchmark Tests

func BenchmarkHighThroughput(b *testing.B) {
	const numWorkers = 8
	pool := NewWorkerPool(numWorkers)
	defer pool.Wait()

	b.ResetTimer()
	for b.Loop() {
		pool.Go(func() {
			// Simulate very light work
			for j := range 100 {
				_ = j * j
			}
		})
		pool.Wait()
	}
}

func BenchmarkPoolBurstyLoad(b *testing.B) {
	const poolSize = 4
	const burstSize = 20

	pool := NewWorkerPool(poolSize)
	defer pool.Wait()

	b.ResetTimer()
	for b.Loop() {

		// Submit burst of tasks
		for range burstSize {
			pool.Go(func() { time.Sleep(time.Microsecond) })
		}
		pool.Wait()
	}
}

// Stress and Concurrency Tests

func TestStressTest(t *testing.T) {
	defer goleak.VerifyNone(t)

	const numWorkers = 10
	const numTasks = 1000
	const numIterations = 10

	for range numIterations {
		pool := NewWorkerPool(numWorkers)

		var counter int64

		// Submit many tasks concurrently
		for range numTasks {
			pool.Go(func() {
				atomic.AddInt64(&counter, 1)
				// Simulate variable work duration
				time.Sleep(time.Duration(atomic.LoadInt64(&counter)%5) * time.Millisecond)
			})
		}

		pool.Wait()

		assert.Equal(t, int64(numTasks), atomic.LoadInt64(&counter))
	}
}

func TestRaceConditions(t *testing.T) {
	defer goleak.VerifyNone(t)

	pool := NewWorkerPool(5)
	defer pool.Wait()

	const numGoroutines = 50
	const tasksPerGoroutine = 20

	var wg sync.WaitGroup
	var counter int64

	// Launch many goroutines that add tasks and close pool concurrently
	for range numGoroutines {
		wg.Go(func() {
			for range tasksPerGoroutine {
				pool.Go(func() {
					atomic.AddInt64(&counter, 1)
				})
			}
		})
	}

	// Start a goroutine that tries to close the pool
	go func() {
		time.Sleep(50 * time.Millisecond)
		pool.Wait() // This should not race with AddTask
	}()

	wg.Wait()

	// Some tasks might be discarded due to shutdown, so counter <= expected
	expected := int64(numGoroutines * tasksPerGoroutine)
	actual := atomic.LoadInt64(&counter)
	assert.LessOrEqual(t, actual, expected)
}

func TestMemoryLeaks(t *testing.T) {
	defer goleak.VerifyNone(t)

	// Create and destroy many pools to check for leaks
	for range 100 {
		pool := NewWorkerPool(2)

		for range 5 {
			pool.Go(func() { time.Sleep(time.Millisecond) })
		}

		pool.Wait()
	}
}
