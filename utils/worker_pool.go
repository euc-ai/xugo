// worker_pool.go — goroutine pool implementations for concurrent task execution.
// A fixed-size goroutine pool that pre-allocates a fixed number of worker goroutines.
//   - Best for: Stable, continuous workloads with predictable task volumes
//   - Characteristics: Low latency, fixed memory usage, immediate task execution
//   - Use case: High-throughput systems with consistent load
//
// Example usage:
//
//	pool := NewWorkerPool(5)
//	defer pool.Wait()
//	pool.Go(func() { fmt.Println("pool task") })

package utils

import "sync"

// _WorkerPool represents a fixed-size goroutine pool implementation.
//
// This pool maintains a constant number of worker goroutines throughout its lifetime.
// All workers are created during initialization and remain active until the pool is closed.
//
// Key characteristics:
// - Fixed number of workers: Workers are pre-allocated and never change
// - Low latency: Tasks can be executed immediately if queue has space
// - Predictable resource usage: Memory and goroutine count remain constant
// - Graceful shutdown: Waits for all workers to complete before closing
//
// Best suited for:
// - Applications with consistent, high-volume task loads
// - Systems requiring predictable performance characteristics
// - Scenarios where resource allocation can be predetermined
//
// Trade-offs:
// - Uses more resources during idle periods
// - Cannot scale beyond initial worker count
// - May waste resources if load is consistently lower than capacity
type _WorkerPool struct {
	queue          chan func()   // Buffered channel for task queue
	shutdown       chan struct{} // Signal channel for shutdown coordination
	sync.WaitGroup               // Tracks active worker goroutines
	sync.Once                    // Ensures shutdown logic runs only once
}

// NewWorkerPool creates a new fixed-size goroutine pool with the specified number of workers.
//
// The pool immediately spawns numWorker goroutines that will continuously listen for tasks.
// The task queue is buffered with the same capacity as the number of workers.
//
// Parameters:
//   - numWorker: The fixed number of worker goroutines to create and maintain
//
// Returns:
//   - *_WorkerPool: A new pool instance ready to accept tasks
func NewWorkerPool(numWorker int) *_WorkerPool {
	pool := &_WorkerPool{
		queue:    make(chan func(), numWorker), // Buffered channel for task storage
		shutdown: make(chan struct{}),          // Unbuffered channel for shutdown signaling
	}

	// Start worker goroutines
	for range numWorker {
		pool.WaitGroup.Go(func() {
			// Continuously process tasks until queue is closed
			for task := range pool.queue {
				task()
			}
		})
	}
	return pool
}

// Go submits a task to the pool for execution.
//
// The task will be executed by one of the worker goroutines. This method
// guarantees that tasks are never silently discarded while the pool is active.
//
// Parameters:
//   - task: A function to be executed by a worker goroutine
//
// Behavior:
//   - Blocks if queue is full until a worker becomes available (guaranteed execution)
//   - Returns immediately if pool is shut down (task is silently discarded)
//   - Returns immediately for zero-worker pools (task is silently discarded)
//   - Thread-safe: can be called concurrently from multiple goroutines
//
// Note: Tasks are only discarded in two cases:
//  1. Pool has been shut down via Wait()
//  2. Pool was created with zero workers (no workers to execute tasks)
func (pool *_WorkerPool) Go(task func()) {
	// Handle zero-worker pools immediately
	if cap(pool.queue) == 0 {
		return // No workers to process tasks, discard immediately
	}

	select {
	case <-pool.shutdown:
		// Pool is shut down, discard the task
	default:
		pool.queue <- task
		// Successfully sent task to queue
	}
}

// Wait gracefully shuts down the pool after all tasks are completed.
//
// This method ensures that:
// 1. No new tasks are accepted (shutdown channel is closed)
// 2. The task queue is closed to signal workers to exit
// 3. All worker goroutines complete their current tasks and exit
// 4. The method blocks until all workers have finished
//
// Wait is safe to call multiple times - subsequent calls will have no effect.
// After Wait returns, all worker goroutines have terminated and no more tasks
// will be processed.
func (pool *_WorkerPool) Wait() {
	pool.Once.Do(func() {
		close(pool.shutdown) // Signal that pool is shutting down
		close(pool.queue)    // Close task queue to make workers exit
	})
	pool.WaitGroup.Wait() // Wait for all workers to complete
}

// _WorkerPoolWithResChan is a wrapper around _WorkerPool that manages a result channel.
//
// This wrapper extends the basic worker pool functionality by automatically handling
// the lifecycle of a result channel. It ensures that the result channel is properly
// closed when the pool shuts down, providing a clean interface for collecting results
// from worker tasks.
//
// Usage pattern:
//
//		results := make(chan MyResult, 100)
//		pool := NewWorkerPoolWithResChan(5, results)
//
//		// Submit tasks that send results to the channel
//		pool.Go(func() { results <- processData() })
//
//		// The result channel will be closed when all work in the pool is done.
//		pool.CloseAsync()
//
//	 // Start consuming results from the channel
//	 for result := range results { ... }
type _WorkerPoolWithResChan[T any] struct {
	*_WorkerPool          // Embedded worker pool for task execution
	resChan      chan<- T // Result channel to be closed on shutdown
}

// NewWorkerPoolWithResChan creates a new worker pool with automatic result channel management.
//
// The pool will manage the lifecycle of the provided result channel, ensuring it is
// properly closed when the worker pool shuts down. This enables clean producer-consumer
// patterns where the channel closure signals completion to consumers.
//
// Parameters:
//   - numWorker: The fixed number of worker goroutines to create and maintain
//   - resChan: A send-only channel that will be closed when the pool shuts down
//
// Returns:
//   - *_WorkerPoolWithResChan[T]: A new pool instance ready to accept tasks and manage results
func NewWorkerPoolWithResChan[T any](numWorker int, resChan chan<- T) *_WorkerPoolWithResChan[T] {
	pool := &_WorkerPoolWithResChan[T]{
		_WorkerPool: NewWorkerPool(numWorker),
		resChan:     resChan,
	}
	return pool
}

// CloseAsync waits for the pool to finish and closes the result channel.
//
// This method extends the base _WorkerPool.Wait() behavior by automatically closing
// the managed result channel after all workers have completed. The channel closure
// happens in a separate goroutine, allowing this method to return immediately.
//
// Behavior:
// 1. Returns immediately (non-blocking)
// 2. Starts background goroutine that:
//   - Waits for all worker tasks to complete
//   - Closes the result channel to signal completion to consumers
//
// This design allows the calling code to immediately start consuming results
// from the channel while the pool shuts down in the background. The channel
// will be closed when all tasks are complete, providing a clean termination signal.
//
// CloseAsync is unsafe to call multiple times as it closes the result channel.
func (pool *_WorkerPoolWithResChan[T]) CloseAsync() {
	go func() {
		pool._WorkerPool.Wait()
		close(pool.resChan)
	}()
}
