package utils

import "sync"

// Wrap a sync Map with type check.
type Map[K comparable, V any] struct{ sync.Map }

// Load returns the value stored in the map for a key, or the zero value if no
// value is present.
// The ok result indicates whether value was found in the map.
func (m *Map[K, V]) Load(key K) (value V, ok bool) {
	if v, ok := m.Map.Load(key); ok {
		return v.(V), true
	}
	return value, false
}

// Store sets the value for a key.
func (m *Map[K, V]) Store(key K, value V) { m.Map.Store(key, value) }

// LoadOrStore returns the existing value for the key if present.
// Otherwise, it stores and returns the given value.
// The loaded result is true if the value was loaded, false if stored.
func (m *Map[K, V]) LoadOrStore(key K, value V) (actual V, loaded bool) {
	v, ok := m.Map.LoadOrStore(key, value)
	return v.(V), ok
}

// LoadAndDelete deletes the value for a key, returning the previous value if any.
// The loaded result reports whether the key was present.
func (m *Map[K, V]) LoadAndDelete(key K) (value V, loaded bool) {
	if v, ok := m.Map.LoadAndDelete(key); ok {
		return v.(V), ok
	}
	var v V
	return v, false
}

// Delete deletes the value for a key.
func (m *Map[K, V]) Delete(key K) { m.Map.Delete(key) }

// Range calls f sequentially for each key and value present in the map.
func (m *Map[K, V]) Range(f func(K, V) bool) {
	m.Map.Range(func(key, value any) bool { return f(key.(K), value.(V)) })
}

// Copy
func (m *Map[K, V]) Copy(dest *Map[K, V]) {
	for key, value := range m.Map.Range {
		dest.Store(key.(K), value.(V))
	}
}

// Clear
func (m *Map[K, V]) Clear() {
	for key := range m.Map.Range {
		m.Map.Delete(key)
	}
}

// Size
func (m *Map[K, V]) Size() int {
	size := 0
	for range m.Map.Range {
		size++
	}
	return size
}
