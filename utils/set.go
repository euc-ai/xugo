package utils

import "maps"

type Set[T comparable] map[T]struct{}

func EmptySet[T comparable]() Set[T] { return make(map[T]struct{}) }

func (s Set[T]) Has(v T) bool {
	_, ok := s[v]
	return ok
}

func (s Set[T]) Add(v T) { s[v] = struct{}{} }

func (s Set[T]) Delete(v T) { delete(s, v) }

func (s Set[T]) Merge(t Set[T]) { maps.Copy(s, t) }

func (s Set[T]) Clone() Set[T] { return maps.Clone(s) }

func (s Set[T]) Size() int { return len(s) }

func (s Set[T]) Equals(t Set[T]) bool { return maps.Equal(s, t) }
