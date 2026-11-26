package utils

import "slices"

type Predicate[T any] func(T) bool

func EmptyPredicate[T any](T) bool { return false }

func FullPredicate[T any](T) bool { return true }

func Disjunct[T any](f, g Predicate[T]) Predicate[T] {
	return func(t T) bool { return f(t) || g(t) }
}

func Any[S ~[]T, T any](s S, f Predicate[T]) bool {
	return slices.ContainsFunc(s, f)
}

func None[S ~[]T, T any](s S, f Predicate[T]) bool { return !Any(s, f) }

func All[S ~[]T, T any](s S, f Predicate[T]) bool {
	for i := range s {
		if !f(s[i]) {
			return false
		}
	}
	return true
}
