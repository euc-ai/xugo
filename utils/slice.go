package utils

import (
	"slices"
	"sync"
)

func Last[S ~[]T, T any](s S) T { return s[len(s)-1] }

func BeforeLast[S ~[]T, T any](s S) S { return s[:len(s)-1] }

func Clone[S ~[]T, T any](s S) S {
	if s == nil {
		return nil
	}
	dst := make(S, len(s))
	copy(dst, s)
	return dst
}

func CloneAppend[S ~[]T, T any](s S, e T) S {
	if s == nil {
		return S{e}
	}
	dst := make(S, len(s)+1)
	copy(dst, s)
	dst[len(s)] = e
	return dst
}

func MapSlice[S ~[]In, In, Out any](s S, f func(In) Out) []Out {
	if s == nil {
		return nil
	}
	t := make([]Out, len(s))
	for i := range s {
		t[i] = f(s[i])
	}
	return t
}

func MapSliceAsync[S ~[]In, In, Out any](s S, f func(In) Out) []Out {
	if s == nil {
		return nil
	}
	t := make([]Out, len(s))
	wg := sync.WaitGroup{}
	for i := range s {
		wg.Go(func() { t[i] = f(s[i]) })
	}
	wg.Wait()
	return t
}

func Foldl[S ~[]T, T, U any](f func(U, T) U, init U, s S) U {
	acc := init
	for i := range s {
		acc = f(acc, s[i])
	}
	return acc
}

func Foldr[S ~[]T, T, U any](f func(U, T) U, init U, s S) U {
	acc := init
	for i := len(s) - 1; i >= 0; i-- {
		acc = f(acc, s[i])
	}
	return acc
}

// whether l0 ⊆ l1
func IsSubset[S ~[]T, T any](s0, s1 S, eq func(T, T) bool) bool {
	return All(s0, func(t T) bool { return Any(s1, Curry(eq, t)) })
}

// whether s0 ⊆ s1, both ORDERED and deduplicated by compare (the
// precondition OrderedSlicesUnion takes). One merge — each slice is
// walked once, len(s0) + len(s1) comparisons, and a missing element
// ends it — where IsSubset, which knows only equality, scans s1 per
// element of s0.
func OrderedSlicesSubset[S ~[]T, T any](s0, s1 S, compare func(T, T) int) bool {
	j := 0
	for _, t := range s0 {
		for {
			if j == len(s1) {
				return false
			}
			if c := compare(s1[j], t); c > 0 {
				return false
			} else {
				j++
				if c == 0 {
					break
				}
			}
		}
	}
	return true
}

// l0 ∪ l1. l0 and l1 must be ordered and deduplicated.
func OrderedSlicesUnion[S ~[]T, T any](
	s0, s1 S,
	eq func(T, T) bool,
	compare func(T, T) int) S {
	if len(s1) > len(s0) {
		s0, s1 = s1, s0
	}
	if len(s1) == 0 {
		return s0
	}
	i, found := slices.BinarySearchFunc(s0, s1[0], compare)
	if found {
		if len(s1) == 1 {
			return s0
		}
		return append(s0[:i+1], OrderedSlicesUnion(s0[i+1:], s1[1:], eq, compare)...)
	}
	if len(s1) == 1 {
		return slices.Insert(s0, i, s1[0])
	}
	return append(s0[:i],
		append(S{s1[0]}, OrderedSlicesUnion(s0[i:], s1[1:], eq, compare)...)...)
}
