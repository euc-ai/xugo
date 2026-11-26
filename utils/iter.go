package utils

import "iter"

func EmptyIter[T any](func(T) bool) {}

func SingleIter[T any](e T) iter.Seq[T] {
	return func(yield func(T) bool) { yield(e) }
}

func ConcatIter[T any](seqs ...iter.Seq[T]) iter.Seq[T] {
	return func(yield func(T) bool) {
		for _, seq := range seqs {
			for e := range seq {
				if !yield(e) {
					return
				}
			}
		}
	}
}

func ConcatSeqIter[T any](seqs iter.Seq[iter.Seq[T]]) iter.Seq[T] {
	return func(yield func(T) bool) {
		for seq := range seqs {
			for e := range seq {
				if !yield(e) {
					return
				}
			}
		}
	}
}

func FilterIter[T any](seq iter.Seq[T], exclude Predicate[T]) iter.Seq[T] {
	return func(yield func(T) bool) {
		for e := range seq {
			// exclusion should be checked before yield.
			if !exclude(e) && !yield(e) {
				return
			}
		}
	}
}

func MapIter[In, Out any](seq iter.Seq[In], f func(In) Out) iter.Seq[Out] {
	return func(yield func(Out) bool) {
		for e := range seq {
			if !yield(f(e)) {
				return
			}
		}
	}
}

func IterFirst[T any](s iter.Seq[T]) T {
	var zero T
	for e := range s {
		return e
	}
	return zero
}

func EnumerateIter[T any](s iter.Seq[T]) iter.Seq2[int, T] {
	return func(yield func(int, T) bool) {
		i := 0
		for e := range s {
			if !yield(i, e) {
				return
			}
			i++
		}
	}
}
