package utils

type EndoFunc[T any] = func(T) T

// IdentityFunc is a function that returns its input.
func IdentityFunc[T any](e T) T { return e }

func Curry[F ~func(T, S) V, T, S, V any](f F, s S) func(T) V {
	return func(t T) V { return f(t, s) }
}

func ChainFunc[S ~EndoFunc[T], T any](funcs []S) S {
	return func(p T) T {
		for _, f := range funcs {
			p = f(p)
		}
		return p
	}
}

func RevChainFunc[S ~EndoFunc[T], T any](funcs []S) S {
	return func(p T) T {
		for j := len(funcs) - 1; j >= 0; j-- {
			p = funcs[j](p)
		}
		return p
	}
}
