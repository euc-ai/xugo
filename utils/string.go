package utils

import (
	"fmt"
	"io"
	"strconv"
	"strings"
	"sync"
	"unicode"
	"unicode/utf8"

	"github.com/cespare/xxhash/v2"
)

const (
	EqStr        = "="
	HilbertStr   = "ε"
	TrueStr      = "⊤"
	FalseStr     = "⊥"
	NegStr       = "¬"
	AndStr       = "∧"
	OrStr        = "∨"
	ImplyStr     = "⇒"
	ForAllStr    = "∀"
	ExistsStr    = "∃"
	UniqueStr    = "∃!"
	NeqStr       = "≠"
	IffStr       = "⇔"
	XorStr       = "⊕"
	FunStr       = "→"
	MapStr       = "↦"
	TurnstileStr = "⊢"
	PrimeStr     = "ʹ"
	MacronStr    = "ˍ"
	PercentStr   = "%"
	Underscore   = "_"
	AlphaStr     = "α"
	LambdaStr    = "λ"

	F_HOOK   = "ƒ"
	X_DOT    = "ẋ"
	H_STROKE = "ħ"
	Z_STROKE = "ƶ"
)

func padInt(width int, n int) string {
	s := strconv.Itoa(n)
	if len(s) >= width {
		return s
	}
	return strings.Repeat("0", width-len(s)) + s
}

// s => (bodyRaw, underscore, num, ok)
// regex: ^((\d+)?(\p{L}+)+)?(_)?(\d*)$
func parseParts(s string) (bodyRaw, underscore, num string, ok bool) {
	i := 0
	n := len(s)

	// try to parse body: [digits*][letters+]
	j := i
	// digits*
	for j < n {
		r, sz := utf8.DecodeRuneInString(s[j:])
		if '0' <= r && r <= '9' {
			j += sz
		} else {
			break
		}
	}
	// letters+  (at least one Unicode Letter)
	k, sawLetter := j, false
	for k < n {
		r, sz := utf8.DecodeRuneInString(s[k:])
		if unicode.IsLetter(r) {
			sawLetter = true
			k += sz
		} else {
			break
		}
	}
	if sawLetter {
		bodyRaw = s[i:k]
		i = k
	}

	// optional underscore
	if i < n {
		r, sz := utf8.DecodeRuneInString(s[i:])
		if r == '_' {
			underscore = Underscore
			i += sz
		}
	}

	// trailing digits*
	numStart := i
	for i < n {
		r, sz := utf8.DecodeRuneInString(s[i:])
		if '0' <= r && r <= '9' {
			i += sz
		} else {
			// invalid character => not match
			return "", "", "", false
		}
	}
	num = s[numStart:]

	// must match the whole string
	return bodyRaw, underscore, num, true
}

func NextName[T ~string](s T) T {
	Assert(!strings.HasPrefix(string(s), PercentStr))

	bodyRaw, underscore, numStr, ok := parseParts(string(s))
	if !ok {
		return s + PrimeStr
	}

	// bodyRaw = body + primes(if any), cut the tail PRIME:
	body := strings.TrimRight(bodyRaw, PrimeStr)
	prime := strings.TrimPrefix(bodyRaw, body)

	if num, err := strconv.Atoi(numStr); err == nil {
		numDigits := len(numStr)
		var b strings.Builder
		b.Grow(len(body) + len(prime) + len(underscore) + numDigits)
		b.WriteString(body)
		b.WriteString(prime)
		b.WriteString(underscore)
		b.WriteString(padInt(numDigits, num+1))
		return T(b.String())
	}

	// only "_" case
	if len(body) == 0 {
		return s + "0"
	}

	// last rune of body
	r, size := utf8.DecodeLastRuneInString(body)
	rest := body[:len(body)-size]

	suffix := prime + underscore + numStr

	switch r {
	case 'H':
		return T(rest + "A" + PrimeStr + suffix)
	case 'h':
		return T(rest + "a" + PrimeStr + suffix)
	case 'J':
		return T(rest + "I" + PrimeStr + suffix)
	case 'j':
		return T(rest + "i" + PrimeStr + suffix)
	case 'N':
		return T(rest + "K" + PrimeStr + suffix)
	case 'n':
		return T(rest + "k" + PrimeStr + suffix)
	case 'T':
		return T(rest + "T" + PrimeStr + suffix)
	case 't':
		return T(rest + "p" + PrimeStr + suffix)
	case 'Z':
		return T(rest + "U" + PrimeStr + suffix)
	case 'z':
		return T(rest + "u" + PrimeStr + suffix)
	}

	// normal case: increment ASCII letter
	if ('A' <= r && r < 'H') ||
		('I' <= r && r < 'J') ||
		('K' <= r && r < 'N') ||
		('P' <= r && r < 'Z') ||
		('a' <= r && r < 'h') ||
		('i' <= r && r < 'j') ||
		('k' <= r && r < 'n') ||
		('p' <= r && r < 'z') {
		return T(rest + string(r+1) + suffix)
	}

	// special case: ħ/ƶ, the unifier's stand-in letters. They have no
	// successor letter, so the next name counts: `ƶ` → `ƶ0`, and from
	// there the numeric case above (`ƶ0` → `ƶ1`). The count follows
	// the letter, never precedes it: a name is spelled in the text
	// DSL, whose identifiers start with a letter — `0ƶ` lexes as a
	// numeral and a letter, and a goal binding `∃0ƶ_9. …` had no text.
	if rs := string(r); rs == H_STROKE || rs == Z_STROKE {
		return T(body + prime + "0" + underscore)
	}

	return s + PrimeStr
}

func Subscript[T ~string](s T, i int) T { return s + T(Underscore+strconv.Itoa(i)) }

type StringInterner[T ~string] struct{ Map[string, T] }

func (si *StringInterner[T]) Pool(s string) T {
	v, _ := si.LoadOrStore(s, T(s))
	return v
}

// format strings like "x_0" to "x₀"
func FormatSubscript[T ~string](n T) T {
	idx := strings.LastIndex(string(n), Underscore)
	if idx == -1 || idx == 0 || idx == len(n)-1 {
		return n
	}

	var b strings.Builder
	b.WriteString(string(n[:idx]))
	for _, ch := range n[idx+1:] {
		if ch >= '0' && ch <= '9' {
			b.WriteRune('₀' + (ch - '0'))
		} else {
			return n
		}
	}
	return T(b.String())
}

var hasherPool = sync.Pool{
	New: func() any { return xxhash.New() },
}

func GenerateHash[T ~string](seeds ...T) string {
	hasher := hasherPool.Get().(*xxhash.Digest)
	defer func() {
		hasher.Reset()
		hasherPool.Put(hasher)
	}()

	for _, s := range seeds {
		io.WriteString(hasher, string(s))
	}

	return fmt.Sprintf("%x", hasher.Sum64())
}
