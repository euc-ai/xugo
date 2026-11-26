package utils

import (
	"testing"
	"unicode"
	"unicode/utf8"

	"github.com/stretchr/testify/assert"
)

func TestNextName(t *testing.T) {
	assert.Panics(t, func() { NextName("%1") })
	assert.Equal(t, NextName("a"), "b")
	assert.Equal(t, NextName("b0"), "b1")
	assert.Equal(t, NextName("b_0"), "b_1")
	assert.Equal(t, NextName("aʹ_0"), "aʹ_1")
	assert.Equal(t, NextName("aʹ_1"), "aʹ_2")
	assert.Equal(t, NextName("aʹʹ"), "bʹʹ")
	assert.Equal(t, NextName("bʹʹ"), "cʹʹ")
	assert.Equal(t, NextName("aʹʹ0"), "aʹʹ1")
	assert.Equal(t, NextName("aʹʹ1"), "aʹʹ2")
	assert.Equal(t, NextName("aʹʹ01"), "aʹʹ02")
	assert.Equal(t, NextName("caʹʹ01"), "caʹʹ02")
	assert.Equal(t, NextName("caʹʹ99"), "caʹʹ100")
	assert.Equal(t, NextName("a_b"), "a_bʹ")
	assert.Equal(t, NextName("a_bʹ"), "a_bʹʹ")
	assert.Equal(t, NextName("a_b'"), "a_b'ʹ")
	assert.Equal(t, NextName("_"), "_0")
	assert.Equal(t, NextName("0"), "1")
	assert.Equal(t, NextName("_0"), "_1")
	assert.Equal(t, NextName("iʹ"), "jʹ")
	assert.Equal(t, NextName("j"), "iʹ")
	assert.Equal(t, NextName("o"), "oʹ")
	assert.Equal(t, NextName("jʹ"), "iʹʹ")
	assert.Equal(t, NextName("j0"), "j1")
	assert.Equal(t, NextName("y"), "z")
	assert.Equal(t, NextName("z"), "uʹ")
	assert.Equal(t, NextName("A"), "B")
	assert.Equal(t, NextName("H"), "Aʹ")
	assert.Equal(t, NextName("z0"), "z1")
	assert.Equal(t, NextName("z01"), "z02")
	assert.Equal(t, NextName("zʹ01"), "zʹ02")
	assert.Equal(t, NextName("azʹ01"), "azʹ02")
	assert.Equal(t, NextName("α"), "αʹ")
	assert.Equal(t, NextName("α_0"), "α_1")
	assert.Equal(t, NextName("ƒ"), "ƒʹ")
	assert.Equal(t, NextName("ƒ_0"), "ƒ_1")
	assert.Equal(t, NextName("ẋ"), "ẋʹ")
	assert.Equal(t, NextName("aẋ"), "aẋʹ")
	// The unifier's stand-in letters (ƶ, ħ) count after the letter —
	// `ƶ` → `ƶ0` → `ƶ1` — so every name in the chain starts with a
	// letter, an identifier of the text DSL (ext/dsl isIdentStart),
	// which a goal's typed text must spell; `0ƶ` lexed as a numeral
	// and a letter.
	assert.Equal(t, NextName("ƶ"), "ƶ0")
	assert.Equal(t, NextName("ħ"), "ħ0")
	assert.Equal(t, NextName("ƶ0"), "ƶ1")
	assert.Equal(t, NextName("ƶʹ"), "ƶʹ0")
	assert.Equal(t, NextName("ƶʹ0"), "ƶʹ1")
	for name, i := Z_STROKE, 0; i < 40; i, name = i+1, NextName(name) {
		r, _ := utf8.DecodeRuneInString(name)
		assert.True(t, unicode.IsLetter(r), "%s: a minted stand-in starts with a letter", name)
	}
	assert.Equal(t, NextName("ƶ_0"), "ƶ_1")
	assert.Equal(t, NextName("aƶ"), "aƶ0")
	assert.Equal(t, NextName("aƶ0"), "aƶ1")
	assert.Equal(t, NextName("aƶ_0"), "aƶ_1")
	assert.Equal(t, NextName("aƶʹ_0"), "aƶʹ_1")
	assert.Equal(t, NextName("1baƶ0"), "1baƶ1")
	assert.Equal(t, NextName("ƶ01"), "ƶ02")
	assert.Equal(t, NextName("0ƶ01"), "0ƶ02")
	assert.Equal(t, NextName("0ƶ_1"), "0ƶ_2")
	assert.Equal(t, NextName("ƶʹ01"), "ƶʹ02")
	assert.Equal(t, NextName("aƶʹ"), "aƶʹ0")
	assert.Equal(t, NextName("aƶʹ01"), "aƶʹ02")
	// A name the stand-in letters once minted with the count in front
	// (`1ƶʹ`, decoded from an older recording) counts after the letter
	// from here on, like any other.
	assert.Equal(t, NextName("1ƶʹ"), "1ƶʹ0")
	assert.Equal(t, NextName("1ƶʹ_1"), "1ƶʹ_2")
	assert.Equal(t, NextName("01ƶʹ"), "01ƶʹ0")
	assert.Equal(t, NextName("1ƶʹ01"), "1ƶʹ02")
	assert.Equal(t, NextName("1aƶʹ01"), "1aƶʹ02")
	assert.Equal(t, NextName("01ƶʹ01"), "01ƶʹ02")
}

func TestFormatSubscript(t *testing.T) {
	assert.Equal(t, FormatSubscript("x_0"), "x₀")
	assert.Equal(t, FormatSubscript("y_1"), "y₁")
	assert.Equal(t, FormatSubscript("ab_2"), "ab₂")
	assert.Equal(t, FormatSubscript("s0_3"), "s0₃")
	assert.Equal(t, FormatSubscript("0x_4"), "0x₄")
	assert.Equal(t, FormatSubscript("x_1_5"), "x_1₅")
	assert.Equal(t, FormatSubscript("x_6"), "x₆")
	assert.Equal(t, FormatSubscript("xʹ_7"), "xʹ₇")
	assert.Equal(t, FormatSubscript("x_8"), "x₈")
	assert.Equal(t, FormatSubscript("x_9"), "x₉")
	assert.Equal(t, FormatSubscript("x_10"), "x₁₀")
	assert.Equal(t, FormatSubscript("x_01"), "x₀₁")
	assert.Equal(t, FormatSubscript("x_i"), "x_i")
	assert.Equal(t, FormatSubscript("_6"), "_6")
	assert.Equal(t, FormatSubscript("x_"), "x_")
	assert.Equal(t, FormatSubscript("xy"), "xy")
	assert.Equal(t, FormatSubscript("x_0a"), "x_0a")
}
