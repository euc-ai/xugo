// vocab.go — the chapter's statement vocabulary.
//
// Two alphabets meet here, because the chapter's subject is an
// operation DEFINED across the boundary between them: the ℤ side
// (int_pow itself, the embedding int_of_num, and the multiplication its
// recursion equations are written in), whose types come from the
// domain's one NAME → type table (int_num/internal/intvocab); and the ℝ
// side the operation transports through — real_of_int, real_pow, and
// the `integer` predicate the transfer theorem's closure argument
// speaks. The ℝ names are not in ℤ's table and real/'s own table is not
// importable across the domain boundary (it is internal to real/), so
// their types are spelled here, once per package — the Spelled rows,
// the same move int_construction makes for its bridge vocabulary.
//
// Declaring the alphabet is what makes a text-form statement PARSE, and
// it is identical in every member, so the family installs the rows into
// each member's ParseScope (family.go's WithVocabSpec) rather than each
// proof re-typing a `ctx.Const` preamble. The term-BUILDING half is the
// surface rendered from the same rows (zz_vocab_gen.go), and only the
// transfer theorem takes it — the two lifted members state their texts
// and build nothing.
//
// What is deliberately NOT declared: ℕ's own `nat_pow`, `suc` and the
// numerals, which the text-DSL's default nat scope already supplies;
// and `&`, the type-directed coercion the DSL resolves to int_of_num
// (whose constant IS declared) once the surrounding term is int-typed.

package int_pow

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/internal/intvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// realType is ℝ — the carrier the Spelled rows' types are written over.
// The domain table types the chapter's ℤ constants; ℝ's the chapter
// spells itself, for the boundary reason in the header.
func realType() HolType { return MakeType("real") }

// vocab is the chapter alphabet as data — one row per name. The
// transfer theorem's closure argument assembles the representative map,
// the ℝ power it lands in, the `&` of the base case's witness, and the
// `integer` predicate its induction carries.
var vocab = registry.NewVocabSpec(intvocab.Table()).
	OpsName("powOps").
	Term("int_of_num").
	Term("int_mul").
	Term("int_pow").
	// ℤ ↪ ℝ — the representative map
	Spelled("real_of_int", func() HolType { return MakeFun(MakeType("int"), realType()) }).
	// powers in ℝ — what int_pow transports
	Spelled("real_pow", func() HolType { return MakeFun(realType(), MakeFun(NumType, realType())) }).
	// integer(x) — the ℝ subset ℤ is carved from
	Spelled("integer", func() HolType { return MakeFun(realType(), TypeBool) })
