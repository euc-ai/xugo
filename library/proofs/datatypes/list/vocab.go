// vocab.go — the chapter's statement vocabulary.
//
// The chapter's alphabet is its own definitions (definitions.go),
// declared here by name with each type read off its mint: the two
// constructors `nil` and `cons`, the operations `list_append`, `list_length`,
// `list_reverse`, `list_map`, `list_member`, `list_fold`, `list_distinct`, `list_sum` and
// `list_product`, and the relation `list_permutation`. All but the two over
// `list(num)` are polymorphic in the element type and declared at the
// abstract letter; each occurrence in a statement instantiates
// independently, the binder annotations anchoring every letter.
// Everything else a statement here mentions is bound by the statement
// itself, is arithmetic the text parser supplies (`+`, `*`, `suc`, the
// numerals), or is another chapter's constant read through the
// definitional layer (`finite`, `card`, `has_size`, `monoid_pow`), so no
// domain table applies. The ascending listing's two constants
// (ascending.go), `list_ascending` and `ascending_list`, take no row: a
// stated name resolves through its mint, and no body builds with them.

package list

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var vocab = registry.NewVocabSpec(nil).
	OpsName("listOps").
	Term("nil").             // list(A)
	Term("cons").            // A → list(A) → list(A)
	Term("list_append").     // list(A) → list(A) → list(A)
	Term("list_length").     // list(A) → num
	Term("list_reverse").    // list(A) → list(A)
	Term("list_map").        // (A → B) → list(A) → list(B)
	Term("list_member").     // A → list(A) → bool
	Term("list_fold").       // (A → B → B) → list(A) → B → B
	Term("list_distinct").   // list(A) → bool
	Term("list_sum").        // list(num) → num
	Term("list_product").    // list(num) → num
	Term("list_permutation") // list(A) → list(A) → bool

// List is `list(A)` as a phantom of the typed term surface — the
// type-level twin of the chapter's carrier, declared beside its
// vocabulary per the phantom vocabulary's decentralization rule
// (ext/holtype_phantom.go). A signature over the chapter reads
// `Typed[List[A]]` exactly as its statement reads `x:list(A)`; the
// typed-wrapper generator (gen_family) spells the type through it.
type List[Elem ext.TypePhantom] struct{}

func (List[Elem]) Reify() ext.HolType { return MakeType("list", ext.HolTypeOf[Elem]()) }
