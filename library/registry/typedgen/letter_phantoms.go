package typedgen

import (
	"fmt"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/registry/aliasgen"
	"github.com/euc-ai/xugo/prover/proof"
)

// The statement letters: a phantom of the HOL type variable `:X` is a
// zero-size type X whose Reify is MakeVarType("X"), the contract ext
// declares the shared letters by (ext/holtype_phantom.go). A proof file
// spells a letter bare, so a letter's phantom is one of three things,
// decided by its name alone (OwnerOfLetter):
//
//   - a shared letter, A–E: library/authoring aliases ext's phantom for
//     every proof file;
//   - a family letter: the family's zz_typed_thms_gen.go declares the
//     phantom once, for every letter its registered statements bind
//     beyond the shared ones, so no member declares one and two members
//     filled apart cannot both;
//   - a type variable without a phantom: its name is no exported Go
//     identifier, or a multi-letter `var:` name library/authoring
//     exports under another meaning. Never a capital letter: the surface
//     exports none beyond A–E, its truth constants and dimension letters
//     going by full names (TestSurfaceSpellsNoOtherLetter). A
//     declaration in the family would collide with every proof file's
//     dot import, so the generated file names the variable in a comment
//     and declares nothing; a member that wants it typed declares a
//     phantom under a name of its own, the one hand-declared letter
//     phantom the gates allow (TestLintTypeLetterPhantomIsGenerated).

// LetterOwner is the declaration a statement letter's phantom is, in a
// proof file of a family whose statements bind the letter.
type LetterOwner int

const (
	// LetterOfAuthoring: library/authoring aliases ext's phantom.
	LetterOfAuthoring LetterOwner = iota
	// LetterOfFamily: the family's generated wrapper file declares it.
	LetterOfFamily
	// LetterWithoutPhantom: nothing declares a phantom under the
	// letter's name.
	LetterWithoutPhantom
)

// sharedLetters are the letters library/authoring declares for every
// proof file, aliases of ext.A…E.
// TestAuthoringDeclaresTheSharedLetters holds this set against the
// aliases library/authoring declares, and TestSurfaceSpellsNoOtherLetter
// holds it against every capital the surface exports.
var sharedLetters = map[string]bool{"A": true, "B": true, "C": true, "D": true, "E": true}

// OwnerOfLetter is where the phantom of the statement letter named
// letter is declared.
func OwnerOfLetter(letter string) LetterOwner {
	switch {
	case sharedLetters[letter]:
		return LetterOfAuthoring
	case !isExportedIdent(letter) || aliasgen.OnSurface(letter):
		return LetterWithoutPhantom
	}
	return LetterOfFamily
}

// familyLetters reads every statement fam registers, its hypotheses
// included, for the letters it binds beyond the shared ones: declared
// are the letters the family's generated file declares a phantom for,
// unspelled the ones nothing declares one for. Both sorted.
func familyLetters(fam *registry.Family) (declared, unspelled []string) {
	seen := map[string]bool{}
	for _, e := range fam.Entries() {
		for _, v := range proof.OrderedPropTypeVars(e.Statement().Prop) {
			letter := string(v.Name())
			if seen[letter] {
				continue
			}
			seen[letter] = true
			switch OwnerOfLetter(letter) {
			case LetterOfFamily:
				declared = append(declared, letter)
			case LetterWithoutPhantom:
				unspelled = append(unspelled, letter)
			}
		}
	}
	sort.Strings(declared)
	sort.Strings(unspelled)
	return declared, unspelled
}

// LettersInScope is the set of statement letters a proof file of fam
// spells as phantoms: the shared letters, and the letters the family's
// generated file declares. fam is nil for a chapter that registers
// nothing yet. A letter only a statement about to join binds is not in
// scope: its phantom is declared when the family regenerates, which
// links the family's package, so a proof file naming it before then
// would keep the package from compiling for the regeneration.
func LettersInScope(fam *registry.Family) map[string]bool {
	inScope := map[string]bool{}
	for letter := range sharedLetters {
		inScope[letter] = true
	}
	if fam != nil {
		declared, _ := familyLetters(fam)
		for _, letter := range declared {
			inScope[letter] = true
		}
	}
	return inScope
}

// renderLetterPhantoms writes the family letters' phantoms, and names
// the letters the family's statements bind that have none.
func renderLetterPhantoms(b *strings.Builder, declared, unspelled []string) {
	switch len(declared) {
	case 0:
	case 1:
		fmt.Fprintf(b, "// %s is the statement letter this family's statements bind beyond\n"+
			"// the shared A–E: the phantom of the HOL type variable :%s, declared\n"+
			"// here for every proof file of the family.\n", declared[0], declared[0])
		fmt.Fprintf(b, "type %s struct{}\n\n", declared[0])
	default:
		fmt.Fprintf(b, "// %s are the statement letters this family's statements bind\n"+
			"// beyond the shared A–E: each the phantom of the HOL type variable of\n"+
			"// its name, declared here for every proof file of the family.\n", joinLetters(declared))
		b.WriteString("type (\n")
		for _, letter := range declared {
			fmt.Fprintf(b, "\t%s struct{}\n", letter)
		}
		b.WriteString(")\n\n")
	}
	for _, letter := range declared {
		fmt.Fprintf(b, "func (%s) Reify() HolType { return MakeVarType(%q) }\n", letter, letter)
	}
	if len(declared) > 0 {
		b.WriteString("\n")
	}

	var taken, unnamed []string
	for _, letter := range unspelled {
		if isExportedIdent(letter) {
			taken = append(taken, letter)
		} else {
			unnamed = append(unnamed, letter)
		}
	}
	if len(taken) > 0 {
		fmt.Fprintf(b, "// The statement %s %s %s no phantom here:\n"+
			"// library/authoring exports %s under another meaning, and\n"+
			"// a declaration in this package would collide with every proof file's\n"+
			"// dot import. A binder at %s binds untyped, or at a phantom a member\n"+
			"// declares under a name of its own (typedgen.OwnerOfLetter).\n\n",
			plural(len(taken), "letter", "letters"), joinLetters(taken), plural(len(taken), "has", "have"),
			plural(len(taken), "the bare name", "each bare name"), plural(len(taken), "it", "one"))
	}
	if len(unnamed) > 0 {
		fmt.Fprintf(b, "// The statement %s %s %s no phantom: a phantom's name is the\n"+
			"// letter's, and it is no exported Go identifier.\n\n",
			plural(len(unnamed), "letter", "letters"), joinLetters(unnamed), plural(len(unnamed), "has", "have"))
	}
}

// joinLetters lists letters as prose: "I", "I and U", "G, H and I".
func joinLetters(letters []string) string {
	if len(letters) == 1 {
		return letters[0]
	}
	return strings.Join(letters[:len(letters)-1], ", ") + " and " + letters[len(letters)-1]
}

func plural(n int, one, many string) string {
	if n == 1 {
		return one
	}
	return many
}
