// Package carddata holds the generated spellings of the corpus's cards.
// The registry decides which entries are cards; these texts let a reader
// display them without normalizing or parsing their statements. The
// generator and TestCardDataCurrent verify the keys and both spellings.
package carddata

//go:generate go run ../cmd/card_data_gen -output cards_gen.go

// Text is a card's registered key and its display and paste-ready text.
type Text struct {
	Key            string
	Statement      string
	StatementTyped string
}

// The generated file installs the table. An absent file leaves it empty
// so the generator can bootstrap without its own output.
var texts map[string]Text

// Lookup reads the generated text for an entry with this name and key.
// A new or restated entry has no matching row until regeneration.
func Lookup(name, key string) (Text, bool) {
	text, ok := texts[name]
	return text, ok && text.Key == key
}
