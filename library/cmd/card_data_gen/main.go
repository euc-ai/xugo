// Command card_data_gen writes the generated spellings of the corpus's
// cards. Run go generate ./library/carddata to refresh the table.
package main

import (
	"bytes"
	"flag"
	"log"
	"os"

	"github.com/euc-ai/xugo/library/carddata/cardgen"
	_ "github.com/euc-ai/xugo/library/proofs"
)

func main() {
	output := flag.String("output", "library/carddata/"+cardgen.File, "generated Go file")
	flag.Parse()
	want := cardgen.Render()
	prev, err := os.ReadFile(*output)
	if err != nil && !os.IsNotExist(err) {
		log.Fatal(err)
	}
	if bytes.Equal(prev, want) {
		return
	}
	if err := os.WriteFile(*output, want, 0o644); err != nil {
		log.Fatal(err)
	}
}
