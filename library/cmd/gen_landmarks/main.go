// Command gen_landmarks writes the site's landmarks list,
// site/landmarks.json, into the site's two landmarks pages between the
// marks package landmarks fills. It runs from the package's go:generate
// line:
//
//	go generate ./library/landmarks
package main

import (
	"flag"
	"fmt"
	"os"

	"github.com/euc-ai/xugo/library/landmarks"
)

func main() {
	site := flag.String("site", "site", "the site's directory")
	flag.Parse()
	if err := landmarks.Write(*site); err != nil {
		fmt.Fprintln(os.Stderr, "gen_landmarks:", err)
		os.Exit(1)
	}
}
