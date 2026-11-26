// Package landmarks writes the site's list of landmarks into its two
// landmarks pages. The list is site/landmarks.json: the subjects in order,
// each with its anchor, its heading, its opening paragraph and its rows,
// a row a member's id and what it says in a reader's words. Each page
// keeps its own opening and navigation, in its own language, and holds the
// list between two pairs of marks this package fills: the table of
// contents between `<!-- landmarks subjects -->` and
// `<!-- end landmarks subjects -->`, the topic sections between
// `<!-- landmarks topics -->` and `<!-- end landmarks topics -->`. The two
// pages differ in the list only by the prefix of their links into the
// corpus browser, the Chinese page being one directory down.
// TestLintSiteLandmarksCurrent (library/integrity/gates) holds both pages
// to the list.
package landmarks

//go:generate go run ../cmd/gen_landmarks -site ../../site

import (
	"bytes"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// ListFile is the list's file under the site's directory.
const ListFile = "landmarks.json"

// List is the landmarks list: its subjects, in the order the pages show them.
type List struct {
	Subjects []Subject `json:"subjects"`
}

// Subject is one subject's section: its anchor on the page, its heading,
// the paragraph that opens it, and its rows.
type Subject struct {
	ID      string `json:"id"`
	Heading string `json:"heading"`
	Opening string `json:"opening"`
	Rows    []Row  `json:"rows"`
}

// Row is one landmark: the id of the member its row links and shows, and
// what the member is in a reader's words.
type Row struct {
	Member string `json:"member"`
	What   string `json:"what"`
}

// Page is a landmarks page, by its path under the site's directory, and
// the prefix its links into the corpus browser carry.
type Page struct {
	File   string
	Corpus string
}

// Pages are the site's landmarks pages: the English page at the site's
// root and the Chinese page one directory down.
var Pages = []Page{
	{File: "landmarks.html", Corpus: "corpus/"},
	{File: "zh/landmarks.html", Corpus: "../corpus/"},
}

// The two regions of a page the list fills, by the name their marks carry.
const (
	regionSubjects = "subjects"
	regionTopics   = "topics"
)

// Load reads the list from the site's directory. The list is input written
// by hand, so a defect of it is an error: an unknown field, a subject or
// row with an empty field, an anchor used twice, a member id that is not a
// plain `family.Name`.
func Load(site string) (List, error) {
	file := filepath.Join(site, ListFile)
	src, err := os.ReadFile(file)
	if err != nil {
		return List{}, err
	}
	dec := json.NewDecoder(bytes.NewReader(src))
	dec.DisallowUnknownFields()
	var list List
	if err := dec.Decode(&list); err != nil {
		return List{}, fmt.Errorf("%s: %w", file, err)
	}
	if len(list.Subjects) == 0 {
		return List{}, fmt.Errorf("%s: no subjects", file)
	}
	seen := map[string]bool{}
	for i, s := range list.Subjects {
		if s.ID == "" || s.Heading == "" || s.Opening == "" || len(s.Rows) == 0 {
			return List{}, fmt.Errorf("%s: subject %d (%q) lacks an id, a heading, an opening or rows", file, i+1, s.ID)
		}
		if strings.ContainsAny(s.ID, " \"<>&#") {
			return List{}, fmt.Errorf("%s: subject %d's id %q is no page anchor", file, i+1, s.ID)
		}
		if seen[s.ID] {
			return List{}, fmt.Errorf("%s: the id %q names two subjects", file, s.ID)
		}
		seen[s.ID] = true
		for j, r := range s.Rows {
			if r.What == "" || !strings.Contains(r.Member, ".") || strings.ContainsAny(r.Member, " \"<>&") {
				return List{}, fmt.Errorf("%s: row %d of %q needs a member id `family.Name` and its words", file, j+1, s.ID)
			}
		}
	}
	return list, nil
}

// Render is the list as a page with this corpus prefix shows it: the
// entries of its table of contents and its topic sections, each line
// indented as the page's markup around the marks is.
func Render(list List, corpus string) (subjects, topics string) {
	var toc, body strings.Builder
	for _, s := range list.Subjects {
		fmt.Fprintf(&toc, "        <li><a href=\"#%s\">%s</a></li>\n", s.ID, escape(s.Heading))
		fmt.Fprintf(&body, "    <section class=\"topic\" id=\"%s\">\n", s.ID)
		fmt.Fprintf(&body, "      <h2>%s</h2>\n", escape(s.Heading))
		fmt.Fprintf(&body, "      <p>%s</p>\n", escape(s.Opening))
		body.WriteString("      <ul class=\"rows\">\n")
		for _, r := range s.Rows {
			fmt.Fprintf(&body,
				"        <li><a href=\"%sproof.html?m=%s\"><span class=\"what\">%s</span><code>%s</code></a></li>\n",
				corpus, r.Member, escape(r.What), r.Member)
		}
		body.WriteString("      </ul>\n    </section>\n")
	}
	return toc.String(), body.String()
}

// escape writes text into markup: the three characters that open markup
// or an entity, and no others, so the list's apostrophes and quotation
// marks stand as written.
func escape(text string) string {
	return strings.NewReplacer("&", "&amp;", "<", "&lt;", ">", "&gt;").Replace(text)
}

// splice puts body between a region's marks: after the line that opens
// it, up to the line that ends it. A page without the two marks, or with
// either twice, is a defect of the page.
func splice(page, region, body string) (string, error) {
	open := "<!-- landmarks " + region
	end := "<!-- end landmarks " + region + " -->"
	if strings.Count(page, open) != 1 || strings.Count(page, end) != 1 {
		return "", fmt.Errorf("the page holds the marks `%s … -->` and `%s` %d and %d times; each once",
			open, end, strings.Count(page, open), strings.Count(page, end))
	}
	at := strings.Index(page, open)
	lineEnd := strings.Index(page[at:], "\n")
	stop := strings.Index(page, end)
	if lineEnd < 0 || stop < at+lineEnd {
		return "", fmt.Errorf("the region %q ends before it opens", region)
	}
	from := at + lineEnd + 1
	to := strings.LastIndex(page[:stop], "\n") + 1
	return page[:from] + body + page[to:], nil
}

// Rewritten is a page as it stands and as the list writes it.
func Rewritten(site string, list List, page Page) (now, written []byte, err error) {
	file := filepath.Join(site, page.File)
	now, err = os.ReadFile(file)
	if err != nil {
		return nil, nil, err
	}
	subjects, topics := Render(list, page.Corpus)
	text, err := splice(string(now), regionSubjects, subjects)
	if err == nil {
		text, err = splice(text, regionTopics, topics)
	}
	if err != nil {
		return nil, nil, fmt.Errorf("%s: %w", file, err)
	}
	return now, []byte(text), nil
}

// Write writes the list into every landmarks page whose list differs.
func Write(site string) error {
	list, err := Load(site)
	if err != nil {
		return err
	}
	for _, page := range Pages {
		now, written, err := Rewritten(site, list, page)
		if err != nil {
			return err
		}
		if !bytes.Equal(now, written) {
			if err := os.WriteFile(filepath.Join(site, page.File), written, 0o644); err != nil {
				return err
			}
		}
	}
	return nil
}

// Stale are the landmarks pages whose list is not the list as written.
func Stale(site string) ([]string, error) {
	list, err := Load(site)
	if err != nil {
		return nil, err
	}
	var stale []string
	for _, page := range Pages {
		now, written, err := Rewritten(site, list, page)
		if err != nil {
			return nil, err
		}
		if !bytes.Equal(now, written) {
			stale = append(stale, page.File)
		}
	}
	return stale, nil
}
