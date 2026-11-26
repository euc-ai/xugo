# The site

The pages published at <https://euc-ai.github.io/xugo/> by
`.github/workflows/pages.yml`. They sit at the site's root, and the
corpus browser, `xugo browse --write`, is written under `corpus/` beside
them when the workflow runs. This file is not published.

- `index.html` is the front page: the root `README.md`'s tagline and
  opening, eight results the corpus reaches, and the README's
  questions, each folded. Its drawing of the building is read from
  `corpus/data/families.json` when the page opens, so it is that of
  the corpus published beside it.
- `landmarks.html` lists the landmarks by subject, each row linking to
  the theorem's page in the corpus browser. The list is written into the
  page from `landmarks.json` (below). A row not proved outright, a
  card or a theorem standing on one, is marked on cards: a reader asks
  whether a theorem is proved, not which of the two it is. The mark is
  read from the row's family file under `corpus/data/family/` as its
  subject comes near the screen; the page holds no status of its own.
- `architecture.html` is the account of the design, "Carriers Are All
  You Need", and `practice.html` the account of how the work proceeds.
  Each is the one copy of its document: the tree holds no Markdown of
  either. A member they name links to its page in the corpus browser.
- `style.css` is what the pages share. Its colours are the corpus
  browser's, but for the two of the building on the front page.
- `toc.js` is the contents column of `landmarks.html`,
  `architecture.html` and `practice.html`: folded above the text on a
  narrow screen, and marking the section being read as the page
  scrolls.

`zh/` holds the same pages in Chinese, one directory down, so their links
into the corpus read `../corpus/`. Every page links its counterpart in
the other language from its header and its footer: 中文 on an English
page, EN on a Chinese one. `zh/landmarks.html` says its opening in
Chinese and shows the same list as `landmarks.html`, the one written
from `landmarks.json`. The corpus browser is not translated.

The corpus browser's pages link back to the front page by `../`, so the
browser is written one directory under these pages.

The pages are plain HTML, written by hand, but for the landmarks list,
which `go generate ./library/landmarks` writes into both landmarks pages
from `landmarks.json`, between the pages' `<!-- landmarks … -->` marks. The
front page marks what it says in the root `README.md`'s words, the
tagline, the opening and the folded questions, between
`<!-- from README.md -->` and `<!-- end README.md -->`; the README's
title is the page's own heading. `zh/index.html` marks what it quotes
from `README.zh-CN.md` the same way. `TestLintSiteQuotesReadme`
(`library/integrity/gates`) holds every marked span to its README word
for word, so a change to one is made to the other. A change to a page is
made to its counterpart in the other language by hand.

## Landmarks

A landmark is a theorem a reader looks up by name, the top of a
chapter's plan, or a bridge that says how a structure is read. A lemma
a definition gives in a line, a textbook exercise, or a step inside one
chapter's argument is not one. Neither is a result every reader takes a
body of mathematics to hold — induction, that ℝ is a field, that a
subgroup is a group on its own set — however many chapters cite it:
its row would say nothing. Nor is a result of the first years of an
undergraduate course: calculus, linear algebra, elementary number
theory and the first theorems on groups and rings are in the corpus and
not on the list. Keep a subject to the results that define it; the
chapter's README holds the rest.

A row links to the member's page by its id,
`corpus/proof.html?m=<family>.<Name>`, shows the id, and says what the
member is in a reader's words. A landmark stated ahead of its proof is
listed on the same terms as one proved, and its row stays when the
proof lands: its mark goes with the corpus published beside the page.
The subjects run roughly from the bottom of the tree up: the language
every chapter reads through, then the structures on carrier sets and
the chapters standing on them.

The list is `landmarks.json`, kept by hand: the subjects in order, each
with its anchor, its heading and its opening paragraph, and its rows, a
row a member's id and what it says, all in plain text. Edit it there and
run `go generate ./library/landmarks`, which writes it into
`landmarks.html` and `zh/landmarks.html`; never between a page's
marks. `TestLintSiteLandmarksCurrent` (`library/integrity/gates`) fails
on a page whose list is not the file's. The file is not published, and
nothing in the index or a session reads it.

## Links

A link of these pages that stays on the site names a file the site
holds, and a link to a theorem's page names a theorem the corpus
browser has a page for: a unit's id, so for a member a door call
registered with others, the id of its unit. The workflow checks both
before it publishes. A member renamed or retired since a page was
written fails the run, and the page is corrected here.

## Reading the site before it is published

```sh
go build -o xugo ./engine/cmd/xugo/
./xugo browse --write /tmp/xugo-site/corpus
cp -R site/. /tmp/xugo-site/ && rm /tmp/xugo-site/README.md
```

Then serve `/tmp/xugo-site` with any static file server, for instance
`python3 -m http.server` run in that directory. The pages read their data
with `fetch`, which a page opened as a file cannot do.
