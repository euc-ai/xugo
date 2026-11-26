package registry

import "testing"

// through calls read under n frames of this file, none of them a
// chapter's.
func through(n int, read func() string) string {
	if n == 0 {
		return read()
	}
	return through(n-1, read)
}

// TestChapterSite_ReadsTheInnermostChapterFrame: outside a chapter file
// there is no site; inside one, the site is that file's path from the
// module root and the line being run, however deep the stack above it —
// a whistle cut is reported hundreds of frames into a fixpoint — and it
// is the innermost chapter frame when one chapter's code runs under
// another's. registrationSource reads the same frame, below
// library/proofs.
func TestChapterSite_ReadsTheInnermostChapterFrame(t *testing.T) {
	if got := ChapterSite(); got != "" {
		t.Fatalf("outside a chapter file: got %q, want no site", got)
	}
	for _, depth := range []int{0, 500} {
		if got, want := inChapter(func() string { return through(depth, ChapterSite) }), "library/proofs/fixture/chapter.go:7"; got != want {
			t.Errorf("%d frames above the chapter's: got %q, want %q", depth, got, want)
		}
	}
	if got, want := inOuterChapter(func() string { return inChapter(ChapterSite) }), "library/proofs/fixture/chapter.go:7"; got != want {
		t.Errorf("one chapter under another: got %q, want the innermost, %q", got, want)
	}
	if got, want := inChapter(registrationSource), "fixture/chapter.go:7"; got != want {
		t.Errorf("registrationSource: got %q, want %q", got, want)
	}
}

// The two functions below compile as lines of chapter files: a //line
// directive names the file and line of the line after it.

//line /checkout/library/proofs/fixture/chapter.go:6
func inChapter(read func() string) string {
	return read()
}

//line /checkout/library/proofs/fixture/outer.go:20
func inOuterChapter(read func() string) string {
	return read()
}
