package xugofmt

import (
	"reflect"
	"strings"
	"testing"
)

func TestFillTextLayout(t *testing.T) {
	cases := []struct {
		name        string
		text        string
		first, rest int
		want        []string
	}{{
		name:  "a text that fits is one line, its blanks as they are",
		text:  "one  two three",
		first: 20, rest: 20,
		want: []string{"one  two three"},
	}, {
		name:  "the fewest lines hold the text, as even as that allows",
		text:  "aaaa bbbb cccc dddd eeee ffff g",
		first: 24, rest: 24,
		want: []string{"aaaa bbbb cccc ", "dddd eeee ffff g"},
	}, {
		name:  "a line ends after the last blank of a run",
		text:  "aaaa bbbb   cccc dddd",
		first: 12, rest: 12,
		want: []string{"aaaa bbbb   ", "cccc dddd"},
	}, {
		name:  "a word wider than a line stands on one alone",
		text:  "a wordthatiswiderthanaline b",
		first: 10, rest: 10,
		want: []string{"a ", "wordthatiswiderthanaline ", "b"},
	}, {
		name:  "an escaped character takes the columns its escape does",
		text:  `"a" "b" "c" "d"`,
		first: 12, rest: 12,
		want: []string{`"a" "b" `, `"c" "d"`},
	}}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			got := fillText(c.text, c.first, c.rest, -3)
			if !reflect.DeepEqual(got, c.want) {
				t.Fatalf("got %q, want %q", got, c.want)
			}
			if joined := strings.Join(got, ""); joined != c.text {
				t.Errorf("the pieces spell %q", joined)
			}
		})
	}
}

func TestSourceLaysOutProse(t *testing.T) {
	cases := []struct{ name, in, want string }{{
		name: "a label past the width is a chain of literals broken at blanks",
		in: `	a.Show(
		"so the composite of the two maps carries every point of the first space into the third one, as the goal asks",
		By(h))
`,
		want: `	a.Show(
		"so the composite of the two maps carries every point "+
			"of the first space into the third one, as the goal asks",
		By(h))
`,
	}, {
		name: "a chain that fits is joined into one literal",
		in: `	a.Show(
		"so the composite "+
			"is continuous",
		By(h))
`,
		want: `	a.Show(
		"so the composite is continuous",
		By(h))
`,
	}, {
		name: "a chain broken elsewhere is broken where the layout breaks it",
		in: `	e := Entry{
		Reading: "True because the composites are compared " +
			"with the identities through the zigzag relation; with a single homotopy step it would fail off Kan complexes.",
	}
`,
		want: `	e := Entry{
		Reading: "True because the composites are compared with the identities through " +
			"the zigzag relation; with a single homotopy step it would fail off Kan complexes.",
	}
`,
	}, {
		name: "a raw literal, a text with a line break and a Name keep their lines",
		in: "	e := Entry{\n" +
			"		Name: \"a name of several words that is written on one line however long that line turns out to be\",\n" +
			"		Note: `a raw literal that is written on one line however long that line turns out to be in the file`,\n" +
			"		Text: \"a text of two lines\\nthat is written on one line however long that line turns out to be in the file\",\n" +
			"	}\n",
		want: "	e := Entry{\n" +
			"		Name: \"a name of several words that is written on one line however long that line turns out to be\",\n" +
			"		Note: `a raw literal that is written on one line however long that line turns out to be in the file`,\n" +
			"		Text: \"a text of two lines\\nthat is written on one line however long that line turns out to be in the file\",\n" +
			"	}\n",
	}}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			got, err := Source([]byte("package p\n\nfunc f() {\n" + c.in + "}\n"))
			if err != nil {
				t.Fatal(err)
			}
			want := "package p\n\nfunc f() {\n" + c.want + "}\n"
			if string(got) != want {
				t.Errorf("got\n%s\nwant\n%s", got, want)
			}
		})
	}
}

// A layout writes a text's chain of literals anew, from its first
// literal to its last, and a comment among them has no place in what it
// writes. So a text that holds a comment keeps the lines it is written
// on, and no comment is moved into a text: the one ending a later line
// of a text stays there, where the one ending its first line moves
// above the text.
func TestSourceKeepsACommentInAText(t *testing.T) {
	cases := []struct{ name, in, want string }{{
		name: "a chain that would join keeps its lines where a comment ends one",
		in: `	a.Show(
		"so the composite "+ // why
			"is continuous",
		By(h))
`,
		want: `	a.Show(
		"so the composite "+ // why
			"is continuous",
		By(h))
`,
	}, {
		name: "and where a comment stands between two of them",
		in: `	a.Show(
		"so the composite "+
			// why
			"is continuous",
		By(h))
`,
		want: `	a.Show(
		"so the composite "+
			// why
			"is continuous",
		By(h))
`,
	}, {
		name: "a text past the width keeps its line where a general comment parts its literals",
		in: `	a.Show(
		"so the composite of the two maps carries every point of the first space "+ /* why */ "into the third one, as the goal asks of it",
		By(h))
`,
		want: `	a.Show(
		"so the composite of the two maps carries every point of the first space "+ /* why */ "into the third one, as the goal asks of it",
		By(h))
`,
	}, {
		name: "a math text that holds a comment keeps its lines",
		in: `	x := Statement{
		Conclusion: "∀x:A. " + // the quantifier
			"p(x)",
	}
`,
		want: `	x := Statement{
		Conclusion: "∀x:A. " + // the quantifier
			"p(x)",
	}
`,
	}, {
		name: "the comment ending a text's last line past the width stays, and the text is laid out",
		in: `	a.Show(
		"so the composite "+
			"of the two maps carries every point of the first space into the third one, as the goal asks of it here", // why
		By(h))
`,
		want: `	a.Show(
		"so the composite of the two maps carries every point of the "+
			"first space into the third one, as the goal asks of it here", // why
		By(h))
`,
	}, {
		name: "the comment ending a text's first line past the width moves above the text, which is laid out",
		in: `	a.Show(
		"so the composite of the two maps carries every point of the first space, and every point of the second, "+ // why
			"into the third one, as the goal asks of it",
		By(h))
`,
		want: `	a.Show(
		// why
		"so the composite of the two maps carries every point of the first space, "+
			"and every point of the second, into the third one, as the goal asks of it",
		By(h))
`,
	}}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			got, err := Source([]byte("package p\n\nfunc f() {\n" + c.in + "}\n"))
			if err != nil {
				t.Fatal(err)
			}
			want := "package p\n\nfunc f() {\n" + c.want + "}\n"
			if string(got) != want {
				t.Errorf("got\n%s\nwant\n%s", got, want)
			}
			again, err := Source(got)
			if err != nil || string(again) != string(got) {
				t.Errorf("the layout of its layout is\n%s", again)
			}
		})
	}
}

func TestSourceBreaksWideLines(t *testing.T) {
	cases := []struct{ name, in, want string }{{
		name: "a call's arguments go to the line under it, together where that line holds them",
		in: `	x := polynomial.PolynomialOverMap.At(firstArgument, a.TermAs[A]("L.zero"), a.TermAs[B]("T.zero"), secondArgument)
`,
		want: `	x := polynomial.PolynomialOverMap.At(
		firstArgument, a.TermAs[A]("L.zero"), a.TermAs[B]("T.zero"), secondArgument)
`,
	}, {
		name: "and one to a line where it does not, the closing parenthesis after the last",
		in: `	x := polynomial.PolynomialOverMap.At(firstArgument, a.TermAs[A]("field_of_fractions.zero"), a.TermAs[B]("target_ring.zero"), secondArgument)
`,
		want: `	x := polynomial.PolynomialOverMap.At(
		firstArgument,
		a.TermAs[A]("field_of_fractions.zero"),
		a.TermAs[B]("target_ring.zero"),
		secondArgument)
`,
	}, {
		name: "a literal's brace takes a line of its own after a comma",
		in: `	x := []registry.EntryLike{PullbackIsExtension, SquareZeroPullbackDef, square_zero_extension.SquareZeroExtension}
`,
		want: `	x := []registry.EntryLike{
		PullbackIsExtension,
		SquareZeroPullbackDef,
		square_zero_extension.SquareZeroExtension,
	}
`,
	}, {
		name: "a function's parameters take a group to a line and its body keeps its place",
		in: `	x := family.Theorem(headline, func(a *Argument, R *Expr[RingOps[A]], i, j *Expr[Nat], u, v *Expr[U], universe, distinct Fact) {
		a.Done()
	})
`,
		want: `	x := family.Theorem(headline, func(
		a *Argument,
		R *Expr[RingOps[A]],
		i, j *Expr[Nat],
		u, v *Expr[U],
		universe, distinct Fact,
	) {
		a.Done()
	})
`,
	}, {
		name: "the values of an assignment stand under its operator, on one line where it holds them",
		in: `	closedField, homomorphism, primeIdeal, polynomialOver, nonzero := parts[0], parts[1], parts[2], parts[3], parts[4]
`,
		want: `	closedField, homomorphism, primeIdeal, polynomialOver, nonzero :=
		parts[0], parts[1], parts[2], parts[3], parts[4]
`,
	}, {
		name: "and one to a line where it does not",
		in: `	closure, carrier := a.TermAs[Set[A]]("algebraic_elements(field_of_fractions, k)"), a.TermAs[Set[A]]("field_of_fractions.carrier")
`,
		want: `	closure, carrier :=
		a.TermAs[Set[A]]("algebraic_elements(field_of_fractions, k)"),
		a.TermAs[Set[A]]("field_of_fractions.carrier")
`,
	}, {
		name: "a list of one element is broken where that brings its line inside the width, the outermost first",
		in: `	theSwappedPairWitnessOfThisStep := Witness(a.TermAs[Fun[Prod[Nat, A], Prod[A, Nat]]]("λz:prod(num, A). (snd(z), fst(z))"))
`,
		want: `	theSwappedPairWitnessOfThisStep := Witness(
		a.TermAs[Fun[Prod[Nat, A], Prod[A, Nat]]]("λz:prod(num, A). (snd(z), fst(z))"))
`,
	}, {
		name: "and otherwise at the innermost, which leaves the element the widest line",
		in: `	x := Witness(a.TermAs[Fun[Prod[Nat, Fun[Nat, A]], Prod[Fun[Nat, A], Nat]]]("λz:prod(num, num → A). (snd(z), fst(z))"))
`,
		want: `	x := Witness(a.TermAs[Fun[Prod[Nat, Fun[Nat, A]], Prod[Fun[Nat, A], Nat]]](
		"λz:prod(num, num → A). (snd(z), fst(z))"))
`,
	}, {
		name: "a break that saves no column is passed over for the list inside it",
		in: `	By(comm_monoid.CommutativeOn.Read(comm_ring.MultiplicativeMonoidOn.Read(field.RingOn.Read(compositumField))))
`,
		want: `	By(comm_monoid.CommutativeOn.Read(
		comm_ring.MultiplicativeMonoidOn.Read(field.RingOn.Read(compositumField))))
`,
	}, {
		name: "an element that spans lines keeps its place, and the list is broken after it",
		in: `	x := family.Card(Statement{
		Conclusion: "p(x)",
	}, "the note of the card, which says in a sentence or two how the statement is expected to be proved later")
`,
		want: `	x := family.Card(Statement{
		Conclusion: "p(x)",
	},
		"the note of the card, which says in a sentence or "+
			"two how the statement is expected to be proved later")
`,
	}, {
		name: "a text and the text after it take a line each",
		in: `	x := family.Card("∀x:A. first_predicate(x, alpha) ∧ second_predicate(x, beta)", "the note of the card, which says how it is proved")
`,
		want: `	x := family.Card(
		"∀x:A. first_predicate(x, alpha) ∧ second_predicate(x, beta)",
		"the note of the card, which says how it is proved")
`,
	}, {
		name: "an abbreviation entry is not broken: its Text is laid out after its Name",
		in: `	t := Abbrev{
		{Name: "the entry", Text: "λf:M. λg:M. COND(f = g, first_value(f, g, alpha), second_value(g, f, beta))"},
	}
`,
		want: `	t := Abbrev{
		{Name: "the entry", Text: "λf:M. λg:M. " +
			"    COND(f = g, first_value(f, g, alpha), second_value(g, f, beta))"},
	}
`,
	}, {
		name: "a comment that ends a line past the width stands on the line above",
		in: `	scaled := SmulIn.Read(module).At(cR, fx) // c • F(x): the module M is closed under scaling by the ring's elements
`,
		want: `	// c • F(x): the module M is closed under scaling by the ring's elements
	scaled := SmulIn.Read(module).At(cR, fx)
`,
	}, {
		name: "a text on a line the code has no break for is laid out after the code",
		in: `	x := family.Theorem("∀x:A. first_predicate(x, alpha) ∧ second_predicate(x, beta) ∧ third_predicate(x, gamma)", func(a *Argument) {
		a.Done()
	})
`,
		want: `	x := family.Theorem("∀x:A. "+
		"    first_predicate(x, alpha) ∧ "+
		"    second_predicate(x, beta) ∧ "+
		"    third_predicate(x, gamma)", func(a *Argument) {
		a.Done()
	})
`,
	}}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			got, err := Source([]byte("package p\n\nfunc f() {\n" + c.in + "}\n"))
			if err != nil {
				t.Fatal(err)
			}
			want := "package p\n\nfunc f() {\n" + c.want + "}\n"
			if string(got) != want {
				t.Errorf("got\n%s\nwant\n%s", got, want)
			}
			again, err := Source(got)
			if err != nil || string(again) != string(got) {
				t.Errorf("the layout of its layout is\n%s", again)
			}
		})
	}
}

func TestSourceLeavesAGeneratedFile(t *testing.T) {
	src := "// Code generated by a generator. DO NOT EDIT.\n\npackage p\n\n" +
		"var x = f(firstArgumentOfTheCall, secondArgumentOfTheCall, thirdArgumentOfTheCall, fourthArgumentOfTheCall, fifth)\n"
	got, err := Source([]byte(src))
	if err != nil {
		t.Fatal(err)
	}
	if string(got) != src {
		t.Errorf("got\n%s", got)
	}
}

// TestSourceCountsFromIndentation — a line nested deep has the columns
// a line at the margin has. Thirteen tabs in, a call that takes under
// LineWidth columns past its indentation stays the one line it is, and
// a label past them is laid out in lines that each fit.
func TestSourceCountsFromIndentation(t *testing.T) {
	const blocks = 12
	opening, closing := "", ""
	for i := 1; i <= blocks; i++ {
		opening += strings.Repeat("\t", i) + "{\n"
		closing = strings.Repeat("\t", i) + "}\n" + closing
	}
	indent := strings.Repeat("\t", blocks+1)
	call := indent + "x := By(firstFactNameHere, secondFactNameHere, thirdFactNameHere, fourthFactNameHere, fifthFact)\n"
	label := indent + "a.Show(\n" +
		indent + "\t\"so the composite of the two maps carries every point of the first space into the third one, as the goal asks\",\n" +
		indent + "\tBy(h))\n"
	src := "package p\n\nfunc f() {\n" + opening + call + label + closing + "}\n"
	if Width(strings.TrimSuffix(call, "\n")) <= LineWidth || ContentWidth(strings.TrimSuffix(call, "\n")) > LineWidth {
		t.Fatalf("the call is to run past the width from the margin and fit from its indentation")
	}
	out, err := Source([]byte(src))
	if err != nil {
		t.Fatalf("Source: %v", err)
	}
	if !strings.Contains(string(out), call) {
		t.Errorf("the call did not stay one line:\n%s", out)
	}
	want := indent + "\t\"so the composite of the two maps carries every point \"+\n" +
		indent + "\t\t\"of the first space into the third one, as the goal asks\",\n"
	if !strings.Contains(string(out), want) {
		t.Errorf("the label is not laid out as it is at the margin:\n%s", out)
	}
	for _, line := range strings.Split(string(out), "\n") {
		if ContentWidth(line) > LineWidth {
			t.Errorf("a line runs past the width from its indentation: %q", line)
		}
	}
}
