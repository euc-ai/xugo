package visualize

// A README's formulas typeset. A chapter README writes a formula in
// LaTeX where Unicode cannot set it plainly (chapter_constitution.md,
// the paragraph on formulas in a README): `$…$` on one line, or the
// lines between two `$$` lines. A page shows such a formula as MathML,
// which a browser draws with no script and no font of the page's own,
// so the page still fetches nothing.
//
// The reader (texMathML) knows the LaTeX a formula is written in here —
// letters, numbers, scripts, groups, fractions, roots, fences, the
// symbols and function names, a few type styles and accents — and no
// more: no environment, no macro, no alignment. A formula holding
// anything else is an error, and is never shown half read.

import (
	"fmt"
	"html"
	"regexp"
	"strings"
	"unicode"
	"unicode/utf8"
)

// A formula stands in a text as its MathML between mathOpen and
// mathClose, two characters no README writes: the page sets what lies
// between them as it is, and marks up the rest.
const (
	mathOpen  = "\x02"
	mathClose = "\x03"
)

var (
	texCodeSpan = regexp.MustCompile("`[^`]*`")
	texInline   = regexp.MustCompile(`\$([^$]*)\$`)
)

// typeset writes a text's formulas as MathML: every `$…$` of the text
// that lies outside a code span, set between mathOpen and mathClose.
// The rest of the text is left as written.
func typeset(text string) (string, error) {
	if !strings.Contains(text, "$") {
		return text, nil
	}
	var out strings.Builder
	var failed error
	formulas := func(plain string) {
		out.WriteString(texInline.ReplaceAllStringFunc(plain, func(span string) string {
			math, err := texMathML(span[1:len(span)-1], false)
			if err != nil && failed == nil {
				failed = err
			}
			return mathOpen + math + mathClose
		}))
	}
	rest := text
	for {
		code := texCodeSpan.FindStringIndex(rest)
		if code == nil {
			formulas(rest)
			break
		}
		formulas(rest[:code[0]])
		out.WriteString(rest[code[0]:code[1]])
		rest = rest[code[1]:]
	}
	return out.String(), failed
}

// texMathML reads a formula and writes it as a MathML math element, a
// block where display is set.
func texMathML(tex string, display bool) (string, error) {
	r := &_TexReader{source: tex}
	if err := r.lex(); err != nil {
		return "", fmt.Errorf("the formula $%s$: %v", tex, err)
	}
	nodes, err := r.row(display, func(_TexToken) bool { return false })
	if err == nil && r.at < len(r.tokens) {
		err = fmt.Errorf("a } with no { before it")
	}
	if err != nil {
		return "", fmt.Errorf("the formula $%s$: %v", tex, err)
	}
	open := "<math>"
	if display {
		open = `<math display="block">`
	}
	return open + "<mrow>" + strings.Join(nodes, "") + "</mrow></math>", nil
}

// _TexKind is what a token of a formula is.
type _TexKind int

const (
	texCommand _TexKind = iota // a backslash and a name, or a backslash and one character
	texOpen                    // {
	texClose                   // }
	texSub                     // _
	texSup                     // ^
	texPrime                   // '
	texNumber
	texLetter
	texSymbol
)

// _TexToken is a token: its text — a command's name without the
// backslash, a number's digits, or the character — and where it starts
// in the formula.
type _TexToken struct {
	kind _TexKind
	text string
	from int
}

// _TexReader reads a formula's tokens, at being the next one.
type _TexReader struct {
	source string
	tokens []_TexToken
	at     int
}

// lex cuts the formula into tokens. Space between them is dropped: a
// formula's spacing is its operators'.
func (r *_TexReader) lex() error {
	s := r.source
	for i := 0; i < len(s); {
		c, size := utf8.DecodeRuneInString(s[i:])
		switch {
		case unicode.IsSpace(c):
			i += size
		case c == '\\':
			j := i + 1
			for j < len(s) && (s[j] >= 'a' && s[j] <= 'z' || s[j] >= 'A' && s[j] <= 'Z') {
				j++
			}
			if j == i+1 {
				if j == len(s) {
					return fmt.Errorf("a backslash ends it")
				}
				_, next := utf8.DecodeRuneInString(s[j:])
				j += next
			}
			r.tokens = append(r.tokens, _TexToken{texCommand, s[i+1 : j], i})
			i = j
		case c == '{' || c == '}' || c == '_' || c == '^' || c == '\'':
			kind := map[rune]_TexKind{'{': texOpen, '}': texClose, '_': texSub, '^': texSup, '\'': texPrime}[c]
			r.tokens = append(r.tokens, _TexToken{kind, string(c), i})
			i += size
		case c >= '0' && c <= '9':
			j := i
			for j < len(s) && (s[j] >= '0' && s[j] <= '9' || s[j] == '.' && j+1 < len(s) && s[j+1] >= '0' && s[j+1] <= '9') {
				j++
			}
			r.tokens = append(r.tokens, _TexToken{texNumber, s[i:j], i})
			i = j
		case unicode.IsLetter(c):
			r.tokens = append(r.tokens, _TexToken{texLetter, string(c), i})
			i += size
		default:
			r.tokens = append(r.tokens, _TexToken{texSymbol, string(c), i})
			i += size
		}
	}
	return nil
}

// peek is the next token, and whether there is one.
func (r *_TexReader) peek() (_TexToken, bool) {
	if r.at < len(r.tokens) {
		return r.tokens[r.at], true
	}
	return _TexToken{}, false
}

// _TexNode is a part of a formula read: its MathML; whether it is an
// operator whose scripts a display sets under and over it (a sum, a
// minimum); and whether it is a function's name, which an application
// follows.
type _TexNode struct {
	xml    string
	limits bool
	apply  bool
}

// row reads the parts up to the formula's end or the token until
// names, which is left unread. display says the row is set in display
// style: a formula on its own line, outside a fraction and a script.
func (r *_TexReader) row(display bool, until func(_TexToken) bool) ([]string, error) {
	var nodes []string
	for {
		t, more := r.peek()
		if !more || t.kind == texClose || until(t) {
			return nodes, nil
		}
		xml, err := r.scripted(display)
		if err != nil {
			return nil, err
		}
		nodes = append(nodes, xml)
	}
}

// scripted reads a part with the scripts and primes written after it.
func (r *_TexReader) scripted(display bool) (string, error) {
	base, err := r.atom(display)
	if err != nil {
		return "", err
	}
	sub, sup, primes := "", "", 0
	for scripts := true; scripts; {
		t, _ := r.peek()
		switch {
		case r.at < len(r.tokens) && t.kind == texSub:
			if sub != "" {
				return "", fmt.Errorf("two subscripts on one base")
			}
			r.at++
			if sub, err = r.argument(); err != nil {
				return "", err
			}
		case r.at < len(r.tokens) && t.kind == texSup:
			if sup != "" {
				return "", fmt.Errorf("two superscripts on one base")
			}
			r.at++
			if sup, err = r.argument(); err != nil {
				return "", err
			}
		case r.at < len(r.tokens) && t.kind == texPrime:
			if sup != "" {
				return "", fmt.Errorf("a prime after a superscript")
			}
			r.at++
			primes++
		default:
			scripts = false
		}
	}
	if primes > 0 {
		mark := "<mo>" + strings.Repeat("′", primes) + "</mo>"
		if sup == "" {
			sup = mark
		} else {
			sup = "<mrow>" + mark + sup + "</mrow>"
		}
	}
	xml := base.xml
	under := base.limits && display
	switch {
	case sub != "" && sup != "" && under:
		xml = "<munderover>" + xml + sub + sup + "</munderover>"
	case sub != "" && sup != "":
		xml = "<msubsup>" + xml + sub + sup + "</msubsup>"
	case sub != "" && under:
		xml = "<munder>" + xml + sub + "</munder>"
	case sub != "":
		xml = "<msub>" + xml + sub + "</msub>"
	case sup != "" && under:
		xml = "<mover>" + xml + sup + "</mover>"
	case sup != "":
		xml = "<msup>" + xml + sup + "</msup>"
	}
	if base.apply {
		xml += "<mo>&#x2061;</mo>"
		// A function's name stands a thin space off what it is applied
		// to, but not off a fence opening its argument.
		if t, more := r.peek(); more && t.kind != texClose && !(t.kind == texSymbol && (t.text == "(" || t.text == "[")) &&
			!(t.kind == texCommand && (t.text == "left" || strings.HasPrefix(strings.ToLower(t.text), "big"))) {
			xml += `<mspace width="0.1667em"/>`
		}
	}
	return xml, nil
}

// argument reads what a script or a command takes: a group, or one
// part. It is never in display style.
func (r *_TexReader) argument() (string, error) {
	if _, more := r.peek(); !more {
		return "", fmt.Errorf("it ends where an argument is due")
	}
	node, err := r.atom(false)
	return node.xml, err
}

// group reads a braced group's parts as one row.
func (r *_TexReader) group(display bool) (string, error) {
	r.at++
	nodes, err := r.row(display, func(_TexToken) bool { return false })
	if err != nil {
		return "", err
	}
	if t, more := r.peek(); !more || t.kind != texClose {
		return "", fmt.Errorf("a { that no } closes")
	}
	r.at++
	if len(nodes) == 1 {
		return nodes[0], nil
	}
	return "<mrow>" + strings.Join(nodes, "") + "</mrow>", nil
}

// atom reads one part: a group, a letter, a number, a symbol, or a
// command with its arguments. A script with nothing before it has an
// empty part for its base.
func (r *_TexReader) atom(display bool) (_TexNode, error) {
	t := r.tokens[r.at]
	switch t.kind {
	case texOpen:
		xml, err := r.group(display)
		return _TexNode{xml: xml}, err
	case texSub, texSup, texPrime:
		return _TexNode{xml: "<mrow></mrow>"}, nil
	case texClose:
		return _TexNode{}, fmt.Errorf("a } where a part of the formula is due")
	case texLetter:
		r.at++
		return _TexNode{xml: "<mi>" + t.text + "</mi>"}, nil
	case texNumber:
		r.at++
		return _TexNode{xml: "<mn>" + t.text + "</mn>"}, nil
	case texSymbol:
		r.at++
		return _TexNode{xml: texSymbolXML(t.text)}, nil
	}
	r.at++
	return r.command(t.text, display)
}

// texSymbolXML is a character written as itself: an operator, a fence
// that does not grow with what it holds, or punctuation.
func texSymbolXML(char string) string {
	c, _ := utf8.DecodeRuneInString(char)
	switch {
	case char == "-":
		return "<mo>−</mo>"
	case char == "/" || char == ".":
		return `<mo lspace="0" rspace="0">` + char + "</mo>"
	case char == "|":
		return `<mo stretchy="false" lspace="0" rspace="0">|</mo>`
	case unicode.Is(unicode.Ps, c) || unicode.Is(unicode.Pe, c):
		return `<mo stretchy="false">` + char + "</mo>"
	}
	return "<mo>" + html.EscapeString(char) + "</mo>"
}

// command reads a command, its name already read, with its arguments.
func (r *_TexReader) command(name string, display bool) (_TexNode, error) {
	if s, known := texSymbols[name]; known {
		return _TexNode{xml: s.xml(), limits: s.limits}, nil
	}
	if limits, known := texFunctions[name]; known {
		return _TexNode{xml: "<mi>" + name + "</mi>", limits: limits, apply: true}, nil
	}
	if size, known := texSizes[strings.TrimRight(name, "lrm")]; known {
		mark, err := r.delimiter()
		if err != nil {
			return _TexNode{}, err
		}
		return _TexNode{xml: fmt.Sprintf(`<mo fence="true" stretchy="true" minsize="%s" maxsize="%s">%s</mo>`, size, size, mark)}, nil
	}
	if style, known := texStyles[name]; known {
		letters, err := r.raw()
		if err != nil {
			return _TexNode{}, err
		}
		var styled strings.Builder
		for _, c := range letters {
			if unicode.IsSpace(c) {
				continue
			}
			styled.WriteRune(style(c))
		}
		if name == "mathrm" {
			return _TexNode{xml: `<mi mathvariant="normal">` + html.EscapeString(styled.String()) + "</mi>"}, nil
		}
		return _TexNode{xml: "<mi>" + html.EscapeString(styled.String()) + "</mi>"}, nil
	}
	if accent, known := texAccents[name]; known {
		body, err := r.argument()
		if err != nil {
			return _TexNode{}, err
		}
		if name == "underline" {
			return _TexNode{xml: `<munder accentunder="true">` + body + accent + "</munder>"}, nil
		}
		return _TexNode{xml: `<mover accent="true">` + body + accent + "</mover>"}, nil
	}
	switch name {
	case "frac", "dfrac", "tfrac", "binom":
		over, err := r.argument()
		if err != nil {
			return _TexNode{}, err
		}
		under, err := r.argument()
		if err != nil {
			return _TexNode{}, err
		}
		if name == "binom" {
			return _TexNode{xml: `<mrow><mo fence="true">(</mo><mfrac linethickness="0">` + over + under + `</mfrac><mo fence="true">)</mo></mrow>`}, nil
		}
		return _TexNode{xml: "<mfrac>" + over + under + "</mfrac>"}, nil
	case "sqrt":
		index := ""
		if t, more := r.peek(); more && t.kind == texSymbol && t.text == "[" {
			r.at++
			nodes, err := r.row(false, func(t _TexToken) bool { return t.kind == texSymbol && t.text == "]" })
			if err != nil {
				return _TexNode{}, err
			}
			if t, more := r.peek(); !more || t.text != "]" {
				return _TexNode{}, fmt.Errorf(`\sqrt[ that no ] closes`)
			}
			r.at++
			index = "<mrow>" + strings.Join(nodes, "") + "</mrow>"
		}
		body, err := r.argument()
		if err != nil {
			return _TexNode{}, err
		}
		if index != "" {
			return _TexNode{xml: "<mroot>" + body + index + "</mroot>"}, nil
		}
		return _TexNode{xml: "<msqrt>" + body + "</msqrt>"}, nil
	case "left":
		open, err := r.delimiter()
		if err != nil {
			return _TexNode{}, err
		}
		nodes, err := r.row(display, func(t _TexToken) bool { return t.kind == texCommand && t.text == "right" })
		if err != nil {
			return _TexNode{}, err
		}
		if t, more := r.peek(); !more || t.kind != texCommand || t.text != "right" {
			return _TexNode{}, fmt.Errorf(`a \left that no \right closes`)
		}
		r.at++
		shut, err := r.delimiter()
		if err != nil {
			return _TexNode{}, err
		}
		fence := func(mark, form string) string {
			if mark == "" {
				return ""
			}
			return `<mo fence="true" stretchy="true" form="` + form + `">` + mark + "</mo>"
		}
		return _TexNode{xml: "<mrow>" + fence(open, "prefix") + strings.Join(nodes, "") + fence(shut, "postfix") + "</mrow>"}, nil
	case "right":
		return _TexNode{}, fmt.Errorf(`a \right with no \left before it`)
	case "operatorname":
		letters, err := r.raw()
		if err != nil {
			return _TexNode{}, err
		}
		return _TexNode{xml: `<mi mathvariant="normal">` + html.EscapeString(strings.Join(strings.Fields(letters), "")) + "</mi>", apply: true}, nil
	case "text", "textrm":
		words, err := r.raw()
		if err != nil {
			return _TexNode{}, err
		}
		return _TexNode{xml: "<mtext>" + html.EscapeString(words) + "</mtext>"}, nil
	case "pmod":
		body, err := r.argument()
		if err != nil {
			return _TexNode{}, err
		}
		space := "0.4444em"
		if display {
			space = "1em"
		}
		return _TexNode{xml: `<mspace width="` + space + `"/><mo stretchy="false">(</mo><mi>mod</mi><mspace width="0.3333em"/>` + body + `<mo stretchy="false">)</mo>`}, nil
	case "bmod":
		return _TexNode{xml: `<mo lspace="0.2222em" rspace="0.2222em">mod</mo>`}, nil
	case "quad":
		return _TexNode{xml: `<mspace width="1em"/>`}, nil
	case "qquad":
		return _TexNode{xml: `<mspace width="2em"/>`}, nil
	}
	return _TexNode{}, fmt.Errorf(`\%s is no command the page typesets`, name)
}

// raw is the text of the group that comes next, as written.
func (r *_TexReader) raw() (string, error) {
	open, more := r.peek()
	if !more || open.kind != texOpen {
		return "", fmt.Errorf("a { is due after the command")
	}
	depth := 0
	for i := r.at; i < len(r.tokens); i++ {
		switch r.tokens[i].kind {
		case texOpen:
			depth++
		case texClose:
			depth--
		}
		if depth == 0 {
			r.at = i + 1
			return r.source[open.from+1 : r.tokens[i].from], nil
		}
	}
	return "", fmt.Errorf("a { that no } closes")
}

// delimiter reads the fence a \left, a \right or a size command takes,
// as the character MathML writes; a full stop is the empty fence.
func (r *_TexReader) delimiter() (string, error) {
	t, more := r.peek()
	if !more {
		return "", fmt.Errorf("it ends where a delimiter is due")
	}
	r.at++
	if t.kind == texSymbol {
		switch t.text {
		case ".":
			return "", nil
		case "(", ")", "[", "]", "|", "/":
			return t.text, nil
		case "<":
			return "⟨", nil
		case ">":
			return "⟩", nil
		}
	}
	if mark, known := texDelimiters[t.text]; known && t.kind == texCommand {
		return mark, nil
	}
	return "", fmt.Errorf("%q is no delimiter", r.source[t.from:])
}

// _TexSymbol is a command that stands for one character: an identifier
// (mi), upright where normal is set, or an operator (mo) with the
// attributes given, its scripts set under and over it in a display
// where limits is set.
type _TexSymbol struct {
	char       string
	identifier bool
	normal     bool
	attributes string
	limits     bool
}

func (s _TexSymbol) xml() string {
	switch {
	case s.identifier && s.normal:
		return `<mi mathvariant="normal">` + s.char + "</mi>"
	case s.identifier:
		return "<mi>" + s.char + "</mi>"
	case s.attributes != "":
		return "<mo " + s.attributes + ">" + s.char + "</mo>"
	}
	return "<mo>" + html.EscapeString(s.char) + "</mo>"
}

// texSymbols are the commands that stand for one character.
var texSymbols = func() map[string]_TexSymbol {
	symbols := map[string]_TexSymbol{}
	// Identifiers: the Greek letters, a capital upright as LaTeX sets it.
	for name, char := range map[string]string{
		"alpha": "α", "beta": "β", "gamma": "γ", "delta": "δ", "epsilon": "ϵ", "varepsilon": "ε", "zeta": "ζ",
		"eta": "η", "theta": "θ", "vartheta": "ϑ", "iota": "ι", "kappa": "κ", "lambda": "λ", "mu": "μ", "nu": "ν",
		"xi": "ξ", "pi": "π", "varpi": "ϖ", "rho": "ρ", "varrho": "ϱ", "sigma": "σ", "varsigma": "ς", "tau": "τ",
		"upsilon": "υ", "phi": "ϕ", "varphi": "φ", "chi": "χ", "psi": "ψ", "omega": "ω",
		"partial": "∂", "ell": "ℓ", "hbar": "ℏ",
	} {
		symbols[name] = _TexSymbol{char: char, identifier: true}
	}
	for name, char := range map[string]string{
		"Gamma": "Γ", "Delta": "Δ", "Theta": "Θ", "Lambda": "Λ", "Xi": "Ξ", "Pi": "Π", "Sigma": "Σ",
		"Upsilon": "Υ", "Phi": "Φ", "Psi": "Ψ", "Omega": "Ω",
		"infty": "∞", "emptyset": "∅", "varnothing": "∅", "nabla": "∇", "aleph": "ℵ", "top": "⊤", "bot": "⊥",
	} {
		symbols[name] = _TexSymbol{char: char, identifier: true, normal: true}
	}
	// Operators and relations, spaced as MathML's own dictionary spaces
	// the character.
	for name, char := range map[string]string{
		"le": "≤", "leq": "≤", "ge": "≥", "geq": "≥", "ne": "≠", "neq": "≠", "equiv": "≡", "cong": "≅",
		"simeq": "≃", "sim": "∼", "approx": "≈", "propto": "∝", "ll": "≪", "gg": "≫", "prec": "≺", "succ": "≻",
		"subset": "⊂", "subseteq": "⊆", "supset": "⊃", "supseteq": "⊇", "in": "∈", "notin": "∉", "ni": "∋",
		"mid": "∣", "nmid": "∤", "parallel": "∥", "perp": "⟂",
		"cdot": "⋅", "times": "×", "otimes": "⊗", "oplus": "⊕", "ast": "∗", "star": "⋆", "circ": "∘",
		"bullet": "∙", "wedge": "∧", "vee": "∨", "cap": "∩", "cup": "∪", "sqcup": "⊔", "setminus": "∖",
		"pm": "±", "mp": "∓", "div": "÷",
		"to": "→", "rightarrow": "→", "leftarrow": "←", "leftrightarrow": "↔", "mapsto": "↦",
		"Rightarrow": "⇒", "Leftarrow": "⇐", "Leftrightarrow": "⇔", "iff": "⟺", "implies": "⟹",
		"longrightarrow": "⟶", "longmapsto": "⟼", "hookrightarrow": "↪", "twoheadrightarrow": "↠",
		"uparrow": "↑", "downarrow": "↓",
		"forall": "∀", "exists": "∃", "neg": "¬", "lnot": "¬", "land": "∧", "lor": "∨",
		"colon": ":", "prime": "′",
	} {
		symbols[name] = _TexSymbol{char: char}
	}
	for name, char := range map[string]string{"cdots": "⋯", "dots": "…", "ldots": "…", "vdots": "⋮", "ddots": "⋱"} {
		symbols[name] = _TexSymbol{char: char, attributes: `lspace="0.1667em" rspace="0.1667em"`}
	}
	// The operators that take a range: under and over in a display.
	for name, char := range map[string]string{
		"sum": "∑", "prod": "∏", "coprod": "∐", "bigcup": "⋃", "bigcap": "⋂", "bigsqcup": "⨆",
		"bigoplus": "⨁", "bigotimes": "⨂", "bigvee": "⋁", "bigwedge": "⋀",
	} {
		symbols[name] = _TexSymbol{char: char, limits: true}
	}
	for name, char := range map[string]string{"int": "∫", "oint": "∮"} {
		symbols[name] = _TexSymbol{char: char}
	}
	// The fences written as commands: each keeps its size and its side.
	for name, char := range map[string]string{"lvert": "|", "lVert": "‖", "lbrace": "{", "langle": "⟨", "lfloor": "⌊", "lceil": "⌈"} {
		symbols[name] = _TexSymbol{char: char, attributes: `fence="true" form="prefix" stretchy="false"`}
	}
	for name, char := range map[string]string{"rvert": "|", "rVert": "‖", "rbrace": "}", "rangle": "⟩", "rfloor": "⌋", "rceil": "⌉"} {
		symbols[name] = _TexSymbol{char: char, attributes: `fence="true" form="postfix" stretchy="false"`}
	}
	for name, char := range map[string]string{"vert": "|", "Vert": "‖"} {
		symbols[name] = _TexSymbol{char: char, attributes: `stretchy="false" lspace="0" rspace="0"`}
	}
	return symbols
}()

// texFunctions are the functions written upright by name, and whether
// a display sets a script under the name: a minimum's range.
var texFunctions = map[string]bool{
	"log": false, "ln": false, "lg": false, "exp": false, "sin": false, "cos": false, "tan": false, "cot": false,
	"sec": false, "csc": false, "arcsin": false, "arccos": false, "arctan": false, "sinh": false, "cosh": false,
	"tanh": false, "deg": false, "dim": false, "ker": false, "hom": false, "arg": false,
	"det": true, "gcd": true, "min": true, "max": true, "inf": true, "sup": true, "lim": true, "liminf": true,
	"limsup": true, "Pr": true,
}

// texSizes are the heights the size commands give a delimiter: \big,
// its \bigl, \bigr and \bigm, and the larger three with theirs.
var texSizes = map[string]string{"big": "1.2em", "Big": "1.8em", "bigg": "2.4em", "Bigg": "3em"}

// texDelimiters are the fences a \left, a \right or a size command
// takes that are written as commands.
var texDelimiters = map[string]string{
	"lvert": "|", "rvert": "|", "vert": "|", "|": "‖", "lVert": "‖", "rVert": "‖", "Vert": "‖",
	"lbrace": "{", "rbrace": "}", "{": "{", "}": "}", "langle": "⟨", "rangle": "⟩",
	"lfloor": "⌊", "rfloor": "⌋", "lceil": "⌈", "rceil": "⌉",
}

// texAccents are the marks set over what follows, and the one set
// under it.
var texAccents = map[string]string{
	"bar": `<mo stretchy="false">¯</mo>`, "overline": `<mo stretchy="true">¯</mo>`,
	"hat": `<mo stretchy="false">^</mo>`, "widehat": `<mo stretchy="true">^</mo>`,
	"tilde": `<mo stretchy="false">~</mo>`, "widetilde": `<mo stretchy="true">~</mo>`,
	"vec": `<mo stretchy="false">→</mo>`, "dot": `<mo>˙</mo>`,
	"underline": `<mo stretchy="true">_</mo>`,
}

// texStyles are the type styles: each gives a letter its character in
// the style.
var texStyles = map[string]func(rune) rune{
	"mathrm": func(c rune) rune { return c },
	"mathbb": texStyle(0x1D538, 0x1D552, 0x1D7D8, map[rune]rune{
		'C': 'ℂ', 'H': 'ℍ', 'N': 'ℕ', 'P': 'ℙ', 'Q': 'ℚ', 'R': 'ℝ', 'Z': 'ℤ'}),
	"mathcal": texStyle(0x1D49C, 0x1D4B6, 0, map[rune]rune{
		'B': 'ℬ', 'E': 'ℰ', 'F': 'ℱ', 'H': 'ℋ', 'I': 'ℐ', 'L': 'ℒ', 'M': 'ℳ', 'R': 'ℛ', 'e': 'ℯ', 'g': 'ℊ', 'o': 'ℴ'}),
	"mathfrak": texStyle(0x1D504, 0x1D51E, 0, map[rune]rune{
		'C': 'ℭ', 'H': 'ℌ', 'I': 'ℑ', 'R': 'ℜ', 'Z': 'ℨ'}),
	"mathbf": texStyle(0x1D400, 0x1D41A, 0x1D7CE, nil),
}

// texStyle is a type style: its capitals, small letters and digits
// start at the three characters given — 0 where the style has none —
// but for the letters Unicode sets apart.
func texStyle(capital, small, digit rune, apart map[rune]rune) func(rune) rune {
	return func(c rune) rune {
		switch styled, set := apart[c]; {
		case set:
			return styled
		case c >= 'A' && c <= 'Z':
			return capital + c - 'A'
		case c >= 'a' && c <= 'z':
			return small + c - 'a'
		case c >= '0' && c <= '9' && digit != 0:
			return digit + c - '0'
		}
		return c
	}
}
