package visualize

// The family graph drawn whole: every family of the corpus a block on
// the row of its height, the families that import nothing at the foot
// of the page, and an edge from a family down to each family it
// imports — the imports transitively reduced (reduceScope), so an edge
// is drawn only where no third family stands between the two.
//
// Families computes the drawing, coordinates and all, in the units of
// the page's viewBox; the page (familygraph.html.tmpl) paints it and
// answers the pointer, and lays nothing out.
//
// A block is as wide as the longer of its two lines, the path its family
// lies under and the family's own name, and the page as wide as its
// fullest row packed, so every other row has room to spare.
//
// The foot row imports nothing to aim at: its blocks are spread evenly
// about the page's vertical axis in the order of their names, and keep
// that order and those places, moved only together towards the axis.
// Every other row's blocks are ordered and placed by their neighbours. A block
// aims at the mean centre of the families it imports and, with a
// smaller weight, of its importers; a row is sorted by its blocks' aims
// and then placed (placeRow) at the positions nearest those aims, in
// weighted least squares, that keep the order, the gap between two
// blocks and the page's margins. The rows are swept upwards and back
// down until the aims settle, each row shifted part of the way towards
// the page's vertical axis after it is placed, so the drawing stays
// centred on the axis; then two blocks of a row change places wherever
// that shortens the row's edges, and the rows are placed a last few
// times in the order reached.

import (
	"fmt"
	"math"
	"path"
	"sort"
	"strings"
	"unicode/utf8"

	"github.com/euc-ai/xugo/library/index"
)

// FamilyGraph is the family graph laid out. Width and Height are the
// viewBox; Axis is the x the drawing is centred on; Base is the top of
// the height-0 row, Step the distance from a row to the row above it
// and Block a block's height. Layers counts the rows. Revision names
// the corpus drawn where the caller knows it, and is the caller's to
// set.
type FamilyGraph struct {
	Revision string       `json:"revision,omitempty"`
	Width    int          `json:"width"`
	Height   int          `json:"height"`
	Axis     float64      `json:"axis"`
	Base     float64      `json:"base"`
	Step     float64      `json:"step"`
	Block    float64      `json:"block"`
	Layers   int          `json:"layers"`
	Nodes    []FamilyNode `json:"nodes"`
	Edges    []FamilyEdge `json:"edges"`
}

// FamilyNode is a family's block: X and Y its top left corner, W
// its width. Of its Members, Proved are those the corpus proves
// outright, Postulates those it assumes for good and Cards those stated
// without a proof (index.Counts): a family is fully proved where every
// member is of the first two, so that none is a card or stands on one.
// Of its theorems, ProvedTheorems are those proved outright and
// TheoremsOnCards those not proved yet: cards, and theorems standing on
// one.
// Gloss is the family's one line, its formulas typeset
// (typeset), and Intro how its README goes on to introduce it
// (readmeIntro). Theorems are the family's theorems, its cards among
// them, and Definitions its definitions, both in the chapter's order.
// The nodes are listed by height, then by name.
type FamilyNode struct {
	Family          string             `json:"family"`
	Height          int                `json:"height"`
	Members         int                `json:"members"`
	Proved          int                `json:"proved"`
	ProvedTheorems  int                `json:"proved_theorems"`
	TheoremsOnCards int                `json:"theorems_on_cards"`
	Postulates      int                `json:"postulates"`
	Cards           int                `json:"cards"`
	Gloss           string             `json:"gloss,omitempty"`
	Intro           []ReadmeBlock      `json:"intro"`
	Definitions     []FamilyDefinition `json:"definitions"`
	Theorems        []FamilyTheorem    `json:"theorems"`
	X               float64            `json:"x"`
	Y               float64            `json:"y"`
	W               float64            `json:"w"`
}

// FamilyDefinition is a definition of a family as a proof graph draws
// one: a definition, a structure or a type registered alone, by its
// bare name, or a door call that registered several members, by the
// call's name (units.go). Status is its stratum (_Fold.status).
type FamilyDefinition struct {
	Name   string `json:"name"`
	Status string `json:"status"`
}

// FamilyTheorem is a theorem of a family by its bare name, with its
// stratum (index.Member.Status): "proved" outright, "on_cards" — proved,
// and standing on a card somewhere under it — a "card", or a
// "postulate".
type FamilyTheorem struct {
	Name   string `json:"name"`
	Status string `json:"status"`
}

// FamilyEdge says S imports T, no family between them. It leaves
// the foot of S's block at X1 and reaches the top of T's at X2.
type FamilyEdge struct {
	S  string  `json:"s"`
	T  string  `json:"t"`
	X1 float64 `json:"x1"`
	X2 float64 `json:"x2"`
}

// The family graph's page, in the units of its viewBox. The rows start
// past the left margin, which holds the heights' labels, and the page
// ends the right margin past the fullest row. A block holds two lines:
// the path its family lies under, in a smaller type, and over it the
// family's own name. Its width is that of the longer line —
// familyGraphLetter for each letter of the name and familyGraphPathLetter
// for each of the path, the advances of the page's two types — and
// familyGraphPad for its two ends.
const (
	familyGraphLeft       = 46.0
	familyGraphRight      = 34.0
	familyGraphLetter     = 5.1
	familyGraphPathLetter = 4.25
	familyGraphPad        = 10.0
	familyGraphBlock      = 24.0
	familyGraphStep       = 32.2
	familyGraphTop        = 20.0
	familyGraphBottom     = 16.0
)

// familyGraphGap is the gap between two blocks of a row of n: a fuller
// row is packed tighter.
func familyGraphGap(n int) float64 {
	switch {
	case n >= 16:
		return 6
	case n >= 10:
		return 8
	}
	return 12
}

// _FamilyRows is the family graph while it is laid out: the x a row's
// blocks lie between, left to right, and the axis midway; the blocks'
// widths and centres, the rows by height, each left to right, and a
// block's neighbours in the reduced graph — down the families it
// imports, up its importers.
type _FamilyRows struct {
	left, right, axis float64

	width  []float64
	centre []float64
	rows   [][]int
	down   [][]int
	up     [][]int
	// aim and weight are a row's aims while it is placed, by block.
	aim, weight []float64
}

// aimAt sets a block's aim: the mean centre of its neighbours, a family
// it imports counting 1 and an importer upward, and for weight the sum
// of those weights. A block with no neighbour aims at where it is.
//
// A product is rounded before it is added, here and wherever a layout
// sums products (the float64 conversions): a processor with a fused
// multiply-add would otherwise give a sum another last bit, and a
// row's order turns one bit into another drawing.
func (r *_FamilyRows) aimAt(i int, upward float64) {
	below := 0.0
	for _, v := range r.down[i] {
		below += r.centre[v]
	}
	above := 0.0
	for _, u := range r.up[i] {
		above += float64(upward * r.centre[u])
	}
	total := float64(len(r.down[i])) + float64(upward*float64(len(r.up[i])))
	if total > 0 {
		r.aim[i], r.weight[i] = (below+above)/total, total
	} else {
		r.aim[i], r.weight[i] = r.centre[i], 1
	}
}

// placeRow is where a row's blocks go, in the order given: the centres
// nearest their aims, by weighted least squares, that leave the row's
// gap between two blocks and no block past a margin. Taking from each
// aim the offset its block has from the first when the row is packed
// leaves one number per block that must not decrease along the row —
// an isotonic regression, solved by pooling adjacent violators: two
// neighbours out of order are merged into one group at their weighted
// mean, and so on until the groups' means increase.
func (r *_FamilyRows) placeRow(ids []int) []float64 {
	gap := familyGraphGap(len(ids))
	offset := make([]float64, len(ids))
	for k := 1; k < len(ids); k++ {
		offset[k] = offset[k-1] + 0.5*(r.width[ids[k-1]]+r.width[ids[k]]) + gap
	}
	last := len(ids) - 1
	low := r.left + 0.5*r.width[ids[0]]
	high := (r.right - 0.5*r.width[ids[last]]) - offset[last]
	// A group is the blocks from to to, its weight and weighted sum.
	type group struct {
		weight, sum float64
		from, to    int
	}
	var groups []group
	for k, i := range ids {
		w := math.Max(0.25, r.weight[i])
		groups = append(groups, group{w, w * (r.aim[i] - offset[k]), k, k})
		for n := len(groups); n >= 2 && groups[n-2].sum/groups[n-2].weight > groups[n-1].sum/groups[n-1].weight; n = len(groups) {
			groups[n-2].weight += groups[n-1].weight
			groups[n-2].sum += groups[n-1].sum
			groups[n-2].to = groups[n-1].to
			groups = groups[:n-1]
		}
	}
	at := make([]float64, len(ids))
	for _, g := range groups {
		z := math.Max(low, math.Min(high, g.sum/g.weight))
		for k := g.from; k <= g.to; k++ {
			at[k] = z + offset[k]
		}
	}
	return at
}

// place sets a row's centres from its aims (placeRow).
func (r *_FamilyRows) place(ids []int) {
	for k, x := range r.placeRow(ids) {
		r.centre[ids[k]] = x
	}
}

// recentre shifts a row towards the axis: by strength times the
// distance from the row's mean centre to the axis, and no further than
// a margin lets it.
func (r *_FamilyRows) recentre(ids []int, strength float64) {
	sum := 0.0
	for _, i := range ids {
		sum += r.centre[i]
	}
	shift := strength * (r.axis - sum/float64(len(ids)))
	room := math.Inf(1)
	left := math.Inf(1)
	for _, i := range ids {
		left = math.Min(left, (r.centre[i]-0.5*r.width[i])-r.left)
		room = math.Min(room, r.right-(r.centre[i]+0.5*r.width[i]))
	}
	shift = math.Max(-left, math.Min(room, shift))
	for _, i := range ids {
		r.centre[i] += shift
	}
}

// sweep aims and places a row, sorting it by its aims first when sorted
// is set, and recentres a row of three blocks or more.
func (r *_FamilyRows) sweep(ids []int, upward float64, sorted bool, strength float64) {
	for _, i := range ids {
		r.aimAt(i, upward)
	}
	if sorted {
		sort.SliceStable(ids, func(a, b int) bool { return r.aim[ids[a]] < r.aim[ids[b]] })
	}
	r.place(ids)
	if len(ids) >= 3 {
		r.recentre(ids, strength)
	}
}

// settle runs the sweeps: thirty rounds up the rows and, for the first
// twenty-four, back down. A row is sorted by its aims on the way up —
// in the last ten rounds by the mean centre of its imports, to a tenth,
// and by aim among the blocks that ties — and on the way down for the
// first eighteen rounds; after that the way down places a row in the
// order it has.
func (r *_FamilyRows) settle() {
	layers := len(r.rows)
	for round := range 30 {
		upward, strength := 0.35, 0.35
		if round >= 22 {
			upward = 0.15
		}
		if round >= 20 {
			strength = 0.18
		}
		for h := 1; h < layers; h++ {
			ids := r.rows[h]
			if round < 20 {
				r.sweep(ids, upward, true, strength)
				continue
			}
			for _, i := range ids {
				r.aimAt(i, upward)
			}
			imports := make(map[int]float64, len(ids))
			for _, i := range ids {
				sum := 0.0
				for _, v := range r.down[i] {
					sum += r.centre[v]
				}
				imports[i] = round1(sum / float64(len(r.down[i])))
			}
			sort.SliceStable(ids, func(a, b int) bool {
				if imports[ids[a]] != imports[ids[b]] {
					return imports[ids[a]] < imports[ids[b]]
				}
				return r.aim[ids[a]] < r.aim[ids[b]]
			})
			r.place(ids)
			if len(ids) >= 3 {
				r.recentre(ids, strength)
			}
		}
		if round < 24 {
			for h := layers - 2; h >= 1; h-- {
				r.sweep(r.rows[h], 0.8, round < 18, 0.25)
			}
			r.recentre(r.rows[0], 1)
		}
	}
}

// swap lets two blocks of a row change places wherever that lowers the
// row's cost by more than 1: the squared distances from its blocks, as
// placeRow would put them, to the families they import, and a quarter
// of those to their importers. Four rounds over the rows, each row
// until no exchange lowers it.
func (r *_FamilyRows) swap() {
	cost := func(ids []int) (float64, []float64) {
		for _, i := range ids {
			r.aimAt(i, 0.25)
		}
		at := r.placeRow(ids)
		below, above := 0.0, 0.0
		for k, i := range ids {
			for _, v := range r.down[i] {
				below += float64((at[k] - r.centre[v]) * (at[k] - r.centre[v]))
			}
			for _, u := range r.up[i] {
				above += float64((r.centre[u] - at[k]) * (r.centre[u] - at[k]))
			}
		}
		return below + 0.25*above, at
	}
	for range 4 {
		for h := 1; h < len(r.rows); h++ {
			ids := r.rows[h]
			if len(ids) <= 1 {
				continue
			}
			best, at := cost(ids)
			for improved := true; improved; {
				improved = false
			pairs:
				for a := 0; a < len(ids)-1; a++ {
					for b := a + 1; b < len(ids); b++ {
						tried := append([]int(nil), ids...)
						tried[a], tried[b] = tried[b], tried[a]
						if c, triedAt := cost(tried); c+1 < best {
							ids, best, at, improved = tried, c, triedAt, true
							break pairs
						}
					}
				}
			}
			r.rows[h] = ids
			for k, i := range ids {
				r.centre[i] = at[k]
			}
		}
	}
}

// polish places every row twelve times more, up the rows and back
// down, in the order the rows have.
func (r *_FamilyRows) polish() {
	layers := len(r.rows)
	for range 12 {
		for h := 1; h < layers; h++ {
			r.sweep(r.rows[h], 0.5, false, 0.2)
		}
		for h := layers - 2; h >= 1; h-- {
			r.sweep(r.rows[h], 0.5, false, 0.2)
		}
		r.recentre(r.rows[0], 1)
	}
}

// Families draws the corpus's families. It reads each family's README,
// and a README that cannot be read is the error.
func Families(c *index.Corpus) (*FamilyGraph, error) {
	families := append([]*index.Family(nil), c.Families...)
	sort.SliceStable(families, func(i, j int) bool {
		a, b := families[i], families[j]
		if a.Height != b.Height {
			return a.Height < b.Height
		}
		return a.Name < b.Name
	})
	g := &FamilyGraph{Step: familyGraphStep, Block: familyGraphBlock, Nodes: []FamilyNode{}, Edges: []FamilyEdge{}}
	fold := foldDoors(c)
	place := map[string]int{}
	names := make([]string, len(families))
	for i, f := range families {
		place[f.Name], names[i] = i, f.Name
		g.Layers = max(g.Layers, f.Height+1)
	}
	sort.Strings(names)
	edges := reduceScope(names, func(name string) []string { return families[place[name]].Imports })

	r := &_FamilyRows{width: make([]float64, len(families)), centre: make([]float64, len(families)),
		rows: make([][]int, g.Layers), down: make([][]int, len(families)), up: make([][]int, len(families)),
		aim: make([]float64, len(families)), weight: make([]float64, len(families))}
	for i, f := range families {
		r.rows[f.Height] = append(r.rows[f.Height], i)
	}
	for _, e := range edges {
		s, t := place[e.S], place[e.T]
		r.down[s] = append(r.down[s], t)
		r.up[t] = append(r.up[t], s)
	}
	// A block is as wide as its name, and the rows as wide as the
	// fullest of them packed.
	fullest := 0.0
	for _, ids := range r.rows {
		packed := float64(len(ids)-1) * familyGraphGap(len(ids))
		for _, i := range ids {
			r.width[i] = familyBlockWidth(families[i].Name)
			packed += r.width[i]
		}
		fullest = math.Max(fullest, packed)
	}
	r.left, r.right = familyGraphLeft, round1(familyGraphLeft+fullest)
	r.axis = 0.5 * (r.left + r.right)
	g.Width, g.Axis = int(math.Ceil(r.right+familyGraphRight)), round1(r.axis)

	// Every block starts on the axis, and the foot row spread evenly
	// about it in the order of its families' names.
	for i := range families {
		r.centre[i] = r.axis
	}
	foot := r.rows[0]
	for k, i := range foot {
		r.aim[i], r.weight[i] = r.axis+(float64(k)-0.5*float64(len(foot)-1))*92, 1
	}
	r.place(foot)
	r.recentre(foot, 1)
	r.settle()
	r.swap()
	r.polish()

	g.Base = round1(familyGraphTop + float64(g.Layers-1)*familyGraphStep)
	g.Height = int(math.RoundToEven(g.Base + familyGraphBlock + familyGraphBottom))
	centre := make([]float64, len(families))
	x := make([]float64, len(families))
	for h, ids := range r.rows {
		gap := familyGraphGap(len(ids))
		for k, i := range ids {
			x[i] = round1(r.centre[i] - 0.5*r.width[i])
			if k > 0 {
				x[i] = math.Max(x[i], round1(x[ids[k-1]]+r.width[ids[k-1]]+gap))
				if x[ids[k-1]]+r.width[ids[k-1]]+(gap-0.5) > x[i] {
					panic(fmt.Sprintf("visualize: family graph: %s and %s overlap on the row of height %d", families[ids[k-1]].Name, families[i].Name, h))
				}
			}
			centre[i] = round1(x[i] + r.width[i]*0.5)
		}
		if first, last := ids[0], ids[len(ids)-1]; x[first] < r.left-0.5 || x[last]+r.width[last] > r.right+0.5 {
			panic(fmt.Sprintf("visualize: family graph: the row of height %d runs past a margin, from %v to %v", h, x[first], x[last]+r.width[last]))
		}
	}
	for i, f := range families {
		blocks, err := intro(c, f)
		if err != nil {
			return nil, fmt.Errorf("visualize: family %s: %v", f.Name, err)
		}
		gloss, err := typeset(f.Gloss)
		if err != nil {
			return nil, fmt.Errorf("visualize: family %s: %v", f.Name, err)
		}
		// A theorem is listed by itself, whatever registered it; a
		// definition as its unit, a door call once, at its first part.
		theorems, definitions := []FamilyTheorem{}, []FamilyDefinition{}
		listed := map[string]bool{}
		provedTheorems, theoremsOnCards := 0, 0
		for _, m := range f.Members {
			switch m.Kind {
			case "theorem", "card", "postulate":
				theorems = append(theorems, FamilyTheorem{Name: m.ID[strings.LastIndex(m.ID, ".")+1:], Status: m.Status()})
				switch m.Status() {
				case "proved":
					provedTheorems++
				case "card", "on_cards":
					theoremsOnCards++
				}
			}
			if u := fold.of(m.ID); !listed[u] && !fold.theorem(u) {
				listed[u] = true
				definitions = append(definitions, FamilyDefinition{Name: fold.name(u), Status: fold.status(u)})
			}
		}
		g.Nodes = append(g.Nodes, FamilyNode{Family: f.Name, Height: f.Height,
			Members: f.Counts.Members, Proved: f.Counts.Proved, ProvedTheorems: provedTheorems, TheoremsOnCards: theoremsOnCards,
			Postulates: f.Counts.Postulates, Cards: f.Counts.Cards, Gloss: gloss, Intro: blocks, Definitions: definitions, Theorems: theorems,
			X: x[i], Y: round1(g.Base - float64(f.Height)*familyGraphStep), W: r.width[i]})
	}

	// A block's edges are spread along its side in the order of the
	// blocks they run to, over a span of 6 an edge, at least 6 and at
	// most the side less 8.
	port := func(i int, others []int) map[int]float64 {
		order := append([]int(nil), others...)
		sort.SliceStable(order, func(a, b int) bool {
			if centre[order[a]] != centre[order[b]] {
				return centre[order[a]] < centre[order[b]]
			}
			return order[a] < order[b]
		})
		span := math.Min(r.width[i]-8, math.Max(6, float64(len(order)-1)*6))
		at := map[int]float64{}
		for k, o := range order {
			along := 0.0
			if len(order) > 1 {
				along = float64(k)/float64(len(order)-1) - 0.5
			}
			at[o] = round1(centre[i] + along*span)
		}
		return at
	}
	foots, tops := make([]map[int]float64, len(families)), make([]map[int]float64, len(families))
	for i := range families {
		foots[i], tops[i] = port(i, r.down[i]), port(i, r.up[i])
	}
	for _, e := range edges {
		s, t := place[e.S], place[e.T]
		g.Edges = append(g.Edges, FamilyEdge{S: e.S, T: e.T, X1: foots[s][t], X2: tops[t][s]})
	}
	return g, nil
}

// familyBlockWidth is the width of a family's block: what the longer of
// its two lines takes on the page, the last segment of its name or the
// path that segment lies under.
func familyBlockWidth(family string) float64 {
	name := float64(utf8.RuneCountInString(path.Base(family))) * familyGraphLetter
	under := float64(utf8.RuneCountInString(family[:strings.LastIndex(family, "/")+1])) * familyGraphPathLetter
	return round1(math.Max(name, under) + familyGraphPad)
}
