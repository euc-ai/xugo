// family_cnf_probe: read a family's CNF blob (<family>/<family>.cnf.pb)
// and answer the questions a key investigation asks of it.
//
//	-stats                  entry and plan counts
//	-list                   every entry key, sorted
//	-goals                  per entry: stored key and the stored goal's α-key
//	                        (no refuter build — cheap)
//	-dump DIR               per entry, one file: stored key, goal key, the
//	                        COLD key (the stored goal fed through a fresh
//	                        CNF pipeline under the current engine), the
//	                        goal, the refute prop and its normal form. The
//	                        stored/cold pair is the drift oracle for one
//	                        entry; the refute text is what a refuter
//	                        diagnosis compares across engines.
//	-alpha                  α-rename every binder of each stored goal and
//	                        recompute the cold key: an entry whose key moves
//	                        is name-sensitive (an engine fault — the key is
//	                        α-invariant by contract). With -dump DIR the two
//	                        refute texts of each such entry are written.
//	-normalize-member NAME  a registry member's stated form, its Normalize
//	                        and the resulting key — the member's own Key.
//	-keep N -out PATH       write a copy of the blob holding the first N
//	                        entries (by sorted key): the negative control
//	                        for a replay ("is the blob load-bearing?").
//	                        Never in place — the caller copies it over.
//
// The tool links the proof registry so chapter-minted constants decode.
//
// Usage:
//
//	go run ./library/cmd/family_cnf_probe -blob library/proofs/iterate/real/real_sum/real_sum.cnf.pb -stats
//	go run ./library/cmd/family_cnf_probe -blob …/real_sum.cnf.pb -dump /tmp/rs
//	go run ./library/cmd/family_cnf_probe -blob …/real_sum.cnf.pb -alpha
//	go run ./library/cmd/family_cnf_probe -normalize-member monoidal.Regroup
package main

import (
	"context"
	"flag"
	"fmt"
	"log"
	"os"
	"path/filepath"
	"sort"

	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	_ "github.com/euc-ai/xugo/library/proofs" // register every chapter's minted constants
	"github.com/euc-ai/xugo/library/registry"
	pproof "github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
)

// coldCNF feeds a stored goal through a fresh CNF pipeline under the
// current engine: the refute prop, its normal form and the key that
// form carries (nil, nil, "" when the goal does not build).
func coldCNF(goal core.Prop) (refute, norm core.Prop, key string) {
	cache := pproof.NewCNFNormalizeCache()
	ref := refuter.CreateRefuterFromPreNormalized(context.Background(), goal, cache)
	if ref == nil || ref.CNF() == nil {
		return nil, nil, ""
	}
	refute = ref.CNF().RefuteProp()
	norm, _ = cache.PreCNF.Normalize(refute)
	return refute, norm, string(norm.AlphaKey())
}

func coldText(goal core.Prop) string {
	refute, norm, _ := coldCNF(goal)
	if refute == nil {
		return "unbuildable\n"
	}
	return "refute " + prop.PrintProp(refute) + "\nnorm " + prop.PrintProp(norm) + "\n"
}

// renameBinders gives every λ-bound variable a fresh name — an
// α-neutral change, so any key it moves is name-sensitivity.
func renameBinders(t core.Term) core.Term {
	switch t := t.Core().(type) {
	case core.AppliedTerm:
		return core.Apply(renameBinders(t.Fun()), renameBinders(t.Arg()))
	case core.AbsTerm:
		v := t.Var()
		nv := ext.Var(core.TermName(string(v.Name())+"ᵅ"), v.Type()).Core().(core.VarTerm)
		body := renameBinders(t.Body()).Substitute(core.MakeTermSubst(v, nv))
		return core.Abs(nv, body)
	default:
		return t
	}
}

func renameProp(goal core.Prop) core.Prop {
	hyps := goal.Hyps()
	for i := range hyps {
		hyps[i] = renameBinders(hyps[i])
	}
	return core.MakeProp(renameBinders(goal.Conclusion()), hyps...)
}

// storedGoal decodes one entry's stored goal, nil when it does not
// decode under the current constant inventory.
func storedGoal(entry *refuter.CNFRefuteProofProto, load ext.LoadConstMeta) (goal core.Prop) {
	defer func() {
		if recover() != nil {
			goal = nil
		}
	}()
	goal, _ = ext.NewPoolReader(entry.Pool, load).Prop(entry.Goal)
	return goal
}

func sortedKeys(entries map[string]*refuter.CNFRefuteProofProto) []string {
	keys := make([]string, 0, len(entries))
	for k := range entries {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

func main() {
	path := flag.String("blob", "", "family CNF blob (<family>.cnf.pb)")
	stats := flag.Bool("stats", false, "print entry and plan counts")
	list := flag.Bool("list", false, "print every entry key, sorted")
	goals := flag.Bool("goals", false, "print stored key and goal α-key per entry")
	dump := flag.String("dump", "", "dir: write stored key, goal key, cold key, goal and refute prop per entry")
	alpha := flag.Bool("alpha", false, "α-rename every binder of each stored goal and compare the cold key")
	normalizeMember := flag.String("normalize-member", "", "registry member name: print its statement, its Normalize and the key")
	keep := flag.Int("keep", -1, "with -out: keep only the first N entries by sorted key")
	out := flag.String("out", "", "with -keep: where to write the truncated copy (never the blob itself)")
	flag.Parse()

	if *normalizeMember != "" {
		e, ok := registry.ByName(*normalizeMember)
		if !ok {
			log.Fatalf("no member %s", *normalizeMember)
		}
		stated := e.Statement().Prop
		norm, _ := prop.Normalize(stated)
		fmt.Println("stated:    ", prop.PrintProp(stated))
		fmt.Println("normalized:", prop.PrintProp(norm))
		fmt.Println("key:       ", norm.AlphaKey())
		return
	}
	if *path == "" {
		log.Fatal("-blob is required")
	}
	raw, err := os.ReadFile(*path)
	if err != nil {
		log.Fatal(err)
	}
	var blob pproof.CNFCache
	if err := proto.Unmarshal(raw, &blob); err != nil {
		log.Fatal(err)
	}

	switch {
	case *stats:
		fmt.Printf("entries=%d plans=%d\n", len(blob.Entries), len(blob.Plans))

	case *list:
		for _, k := range sortedKeys(blob.Entries) {
			fmt.Println(k)
		}

	case *goals:
		load := registry.GetConstMetaManager().LoadConstMeta
		for _, k := range sortedKeys(blob.Entries) {
			goal := storedGoal(blob.Entries[k], load)
			if goal == nil {
				fmt.Println(k, "undecodable")
				continue
			}
			fmt.Println(k, goal.AlphaKey())
		}

	case *alpha:
		load := registry.GetConstMetaManager().LoadConstMeta
		same, different, undecodable := 0, 0, 0
		for _, k := range sortedKeys(blob.Entries) {
			goal := storedGoal(blob.Entries[k], load)
			if goal == nil {
				undecodable++
				continue
			}
			_, _, k1 := coldCNF(goal)
			renamed := renameProp(goal)
			if !renamed.AlphaEquals(goal) {
				log.Fatalf("%s: the rename is not α-neutral", k)
			}
			_, _, k2 := coldCNF(renamed)
			if k1 == k2 {
				same++
				continue
			}
			different++
			fmt.Println("ALPHA-SENSITIVE", k, k1, k2)
			if *dump != "" {
				if err := os.MkdirAll(*dump, 0o755); err != nil {
					log.Fatal(err)
				}
				write := func(name string, g core.Prop) {
					txt := "goal " + prop.PrintProp(g) + "\n" + coldText(g)
					if err := os.WriteFile(filepath.Join(*dump, name), []byte(txt), 0o644); err != nil {
						log.Fatal(err)
					}
				}
				write("alpha_"+k+"_original.txt", goal)
				write("alpha_"+k+"_renamed.txt", renamed)
			}
		}
		fmt.Printf("alpha-check: same=%d different=%d undecodable=%d\n", same, different, undecodable)

	case *dump != "":
		load := registry.GetConstMetaManager().LoadConstMeta
		if err := os.MkdirAll(*dump, 0o755); err != nil {
			log.Fatal(err)
		}
		for _, k := range sortedKeys(blob.Entries) {
			goal := storedGoal(blob.Entries[k], load)
			if goal == nil {
				fmt.Println("undecodable", k)
				continue
			}
			refute, norm, cold := coldCNF(goal)
			if refute == nil {
				fmt.Println("unbuildable", k)
				continue
			}
			txt := "storedkey " + k + "\ngoalkey " + string(goal.AlphaKey()) + "\ncoldkey " + cold +
				"\ngoal " + prop.PrintProp(goal) + "\nrefute " + prop.PrintProp(refute) + "\nnorm " + prop.PrintProp(norm) + "\n"
			if err := os.WriteFile(filepath.Join(*dump, "stored_"+k+".txt"), []byte(txt), 0o644); err != nil {
				log.Fatal(err)
			}
		}

	case *keep >= 0:
		if *out == "" {
			log.Fatal("-keep needs -out: the blob itself is never rewritten")
		}
		kept := map[string]*refuter.CNFRefuteProofProto{}
		for i, k := range sortedKeys(blob.Entries) {
			if i < *keep {
				kept[k] = blob.Entries[k]
			}
		}
		fmt.Printf("entries %d -> %d (plans %d kept)\n", len(blob.Entries), len(kept), len(blob.Plans))
		blob.Entries = kept
		b, err := proto.Marshal(&blob)
		if err != nil {
			log.Fatal(err)
		}
		if err := os.WriteFile(*out, b, 0o644); err != nil {
			log.Fatal(err)
		}
		fmt.Println("written", *out)

	default:
		log.Fatal("one of -stats, -list, -goals, -dump, -alpha, -keep or -normalize-member is required")
	}
}
