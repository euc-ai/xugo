// rekey_cnf_blob: re-key and verify one family CNF blob in place, or
// carry an entry rename into the family blobs.
//
// A certificate's key is Normalize's word — AlphaKey(Normalize(the
// refute's CNF prop)) — so when Normalize changes, the keys move while
// the certificates still refute the same clause sets. This tool
// recomputes every entry's key from the goal it stores and checks that
// the certificate reconstructs against the clause set the current
// engine builds: an entry whose key is unchanged stays, a moved entry
// is renamed, one that no longer reconstructs is dropped (unless
// -keep-stale), and one whose CNF cannot be rebuilt in the budget is
// kept as it is. Nothing is re-searched. It is the alternative to a
// family GC when a member's refute no longer closes by live search
// while its certificate is still valid.
//
// The blob's exact-key table (CNFCache.exact_keys) names each
// certificate by the AlphaKey of its refute prop as the CNF conversion
// builds it, the key a lookup asks before it normalizes anything. The
// tool builds that refute prop for every certificate to re-key it, so
// it writes the table from what it built: a row for every certificate
// it keeps, under the certificate's key after the re-keying, and none
// for one it drops. A certificate whose CNF cannot be rebuilt keeps the
// rows it had. A change to the CNF conversion or to its naming moves
// the exact keys as a change to Normalize moves the certificates'; this
// run carries either. Without -blob it runs over every blob under
// library/proofs.
//
// Plans store no goal, so their keys cannot be recomputed here: a
// member record re-records them. A member's row record (member_rows)
// follows its certificates: a moved key is named by its new key, and
// a dropped certificate leaves the rows that named it, whose members
// the tool names — each replays at a MISS there until it is recorded
// again.
//
// -rename-consts OLD=new,… is the constant-rename migration: before
// re-keying, every constant node of every certificate's pool and every
// plan's pool is pointed at its new name (a pool's strings table is
// shared with variable and type-variable names, so the table is
// extended, never rewritten). The certificates then re-key under the
// renamed constants and are reconstructed there — a data migration of
// the recorded surface instead of a fresh, nondeterministic re-search.
//
// A blob holds only the corpus's own constants: the tool links every
// chapter, so the registry serves them.
//
// -rename-entries Old=New,… is the entry-rename migration, and it
// touches no certificate. A blob records members by registered name —
// the entries each member's proof reads and the definitions it opens
// (member_deps and member_unfolds, which the registry reads back as the
// member's dependencies), each member's capability row
// (member_capabilities), its row record (member_rows)
// and the measured members (recorded_members) — so a renamed entry
// leaves those names stale, and
// ProofEntry.DepEntries panics on a recorded dep no entry registers.
// After the source is renamed, this mode points every recorded Old at
// New, in the blob -blob names or, without it, in every blob under
// library/proofs (run from the repository root). Names are full
// registered names (`nat_arith.AddSym`), so a member moved to another
// family is the same migration. A pair is refused unless New is
// registered and Old is not — the source is renamed first — and a
// rename that would merge two rows is refused.
//
// -drop-entries Old,… is the entry-deletion migration, the same records
// and no certificate. A deleted entry's name stays in the dependency
// row of every member whose proof read it, and every reader of the
// corpus graph panics on it — the recorder of any family, the DAG gate,
// the index — until the rows are carried: this mode takes the entry's
// own rows out of every blob and its name out of every other row. A
// citer's row is then the entries its proof still reads, where the
// proof cites nothing new in the deleted entry's place; the citer's
// replay checks that row against its build, and names the citer to
// re-record where it does not hold. A name is refused while the source
// still registers it — the entry is deleted first.
//
// Every mode rewrites a blob under the writer's lock on its directory
// (cnfblob.Lock), held from the read to the write, one blob at a time:
// a recorder of the family in this tree waits for the rewrite, or the
// rewrite for the recorder, and neither writes over the other. A dry
// run writes nothing and takes no lock.
//
// Usage:
//
//	go run ./library/cmd/rekey_cnf_blob -blob library/proofs/<dir>/<family>.cnf.pb -dry-run
//	go run ./library/cmd/rekey_cnf_blob -blob library/proofs/<dir>/<family>.cnf.pb
//	go run ./library/cmd/rekey_cnf_blob -dry-run
//	go run ./library/cmd/rekey_cnf_blob -blob <pb> -rename-consts IN=set_member,EMPTY=empty_set
//	go run ./library/cmd/rekey_cnf_blob -rename-entries nat_arith.AddSym=nat_arith.AddComm -dry-run
//	go run ./library/cmd/rekey_cnf_blob -drop-entries nat_arith.AddSym -dry-run
package main

import (
	"context"
	"flag"
	"fmt"
	"io/fs"
	"log"
	"os"
	"path/filepath"
	"slices"
	"sort"
	"strings"
	"time"

	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/library/cnfblob"
	_ "github.com/euc-ai/xugo/library/proofs" // every chapter's minted constants: a family blob's goals mention them
	"github.com/euc-ai/xugo/library/registry"
	pproof "github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
)

var (
	blobPath  = flag.String("blob", "", "the family CNF blob (<family>.cnf.pb) to re-key and verify in place; every blob under library/proofs when left out")
	dryRun    = flag.Bool("dry-run", false, "compute and report; write nothing")
	verbose   = flag.Bool("v", false, "print every key move")
	rowBudget = flag.Duration("cnf-row-timeout", 2*time.Minute, "per-entry CNF rebuild budget")
	renames   = flag.String("rename-consts", "", "OLD=new,… — rename constant nodes in every pool before re-keying")
	entries   = flag.String("rename-entries", "", "Old=New,… — registered entry names to carry into the blobs' member records; no re-key; every blob under library/proofs unless -blob names one")
	drops     = flag.String("drop-entries", "", "Old,… — names of deleted entries to take out of the blobs' member records; no re-key; every blob under library/proofs unless -blob names one")
	keepStale = flag.Bool("keep-stale", false, "keep an entry that does not reconstruct here, under its new key (the replay, not this tool, is the oracle for a family blob)")
)

func main() {
	flag.Parse()
	if *entries != "" || *drops != "" {
		if *renames != "" {
			log.Fatal("-rename-entries and -drop-entries rewrite recorded entry names only; run -rename-consts on its own")
		}
		if *entries != "" && *drops != "" {
			log.Fatal("-rename-entries and -drop-entries are two migrations; run them one at a time")
		}
		paths := []string{*blobPath}
		if *blobPath == "" {
			paths = corpusBlobs()
		}
		if *entries != "" {
			table := parsePairs("-rename-entries", *entries)
			checkEntryRenames(table)
			for _, path := range paths {
				renameEntriesInBlob(path, table)
			}
			return
		}
		names := parseNames("-drop-entries", *drops)
		checkEntryDrops(names)
		for _, path := range paths {
			dropEntriesInBlob(path, names)
		}
		return
	}
	paths := []string{*blobPath}
	if *blobPath == "" {
		if *renames != "" {
			log.Fatal("-rename-consts renames in one blob: name it with -blob")
		}
		paths = corpusBlobs()
	}
	for _, path := range paths {
		rekeyBlob(path, registry.GetConstMetaManager().LoadConstMeta)
	}
}

// lockBlob takes the writer's lock on the directory of the blob at
// path, saying so where another writer holds it, and returns its
// release. A dry run writes nothing and takes no lock.
func lockBlob(path string) (release func()) {
	if *dryRun {
		return func() {}
	}
	release, err := cnfblob.Lock(filepath.Dir(path), func() {
		fmt.Printf("%s: another writer holds the blob; waiting for it to write\n", path)
	})
	if err != nil {
		log.Fatalf("lock %s: %v", path, err)
	}
	return release
}

func rekeyBlob(path string, load ext.LoadConstMeta) {
	fmt.Printf("Blob: re-keying %s\n", path)
	defer lockBlob(path)()
	raw, err := os.ReadFile(path)
	if err != nil {
		log.Fatalf("read %s: %v", path, err)
	}
	var c pproof.CNFCache
	if err := proto.Unmarshal(raw, &c); err != nil {
		log.Fatalf("decode %s: %v", path, err)
	}
	if *renames != "" {
		table := parsePairs("-rename-consts", *renames)
		nodes := 0
		for _, p := range c.Entries {
			nodes += renamePoolConsts(p.Pool, table)
		}
		for _, plan := range c.Plans {
			nodes += renamePoolConsts(plan.Pool, table)
		}
		fmt.Printf("  renamed %d constant node(s)\n", nodes)
	}
	keys := make([]string, 0, len(c.Entries))
	for k := range c.Entries {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	out := map[string]*refuter.CNFRefuteProofProto{}
	counts := map[string]int{}
	moved := map[string]string{} // a certificate's old key → its new key
	dropped := map[string]bool{} // the stale certificates not kept
	exact := map[string]string{} // a kept certificate's exact key → its key
	// name files the exact key of the certificate kept under key; the
	// first certificate in key order stands where two share a refute prop.
	name := func(exactKey, key string) {
		if _, named := exact[exactKey]; !named && exactKey != "" {
			exact[exactKey] = key
		}
	}
	for _, k := range keys {
		p := c.Entries[k]
		status, newKey, exactKey := rekeyAndVerifyProto(p, load)
		if status == "moved" && newKey == k {
			status = "ok"
		}
		counts[status]++
		switch status {
		case "ok":
			out[k] = p
			name(exactKey, k)
		case "unbuildable":
			// unverifiable: the certificate and the rows it had stand
			out[k] = p
			for old, key := range c.ExactKeys {
				if key == k {
					name(old, k)
				}
			}
		case "moved":
			if _, taken := out[newKey]; !taken {
				out[newKey] = p
				name(exactKey, newKey)
			}
			moved[k] = newKey
			if *verbose {
				fmt.Printf("  REKEY %s -> %s\n", k, newKey)
			}
		case "stale":
			if *keepStale {
				if _, taken := out[newKey]; !taken {
					out[newKey] = p
					name(exactKey, newKey)
				}
				moved[k] = newKey
			} else {
				dropped[k] = true
			}
			if *verbose {
				fmt.Printf("  STALE %s -> %s (kept=%v)\n", k, newKey, *keepStale)
			}
		}
	}
	fmt.Printf("  entries=%d %v -> kept=%d, exact keys %d -> %d\n", len(keys), counts, len(out), len(c.ExactKeys), len(exact))
	for _, member := range followRekeys(&c, moved, dropped) {
		fmt.Printf("  %s's row lost a dropped certificate: record the member again\n", member)
	}
	if *dryRun {
		return
	}
	c.Entries = out
	c.ExactKeys = nil
	if len(exact) > 0 {
		c.ExactKeys = exact
	}
	writeBlob(path, &c)
	fmt.Println("  written")
}

// followRekeys carries a re-keying into the member rows: a row naming
// a moved certificate names it by its new key, and a dropped
// certificate leaves every row that named it. Returns, sorted, the
// members whose row lost a certificate.
func followRekeys(c *pproof.CNFCache, moved map[string]string, dropped map[string]bool) (lost []string) {
	for member, row := range c.MemberRows {
		keys := make([]string, 0, len(row.GetCertificates()))
		changed := false
		for _, k := range row.GetCertificates() {
			switch {
			case dropped[k]:
				changed = true
			case moved[k] != "":
				keys = append(keys, moved[k])
				changed = true
			default:
				keys = append(keys, k)
			}
		}
		if !changed {
			continue
		}
		if len(keys) < len(row.GetCertificates()) {
			lost = append(lost, member)
		}
		sort.Strings(keys)
		c.MemberRows[member] = &pproof.RowList{Certificates: slices.Compact(keys), Plans: row.GetPlans()}
	}
	sort.Strings(lost)
	return lost
}

// writeBlob encodes c the way the family recorder does — a
// deterministic marshal, so the same content is the same bytes — and
// replaces the blob at path with it (cnfblob.Write).
func writeBlob(path string, c *pproof.CNFCache) {
	bytes, err := proto.MarshalOptions{Deterministic: true}.Marshal(c)
	if err != nil {
		log.Fatalf("encode %s: %v", path, err)
	}
	if err := cnfblob.Write(path, bytes); err != nil {
		log.Fatalf("write %s: %v", path, err)
	}
}

// parsePairs reads a rename flag's OLD=new pairs, comma-separated.
func parsePairs(flagName, spec string) map[string]string {
	table := map[string]string{}
	for _, pair := range strings.Split(spec, ",") {
		pair = strings.TrimSpace(pair)
		if pair == "" {
			continue
		}
		old, nw, ok := strings.Cut(pair, "=")
		if !ok || old == "" || nw == "" || old == nw {
			log.Fatalf("%s: %q is not OLD=new", flagName, pair)
		}
		if _, twice := table[old]; twice {
			log.Fatalf("%s: %s is renamed twice", flagName, old)
		}
		table[old] = nw
	}
	return table
}

// checkEntryRenames refuses a pair the source has not made yet: New
// must be a registered entry and Old must not, so the blobs are carried
// to the names the corpus now registers and a typo is caught here.
func checkEntryRenames(table map[string]string) {
	for old, nw := range table {
		if _, ok := registry.ByName(nw); !ok {
			log.Fatalf("-rename-entries %s=%s: %s is not a registered entry — rename the source first, then the blobs", old, nw, nw)
		}
		if _, ok := registry.ByName(old); ok {
			log.Fatalf("-rename-entries %s=%s: %s is still registered — the source still carries it", old, nw, old)
		}
	}
}

// parseNames reads a flag's comma-separated entry names.
func parseNames(flagName, spec string) map[string]bool {
	names := map[string]bool{}
	for _, name := range strings.Split(spec, ",") {
		name = strings.TrimSpace(name)
		if name == "" {
			continue
		}
		if names[name] {
			log.Fatalf("%s: %s is named twice", flagName, name)
		}
		names[name] = true
	}
	if len(names) == 0 {
		log.Fatalf("%s: no entry named", flagName)
	}
	return names
}

// checkEntryDrops refuses a name the source still registers: the entry
// is deleted first, and the blobs are then carried to the corpus that
// no longer has it.
func checkEntryDrops(names map[string]bool) {
	for name := range names {
		if _, ok := registry.ByName(name); ok {
			log.Fatalf("-drop-entries %s: %s is still registered — delete the source first, then carry the blobs", name, name)
		}
	}
}

// corpusBlobs lists every family blob under library/proofs, sorted.
func corpusBlobs() []string {
	const root = "library/proofs"
	if _, err := os.Stat(root); err != nil {
		log.Fatalf("%s: %v — run from the repository root, or name one blob with -blob", root, err)
	}
	var out []string
	err := filepath.WalkDir(root, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if !d.IsDir() && strings.HasSuffix(path, ".cnf.pb") {
			out = append(out, path)
		}
		return nil
	})
	if err != nil {
		log.Fatalf("walk %s: %v", root, err)
	}
	sort.Strings(out)
	return out
}

// renameEntriesInBlob carries table into the member records of the
// blob at path, writing it only when a name moved (and never under
// -dry-run).
func renameEntriesInBlob(path string, table map[string]string) {
	defer lockBlob(path)()
	raw, err := os.ReadFile(path)
	if err != nil {
		log.Fatalf("read %s: %v", path, err)
	}
	var c pproof.CNFCache
	if err := proto.Unmarshal(raw, &c); err != nil {
		log.Fatalf("decode %s: %v", path, err)
	}
	moved, err := renameEntries(&c, table)
	if err != nil {
		log.Fatalf("%s: %v", path, err)
	}
	if moved == 0 {
		return
	}
	verb := "renamed"
	if *dryRun {
		verb = "would rename"
	}
	fmt.Printf("%s: %s %d recorded name(s)\n", path, verb, moved)
	if !*dryRun {
		writeBlob(path, &c)
	}
}

// dropEntriesInBlob takes names out of the member records of the blob
// at path, writing it only when a name was recorded (and never under
// -dry-run).
func dropEntriesInBlob(path string, names map[string]bool) {
	defer lockBlob(path)()
	raw, err := os.ReadFile(path)
	if err != nil {
		log.Fatalf("read %s: %v", path, err)
	}
	var c pproof.CNFCache
	if err := proto.Unmarshal(raw, &c); err != nil {
		log.Fatalf("decode %s: %v", path, err)
	}
	dropped := dropEntries(&c, names)
	if dropped == 0 {
		return
	}
	verb := "dropped"
	if *dryRun {
		verb = "would drop"
	}
	fmt.Printf("%s: %s %d recorded name(s)\n", path, verb, dropped)
	if !*dryRun {
		writeBlob(path, &c)
	}
}

// dropEntries takes every recorded registered name in names out of the
// member records — the entry's own member_deps and member_unfolds rows,
// its name in every other row of the two, its member_capabilities row
// and its recorded_members mark — and returns how many names it
// removed. A row left empty stays: it is the citer's measurement,
// "reads nothing" once the one entry it read is gone.
func dropEntries(c *pproof.CNFCache, names map[string]bool) int {
	dropped := dropFromEntryRows(c.MemberDeps, names) + dropFromEntryRows(c.MemberUnfolds, names)
	for member := range c.MemberCapabilities {
		if names[member] {
			delete(c.MemberCapabilities, member)
			dropped++
		}
	}
	for member := range c.MemberRows {
		if names[member] {
			delete(c.MemberRows, member)
			dropped++
		}
	}
	kept := make([]string, 0, len(c.RecordedMembers))
	for _, member := range c.RecordedMembers {
		if names[member] {
			dropped++
			continue
		}
		kept = append(kept, member)
	}
	if len(kept) != len(c.RecordedMembers) {
		c.RecordedMembers = kept
	}
	return dropped
}

// dropFromEntryRows takes the names out of one table of entry rows —
// the row of a member that is one of them, and each of them in every
// other row — and returns how many it removed.
func dropFromEntryRows(rows map[string]*pproof.EntryList, names map[string]bool) int {
	dropped := 0
	for member, list := range rows {
		if names[member] {
			delete(rows, member)
			dropped++
			continue
		}
		kept := make([]string, 0, len(list.GetNames()))
		for _, name := range list.GetNames() {
			if names[name] {
				dropped++
				continue
			}
			kept = append(kept, name)
		}
		if len(kept) != len(list.GetNames()) {
			rows[member] = &pproof.EntryList{Names: kept}
		}
	}
	return dropped
}

// renameEntries points every recorded registered name that is a key of
// table at its new name — the member_deps and member_unfolds rows and
// the names in them, the member_capabilities rows, recorded_members —
// and returns how many names it moved. A rename that would make two
// rows one row, or put one name twice in a row, is an error: that is a
// merge, not a rename.
func renameEntries(c *pproof.CNFCache, table map[string]string) (int, error) {
	moved := 0
	rename := func(name string) string {
		if nw, ok := table[name]; ok {
			moved++
			return nw
		}
		return name
	}
	renameEntryRows := func(field string, table map[string]*pproof.EntryList) (map[string]*pproof.EntryList, error) {
		if len(table) == 0 {
			return table, nil
		}
		rows := make(map[string]*pproof.EntryList, len(table))
		for member, list := range table {
			member = rename(member)
			if _, twice := rows[member]; twice {
				return nil, fmt.Errorf("%s: two rows would be %s", field, member)
			}
			names := make([]string, 0, len(list.GetNames()))
			seen := map[string]bool{}
			for _, name := range list.GetNames() {
				name = rename(name)
				if seen[name] {
					return nil, fmt.Errorf("%s[%s]: %s would appear twice", field, member, name)
				}
				seen[name] = true
				names = append(names, name)
			}
			sort.Strings(names)
			rows[member] = &pproof.EntryList{Names: names}
		}
		return rows, nil
	}
	var err error
	if c.MemberDeps, err = renameEntryRows("member_deps", c.MemberDeps); err != nil {
		return 0, err
	}
	if c.MemberUnfolds, err = renameEntryRows("member_unfolds", c.MemberUnfolds); err != nil {
		return 0, err
	}
	if len(c.MemberCapabilities) > 0 {
		rows := make(map[string]*pproof.CapabilityList, len(c.MemberCapabilities))
		for member, list := range c.MemberCapabilities {
			member = rename(member)
			if _, twice := rows[member]; twice {
				return 0, fmt.Errorf("member_capabilities: two rows would be %s", member)
			}
			rows[member] = list
		}
		c.MemberCapabilities = rows
	}
	if len(c.MemberRows) > 0 {
		rows := make(map[string]*pproof.RowList, len(c.MemberRows))
		for member, list := range c.MemberRows {
			member = rename(member)
			if _, twice := rows[member]; twice {
				return 0, fmt.Errorf("member_rows: two rows would be %s", member)
			}
			rows[member] = list
		}
		c.MemberRows = rows
	}
	if len(c.RecordedMembers) > 0 {
		seen := map[string]bool{}
		for i, member := range c.RecordedMembers {
			member = rename(member)
			if seen[member] {
				return 0, fmt.Errorf("recorded_members: %s would appear twice", member)
			}
			seen[member] = true
			c.RecordedMembers[i] = member
		}
		sort.Strings(c.RecordedMembers)
	}
	return moved, nil
}

// renamePoolConsts points every constant node of pool whose name is a
// key of table at the new name, and returns how many it moved. The
// strings table is shared with variable and type-variable names, so a
// new name is appended (or reused where the table already has it) and
// the old string stays for whatever else refers to it.
func renamePoolConsts(pool *ext.PoolProto, table map[string]string) int {
	if pool == nil {
		return 0
	}
	index := map[string]uint32{}
	for i, str := range pool.Strings {
		if _, seen := index[str]; !seen {
			index[str] = uint32(i)
		}
	}
	moved := 0
	for _, node := range pool.Nodes {
		c := node.GetCnst()
		if c == nil {
			continue
		}
		nw, ok := table[pool.Strings[c.Name]]
		if !ok {
			continue
		}
		at, have := index[nw]
		if !have {
			at = uint32(len(pool.Strings))
			pool.Strings = append(pool.Strings, nw)
			index[nw] = at
		}
		c.Name = at
		moved++
	}
	return moved
}

// rekeyAndVerifyProto recomputes one certificate's key and checks that
// it reconstructs against the clause set the current engine builds:
// "ok" (key unchanged, reconstructs), "moved" (new key, reconstructs
// under it), "stale" (does not reconstruct), "unbuildable" (its CNF
// cannot be rebuilt in the budget). exactKey is the AlphaKey of the
// refute prop it built, the certificate's row in the exact-key table;
// "" where the CNF was not rebuilt.
func rekeyAndVerifyProto(p *refuter.CNFRefuteProofProto, load ext.LoadConstMeta) (status string, newKey string, exactKey string) {
	status = "unbuildable"
	defer func() {
		if r := recover(); r != nil {
			status = "unbuildable"
		}
	}()
	goal, _ := ext.NewPoolReader(p.Pool, load).Prop(p.Goal)
	if goal == nil {
		return
	}
	ctx, cancel := context.WithTimeout(context.Background(), *rowBudget)
	defer cancel()
	cache := pproof.NewCNFNormalizeCache()
	ref := refuter.CreateRefuterFromPreNormalized(ctx, goal, cache)
	if ref == nil || ref.CNF() == nil {
		return
	}
	exactKey = string(ref.CNF().RefuteProp().AlphaKey())
	norm, _ := cache.PreCNF.Normalize(ref.CNF().RefuteProp())
	newKey = string(norm.AlphaKey())
	if ref.ReconstructStoredProof(ctx, p, cache, load).IsZero() {
		return "stale", newKey, exactKey
	}
	return "moved", newKey, exactKey
}
