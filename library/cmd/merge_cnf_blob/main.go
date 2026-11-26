// merge_cnf_blob: bring another tree's family CNF blobs into this tree
// by a set merge, with no proof run.
//
// A landing made in another tree (a worktree an agent proved in,
// another person's branch) records its members into that tree's family
// blobs. Bringing the landing here merges three blobs per family: base,
// the blob at the commit the other tree was cut from; ours, this
// tree's; theirs, the other tree's. Each table merges by what its keys
// name:
//
//   - entries (certificates) and plans are keyed by the goal they serve,
//     its α-key, so a row means the same in every tree: the merge is
//     their union. A key both trees hold with different bytes keeps
//     ours: both certificates prove the one goal, and ours's plans lead
//     to ours's certificates. No row is dropped: a row ours no longer
//     holds can be one a member of theirs read, and it then sits in
//     theirs unchanged from base. Dropping the rows no member's row
//     names is the family GC's, run once at the commit boundary. The
//     exact keys (exact_keys) are keyed by a certificate's refute prop
//     and merge the same way, each naming a certificate of the union.
//   - member_deps, member_unfolds, member_capabilities, member_rows
//     and recorded_members are keyed by member name, each the observation
//     of that member's last recording, so they merge per member, three
//     ways: where one tree's row is base's, the other tree's row stands
//     — a member recorded, added or deleted in one tree. A member whose
//     row changed in both trees, to different rows, was recorded in
//     both: ours stands and the run names the member. The replay the
//     landing runs holds every member to its capability and dependency
//     rows and names one whose rows are not its proof's, and a member
//     it names is recorded again, alone.
//
// The walk is over the other tree's blobs. One equal to ours, or to
// base, brings nothing; a blob of a family new in the other tree is
// copied. A family the other tree deleted is not deleted here, and a
// family deleted here and changed there stops the run.
//
// The tool links no chapter: a merge reads keys and member names, never
// a goal.
//
// This tree's blob is read under the writer's lock on its directory
// (cnfblob.Lock). A blob the merge brings nothing to is released at
// once; one it will write is held to the write, so a recorder of the
// family in this tree waits for the merge, or the merge for the
// recorder, and neither writes over the other. The blobs are taken in
// one order, so two merges into one tree wait for each other in turn.
// A dry run writes nothing and takes no lock.
//
// Usage, from this tree's root:
//
//	go run ./library/cmd/merge_cnf_blob -base <commit> -theirs <other tree root> -dry-run
//	go run ./library/cmd/merge_cnf_blob -base <commit> -theirs <other tree root>
package main

import (
	"bytes"
	"errors"
	"flag"
	"fmt"
	"io/fs"
	"log"
	"maps"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"

	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/library/cnfblob"
	pproof "github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
)

var (
	baseRev    = flag.String("base", "", "the commit the other tree was cut from (a worktree's Expected commit, or the merge base of two branches)")
	theirsRoot = flag.String("theirs", "", "the root of the other tree")
	dryRun     = flag.Bool("dry-run", false, "report the merge; write nothing")
)

// proofsDir is where the family blobs live, relative to a tree's root.
const proofsDir = "library/proofs"

func main() {
	flag.Parse()
	if *baseRev == "" || *theirsRoot == "" {
		log.Fatal("-base and -theirs are both required")
	}
	if _, err := os.Stat(proofsDir); err != nil {
		log.Fatalf("run from this tree's root: %v", err)
	}
	commit, err := exec.Command("git", "rev-parse", "--verify", "--quiet", *baseRev+"^{commit}").Output()
	if err != nil {
		log.Fatalf("-base %s: not a commit of this repository", *baseRev)
	}
	base := strings.TrimSpace(string(commit))
	ours, err := filepath.Abs(".")
	if err != nil {
		log.Fatal(err)
	}
	theirs, err := filepath.Abs(*theirsRoot)
	if err != nil {
		log.Fatal(err)
	}
	if ours == theirs {
		log.Fatal("-theirs names this tree")
	}

	paths, err := blobPaths(filepath.Join(theirs, proofsDir))
	if err != nil {
		log.Fatal(err)
	}
	var writes []_Write
	var stops []string
	for _, rel := range paths {
		path := filepath.Join(proofsDir, rel)
		theirsBlob, err := os.ReadFile(filepath.Join(theirs, path))
		if err != nil {
			log.Fatal(err)
		}
		release := lockBlob(path)
		oursBlob, oursErr := os.ReadFile(path)
		if oursErr != nil && !errors.Is(oursErr, fs.ErrNotExist) {
			log.Fatal(oursErr)
		}
		baseBlob, inBase, err := blobAt(base, filepath.ToSlash(path))
		if err != nil {
			log.Fatal(err)
		}
		outcome, err := mergeFile(_Sides{
			base: baseBlob, inBase: inBase,
			ours: oursBlob, inOurs: oursErr == nil,
			theirs: theirsBlob,
		})
		if err != nil {
			log.Fatalf("%s: %v", path, err)
		}
		switch {
		case outcome.stop != "":
			stops = append(stops, path+": "+outcome.stop)
			release()
		case outcome.write:
			writes = append(writes, _Write{path: path, blob: outcome.merged, release: release})
			fmt.Printf("%s: %s\n", path, outcome.describe())
		default:
			release()
		}
	}
	if len(stops) > 0 {
		log.Fatalf("no blob written:\n  %s", strings.Join(stops, "\n  "))
	}
	if len(writes) == 0 {
		fmt.Println("nothing to merge")
		return
	}
	if *dryRun {
		fmt.Printf("dry run: %d blob(s) would be written\n", len(writes))
		return
	}
	for _, w := range writes {
		if err := cnfblob.Write(w.path, w.blob); err != nil {
			log.Fatal(err)
		}
		w.release()
	}
	fmt.Printf("wrote %d blob(s); replay the families they belong to\n", len(writes))
}

// _Write is one merged blob waiting for the run to end without a
// conflict, with the release of the lock its directory is held under.
type _Write struct {
	path    string
	blob    []byte
	release func()
}

// lockBlob takes the writer's lock on the directory of this tree's blob
// at path, saying so where another writer holds it, and returns its
// release. A dry run takes no lock, and neither does a blob whose
// directory this tree does not have: no writer of this tree writes
// there.
func lockBlob(path string) (release func()) {
	if *dryRun {
		return func() {}
	}
	release, err := cnfblob.Lock(filepath.Dir(path), func() {
		fmt.Printf("%s: another writer holds the blob; waiting for it to write\n", path)
	})
	if errors.Is(err, fs.ErrNotExist) {
		return func() {}
	}
	if err != nil {
		log.Fatalf("lock %s: %v", path, err)
	}
	return release
}

// blobPaths lists the family blobs under dir, relative to it, sorted.
func blobPaths(dir string) ([]string, error) {
	var paths []string
	err := filepath.WalkDir(dir, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if !d.IsDir() && strings.HasSuffix(path, ".cnf.pb") {
			rel, err := filepath.Rel(dir, path)
			if err != nil {
				return err
			}
			paths = append(paths, rel)
		}
		return nil
	})
	slices.Sort(paths)
	return paths, err
}

// blobAt reads path at rev from this repository, and whether rev has it.
func blobAt(rev, path string) ([]byte, bool, error) {
	object := rev + ":" + path
	if err := exec.Command("git", "cat-file", "-e", object).Run(); err != nil {
		var exit *exec.ExitError
		if errors.As(err, &exit) {
			return nil, false, nil
		}
		return nil, false, err
	}
	out, err := exec.Command("git", "cat-file", "blob", object).Output()
	if err != nil {
		return nil, false, fmt.Errorf("git cat-file blob %s: %w", object, err)
	}
	return out, true, nil
}

// _Sides is one family blob in the three trees: base's and ours's
// bytes with whether the tree has the file, and theirs's.
type _Sides struct {
	base   []byte
	inBase bool
	ours   []byte
	inOurs bool
	theirs []byte
}

// _Outcome is what the merge does with one family blob: write merged
// (or nothing), with the counts the report prints, or what stops the
// run.
type _Outcome struct {
	write  bool
	merged []byte
	// copied: the family is new in the other tree and its blob is taken
	// whole.
	copied bool
	// keysAdded and plansAdded are the rows theirs brings; keysCollided
	// and plansCollided the keys both trees hold with different bytes,
	// where ours stands.
	keysAdded, plansAdded       int
	keysCollided, plansCollided int
	// members are the members whose rows the other tree's stand for;
	// recordedInBoth the members whose rows changed in both trees to
	// different rows, where ours stands.
	members        []string
	recordedInBoth []string
	// stop is why the run writes nothing, when it does not.
	stop string
}

func (o _Outcome) describe() string {
	if o.copied {
		return "new family, copied"
	}
	parts := []string{fmt.Sprintf("+%d key(s), +%d plan(s)", o.keysAdded, o.plansAdded)}
	if o.keysCollided+o.plansCollided > 0 {
		parts = append(parts, fmt.Sprintf("%d key(s) and %d plan(s) held in both with different bytes, ours kept",
			o.keysCollided, o.plansCollided))
	}
	if len(o.members) > 0 {
		parts = append(parts, "member rows from theirs: "+strings.Join(o.members, ", "))
	}
	if len(o.recordedInBoth) > 0 {
		parts = append(parts, "recorded in both trees, ours kept, the replay is the judge: "+strings.Join(o.recordedInBoth, ", "))
	}
	return strings.Join(parts, "; ")
}

// mergeFile decides one family blob: nothing to bring, a copy, or the
// merge of the three caches.
func mergeFile(s _Sides) (_Outcome, error) {
	switch {
	case s.inOurs && bytes.Equal(s.ours, s.theirs):
		return _Outcome{}, nil
	case s.inBase && bytes.Equal(s.base, s.theirs):
		return _Outcome{}, nil
	case !s.inOurs && !s.inBase:
		return _Outcome{write: true, merged: s.theirs, copied: true}, nil
	case !s.inOurs:
		return _Outcome{stop: "the family's blob is gone from this tree and changed in the other"}, nil
	}
	var base, ours, theirs pproof.CNFCache
	for _, side := range []struct {
		name  string
		bytes []byte
		into  *pproof.CNFCache
	}{{"base", s.base, &base}, {"ours", s.ours, &ours}, {"theirs", s.theirs, &theirs}} {
		if err := proto.Unmarshal(side.bytes, side.into); err != nil {
			return _Outcome{}, fmt.Errorf("decode %s: %w", side.name, err)
		}
	}
	out := mergeCaches(&base, &ours, &theirs)
	if bytes.Equal(out.merged, s.ours) {
		return _Outcome{}, nil
	}
	out.write = true
	return out, nil
}

// mergeCaches merges theirs into ours over base (file header): the
// union of the goal-keyed tables, ours standing on a collision, and the
// member-keyed tables three ways per member.
func mergeCaches(base, ours, theirs *pproof.CNFCache) _Outcome {
	var out _Outcome
	merged := proto.Clone(ours).(*pproof.CNFCache)

	// An empty map marshals as an absent one, so filling these changes
	// no byte of a merge that adds nothing.
	if merged.Entries == nil {
		merged.Entries = map[string]*refuter.CNFRefuteProofProto{}
	}
	if merged.Plans == nil {
		merged.Plans = map[string]*pproof.ByConditionPlanProto{}
	}
	out.keysAdded, out.keysCollided = unionRows(merged.Entries, theirs.Entries)
	out.plansAdded, out.plansCollided = unionRows(merged.Plans, theirs.Plans)
	// The exact keys go with the certificates: theirs's rows ours lacks,
	// ours standing where both name a certificate for one refute prop.
	for exact, key := range theirs.ExactKeys {
		if _, ok := merged.ExactKeys[exact]; ok {
			continue
		}
		if merged.ExactKeys == nil {
			merged.ExactKeys = map[string]string{}
		}
		merged.ExactKeys[exact] = key
	}

	deps, depsFromTheirs, depsInBoth := mergeMemberRows(base.MemberDeps, ours.MemberDeps, theirs.MemberDeps)
	capabilities, capabilitiesFromTheirs, capabilitiesInBoth := mergeMemberRows(
		base.MemberCapabilities, ours.MemberCapabilities, theirs.MemberCapabilities)
	rows, rowsFromTheirs, rowsInBoth := mergeMemberRows(base.MemberRows, ours.MemberRows, theirs.MemberRows)
	unfolds, unfoldsFromTheirs, unfoldsInBoth := mergeMemberRows(base.MemberUnfolds, ours.MemberUnfolds, theirs.MemberUnfolds)
	merged.MemberDeps, merged.MemberCapabilities, merged.MemberRows, merged.MemberUnfolds = deps, capabilities, rows, unfolds
	merged.RecordedMembers = mergeNames(base.RecordedMembers, ours.RecordedMembers, theirs.RecordedMembers)
	out.members = sortedUnion(depsFromTheirs, capabilitiesFromTheirs, rowsFromTheirs, unfoldsFromTheirs)
	out.recordedInBoth = sortedUnion(depsInBoth, capabilitiesInBoth, rowsInBoth, unfoldsInBoth)

	// The recorder marshals deterministically, so a merge that brings
	// nothing gives ours's bytes back.
	blob, err := proto.MarshalOptions{Deterministic: true}.Marshal(merged)
	if err != nil {
		panic(fmt.Sprintf("merge_cnf_blob: marshal the merged cache: %v", err))
	}
	out.merged = blob
	return out
}

// unionRows adds theirs's rows ours lacks into ours. Returns how many it
// added and how many keys both hold with different rows (ours stands).
func unionRows[R proto.Message](ours, theirs map[string]R) (added, collided int) {
	for k, row := range theirs {
		mine, ok := ours[k]
		switch {
		case !ok:
			ours[k] = row
			added++
		case !proto.Equal(mine, row):
			collided++
		}
	}
	return added, collided
}

// mergeMemberRows merges one member-keyed table three ways per member:
// rows equal in ours and theirs stand; else the tree whose row is
// base's takes the other's (an absent row is a row: the member deleted
// or never recorded there); a row changed in both trees to different
// rows stays ours's. Returns the merged table (nil when empty), the
// members whose row is theirs's where it differs from ours's, and the
// members whose row changed in both.
func mergeMemberRows[R proto.Message](base, ours, theirs map[string]R) (merged map[string]R, fromTheirs, inBoth []string) {
	names := map[string]bool{}
	for _, table := range []map[string]R{base, ours, theirs} {
		for name := range table {
			names[name] = true
		}
	}
	for _, name := range slices.Sorted(maps.Keys(names)) {
		b, inBase := base[name]
		o, inOurs := ours[name]
		t, inTheirs := theirs[name]
		row, present := o, inOurs
		switch {
		case sameRow(o, inOurs, t, inTheirs):
		case sameRow(b, inBase, o, inOurs):
			row, present = t, inTheirs
			fromTheirs = append(fromTheirs, name)
		case sameRow(b, inBase, t, inTheirs):
		default:
			inBoth = append(inBoth, name)
		}
		if present {
			if merged == nil {
				merged = map[string]R{}
			}
			merged[name] = row
		}
	}
	return merged, fromTheirs, inBoth
}

// sameRow reports whether two rows of a member-keyed table are one: both
// absent, or both present and equal.
func sameRow[R proto.Message](a R, inA bool, b R, inB bool) bool {
	return inA == inB && (!inA || proto.Equal(a, b))
}

// mergeNames merges recorded_members three ways per name, sorted: a name
// present in both trees or absent from both stands, else the tree that
// agrees with base takes the other's.
func mergeNames(base, ours, theirs []string) []string {
	var merged []string
	for _, name := range sortedUnion(base, ours, theirs) {
		inBase, inOurs, inTheirs := slices.Contains(base, name), slices.Contains(ours, name), slices.Contains(theirs, name)
		present := inOurs
		if inOurs != inTheirs && inBase == inOurs {
			present = inTheirs
		}
		if present {
			merged = append(merged, name)
		}
	}
	return merged
}

// sortedUnion is the sorted, de-duplicated union of the lists.
func sortedUnion(lists ...[]string) []string {
	var all []string
	for _, l := range lists {
		all = append(all, l...)
	}
	slices.Sort(all)
	return slices.Compact(all)
}
