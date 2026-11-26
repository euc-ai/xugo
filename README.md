[Website](https://euc-ai.github.io/xugo/) · [中文](./README.zh-CN.md)

# XuGo:
**People and AI write mathematics together—verified by a kernel, readable as a paper.**

On 20 November 2026, Levent Alpöge, working with AI, delivered a formal proof of the Riemann hypothesis in about 17 million lines of Lean code, and it passed verification by the machine kernel and by independent checkers.

The hard question that comes next has moved from verification to understanding and coexistence: once the correctness of a proof can be left to a machine to confirm, how are people to read it, digest it, and go on doing mathematics on top of it?

XuGo is infrastructure designed from the ground up for this, for people and AI doing mathematics together:

- **Proof as narrative: readability as a constraint of the system, not a translation after the fact.** XuGo enforces *proof as narrative* at the source, where proofs are made: every intermediate conclusion must state its formal proposition, and an automated prover is strictly isolated and sees only the premise variables passed to it explicitly, to the standard that even with every comment deleted, the body of the code alone still reconstructs the whole mathematical argument. A proof is not run first and explained to people afterwards; from the first line it grows as a mathematical narrative that people can read, review and converse with.

- **Compression and distillation: from proofs that swell once to structure that keeps being compacted.** Mathematics advances in the long run by distilling scattered techniques into reusable foundations. XuGo's design turns the software-engineering skill of restructuring that AI is good at (finding repeated code, extracting common abstractions, changing the call sites) directly into the distillation of mathematical concepts: structures are built on carrier sets, with no burden of transport across types; the dependencies of theorems are fully explicit in the source; and the fields it covers, from the Peano axioms to the complete Weil conjectures for curves, the finiteness of the class group, deformation theory, quasi-categories, probability and causal analysis, use only ten thousand-odd members in all. With fast replay that a multicore home computer can run, agents can deduplicate across chapters, strip redundant hypotheses and promote local stepping stones to shared foundational theorems again and again.

- **Interaction and human agency: people are architects, not spectators.** Most everyday mathematical research is not a bet of computing power on a dash up one isolated peak; it is trying new definitions, adjusting the boundaries of a theory, sorting out the structure of a field, and forming new intuition through repeated conversation. XuGo's card graph lets a person draw the blueprint in cards first, check that the top-level interfaces are natural while the foundations are still unproved, then hand the cards out, decoupled, to agents to fill in parallel, and finally make the rulings of taste and concept.

XuGo is built in Go. People and AI decide together what to prove and how a chapter is organized; the AI explores the proofs; a logical kernel checks every inference. In XuGo a theorem is a variable, a chapter of mathematics is a Go package, and the whole library is a software project that compiles, runs and is reused like any other.

XuGo carries analysis, topology, number theory, model theory, ∞-categories, algebraic geometry, probability and causal reasoning together on a very small set of concepts, with none of the internal friction of type transport. The mathematics XuGo covers can be seen in the [Corpus](https://euc-ai.github.io/xugo/corpus/); representative theorems XuGo has proved are on the [Landmarks](https://euc-ai.github.io/xugo/landmarks.html) page.

<details>
<summary>Is XuGo for AI agents or for people?</summary>

XuGo gives the two sides a clear division of labour, and leaves the mathematical direction, taste and structural trade-offs to people:
  - A person and an agent first settle, in conversation, a chapter's boundaries, the form of its definitions and the order of its theorems, and write the theorems not yet proved as cards, formal interfaces that pass type and dependency checks; the person has the final say on these statements and on the architecture as a whole.  
  - The card graph decouples design entirely from filling cards: an agent completes each proof on its own in a kernel session that can be saved, rolled back and resumed across interruptions. The tool shortcomings and repeated derivations exposed while exploring do not stay in one conversation: after discussion with a person they are deposited as new engine features and shared foundational lemmas, so that the next agent begins from a higher point.  
  - Once a proof lands, an independent referee agent reviews it. Mechanical problems are fixed by agents automatically, while judgments of mathematical taste, such as whether a definition is natural or whether a repeated derivation deserves to be abstracted as a new concept, always go back to people.

A typical session runs:
  a person poses a mathematical question  
  → the person and an agent settle the formal statement  
  → the agent explores a proof  
  → the kernel checks it, and a replay confirms that the proof stands  
  → another agent reviews it independently  
  → mechanical improvements are made by agents, and conceptual comments are discussed with the person  
  → the result is a proof that can be read and reused, together with proposals for improving the library and the engine  

Progress in the engine lowers the cost of proving and restructuring; distilling the mathematics reduces repeated work and exposes the next tool worth improving. Fast compilation and replay let both kinds of improvement happen often: the better the tools, the easier proving and restructuring become; the more refined the structures, the more directly later proofs reach the point. The growth of the library keeps improving the tools that produce it and the concepts that organize it, and creates the conditions for finding new structure in mathematics.

For the collaboration between people and AI and the double loop of restructuring, see [Practice](https://euc-ai.github.io/xugo/practice.html).
</details>

<details>

<summary>Lean and mathlib already exist. Why XuGo?</summary>

Lean and mathlib have built an enormous ecosystem of formalized mathematics, designed around people writing proofs by hand with dependent types and an interactive IDE. XuGo explores another road: mathematical infrastructure designed from scratch for collaboration between people and AI agents at scale.

XuGo's design choices aim at three core problems that are hard to reconcile in traditional theorem provers:
- **Proof as narrative.** In a typical Lean script a proof is a series of instructions that change state implicitly (such as `rw` and `simp`); the intermediate conclusions and the premises actually used are hidden in the IDE state, and the source itself is hard to read straight through. XuGo requires every step to write out its intermediate conclusion and the premises it depends on, so a proof can be read like a paper.
- **Structures on carrier sets instead of types, removing the "type transport tax".** Dependent types make each subfield or quotient a type of its own, so moving between objects takes coercions and transport. XuGo takes another route: elements live in simple types, and algebraic and geometric structures are defined as predicates on sets. With no isomorphism transport across types, the theorem dependencies of the whole library are visible in the source.
- **Driving the double loop of tool evolution and mathematical distillation.** In a large and complex type system, changing a foundational algebraic definition often means hours of recompilation, and restructuring the foundations is very expensive. XuGo's minimal LCF kernel and modular replay re-verify a change to the foundations quickly, so the two loops of improving the tools and distilling the concepts can turn often.

XuGo cares not only about whether a machine can check a known theorem, but about practising a new way of doing mathematical research. XuGo's proofs record their intermediate conclusions and the premises they use explicitly, so people and agents can compare the arguments of different chapters, extract repeated steps as shared lemmas, and check which hypotheses are in fact unnecessary. A local argument that served one problem may thus become a general theorem that applies to more objects. Fast compilation and proof replay make the cycle of extracting a lemma, changing the citations and verifying the result an everyday iteration.

For this mechanism, see [Practice](https://euc-ai.github.io/xugo/practice.html).


For the details of the underlying architecture, see [Architecture](https://euc-ai.github.io/xugo/architecture.html).
</details>


<details>

<summary>How do I install XuGo and use it for the first time?</summary>

**Let an AI install it**

Send the following to an AI that can run terminal commands:

> Please install XuGo for me. Clone https://github.com/euc-ai/xugo.git, read the skill documents in the repository, prepare Go as go.mod requires, and build xugo at the repository root. Then open the browse page locally. When done, tell me where the repository is installed and the address of the page.

**Install it yourself in a terminal**

Download the whole repository, because the mathematical library is part of the source. Prepare Git and Go first. The Go version is the one the repository's `go.mod` names, at least Go 1.27; if Go 1.21 or later is installed, the Go toolchain downloads the version `go.mod` asks for by itself, with no need to reinstall by hand.

In a terminal:
```sh
git clone https://github.com/euc-ai/xugo.git
cd xugo
go build -o xugo ./engine/cmd/xugo/
```

**Browse the whole library in a browser**

The whole library is published as a website that needs no installation, the [corpus browser](https://euc-ai.github.io/xugo/corpus/), written from the latest commit of the master branch.

Its first page is the dependency graph of the library's chapters: click a chapter and the right side shows its introduction and the lists of its definitions and theorems. Click a theorem to open its page, with its statement, its explanation and the results its proof depends on, and follow the dependencies further; click a definition to see what it is built from and which theorems use it. The search box at the top searches the library's theorems by name, chapter or statement.

The same pages open locally too, showing the code you checked out:
```sh
./xugo browse
```
Reading the library takes a few seconds; it then prints the address, by default `http://127.0.0.1:8717/`, to open in a browser. Ctrl-C stops it; if the port is taken, choose another with `--port`.

**Start working with an AI**

The repository comes with the `prove` skill, which describes the whole workflow, from discussing a mathematical goal and exploring proofs to checking and review.

- **Claude Code**: start `claude` at the repository root, then type `/prove` in the conversation, followed by your mathematical goal.
- **Codex**: open the local repository as a project, or start `codex` at the repository root, then type `$prove` in the conversation, followed by your mathematical goal.
- **Gemini (Antigravity / Gemini CLI)**: open the local repository as a project in Antigravity, or start `gemini` at the repository root, then ask in the conversation for the `prove` skill (or type `/prove`) and describe your mathematical goal.

For example, in Claude Code:

```text
/prove I want to study divisibility of the natural numbers. First look up
the existing results, tell me what this chapter has already proved, and
discuss with me which propositions are worth proving next.
```

In Codex, replace the leading `/prove` with `$prove`; in Antigravity or the Gemini CLI, describe the mathematical goal directly and ask for the `prove` workflow. These are typed into the AI's chat box.

You can describe the problem in natural language, without writing a formal statement first. The agent queries the library, explains the existing definitions and results, and confirms the goal and the proof route with you.

The clients find the repository's skill under `.claude/skills/`, `.agents/skills/` and `.gemini/skills/` respectively.

</details>

<details>

<summary>How does a XuGo proof script read differently from a Lean one?</summary>

XuGo has explicit requirements for the proofs it admits: the key intermediate conclusions are written in the body, the facts supporting them are connected by named references, and the mathematical role of the steps is explained. Every key node corresponds to a checkable statement. Comments help explain the idea; with the comments deleted, the program must still hold the whole derivation. A common Lean tactic script records operations such as "unfold a definition, rewrite, apply a lemma, simplify", and understanding the goal after them sometimes needs the proof state the editor displays. The difference lies mainly in the writing convention: in XuGo, an automated prover is strictly isolated and sees only the premise variables passed to it explicitly.

This has three effects:
- A stranger can rebuild the argument from the body, and reading proof code comes very close to reading a mathematics paper. Even with every comment in the file deleted, a stranger can reconstruct the whole mathematical argument from the graph of propositions and variable references in the code alone. The requirement is enforced jointly by static gates (lint) and independent review.
- The dependencies of a theorem are visible in the source.
- Derivations that are mathematically isomorphic show up as repetition in the structure of the code, so shared lemmas can be distilled as code is deduplicated.

For example, a fragment of the proof of the [Cauchy–Schwarz inequality](./library/proofs/vector/euclidean/norm.go) in the library:

```go
nonneg := a.Have(
    "the form at w is nonnegative",
    "&0 ≤ «cauchyExpansion»",
    expand.RwRev(),
    By(DotPosLe.At(a.VecAs[Real, DimN]("w"))))

// Halve — linear over the two products — then cancel the
// positive factor ‖u‖‖v‖.
bound := a.Have(
    "so ‖u‖‖v‖·⟨u,v⟩ ≤ ‖u‖‖v‖·(‖u‖‖v‖)",
    "‖u‖_n * ‖v‖_n * ⟪u, v⟫_n ≤ ‖u‖_n * ‖v‖_n * (‖u‖_n * ‖v‖_n)",
    ByArith(nonneg))
prodPos := a.Have(
    "‖u‖‖v‖ is positive",
    "&0 < ‖u‖_n * ‖v‖_n",
    By(uPos, vPos, At(real_order_ring.MulPos, normU, normV)))
a.Show(
    "cancel the positive factor ‖u‖‖v‖",
    By(
        prodPos,
        bound,
        At(real_order_ring.LessEqCancelMulLeft, normProduct, form, normProduct)))
```

This is what XuGo means by the principle of proof as narrative: the structure of the argument is kept in checkable propositions and the references between them. Even skipping the comments, a reader can read off the route of the proof; where a step needs questioning, the reader can open the theorem it cites and read on. Natural language explains the idea, the formal body carries the derivation, and the kernel checks that every step holds.

This way of writing also gives later reorganization something to work from: people and agents can compare the intermediate propositions and dependencies of different proofs, recognize repeated arguments, and extract the parts with value of their own as shared lemmas. Static gates check the writing conventions that can be checked mechanically; independent review checks that the argument can in fact be understood by a stranger.

For comparison, a fragment of the Lean script of the [Cauchy–Schwarz inequality](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/InnerProductSpace/Defs.lean#L317) in mathlib:

```lean
theorem inner_mul_inner_self_le (x y : F) :
    ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ := by
  suffices discrim (normSqF x) (2 * ‖⟪x, y⟫_𝕜‖) (normSqF y) ≤ 0 by
    rw [norm_inner_symm y x]
    rw [discrim, normSq, normSq, sq] at this
    linarith
  refine discrim_le_zero fun t ↦ ?_
  by_cases hzero : ⟪x, y⟫ = 0
  · simp only [← sq, hzero, norm_zero, mul_zero, zero_mul, add_zero]
    obtain ⟨hx, hy⟩ : (0 ≤ normSqF x ∧ 0 ≤ normSqF y) :=
      ⟨inner_self_nonneg, inner_self_nonneg⟩
    positivity
  · have hzero' : ‖⟪x, y⟫‖ ≠ 0 := norm_ne_zero_iff.2 hzero
    convert cauchy_schwarz_aux' (𝕜 := 𝕜) (⟪x, y⟫ • x) y
      (t / ‖⟪x, y⟫‖) using 3
    · field_simp
      rw [normSq, normSq, inner_smul_right, inner_smul_left,
        ← mul_assoc _ _ ⟪x, x⟫, mul_conj]
      rw [← ofReal_pow, re_ofReal_mul]
      ring
    · field_simp
      rw [inner_smul_left, mul_comm _ ⟪x, y⟫_𝕜, mul_conj,
        ← ofReal_pow, ofReal_re]
      ring
```

This Lean code writes out its main intermediate goal, the discriminant, and names facts with `have`; but after `convert`, `field_simp` and the successive `rw`, what equation each branch has become is not reflected, one by one, in the text.

</details>

<details>

<summary>What is a card? Is it the same as Lean's `sorry`?</summary>

A card is a member of the library whose formal statement is written but whose proof has not been given yet. It has a name, an explanation and dependencies that can be queried, and it can be a well-defined proof task. Citing a card means taking its statement as an assumption for now; what the kernel checks is whether, given these assumptions, the derivation that follows holds. It differs in kind from Lean's `sorry`: `sorry` is a universal placeholder that lets the compiler pass for now and collapses in the kernel into an anonymous axiom (`sorryAx`), while a card is an engineering interface for mathematical collaboration, which separates the top-level architecture of a body of mathematics from the construction of the proofs beneath it.

Cards let a large goal be broken, before its proof is finished, into formal propositions that can be reviewed, divided up and tracked. XuGo clearly distinguishes "proved", "proof still stands on cards" and "card", and lists the unproved statements a result finally stands on through its dependency chain.
Under this mechanism:

- Architecture first. Before any proof is written, a person and an agent can design a whole chapter of mathematics in conversation as a network of cards. Because every card is a Go variable with a complete type signature and explicit dependencies, the proof of the top-level main theorem can be run through while the lemmas beneath it are still cards. This checks early whether the definitions are convenient and the lemma interfaces line up; a defect found at the card stage is cheap to correct.
- Many agents building in parallel. Every card in the card graph is an independent task with clear boundaries. The system can dispatch several cold-started agents at once to fill cards in parallel, in any order. A card's statement, definitions, intended route and dependencies can serve directly as an agent's task context. Because a card's name, identity (its key) and type signature are fixed, when its real proof lands and replaces it, the theorems citing it need not change a single line.
- A transparent frontier of what is unproved. Any theorem can quickly query the unproved cards it depends on; when the card dependencies of a top-level theorem reach zero, it truly becomes a theorem that depends on no additional assumption. Every unproved card has its own identity; none is a blanket `sorry`.

Cards admit no circular argument and no hidden assumption. XuGo's built-in checks ensure that 1. the whole dependency graph is acyclic; 2. the automatic computation tools (such as the arithmetic tool Omega) cannot depend on cards; 3. the definition of a new constant (such as an object constructed with the choice operator) cannot be built on cards. Together with the requirement at replay that the dependencies a proof actually reads match its record, the cards in a theorem's dependency list are all the unproved assumptions its proof is recorded to use.

For how cards are used, see [Practice](https://euc-ai.github.io/xugo/practice.html).
</details>

<details>

<summary>
Can it discover new mathematics, or only verify mathematics already known?
</summary>

XuGo can take new propositions that have no reference proof and have an agent try to find a proof. More importantly, in continually restructuring the mathematics it already has, by deduplicating logic and repeatedly stripping away redundant hypotheses, it can find more general and more essential theorems and structures.

Why can reorganizing existing proofs lead to discovery? Suppose a theorem first asks of its object three conditions, A, B and C. Re-examining the argument, we find that B and C alone suffice; writing down that weaker premise formally and verifying it gives a theorem that applies to more objects. Likewise, when the same argument recurs in different fields, extracting it may reveal the mathematical structure they share.

XuGo's design lets this work go on without end. A proof is itself a standard Go program, so what agents are good at, finding repeated code and extracting the common part, can become an entrance to mathematical exploration: why are these two proofs alike? What conditions does the common argument need? Is it worth a lemma or a concept of its own?

XuGo's approach is threefold. First, it writes every structural condition as an explicit predicate on a set. Second, it requires every step of a proof to name the premises it depends on and every key derivation to list the facts it uses, and the system records the dependencies each proof actually reads; an agent can use this to try splitting structural conditions and deleting redundant hypotheses, and the kernel then checks whether the weakened statement still holds. Third, replaying the whole library and restructuring its foundations cost very little. As agents keep searching the whole library for repeated patterns of derivation, and restating theorems so that they ask only for the properties their proofs really use, new mathematics surfaces along the real load-bearing points of the logic:

- New lemmas grow out of local trail-blazing. An agent proving a theorem has to invent intermediate steps in its session tree. In later iterations other agents find that a temporary stepping stone built there is in fact a fact of use across chapters (proving that a splitting field of separable polynomials is Galois, for example, built locally that finitely many algebraic elements generate a finite extension, which was then extracted as a theorem of its own), and promote it to a shared theorem.
- Concepts are taken apart. For the unique factorization of ideals in algebraic number theory, textbooks usually ask, wholesale, for the ring to be a Dedekind domain, a bundle of several axioms. XuGo takes this apart: the existence theorem needs only that the chains of strict ideals above the current ideal are bounded and that maximal ideals are invertible; the uniqueness theorem needs only that the maximal ideals taking part in the factorization are invertible.
- Foundations collapse across fields. When proofs in different fields show isomorphic patterns of derivation in code, agents distil them into one shared foundation. The finiteness of the ideal class group in number theory and the Weil conjectures for curves in geometry, after repeated distillation, flowed into one set of laws of invertible fractional ideals and modules, and in the end many members of the number-field dependency cone are reused directly in the geometric proof of the Weil conjectures.
- New tasks improve the mathematics already there. Every proof in the library can become material for the next discovery, and new mathematical tasks change the organization of old proofs.

In this process agents use the explicit dependency graph for logical decomposition and code deduplication, while people, with independent referee agents, make the rulings of mathematical taste. The granularity of the definitions in human textbooks is fitted to human working memory; XuGo lets us recut mathematical concepts along the real load-bearing structure of the logic, and that is exactly where new mathematical structure can arise.

For the collaboration and restructuring mechanisms, see [Practice](https://euc-ai.github.io/xugo/practice.html).
</details>

<details>

<summary>
How do we know whether XuGo has bugs? Can a bug in XuGo produce a mathematically unsound derivation?
</summary>

XuGo's central safety principle is that even if the engine or an AI has a bug, it cannot forge a false mathematical theorem.
To see why, the key is to tell the kernel from the engine. In XuGo, mathematical rigour is guaranteed by a very small kernel; the powerful engine does not need to be free of bugs for the final derivations to be trusted.

- A minimal kernel that is easy to audit  
    XuGo uses the classic LCF architecture and concentrates all mathematical soundness in one minimal kernel, the `core/` package of a few thousand lines of code. A proved theorem is a protected object whose internal fields are completely closed to the outside: apart from the few basic inference rules in the kernel and a few named trusted entry points, no outside code can construct or tamper with it.  

    Because the kernel is small, fixed in function and almost never changed by everyday work, any person or AI can read it in full and audit every line. XuGo deliberately departs from Go's idiomatic error handling: as soon as a logical inconsistency appears, the program panics instead of returning an error. Any violation of the kernel's or the framework's invariants ends the program at once, instead of letting the error spread through the system.  

- An engine that keeps evolving

    The engine built on the kernel, which manages the proof tree, searches for routes, simplifies and computes, runs automation and talks to agents, is much larger, and in daily practice it changes often, gaining features as agents explore. But however complex it is, the engine has no authority to produce a theorem: every clever move it finds must in the end be broken down, step by step, into primitive inferences that the kernel's rules accept.  

    Suppose the engine's simplifier had a bug and believed two unequal algebraic expressions equal. It still could not turn that claim into a theorem. All its operations must reduce to combinations of the few atomic operations the kernel lists, and within Go's visibility rules it has no access to anything that could rewrite a kernel object.  

    Likewise, if a search algorithm or an agent hallucinates or takes a wrong turn, the worst that can happen is more time spent, a stuck proof or a session error, never a wrong inference slipped into the final library. This design is what lets the engine and the tools evolve quickly without the fear of breaking mathematical rigour.  

- Gates against forged definitions, circular arguments and unproved assumptions

    Around the outside, XuGo also has a full set of automated gate checks:
    - Against forged definitions: every new mathematical constant is checked for legitimacy, so that no contradiction can be smuggled in through a pathological definition.  

    - Against circular arguments: the acyclicity of the dependency graph is guaranteed jointly by the Go compiler and the gates' cycle detection. The compiler forbids circular imports between packages and circular initialization of variables within a package; dependencies read by name, such as the principles of induction and recursion, are checked by the gates on the recorded dependency graph. The gates also lock down the logical base of the automatic decision tools such as arithmetic, forbidding an automaton to depend in turn on the theorems it is proving.  

    - Transparent tracking of unproved cards: the library's statements that are not yet proved exist as cards. The system records the dependencies each proof actually reads, requires a replay to match the record exactly, and from it publishes the dependency chain of every theorem: whether a theorem is fully proved or still stands on an unproved card can be seen at a glance in the index, and unproved cards are strictly barred from the trusted base of the automation tools.  

Provided the kernel and its controlled trust boundary work correctly, no bug in the proof tools above it can forge a theorem. What a bug affects is the efficiency, success rate and usability of proving, not whether a derivation the kernel has checked holds.

So the engine keeps evolving and improving, while the very small kernel stays stable: mathematical reliability rests on that kernel, together with the explicit trusted entry points of axioms, definitions and modular verification.

</details>

<details>

<summary>Do I need to learn Go, formal logic and XuGo's own syntax before using XuGo?</summary>

No.

XuGo is designed from the start for people and AI to work together. You can begin by discussing the goal in natural language; the agent looks up existing results, drafts the formal statement and explains its definitions and conditions. You confirm whether it expresses your mathematical intent, choose the definitions, discuss the proof route and decide how the chapter is organized. Writing the proofs and checking them mechanically can be left to the agent and the kernel.

A proof is a narrative, as in a paper, and its derivation is checked by XuGo's logical kernel. In the workflow you play the part of the mathematical architect and the referee; writing code and finding lemmas can be done by agents. Even when you read the generated Go proof files, what you see is not complex low-level instructions but an explicit chain of logic strung together by `Have("what the step says", "proposition", By(premise variables))`, which you can follow step by step, like a paper, without knowing Go's syntax.

XuGo's theorem statements use the notation of sets and predicates that mathematicians know best (such as `∀x. x ∈ c ⇒ …`). Its exact syntax is described in detail in the documentation, and it is more efficient to let an agent master the details.

For the collaboration mechanism, see [Practice](https://euc-ai.github.io/xugo/practice.html).
</details>

<details>

<summary>Why Go?</summary>

In XuGo, Go does the work both of implementing the system and of writing the proofs. A theorem is a Go variable, a chapter is a package, and a reference from one chapter to another is a dependency between packages.

XuGo has no language dependency besides Go 1.27: the refutation prover, Omega, the diagram-chase closer and the other tools are all written in Go, with no call to an external tool such as Z3, CVC5, Vampire or E. Its AST analysis and documentation tools (`go test`, `go doc`) work out of the box, and the mature compiler, testing tools and refactoring tools of the Go ecosystem can all take part directly in building the mathematical library.

This brings three practical benefits.
- Proofs can be split, reused and reorganized like ordinary programs. What agents are used to doing, finding repeated code, extracting the common part and changing the call sites, here becomes finding repeated arguments, extracting a shared lemma and changing the citations. Whether what is extracted has mathematical value is still judged by people and review.
- Fast compilation and efficient replay make frequent changes to the foundations a feasible everyday task. After a shared lemma is distilled, several proofs can be changed and checked again. Changing a chapter and verifying it by replay takes from seconds to minutes.
- XuGo uses Go's generics to encode logical types, carrier sets and the dimensions of vectors and matrices in Go's static type signatures. When an agent uses the wrong carrier type for a theorem, or multiplies matrices of mismatched dimensions, the compiler reports it and stops. The Go compiler also forbids circular imports between packages, so the dependencies between chapters are acyclic by construction.

</details>

<details>

<summary>How can I contribute?</summary>

Any way of taking part is welcome: discuss where XuGo could be applied, suggest where it should go next, embed it in a project of your own (it is a Go module, and a program outside it can import the kernel and the corpus), or use it to write mathematics and tell us how that went. [Discussions](https://github.com/euc-ai/xugo/discussions) is the place for all of these.

A defect, above all a way to make the kernel accept something false, is an issue with the smallest Go test that shows it.

</details>
