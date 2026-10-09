# How these proofs were made

Everything in this repository was produced by AI models, working from a question posed by a friend of the repository owner. The owner passed the question to the models and chose the next steps (typeset it, formalize it, compare the two proofs, publish); neither of them wrote any of the mathematics, proofs or code. This page records which model produced which artifact, with what settings, how long it took, which tools and outside sources it used, and how the two independent solutions differ. It is meant for readers interested in how current language models do mathematics, not only in the theorem.

All times are UTC on 7 and 8 October 2026. Figures come from the session transcripts, which are not published.

## The prompt

The owner sent the same message to Claude Code (Claude Opus 5.5) and to Codex (gpt-6-astra) one minute apart. Its second paragraph, starting "btw", quotes his friend:

> Given set S of n positive integers a1 to an, define ki to be smallest positive integer such that ai times ki is not in S. Can you give an asymptomatic upper bound on sum_i ki? spend as much time as you possibly can to solve this problem and give a human readable proof
>
> btw: I have a lower bound and I believe it's tight, so lower bound is easy. Upper bound is hard. LB is n log n when S = {1, 2, 3, ... n}

The typo "asymptomatic" was left in on purpose. Codex remarked on it ("I'll take 'asymptomatic' to mean 'asymptotic'"); Claude read it as "asymptotic" without comment.

The friend knew that n log n was a lower bound and conjectured that it was tight. The conjecture is false: both models found the extra log log n factor independently.

## Where each artifact comes from

| Artifact | Produced by | Settings | Wall clock | Checked by |
|---|---|---|---|---|
| [`runs-of-multiples.pdf`](runs-of-multiples.pdf): entropy proof | Claude Code, main session | claude-opus-5-5, effort xhigh | 7 Oct 15:34 to 16:58 (first attempt lost, see below) | an Opus 5.5 "adversarial referee" subagent; numerical lemma checks; Lean |
| [`first-missing-multiple.pdf`](first-missing-multiple.pdf): compression proof | Codex (VS Code extension, codex-cli 0.160.1) | gpt-6-astra, reasoning effort xhigh | 7 Oct 15:35 to 16:20 | two review rounds by Claude Fable 5.1 (effort high, no tools); exhaustive small-case checks; Lean |
| [`runs-of-multiples-rewrite.pdf`](runs-of-multiples-rewrite.pdf): language rewrite of the entropy proof | Codex CLI 0.159.2, `codex exec` | gpt-6-astra, reasoning effort xhigh | 7 Oct 20:37 to 20:49 (12 min, 17k output tokens) | Claude Opus 5.5: script comparing all 228 formulas with the original, plus a full read |
| Lean: `main_theorem` (`RunsOfMultiplesLean/`) | Claude Code main session plus two Opus 5.5 subagents | claude-opus-5-5, effort xhigh | 7 Oct 17:00 to 17:49 | Lean kernel; `#print axioms` |
| Lean: `main_theorem_alt` (`RunsOfMultiplesLean/Alt/`) | Claude Code main session plus two Opus 5.5 subagents | claude-opus-5-5, effort xhigh | 7 Oct 17:53 to 18:13 | Lean kernel; `#print axioms` |
| README "Status and related work" | four Opus 5.5 research subagents plus one report-writing subagent | claude-opus-5-5, effort xhigh | 8 Oct 09:01 to 09:31 | Codex fact-check: gpt-6-astra, xhigh, live web search, 9 min, 12k output tokens |

Both Lean formalizations, including the one for Codex's proof, were written by Claude. Codex wrote only the informal compression proof and the rewrite of Claude's informal proof.

The prose of `runs-of-multiples.pdf` is Claude's original. The owner found it hard to read, so the rewrite was commissioned with instructions to keep the mathematics unchanged and revamp the language. Both versions are kept so the effect of the rewrite can be compared directly. The LaTeX sources of all three documents are in [`src/`](src/).

## Timeline of the two runs

| Time | Claude Code (Opus 5.5) | Codex (gpt-6-astra) |
|---|---|---|
| 15:34 to 15:35 | prompt received | prompt received |
| 15:37 | | web search for the problem (no hits) |
| 15:38 to 15:44 | | exhaustive search over all subsets of {1, …, 24}, then a second web search |
| 15:44 | | reports a construction that beats n log n |
| 15:47 | | construction confirmed; candidate upper bound via compression, checked on 327,675 small cases |
| 15:48 to 15:55 | | looks up lecture notes on Chebyshev's prime estimates; no model output from 15:49 to 15:54 |
| 15:58 | | full answer delivered: Θ(n log n log log n), compression proof and construction (23 min) |
| 16:02 | first attempt dies with an API connection error after 27 minutes; nothing was saved | |
| 15:59 | | asked to typeset, get a review from Claude Fable 5.1, revise and build a PDF (restarted at 16:06 in a follow-up thread) |
| 16:06 | owner asks "where do we stand?"; work restarts from scratch | |
| 16:14 | after 7.7 minutes of uninterrupted thinking (48k thinking tokens), first tool calls: a search for its lost attempt, then Python checks of a smooth-number construction | |
| 16:21 | numerics confirm smooth numbers beat {1, …, n}; an O(n log² n) upper bound is proved; the remaining gap is the large-run tail | |
| 16:10 to 16:18 | | two review rounds by Claude Fable 5.1, both approving; Codex revises |
| 16:20 | | final PDF |
| 16:33 | three web searches for the problem (no hits) | |
| 16:39 | upper bound closed (entropy chain rule with a sparse/dense split); lemmas checked numerically | |
| 16:45 to 16:56 | proof written up; adversarial referee subagent finds no errors and six small issues | |
| 16:57 | PDF built (no review by another model family) | |

Codex reached the complete answer about 23 minutes after the prompt. Claude's comparable point, a complete proof sketch, came at 16:39, about 33 minutes after its restart; its first attempt had been working for 27 minutes when the connection failed, and nothing from it survived.

## How the effort was spent

This section groups the work by type of activity. It covers both models from the prompt on 7 October to the end of the Codex fact-check on 8 October (13:22). Claude's work on the informal proof and Codex's solving run and write-up ran on the owner's laptop (an Apple M3 Max); from the Lean work on, everything ran on a cloud server. How the numbers were counted is described at the end of the section.

| Activity | Claude model time | Claude tool time | Claude tokens | Codex model time | Codex tool time | Codex tokens |
|---|---|---|---|---|---|---|
| Mathematical reasoning | 25.7 min | | 164k (158k) | 16.7 min | | 22.0k (17.7k) |
| Numerical experiments | | 7.5 min | | | 1.5 s | |
| Web and literature lookups | 4.1 min | 0.8 min | 23k (12k) | | 40 s | |
| Review and verification | 3.7 min | 5.0 min | 22k (15k) | 12.5 min | 1.4 min | 17.7k (7.5k) |
| Writing and typesetting | 7.8 min | 2.6 min | 48k (23k) | 19.5 min | 26 s | 31.0k (5.3k) |
| Lean formalization | 34.6 min | 24.9 min | 239k (143k) | | | |
| Publishing and cleanup | 6.5 min | 12.5 min | 41k (13k) | | | |
| Coordination | 1.4 min | 0.5 min | 7k (4k) | 0.7 min | 1 s | 0.8k (0.2k) |
| **Total** | 83.7 min | 53.8 min | 545k (367k) | 49.4 min | 2.5 min | 71.5k (30.7k) |

Claude's columns cover its main session. Codex's columns add up the solving run, the write-up with its review, the language rewrite and the fact-check. Not in the table:

- **Claude's subagents.** Ten Opus 5.5 subagents worked in parallel with the main session for 111 minutes in all: 54 minutes for Lean (4 subagents), 48 for the literature search (5) and 10 for the referee.
- **Claude Fable 5.1**, reviewing Codex's proof in two rounds, generated for 5.6 minutes and 28.8k tokens (25.2k thinking), with no tools.
- **Claude's lost first attempt** ran for 27.3 minutes before the connection error. Nothing from it was recorded, so how much of that time was generation and how much was waiting on a failing connection is unknown.
- **Codex's stalls.** During solving, 5.2 minutes passed with no output from the model (15:49 to 15:54). Its first write-up request, sent at 15:59, produced nothing in 6.7 minutes and was restarted in a new thread. Both stalls overlap the period in which Claude's first attempt failed on the same laptop, which suggests a shared network problem; the records cannot confirm it.

**What dominated.** For Claude, Lean was the largest activity by every measure: 41% of the main session's model time, 44% of its tokens, 46% of its tool time and 54 minutes in subagents. Compiling was the largest single use of tool time: 23.6 minutes in the main session's Lean work, 17.3 in subagents and 6.0 during cleanup. Mathematical reasoning came second by model time but was the most thinking-heavy activity: 96% of its tokens were thinking. Overall, Claude's main session spent 61% of its active time generating and 39% waiting on tools. Codex spent 95% generating: its tool calls were few and fast, and it did no Lean work. Writing was the largest share of Codex's model time (19.5 of 49.4 minutes); solving produced most of its reasoning tokens (17.7k of 30.7k).

**Hardest parts.** For Claude, closing the gap from O(n log² n) to O(n log n log log n): 17.1 of its 25.7 minutes of solving and 108k of its 158k thinking tokens. For Codex the records single out no step: its longest stretch without a tool call (5.5 minutes) led to the construction, and the stretch in which it confirmed the construction and found the compression bound took 3.4 minutes. In Lean, the main upper-bound file of Claude's proof and the chain-compression file of Codex's proof took the most compile rounds, mostly over casts between ℕ and ℝ and over exponent arithmetic; no compiler error forced a change to the mathematics.

**Mathematical reasoning.** Claude's solving came in three long thinking turns separated by short tool calls: 7.7 minutes (48k thinking tokens) before its first tool call, 11.3 minutes (71k) after the numerics and 5.6 minutes (36k) after the web searches. The thinking text is not stored, but Claude's short status notes mark the milestones. The note at 16:21, after the first turn and the first numerics, reports the smooth-number construction and an O(n log² n) upper bound; the note at 16:34 names the remaining obstacle, elements whose k grows faster than any power of log n; the third turn ended with the complete upper bound. Closing the gap from O(n log² n) to O(n log n log log n) took 17.1 of the 25.7 minutes and 108k of the 158k thinking tokens. Codex's longest stretches without a tool call were 5.5 minutes (7.0k reasoning tokens), between the brute-force results and the announcement of a construction that beats n log n, and 3.4 minutes (4.2k), in which it confirmed the construction, found the compression upper bound and wrote a test for it. Codex called the compression step "the key to the proof" and it was the only step it tested numerically, but its records do not show that step costing more than the construction.

**Numerical experiments.** Claude ran Python 5 times while solving, for 7.5 minutes of tool time, but 6.6 minutes of that was a single comparison of smooth-number sets with {1, …, n} that was killed (exit code 137) without output. A rerun with a cap on the set size took 16 seconds, and a log-binned count extended the comparison to 397-smooth numbers in 26 seconds. Codex ran JavaScript twice, for 1.5 seconds in all: the sum over all 2²⁴ subsets of {1, …, 24} (1.1 seconds) and a test of the compression step on 327,675 small cases (0.4 seconds). Numerical checks of finished proofs are counted under review.

**Web and literature lookups.** While solving, Claude made 3 web searches for the problem (21 seconds, no relevant hits), and only after it had the construction and the O(n log² n) bound. Earlier it had searched the owner's previous agent sessions for its lost first attempt. That search also listed the parallel Codex session; Claude printed the first 2 KB of its log (file size and Codex's system prompt, no mathematics) and read no further. Codex sent 8 search queries in 3 calls and read 2 pages of lecture notes on Chebyshev's estimates, for 40 seconds of tool time. On 8 October Claude's main session spent 4.1 minutes of model time on two searches about the result's significance and on running the literature search; its 5 literature subagents ran for 48 minutes in total within 28 minutes of wall clock, with 73 web searches, 35 page fetches and 17 Python runs. Reading Mathlib's source is counted under Lean.

**Review and verification.** Claude checked its proof with a script that tested each inequality of the upper-bound argument on 6 sets (4.2 minutes of tool time) and with the referee subagent (9.7 minutes, 11 Python runs including brute-force and simulated-annealing searches for counterexamples; verdict: correct, six small fixes). Comparing Codex's PDF with its own proof took 1.6 minutes of model time and 9k thinking tokens. Checking the language rewrite took a 2-second script, which compared all 228 formulas with the original, and a read of the PDF. On the Codex side, Claude Fable did the reviewing (see above); Codex spent 4.2 minutes preparing the two requests, polling and reading the answers. The fact-check of the README section took Codex 8.3 minutes of model time and 38 seconds of tool time, for 35 searches and 16 page reads.

**Writing and typesetting.** Claude wrote its proof as a Markdown note and then in LaTeX (2.7 and 1.9 minutes of model time), built the PDF twice (the first build stopped on a LaTeX error) and checked the layout by reading the PDF. For the rewrite it wrote Codex's prompt and installed the Tectonic LaTeX engine (2 minutes) while Codex worked. Codex spent 7.6 minutes of model time on the LaTeX write-up, with 4 builds and 18 rendered pages checked as images, and 11.9 minutes on the language rewrite, with 3 builds and its own check that all 302 mathematical expressions survived. Only 5.3k of Codex's 31k writing tokens were reasoning.

**Lean formalization.** The Lean work ran on a 4-core, 7 GB RAM cloud server. It included installing Lean and Mathlib and working around a 4-minute compile time for `import Mathlib`, solved by importing only the needed Mathlib files. Lean was not installed on the laptop, and the owner chose to move the session to the server (under a minute), where installing Lean with Mathlib's prebuilt cache took 2.6 minutes. The first two compiles used `import Mathlib` and took 4.2 minutes each (about 3 GB of memory); with targeted imports a compile took about 17 seconds. For the second proof, three agents compiled in parallel through a shared lock so that they could not exhaust the 7 GB together.

Before starting, Claude estimated a full formalization at 2,500 to 4,000 lines and many hours of compile-fix iteration; the first proof took about 1,700 lines and 50 minutes. About 13 minutes of model time and 70k thinking tokens went to setup and planning (a written blueprint for the first proof, checked by a subagent; a three-way split for the second). The agents ran the compiler 79 times, 42 in the main session (25 for the first proof, 13 for the second, 4 during cleanup) and 37 in subagents. 32 runs reported errors, the normal edit-compile-fix loop.

| File (lines) | Written by | Compile runs | Errors | Kinds of error |
|---|---|---|---|---|
| `Defs` (108) | main session | 3 | 1 | renamed lemma |
| `OneStep` (193) | main session | 2 | 1 | renamed lemma |
| `Entropy`, `Edges`, `Alt/Upper` (338) | main session | 1 each | 0 | |
| `Upper` (378) | main session | 9 | 13 | 6 type mismatches (4 of them ℕ/ℝ casts), 4 unsolved side goals, 2 automation failures, 1 unknown name |
| `Primes` (229) | main session | 3 | 3 | 2 `linarith` failures, 1 leftover step |
| `Lower` (478) | subagent | 10 | 6 | one each: rewrite, `omega`, `linarith`, instance, cast, leftover step |
| `Examples` (49) | main session | 3 | 4 | missing import, constructor notation, 2 unsolved goals |
| `Alt/Compression` (345) | main session | 3 | 4 | missing import, rewrite, instance, `linarith` |
| `Alt/Chains` (418) | main session | 6 | 13 | 2 missing imports (20 follow-on errors), 4 automation failures, 3 unsolved goals, 2 rewrites, 2 leftover steps |
| `Alt/Radical` (325) | subagent | 9 | 4 | 2 rewrites, unsolved goal, cast |
| `Alt/Lower` (587) | subagent | 13 | 7 | 3 automation failures, 3 type mismatches, 1 leftover step |

The subagents wrote their files in parts and compiled after each part, which explains their higher run counts with fewer errors per run. Each error counts once: a repeat of an unfixed error and the follow-on errors of a missing import are not counted again. Of the 56 errors, 49 were ordinary proof engineering: 14 automation failures (`linarith`, `omega`, `simp` or `rfl` could not close a goal), 14 type mismatches and other elaboration errors (5 of them casts between ℕ and ℝ), 10 unsolved side goals, 6 rewrites that found no match and 5 leftover steps after a goal was already closed. Four were missing imports, a side effect of the import workaround, and they caused 24 follow-on errors. Only 3 were unknown lemma names, 2 of them lemmas that Mathlib had renamed (`not_mem` became `notMem`); the agents also met 9 deprecation warnings. API drift was mostly handled before compiling: the plan-review subagent spent 22 minutes confirming that every Mathlib name in the blueprint existed (32 reads of Mathlib's source, 3 test compiles), and the agents read Mathlib's source 58 times in all. No compiler error forced a change to the mathematical argument; each fix was local, at most a rewrite of the failing proof block.

The files that took the most rounds were `Upper` and `Alt/Chains`. `Upper` holds the main argument of Claude's upper bound, the part that took Claude longest on paper; there, counts in ℕ meet logarithms and real powers, so most of its 13 errors were casts and arithmetic side goals, and 2 of its 9 runs only re-ran the unchanged file to see complete messages. `Alt/Chains` holds the chain-compression framework for Codex's proof. Its first compile reported 26 errors, 20 of which disappeared once two missing imports were added; the rest came from exponent arithmetic with truncated subtraction (`p ^ (D - u)`), which defeated `omega` and `rewrite` several times. Together with `Alt/Compression`, the compression step needed 763 lines, the most new Lean for any single step.

**Publishing and cleanup** took 6.5 minutes of model time and 12.5 minutes of tool time: 3 pushes to GitHub, each followed by a watched CI build, 3 full rebuilds to clear linter warnings (one showed that a cleanup edit had broken a call site), a README rewritten for outside readers, and the license. **Coordination** took 1.4 minutes: recovering after the lost attempt, moving the session to the server and relaying the rewritten PDF to the owner.

**Comparing the two runs.** After its restart Claude needed 33.6 minutes (25.7 of them generating) to reach a complete proof sketch, on top of the 27 minutes lost before; Codex needed 22.6 minutes (16.7 generating, 5.2 stalled) to reach a complete answer. Claude's counter shows seven times as many output tokens for that phase (164k against 22k), but the counters may not measure the same thing. Per minute of model time, Claude recorded about 6,400 output tokens while solving and Claude Fable about 5,100 while reviewing, against about 1,300 for Codex while solving and 1,500 during the rewrite. Either the models generate at very different speeds or the products count differently, and the records cannot tell which, so time is a safer basis for comparison than tokens. This is one run per model on one problem, so it supports no general claim about either model.

**How the numbers were counted.**

- **Model time** runs from the record that started a model call (the owner's message, a tool result or a subagent's report) to the end of the model's message. **Tool time** runs from a tool call to its result. Waiting for the owner and idle time between requests count as neither.
- A model thinks before it acts, so a long thinking turn that ends in a Python call is still mathematical reasoning. Inside the two solving windows (Claude 16:06 to 16:40 after its restart, Codex 15:35 to 15:58), all model time and tokens count as mathematical reasoning, and only tool time goes to numerics or lookups. Elsewhere a model message counts toward the activity of the tool it calls, or toward the task the owner asked for if it calls none.
- Tokens are output tokens, with thinking (Claude) or reasoning (Codex) tokens in brackets. Claude Code records them per message. Codex reports a running total; each increase goes to the tool call just before it. Claude's subagent transcripts record usage only in part, so subagents appear with wall time and tool calls only.
- Background work (subagents, Codex runs started by Claude, CI builds) overlapped with other work and is listed separately.

## What the models relied on

**Claude** solved the problem from its own knowledge: smooth numbers and Rankin's trick for the construction, and the entropy chain rule, Han's inequality and Chebyshev's prime estimates for the upper bound. Its only web searches while solving were three searches for the problem itself at 16:33, after the construction and the first upper bound; they found nothing. For the Lean work it read Mathlib's source with `grep` and discovered a recent Mathlib file with Chebyshev bounds, which removed the need to prove those estimates from scratch.

**Codex** searched the web for the problem twice in its first 10 minutes (no relevant hits), then looked up two sets of lecture notes on Chebyshev's estimates (Gordon College's *Number Theory: In Context and Interactive* and MIT 18.785). Its write-up includes an elementary appendix proving those estimates. Its search for an extremal example was computational: it maximized the sum over all subsets of {1, …, 24} before generalizing.

Both runs had access to the owner's local configuration (agent instructions, skills and tool notes). Codex read these to choose a reviewer from a different model family.

## How the approaches differ

**Finding the answer.** Codex worked bottom-up: exhaustive search on small cases showed that {1, …, n} is not optimal, the optimal small sets pointed to smooth numbers, and a compression argument followed. Claude worked top-down: a long stretch of reasoning before its first tool call produced the smooth-number heuristic and an O(n log² n) bound. Numerics then confirmed the construction, and a further stretch of reasoning closed the gap.

**Upper bound.** Claude's proof runs an entropy chain rule over prime exponents and splits by "sparse" and "dense" fibers. Codex's proof compresses the set until it is closed under taking divisors and under replacing a prime factor by a smaller prime, then bounds the radical of every element. Codex's proof is shorter and, by our rough estimate, gives a better constant (about 3 against about 23). Claude's proof shows where the log log n factor comes from: only primes below (log n)⁴ contribute it.

**Lower bound.** Claude used the smooth numbers up to X, which needed Rankin's estimate and a pigeonhole step. Codex used a box of small-prime exponents times a simplex of large-prime exponents, whose size has an exact formula.

**Review.** Claude reviewed its proof with another instance of the same model, prompted as an adversarial referee. Codex sent its proof to a model from a different family (Claude Fable 5.1) for two rounds. It also adjudicated the feedback rather than accepting it wholesale: it declined one incidental claim in the first review that was wrong. Neither informal proof had a mathematical error that the later Lean formalization exposed.

**Readability.** The owner found Claude's write-up dense. Codex's rewrite of it, with the mathematics frozen, grew from 5 to 7 pages: it added a proof overview, labelled steps and shorter sentences.

**Formalization.** Claude formalized its own proof in about 50 minutes, including setup, and Codex's proof in about 20, reusing infrastructure. Codex's compression step needed the most new Lean, about 760 lines for a general "chain compression" framework. Lean exposed no mathematical errors in either proof. The formalizations made several small changes, such as a minimal-sum argument in place of "repeat the compression until nothing changes", and a bound of m^m in place of m!.

## What these records cannot show

- **Reasoning content.** Claude's thinking and Codex's reasoning are stored redacted or encrypted, so the transcripts show how much each model thought and when, not what it thought.
- **The lost first Claude attempt.** It ran for 27 minutes and ended with a connection error before any output was recorded, so its token use is unknown.
- **Subagent token use.** Claude Code transcripts do not record it; only wall-clock time and tool calls are known.
- **Generality.** This is a single run per model on a single problem, with the models' own tooling and the owner's configuration. It is a case study, not a benchmark.
