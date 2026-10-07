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
| [`runs-of-multiples-rewrite.pdf`](runs-of-multiples-rewrite.pdf): language rewrite of the entropy proof | Codex CLI 0.159.2, `codex exec` | gpt-6-astra, reasoning effort xhigh | 7 Oct 20:37 to 20:49 (12 min, 72k tokens) | Claude Opus 5.5: script comparing all 228 formulas with the original, plus a full read |
| Lean: `main_theorem` (`RunsOfMultiplesLean/`) | Claude Code main session plus two Opus 5.5 subagents | claude-opus-5-5, effort xhigh | 7 Oct 17:00 to 17:49 | Lean kernel; `#print axioms` |
| Lean: `main_theorem_alt` (`RunsOfMultiplesLean/Alt/`) | Claude Code main session plus two Opus 5.5 subagents | claude-opus-5-5, effort xhigh | 7 Oct 17:53 to 18:13 | Lean kernel; `#print axioms` |
| README "Status and related work" | four Opus 5.5 research subagents plus one report-writing subagent | claude-opus-5-5, effort xhigh | 8 Oct 09:01 to 09:31 | Codex fact-check: gpt-6-astra, xhigh, live web search, 9 min, 177k tokens |

Both Lean formalizations, including the one for Codex's proof, were written by Claude. Codex wrote only the informal compression proof and the rewrite of Claude's informal proof.

The prose of `runs-of-multiples.pdf` is Claude's original. The owner found it hard to read, so the rewrite was commissioned with instructions to keep the mathematics unchanged and revamp the language. Both versions are kept so the effect of the rewrite can be compared directly. The LaTeX sources of all three documents are in [`src/`](src/).

## Timeline of the two runs

| Time | Claude Code (Opus 5.5) | Codex (gpt-6-astra) |
|---|---|---|
| 15:34 to 15:35 | prompt received | prompt received |
| 15:37 | | web search for the problem (no hits) |
| 15:38 to 15:44 | | exhaustive search over all subsets of {1, …, 24}, then a second web search |
| 15:44 | | reports a construction that beats n log n |
| 15:47 | | construction confirmed; candidate upper bound via compression |
| 15:48 to 15:55 | | looks up references for Chebyshev's prime estimates; checks the compression step on 327,675 small cases |
| 15:58 | | full answer delivered: Θ(n log n log log n), compression proof and construction (23 min) |
| 16:02 | first attempt dies with an API connection error after 27 minutes; nothing was saved | |
| 15:59 | | asked to typeset, get a review from Claude Fable 5.1, revise and build a PDF (restarted at 16:06 in a follow-up thread) |
| 16:06 | owner asks "where do we stand?"; work restarts from scratch | |
| 16:14 | after 7.7 minutes of uninterrupted thinking (48k thinking tokens), first tool call: Python checks of a smooth-number construction | |
| 16:21 | numerics confirm smooth numbers beat {1, …, n}; an O(n log² n) upper bound is proved; the remaining gap is the large-run tail | |
| 16:10 to 16:18 | | two review rounds by Claude Fable 5.1, both approving; Codex revises |
| 16:20 | | final PDF |
| 16:33 | three web searches for the problem (no hits) | |
| 16:39 | upper bound closed (entropy chain rule with a sparse/dense split); lemmas checked numerically | |
| 16:45 to 16:56 | proof written up; adversarial referee subagent finds no errors and six small issues | |
| 16:57 | PDF built (no review by another model family) | |

Codex reached the complete answer about 23 minutes after the prompt. Claude's comparable point, a complete proof sketch, came at 16:39, about 33 minutes after its restart; its first attempt had been working for 27 minutes when the connection failed, and nothing from it survived.

## How the effort was spent

| Run | Wall clock | Output tokens (of which reasoning) | Tool use |
|---|---|---|---|
| Claude, solving (after restart) | 51 min to PDF | 204k (174k thinking) | 13 Python runs (numerics and lemma checks), 3 web searches for the problem (no hits), 1 referee subagent, LaTeX build |
| Codex, solving | 23 min | 22k (18k reasoning) | 3 web searches and 2 page reads, JavaScript brute force and compression checks |
| Codex, write-up and review | 14 min | 43k (23k reasoning) | LaTeX build, rendering pages to images for a visual check, two calls to Claude Fable 5.1 |
| Claude Fable 5.1, review of Codex's proof | 7 min | 29k (25k thinking) | none (the source was inlined into the prompt) |
| Claude, Lean for proof 1 | 50 min | 158k (94k thinking) | 40 Lean compiles in the main session, 2 subagents (plan review, lower bound) |
| Claude, Lean for proof 2 | 20 min | 90k (51k thinking) | 18 Lean compiles in the main session, 2 subagents in parallel (radical bound, box × simplex lower bound) |

Token counts are not directly comparable across the two products. Claude Code records thinking tokens per message; Codex reports cumulative reasoning tokens. Both hide the reasoning text itself. On the face of it, Codex reached the answer with about a tenth of the output tokens and under half the wall-clock time. This is one run per model on one problem, so it supports no general claim about either model.

The Lean work ran on a small cloud server. It included installing Lean and Mathlib and working around a 4-minute compile time for `import Mathlib`, solved by importing only the needed Mathlib files.

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
