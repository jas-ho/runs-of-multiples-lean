import RunsOfMultiplesLean.Primes
import RunsOfMultiplesLean.Lower

/-!
# Main theorem

For a finite set `S` of positive integers and `a ∈ S`, let `k(a) = kVal S a` be the least positive
integer `k` with `k * a ∉ S`. Then `max_{|S| = n} ∑_{a ∈ S} k(a) = Θ(n log n log log n)`:

* `upper_bound` (`Primes.lean`, via the entropy argument in `Upper.lean`): every such `S` with
  `|S| = n ≥ N` has `∑ k(a) ≤ C n log n log log n`;
* `lower_bound` (`Lower.lean`, smooth numbers): for every `n ≥ N` some such `S` with `|S| = n` has
  `∑ k(a) ≥ c n log n log log n`.

Lemma and equation numbers outside `Alt/` refer to `docs/runs-of-multiples.pdf`; `Alt/` contains a
second proof (`main_theorem_alt`) following `docs/first-missing-multiple.pdf`.
-/

namespace RunsOfMultiples

theorem main_theorem :
    (∃ C : ℝ, ∃ N : ℕ, ∀ S : Finset ℕ, (∀ a ∈ S, 0 < a) → N ≤ S.card →
      ((∑ a ∈ S, kVal S a : ℕ) : ℝ) ≤
        C * S.card * Real.log S.card * Real.log (Real.log S.card)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ S : Finset ℕ, (∀ a ∈ S, 0 < a) ∧
      S.card = n ∧ c * n * Real.log n * Real.log (Real.log n) ≤ ((∑ a ∈ S, kVal S a : ℕ) : ℝ)) :=
  ⟨upper_bound, lower_bound⟩

end RunsOfMultiples
