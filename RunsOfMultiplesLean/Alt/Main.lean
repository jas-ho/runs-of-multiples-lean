import RunsOfMultiplesLean.Alt.Upper
import RunsOfMultiplesLean.Alt.Lower

/-!
# Main theorem, compression proof

Same statement as `main_theorem`, proved along the route of `docs/first-missing-multiple.pdf`
(lemma and equation numbers in `Alt/` refer to that document):
* upper bound: `exists_closed` (Lemma 2, chain compressions) + `sum_L_le_of_closed`
  (Lemma 3, radical bound and double counting) in `upper_bound_alt`;
* lower bound: the box × simplex construction in `lower_bound_alt`.
-/

namespace RunsOfMultiples

theorem main_theorem_alt :
    (∃ C : ℝ, ∃ N : ℕ, ∀ S : Finset ℕ, (∀ a ∈ S, 0 < a) → N ≤ S.card →
      ((∑ a ∈ S, kVal S a : ℕ) : ℝ) ≤
        C * S.card * Real.log S.card * Real.log (Real.log S.card)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ S : Finset ℕ, (∀ a ∈ S, 0 < a) ∧
      S.card = n ∧ c * n * Real.log n * Real.log (Real.log n) ≤ ((∑ a ∈ S, kVal S a : ℕ) : ℝ)) :=
  ⟨upper_bound_alt, lower_bound_alt⟩

end RunsOfMultiples
