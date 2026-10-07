import RunsOfMultiplesLean.Defs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.SmoothNumbers

/-!
# Runs of multiples: the lower bound

For every large `n` there is an `n`-element set `S` of positive integers with
`∑ a ∈ S, kVal S a ≥ c n log n log log n`.

Route (see `docs/runs-of-multiples.pdf`, §2):
* `Sm X y` is the set of `y`-smooth numbers in `[1, X]`. If `a ∈ Sm X y` then `j * a ∈ Sm (X * y) y`
  for all `1 ≤ j ≤ y`.
* Rankin's trick (via Mathlib's Euler product over smooth numbers) with `σ = 1 / log y` gives
  `|Sm (y ^ K) y| ≤ exp (K + C₀ y / log y)`.
* Pigeonhole over `X_i = y ^ i`, `i ≤ K = ⌈y / log y⌉`, gives a block `B = Sm (y ^ (i+1)) y`
  with `|B| ≤ exp (C₂ y / log y)` containing `G = Sm (y ^ i) y`, `|G| ≥ δ |B|`, all of whose
  first `y` multiples lie in `B`.
* `⌊n / |B|⌋` scaled copies `M ^ j • B` plus padding give the set for every large `n`.
-/

open Finset Real

namespace RunsOfMultiples

/-! ### Replication of a block -/

lemma pow_mul_inj {M j j' a a' : ℕ} (ha : 0 < a) (ha' : 0 < a') (haM : a < M) (haM' : a' < M)
    (h : M ^ j * a = M ^ j' * a') : j = j' ∧ a = a' := by
  have hM : 0 < M := by omega
  have key : ∀ {j j' a a' : ℕ}, 0 < a' → a < M → j < j' → M ^ j * a ≠ M ^ j' * a' := by
    intro j j' a a' ha' haM hjj' h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hjj'
    have h' : M ^ j * a = M ^ j * (M ^ d * M * a') := by rw [h]; ring
    have h2 := Nat.eq_of_mul_eq_mul_left (pow_pos hM j) h'
    have h1 : 1 ≤ M ^ d := Nat.one_le_pow _ _ hM
    have h3 : 1 * M * 1 ≤ M ^ d * M * a' := Nat.mul_le_mul (Nat.mul_le_mul h1 le_rfl) ha'
    omega
  rcases lt_trichotomy j j' with hlt | rfl | hgt
  · exact absurd h (key ha' haM hlt)
  · exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (pow_pos hM j) h⟩
  · exact absurd h.symm (key ha haM' hgt)

/-- Replication: from a block `B` with a subset `G` whose first `y` multiples lie in `B`,
build an `n`-element set of positive integers whose `kVal`-sum is at least
`⌊n / |B|⌋ · |G| · (y + 1)`. -/
lemma replicate (B G : Finset ℕ) (y n : ℕ) (hB : ∀ a ∈ B, 0 < a) (hGB : G ⊆ B)
    (hG : ∀ a ∈ G, ∀ j, 1 ≤ j → j ≤ y → j * a ∈ B) :
    ∃ S : Finset ℕ, (∀ a ∈ S, 0 < a) ∧ S.card = n ∧
      n / B.card * G.card * (y + 1) ≤ ∑ a ∈ S, kVal S a := by
  set M := B.sup id + 1 with hM
  set t := n / B.card with ht
  have hMpos : 0 < M := Nat.succ_pos _
  have hltM : ∀ a ∈ B, a < M := fun a ha => Nat.lt_succ_of_le (Finset.le_sup (f := id) ha)
  set φ : ℕ × ℕ → ℕ := fun p => M ^ p.1 * p.2 with hφ
  have hinj : Set.InjOn φ ↑(range t ×ˢ B) := by
    rintro ⟨j, a⟩ hja ⟨j', a'⟩ hja' h
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio, mem_coe] at hja hja'
    obtain ⟨h1, h2⟩ := pow_mul_inj (hB a hja.2) (hB a' hja'.2) (hltM a hja.2) (hltM a' hja'.2) h
    exact Prod.ext h1 h2
  set T := (range t ×ˢ B).image φ with hT
  set G' := (range t ×ˢ G).image φ with hG'
  have hTcard : T.card ≤ n := by
    refine card_image_le.trans ?_
    rw [card_product, card_range]
    exact Nat.div_mul_le_self n B.card
  have hUcard : n ≤ (T ∪ Icc 1 n).card := by
    have := card_le_card (subset_union_right (s₁ := T) (s₂ := Icc 1 n))
    simpa using this
  obtain ⟨S, hTS, hSU, hScard⟩ := exists_subsuperset_card_eq subset_union_left hTcard hUcard
  have hTpos : ∀ x ∈ T, 0 < x := by
    intro x hx
    obtain ⟨⟨j, a⟩, hja, rfl⟩ := mem_image.1 hx
    rw [mem_product] at hja
    exact Nat.mul_pos (pow_pos hMpos j) (hB a hja.2)
  have hSpos : ∀ a ∈ S, 0 < a := by
    intro a ha
    rcases mem_union.1 (hSU ha) with h | h
    · exact hTpos a h
    · exact (mem_Icc.1 h).1
  have hG'T : G' ⊆ T := image_subset_image (product_subset_product_right hGB)
  have hk : ∀ x ∈ G', y + 1 ≤ kVal S x := by
    intro x hx
    obtain ⟨⟨j, a⟩, hja, rfl⟩ := mem_image.1 hx
    rw [mem_product] at hja
    have hxpos : 0 < φ (j, a) := hTpos _ (hG'T hx)
    have := (forall_mul_mem_iff S hxpos y).1 (fun i hi => by
      rw [mem_Icc] at hi
      refine hTS (mem_image.2 ⟨(j, i * a), mem_product.2 ⟨hja.1, hG a hja.2 i hi.1 hi.2⟩, ?_⟩)
      simp only [hφ]
      ring)
    omega
  have hG'card : G'.card = t * G.card := by
    rw [card_image_of_injOn (hinj.mono (coe_subset.2 (product_subset_product_right hGB))),
      card_product, card_range]
  refine ⟨S, hSpos, hScard, ?_⟩
  calc t * G.card * (y + 1) = ∑ x ∈ G', (y + 1) := by rw [sum_const, smul_eq_mul, hG'card]
    _ ≤ ∑ x ∈ G', kVal S x := sum_le_sum hk
    _ ≤ ∑ x ∈ S, kVal S x := sum_le_sum_of_subset (hG'T.trans hTS)

/-! ### Elementary analytic estimates -/

lemma log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) : log x ≤ 2 * √x := by
  have h1 : log √x = log x / 2 := log_sqrt (by linarith)
  have h2 : log √x ≤ √x - 1 := log_le_sub_one_of_pos (sqrt_pos.2 (by linarith))
  linarith

lemma log_sq_le {x : ℝ} (hx : 1 ≤ x) : log x ^ 2 ≤ 16 * √x := by
  have hs : 1 ≤ √x := by rw [show (1:ℝ) = √1 by simp]; exact sqrt_le_sqrt hx
  have h1 : log x = 4 * log √(√x) := by
    rw [log_sqrt (sqrt_nonneg _), log_sqrt (by linarith)]; ring
  have h2 : log √(√x) ≤ √(√x) - 1 := log_le_sub_one_of_pos (sqrt_pos.2 (by linarith))
  have h3 : √(√x) ^ 2 = √x := sq_sqrt (sqrt_nonneg _)
  have h4 : 0 ≤ log √(√x) := log_nonneg (by rw [show (1:ℝ) = √1 by simp]; exact sqrt_le_sqrt hs)
  have h5 : log √(√x) ^ 2 ≤ √(√x) ^ 2 := pow_le_pow_left₀ h4 (by linarith) 2
  rw [h1]
  nlinarith

lemma sqrt_le_div_log {x : ℝ} (hx : 1 < x) : √x ≤ 2 * (x / log x) := by
  have hl : 0 < log x := log_pos hx
  have h1 := log_le_two_sqrt hx.le
  have h2 : √x * √x = x := mul_self_sqrt (by linarith)
  rw [mul_div_assoc', le_div_iff₀ hl]
  have : 0 ≤ √x := sqrt_nonneg _
  nlinarith

lemma sqrt_mul_log_le {x : ℝ} (hx : 1 < x) : √x * log x ≤ 16 * (x / log x) := by
  have hl : 0 < log x := log_pos hx
  have h1 := log_sq_le hx.le
  have h2 : √x * √x = x := mul_self_sqrt (by linarith)
  rw [mul_div_assoc', le_div_iff₀ hl]
  have : 0 ≤ √x := sqrt_nonneg _
  nlinarith

lemma inv_one_sub_exp_neg_le {u : ℝ} (hu : 0 < u) : (1 - exp (-u))⁻¹ ≤ exp (1 / u) := by
  have h1 : 1 + u ≤ exp u := by linarith [add_one_le_exp u]
  have h2 : exp (-u) ≤ (1 + u)⁻¹ := by rw [exp_neg]; exact inv_anti₀ (by linarith) h1
  have h3 : u / (1 + u) ≤ 1 - exp (-u) := by
    have : u / (1 + u) = 1 - (1 + u)⁻¹ := by field_simp; ring
    linarith
  have h4 : 0 < u / (1 + u) := by positivity
  calc (1 - exp (-u))⁻¹ ≤ (u / (1 + u))⁻¹ := inv_anti₀ h4 h3
    _ = 1 / u + 1 := by field_simp
    _ ≤ exp (1 / u) := add_one_le_exp _

/-! ### Smooth numbers and Rankin's bound -/

/-- The `y`-smooth numbers in `[1, X]`. -/
def Sm (X y : ℕ) : Finset ℕ := Nat.smoothNumbersUpTo X (y + 1)

lemma pos_of_mem_Sm {X y m : ℕ} (hm : m ∈ Sm X y) : 0 < m :=
  Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (Nat.mem_smoothNumbersUpTo.1 hm).2)

lemma one_mem_Sm {X y : ℕ} (hX : 1 ≤ X) : 1 ∈ Sm X y :=
  Nat.mem_smoothNumbersUpTo.2 ⟨hX, Nat.mem_smoothNumbers.2 ⟨one_ne_zero, fun p hp => by simp at hp⟩⟩

lemma Sm_mono {X X' y : ℕ} (h : X ≤ X') : Sm X y ⊆ Sm X' y := by
  intro m hm
  rw [Sm, Nat.mem_smoothNumbersUpTo] at hm ⊢
  exact ⟨hm.1.trans h, hm.2⟩

lemma mul_mem_Sm {X y a j : ℕ} (ha : a ∈ Sm X y) (hj1 : 1 ≤ j) (hjy : j ≤ y) :
    j * a ∈ Sm (X * y) y := by
  rw [Sm, Nat.mem_smoothNumbersUpTo] at ha ⊢
  refine ⟨?_, Nat.mul_mem_smoothNumbers (Nat.mem_smoothNumbers_of_lt hj1 (by omega)) ha.2⟩
  rw [mul_comm X y]
  exact Nat.mul_le_mul hjy ha.1

/-- The completely multiplicative function `m ↦ m ^ (-σ)`. -/
noncomputable def rpowHom (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-σ)
  map_one' := by simp
  map_mul' m n := by push_cast; exact Real.mul_rpow m.cast_nonneg n.cast_nonneg

lemma rankin_sum (σ : ℝ) (hσ : 0 < σ) (y X : ℕ) :
    ∑ m ∈ Sm X y, (m : ℝ) ^ (-σ) ≤ ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  have h := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := rpowHom σ) ?_ (y + 1)).2
  · have h' := (hasSum_subtype_iff_indicator (f := fun m => rpowHom σ m)).mp h
    refine le_trans (le_of_eq ?_) (sum_le_hasSum (Nat.smoothNumbersUpTo X (y + 1)) ?_ h')
    · refine Finset.sum_congr rfl fun m hm => ?_
      rw [Set.indicator_of_mem (Nat.mem_smoothNumbersUpTo.mp hm).2]
      rfl
    · intro i _
      apply Set.indicator_nonneg
      intro j _
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · intro p hp
    simp only [rpowHom, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

/-- Rankin's trick: `|Sm X y| ≤ X ^ σ ∏_{p ≤ y} (1 - p ^ (-σ))⁻¹`. -/
lemma rankin_card (σ : ℝ) (hσ : 0 < σ) (y X : ℕ) (hX : 0 < X) :
    ((Sm X y).card : ℝ) ≤ (X : ℝ) ^ σ * ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have h1 : ∀ m ∈ Sm X y, (X : ℝ) ^ (-σ) ≤ (m : ℝ) ^ (-σ) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast pos_of_mem_Sm hm
    rw [Sm, Nat.mem_smoothNumbersUpTo] at hm
    exact Real.rpow_le_rpow_of_nonpos hm0 (by exact_mod_cast hm.1) (by linarith)
  have h2 : ((Sm X y).card : ℝ) * (X : ℝ) ^ (-σ) ≤
      ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
    calc ((Sm X y).card : ℝ) * (X : ℝ) ^ (-σ) = ∑ m ∈ Sm X y, (X : ℝ) ^ (-σ) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ Sm X y, (m : ℝ) ^ (-σ) := sum_le_sum h1
      _ ≤ _ := rankin_sum σ hσ y X
  have h3 : (X : ℝ) ^ σ * (X : ℝ) ^ (-σ) = 1 := by
    rw [← Real.rpow_add hXpos]; simp
  calc ((Sm X y).card : ℝ) = ((Sm X y).card : ℝ) * ((X : ℝ) ^ σ * (X : ℝ) ^ (-σ)) := by
        rw [h3, mul_one]
    _ = (X : ℝ) ^ σ * (((Sm X y).card : ℝ) * (X : ℝ) ^ (-σ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- Each Euler factor with `σ = 1 / log y` is at most `exp (log y / log p)`. -/
lemma factor_le {y p : ℕ} (hy : 2 ≤ y) (hp : 2 ≤ p) :
    (1 - (p : ℝ) ^ (-(1 / log y)))⁻¹ ≤ exp (log y / log p) := by
  have hly : 0 < log (y : ℝ) := log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast (show 1 < p by omega))
  have hpos : (0 : ℝ) < p := by positivity
  have : (p : ℝ) ^ (-(1 / log y)) = exp (-(log p / log y)) := by
    rw [rpow_def_of_pos hpos]; congr 1; ring
  rw [this]
  have := inv_one_sub_exp_neg_le (div_pos hlp hly)
  rwa [one_div_div] at this

/-- Splitting the primes at `√y`. -/
lemma sum_log_div_le (y : ℕ) (hy : 2 ≤ y) :
    ∑ p ∈ (y + 1).primesBelow, log y / log p ≤
      2 * (y + 1).primesBelow.card + Nat.sqrt y * (log y / log 2) := by
  have hly : 0 < log (y : ℝ) := log_pos (by exact_mod_cast (show 1 < y by omega))
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  set P := (y + 1).primesBelow with hP
  rw [← sum_filter_add_sum_filter_not P (fun p => p * p ≤ y)]
  have hsmall : ∑ p ∈ P with p * p ≤ y, log y / log p ≤ Nat.sqrt y * (log y / log 2) := by
    have hcard : (P.filter (fun p => p * p ≤ y)).card ≤ Nat.sqrt y := by
      calc (P.filter (fun p => p * p ≤ y)).card ≤ (Icc 1 (Nat.sqrt y)).card := by
            refine card_le_card fun p hp => ?_
            rw [mem_filter, hP, Nat.mem_primesBelow] at hp
            exact mem_Icc.2 ⟨hp.1.2.one_lt.le, Nat.le_sqrt.2 hp.2⟩
        _ = Nat.sqrt y := by simp
    calc ∑ p ∈ P with p * p ≤ y, log y / log p ≤ ∑ p ∈ P with p * p ≤ y, log y / log 2 := by
          refine sum_le_sum fun p hp => ?_
          rw [mem_filter, hP, Nat.mem_primesBelow] at hp
          exact div_le_div_of_nonneg_left hly.le hl2
            (log_le_log (by norm_num) (by exact_mod_cast hp.1.2.two_le))
      _ = (P.filter (fun p => p * p ≤ y)).card * (log y / log 2) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ Nat.sqrt y * (log y / log 2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have hbig : ∑ p ∈ P with ¬ p * p ≤ y, log y / log p ≤ 2 * P.card := by
    calc ∑ p ∈ P with ¬ p * p ≤ y, log y / log p ≤ ∑ p ∈ P with ¬ p * p ≤ y, (2 : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          rw [mem_filter, hP, Nat.mem_primesBelow] at hp
          have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.1.2.one_lt
          have hlp : 0 < log (p : ℝ) := log_pos hp1
          rw [div_le_iff₀ hlp]
          have hyp : (y : ℝ) ≤ (p : ℝ) * p := by exact_mod_cast (not_le.1 hp.2).le
          have := log_le_log (by positivity) hyp
          rw [log_mul (by positivity) (by positivity)] at this
          linarith
      _ = 2 * (P.filter (fun p => ¬ p * p ≤ y)).card := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ 2 * P.card := by gcongr; exact filter_subset _ _
  linarith

/-- Chebyshev: `π(y) ≤ (2 log 4 + 2) y / log y`. -/
lemma card_primesBelow_le (y : ℕ) (hy : 2 ≤ y) :
    ((y + 1).primesBelow.card : ℝ) ≤ (2 * log 4 + 2) * (y / log y) := by
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hly : 0 < log (y : ℝ) := log_pos hy1
  have h1 : (y + 1).primesBelow.card = Nat.primeCounting y := by
    rw [Nat.primesBelow_card_eq_primeCounting']; rfl
  have h2 := Chebyshev.pi_le_log4_mul_div hy1
  rw [Nat.floor_natCast, log_sqrt (by linarith)] at h2
  rw [h1]
  have h3 := sqrt_le_div_log hy1
  have h4 : log 4 * (y : ℝ) / (log y / 2) = 2 * log 4 * (y / log y) := by
    field_simp
  linarith

/-- The constant in the Rankin bound. -/
noncomputable def C₀ : ℝ := 2 * (2 * log 4 + 2) + 16 / log 2

lemma C₀_pos : 0 < C₀ := by
  have : 0 < log (4 : ℝ) := log_pos (by norm_num)
  have : 0 < log (2 : ℝ) := log_pos (by norm_num)
  unfold C₀; positivity

lemma sum_log_div_le' (y : ℕ) (hy : 2 ≤ y) :
    ∑ p ∈ (y + 1).primesBelow, log y / log p ≤ C₀ * (y / log y) := by
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have h1 := sum_log_div_le y hy
  have h2 := card_primesBelow_le y hy
  have h3 : (Nat.sqrt y : ℝ) * (log y / log 2) ≤ 16 / log 2 * (y / log y) := by
    calc (Nat.sqrt y : ℝ) * (log y / log 2) ≤ √(y : ℝ) * (log y / log 2) :=
          mul_le_mul_of_nonneg_right Real.nat_sqrt_le_real_sqrt
            (div_nonneg (log_nonneg hy1.le) hl2.le)
      _ = (√(y : ℝ) * log y) / log 2 := by ring
      _ ≤ (16 * (y / log y)) / log 2 := div_le_div_of_nonneg_right (sqrt_mul_log_le hy1) hl2.le
      _ = 16 / log 2 * (y / log y) := by ring
  unfold C₀
  nlinarith

/-- `|Sm (y ^ K) y| ≤ exp (K + C₀ y / log y)`. -/
lemma card_Sm_le (y K : ℕ) (hy : 2 ≤ y) :
    ((Sm (y ^ K) y).card : ℝ) ≤ exp (K + C₀ * (y / log y)) := by
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hly : 0 < log (y : ℝ) := log_pos hy1
  set σ := 1 / log (y : ℝ) with hσdef
  have hσ : 0 < σ := by positivity
  have h1 := rankin_card σ hσ y (y ^ K) (pow_pos (by omega) K)
  have h2 : ((y ^ K : ℕ) : ℝ) ^ σ = exp K := by
    rw [Nat.cast_pow, rpow_def_of_pos (by positivity), log_pow, hσdef]
    congr 1
    field_simp
  have h3 : ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ ≤
      exp (∑ p ∈ (y + 1).primesBelow, log y / log p) := by
    rw [exp_sum]
    apply prod_le_prod₀
    · intro p hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.mem_primesBelow.1 hp).2.one_lt
      have := Real.rpow_lt_one_of_one_lt_of_neg hp1 (show -σ < 0 by linarith)
      exact inv_nonneg.2 (by linarith)
    · intro p hp
      exact factor_le hy (Nat.mem_primesBelow.1 hp).2.two_le
  have h4 := sum_log_div_le' y hy
  rw [h2] at h1
  calc ((Sm (y ^ K) y).card : ℝ) ≤ exp K * ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ :=
        h1
    _ ≤ exp K * exp (∑ p ∈ (y + 1).primesBelow, log y / log p) :=
        mul_le_mul_of_nonneg_left h3 (exp_pos _).le
    _ = exp (K + ∑ p ∈ (y + 1).primesBelow, log y / log p) := (exp_add _ _).symm
    _ ≤ exp (K + C₀ * (y / log y)) := exp_le_exp.2 (by linarith)

/-! ### Pigeonhole: a block with many elements having long runs -/

lemma pigeon (f : ℕ → ℝ) (r : ℝ) (h0 : 1 ≤ f 0) (hr : 0 ≤ r) (K : ℕ) (hK : f K < r ^ K) :
    ∃ i < K, f (i + 1) < r * f i := by
  by_contra h
  push Not at h
  have : ∀ i ≤ K, r ^ i ≤ f i := by
    intro i
    induction i with
    | zero => intro _; simpa using h0
    | succ i ih =>
      intro hi
      calc r ^ (i + 1) = r * r ^ i := by ring
        _ ≤ r * f i := mul_le_mul_of_nonneg_left (ih (by omega)) hr
        _ ≤ f (i + 1) := h i (by omega)
  exact absurd (this K le_rfl) (not_le.2 hK)

/-- The block: for every `y ≥ 2` there are `G ⊆ B`, `|G| ≥ δ |B|`, `|B| ≤ exp (C₂ y / log y)`,
such that the first `y` multiples of every `a ∈ G` lie in `B`. -/
lemma block : ∃ δ : ℝ, 0 < δ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ y : ℕ, 2 ≤ y → ∃ B G : Finset ℕ,
    (∀ a ∈ B, 0 < a) ∧ G ⊆ B ∧ (∀ a ∈ G, ∀ j, 1 ≤ j → j ≤ y → j * a ∈ B) ∧ 0 < B.card ∧
      δ * B.card ≤ G.card ∧ (B.card : ℝ) ≤ exp (C₂ * (y / log y)) := by
  have hC₀ := C₀_pos
  refine ⟨exp (-(2 + C₀)), exp_pos _, 2 + C₀, by linarith, fun y hy => ?_⟩
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hly : 0 < log (y : ℝ) := log_pos hy1
  set Q := (y : ℝ) / log y with hQdef
  have hQ1 : 1 < Q := by
    rw [hQdef, one_lt_div hly]
    linarith [log_le_sub_one_of_pos (show (0 : ℝ) < y by linarith)]
  set K := ⌈Q⌉₊ with hKdef
  have hKQ : Q ≤ K := Nat.le_ceil Q
  have hKQ' : (K : ℝ) < Q + 1 := Nat.ceil_lt_add_one (by linarith)
  have hKpos : (0 : ℝ) < K := by linarith
  set f : ℕ → ℝ := fun i => ((Sm (y ^ i) y).card : ℝ) with hf
  have hf0 : 1 ≤ f 0 := by
    simp only [hf, pow_zero, Nat.one_le_cast]
    exact card_pos.2 ⟨1, one_mem_Sm le_rfl⟩
  have hfK : f K ≤ exp ((2 + C₀) * Q) := by
    refine (card_Sm_le y K hy).trans (exp_le_exp.2 ?_)
    nlinarith
  have hfK' : f K < exp (2 + C₀) ^ K := by
    rw [← exp_nat_mul]
    refine (card_Sm_le y K hy).trans_lt (exp_lt_exp.2 ?_)
    nlinarith
  obtain ⟨i, hiK, hi⟩ := pigeon f (exp (2 + C₀)) hf0 (exp_pos _).le K hfK'
  have hmono : ∀ {i j : ℕ}, i ≤ j → Sm (y ^ i) y ⊆ Sm (y ^ j) y :=
    fun hij => Sm_mono (Nat.pow_le_pow_right (by omega) hij)
  refine ⟨Sm (y ^ (i + 1)) y, Sm (y ^ i) y, fun a ha => pos_of_mem_Sm ha,
    hmono (Nat.le_succ i), ?_, card_pos.2 ⟨1, one_mem_Sm (Nat.one_le_pow _ _ (by omega))⟩, ?_, ?_⟩
  · intro a ha j hj1 hjy
    rw [pow_succ]
    exact mul_mem_Sm ha hj1 hjy
  · rw [exp_neg, inv_mul_le_iff₀ (exp_pos _)]
    exact hi.le
  · calc ((Sm (y ^ (i + 1)) y).card : ℝ) ≤ f K := by
          simp only [hf]
          exact_mod_cast card_le_card (hmono (by omega))
      _ ≤ _ := hfK

/-! ### The lower bound -/

theorem lower_bound : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ S : Finset ℕ,
    (∀ a ∈ S, 0 < a) ∧ S.card = n ∧
      c * n * Real.log n * Real.log (Real.log n) ≤ ((∑ a ∈ S, kVal S a : ℕ) : ℝ) := by
  obtain ⟨δ, hδ, C₂, hC₂, hblock⟩ := block
  set ε := 1 / (2 * C₂) with hεdef
  have hε : 0 < ε := by positivity
  refine ⟨ε * δ / 2, by positivity, ?_⟩
  have hev : ∀ᶠ n : ℕ in Filter.atTop, 4 ≤ n ∧ 2 / ε ≤ log (log (n : ℝ)) :=
    (Filter.eventually_ge_atTop 4).and
      ((tendsto_log_atTop.comp
        (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop (2 / ε))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hn4, hLL⟩ := hN n hn
  set L := log (n : ℝ) with hLdef
  set LL := log L with hLLdef
  have hL0 : 0 ≤ L := Real.log_natCast_nonneg n
  have hLLpos : 0 < LL := lt_of_lt_of_le (by positivity) hLL
  have hL1 : 1 < L := (log_pos_iff hL0).1 hLLpos
  have hεLL : 2 ≤ ε * LL := by
    rw [div_le_iff₀ hε] at hLL; linarith
  set y := ⌊ε * L * LL⌋₊ with hydef
  have hyle : (y : ℝ) ≤ ε * L * LL := Nat.floor_le (by positivity)
  have hylt : ε * L * LL < y + 1 := Nat.lt_floor_add_one _
  have hεLLL : 2 * L ≤ ε * L * LL := by nlinarith
  have hLy : L ≤ y := by linarith
  have hy2 : 2 ≤ y := by
    have h1 : (1 : ℝ) < y := by linarith
    have h2 : 1 < y := by exact_mod_cast h1
    omega
  obtain ⟨B, G, hBpos, hGB, hG, hBcard, hGcard, hBle⟩ := hblock y hy2
  have hlogy : LL ≤ log y := log_le_log (by linarith) hLy
  have hQ : (y : ℝ) / log y ≤ ε * L := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ ε * L := by positivity
    nlinarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hexp : exp (L / 2) ≤ n / 2 := by
    set e := exp (L / 2) with he
    have hepos : 0 < e := exp_pos _
    have hee : e * e = n := by rw [he, ← exp_add, add_halves, hLdef, exp_log hn0]
    have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    have he2 : 2 ≤ e := by
      by_contra h
      push Not at h
      nlinarith
    nlinarith
  have hBn : (B.card : ℝ) ≤ n / 2 := by
    calc (B.card : ℝ) ≤ exp (C₂ * (y / log y)) := hBle
      _ ≤ exp (L / 2) := by
          refine exp_le_exp.2 ?_
          calc C₂ * (y / log y) ≤ C₂ * (ε * L) := mul_le_mul_of_nonneg_left hQ hC₂.le
            _ = L / 2 := by rw [hεdef]; field_simp
      _ ≤ n / 2 := hexp
  have hBn' : 2 * B.card ≤ n := by
    have : (2 * B.card : ℝ) ≤ n := by linarith
    exact_mod_cast this
  obtain ⟨S, hSpos, hScard, hSsum⟩ := replicate B G y n hBpos hGB hG
  refine ⟨S, hSpos, hScard, ?_⟩
  have htB : n ≤ 2 * (n / B.card * B.card) := by
    have := Nat.lt_div_mul_add (a := n) hBcard
    generalize n / B.card * B.card = q at *
    omega
  have htB' : (n : ℝ) / 2 ≤ ((n / B.card : ℕ) : ℝ) * B.card := by
    have : (n : ℝ) ≤ 2 * (((n / B.card : ℕ) : ℝ) * B.card) := by exact_mod_cast htB
    linarith
  have hsum : (((n / B.card * G.card * (y + 1) : ℕ)) : ℝ) ≤ ((∑ a ∈ S, kVal S a : ℕ) : ℝ) := by
    exact_mod_cast hSsum
  have ht0 : (0 : ℝ) ≤ ((n / B.card : ℕ) : ℝ) := Nat.cast_nonneg _
  have hLLL : 0 ≤ ε * L * LL := by positivity
  calc ε * δ / 2 * n * L * LL = δ * (n / 2) * (ε * L * LL) := by ring
    _ ≤ δ * (((n / B.card : ℕ) : ℝ) * B.card) * (y + 1) := by
        gcongr
    _ = ((n / B.card : ℕ) : ℝ) * (δ * B.card) * (y + 1) := by ring
    _ ≤ ((n / B.card : ℕ) : ℝ) * G.card * (y + 1) := by
        gcongr
    _ = (((n / B.card * G.card * (y + 1) : ℕ)) : ℝ) := by push_cast; ring
    _ ≤ _ := hsum

end RunsOfMultiples
