/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ExtendingPollardForTRepresentableSums.RepresentableSums
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity.Finset

/-!
# A lower bound from the additive energy

This file proves Lemma 2.1 of the paper: if most elements of `A - B` have few representations,
then $\sum_{i=1}^t |A +_i B|$ is large.

The additive energy $E(A, B) = \sum_x r_{A,B}(x)^2$ equals $E(A, -B)$, and the hypothesis bounds
$E(A, -B)$. For $0 \le \lambda \le 2(t - \sqrt{t(t-1)})$ and every natural number `r`,
$\lambda r - \lambda^2 r^2 / (4t) \le \min(r, t)$. Summing over `x` with $r = r_{A,B}(x)$ gives
$\sum_{i=1}^t |A +_i B| \ge \lambda |A| |B| - \lambda^2 E(A, B) / (4t)$, and the best choice of
$\lambda$ gives the lemma. The paper bounds the same minimum by relaxing the sizes of the cliques of
the graph of equal sums to real numbers.
-/

@[expose] public section

open Finset Real
open scoped Combinatorics.Additive Pointwise

namespace ExtendingPollard

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {A B T : Finset G} {k t : ℕ}

/-! ### The additive energy -/

lemma addEnergy_neg_right (A B : Finset G) : E[A, -B] = E[A, B] := by
  refine card_nbij' (fun ((a₁, a₂), b₁, b₂) ↦ ((a₁, a₂), -b₂, -b₁))
    (fun ((a₁, a₂), b₁, b₂) ↦ ((a₁, a₂), -b₂, -b₁)) ?_ ?_ ?_ ?_
  · rintro ⟨⟨a₁, a₂⟩, b₁, b₂⟩ hx
    simp only [coe_filter, mem_product, mem_neg, Set.mem_ofPred_eq] at hx ⊢
    obtain ⟨⟨⟨ha₁, ha₂⟩, ⟨c₁, hc₁, rfl⟩, ⟨c₂, hc₂, rfl⟩⟩, h⟩ := hx
    refine ⟨⟨⟨ha₁, ha₂⟩, by simpa, by simpa⟩, ?_⟩
    simp only [neg_neg]
    linear_combination (norm := abel_nf) h
  · rintro ⟨⟨a₁, a₂⟩, b₁, b₂⟩ hx
    simp only [coe_filter, mem_product, mem_neg, Set.mem_ofPred_eq] at hx ⊢
    obtain ⟨⟨⟨ha₁, ha₂⟩, hb₁, hb₂⟩, h⟩ := hx
    refine ⟨⟨⟨ha₁, ha₂⟩, ⟨b₂, hb₂, rfl⟩, ⟨b₁, hb₁, rfl⟩⟩, ?_⟩
    linear_combination (norm := abel_nf) h
  · simp [Set.LeftInvOn]
  · simp [Set.LeftInvOn]

lemma addEnergy_eq_sum_sq_addConvolution (A B : Finset G) :
    E[A, B] = ∑ x ∈ A + B, A.addConvolution B x ^ 2 := by
  rw [addEnergy_eq_sum_sq']
  rfl

/-- If every element outside `T` has at most `k ≤ |B|` representations as `a - b`, then
$E(A, B) \le |B| (|T| (|B| - k) + k |A|)$. -/
lemma addEnergy_le_of_addConvolution_neg_le (hkB : k ≤ #B)
    (hr : ∀ x ∉ T, A.addConvolution (-B) x ≤ k) :
    E[A, B] ≤ #B * (#T * (#B - k) + k * #A) := by
  rw [← addEnergy_neg_right, addEnergy_eq_sum_sq_addConvolution]
  have hrB (x : G) : A.addConvolution (-B) x ≤ #B := card_neg B ▸ addConvolution_le_card_right
  have hT : ∑ x ∈ A + -B with x ∈ T, A.addConvolution (-B) x ≤ #T * #B := by
    refine (sum_le_card_nsmul _ _ #B (by grind)).trans ?_
    rw [smul_eq_mul, filter_mem_eq_inter]
    gcongr
    exact inter_subset_right
  refine (sum_le_sum (g := fun x ↦ k * A.addConvolution (-B) x +
    (#B - k) * if x ∈ T then A.addConvolution (-B) x else 0) ?_).trans ?_
  · intro x _
    by_cases hx : x ∈ T
    · simp only [hx, ↓reduceIte]
      rw [sq, ← add_mul, Nat.add_sub_cancel' hkB]
      exact Nat.mul_le_mul_right _ (hrB x)
    · grind [Nat.mul_le_mul_right (A.addConvolution (-B) x) (hr x hx)]
  · rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← sum_filter, sum_addConvolution, card_neg]
    grind [Nat.mul_le_mul_left (#B - k) hT]

/-! ### The pointwise inequality -/

/-- For $0 \le \lambda \le 2(t - \sqrt{t(t-1)})$ and a natural number `r`,
$\lambda r - \lambda^2 r^2 / (4t) \le \min(r, t)$. -/
lemma mul_sub_sq_div_le_min {t lam : ℝ} (ht : 1 ≤ t) (hlam : 0 ≤ lam)
    (hlam' : lam ≤ 2 * (t - √(t * (t - 1)))) (r : ℕ) :
    lam * r - lam ^ 2 * r ^ 2 / (4 * t) ≤ min (r : ℝ) t := by
  have hs := Real.sq_sqrt (by nlinarith : 0 ≤ t * (t - 1))
  have hs₀ := Real.sqrt_nonneg (t * (t - 1))
  rw [sub_div' (by positivity), le_min_iff, div_le_iff₀ (by positivity),
    div_le_iff₀ (by positivity)]
  constructor
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith [mul_nonneg (mul_nonneg hlam hlam) (by nlinarith : (0 : ℝ) ≤ r ^ 2 - r),
      mul_nonneg (by linarith : (0 : ℝ) ≤ r)
        (mul_nonneg (by linarith : 0 ≤ 2 * (t - √(t * (t - 1))) - lam)
          (by nlinarith : 0 ≤ 2 * (t + √(t * (t - 1))) - lam))]
  · nlinarith [sq_nonneg (2 * t - lam * r)]

/-- For $0 \le \lambda \le 2(t - \sqrt{t(t-1)})$,
$\sum_{i=1}^t |A +_i B| \ge \lambda |A| |B| - \lambda^2 E(A, B) / (4t)$. -/
lemma mul_sub_sq_mul_addEnergy_div_le {lam : ℝ} (ht : 1 ≤ t) (hlam : 0 ≤ lam)
    (hlam' : lam ≤ 2 * (t - √(t * (t - 1)))) :
    lam * (#A * #B) - lam ^ 2 * E[A, B] / (4 * t) ≤ (sumCardRepresentableSums t A B : ℝ) := by
  rw [sumCardRepresentableSums_eq_sum_min, addEnergy_eq_sum_sq_addConvolution, ← Nat.cast_mul,
    ← sum_addConvolution]
  push_cast
  rw [mul_sum, mul_sum, sum_div, ← sum_sub_distrib]
  gcongr with x
  exact mul_sub_sq_div_le_min (by exact_mod_cast ht) hlam hlam' _

/-! ### Lemma 2.1 -/

/-- The core of Lemma 2.1:
$\sum_{i=1}^t |A +_i B| \ge t \min(|A| |B| / (t + \sqrt{t(t-1)}), |A|^2 |B|^2 / E(A, B))$. -/
lemma mul_min_div_addEnergy_le (ht : 1 ≤ t) (hE : 0 < E[A, B]) :
    t * min ((#A * #B : ℝ) / (t + √(t * (t - 1)))) ((#A * #B : ℝ) ^ 2 / E[A, B]) ≤
      (sumCardRepresentableSums t A B : ℝ) := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hs := Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ t * (t - 1))
  rw [mul_min_of_nonneg _ _ (by positivity)]
  by_cases hcase : 2 * t * (#A * #B) / E[A, B] ≤ 2 * (t - √(t * (t - 1)))
  · refine (min_le_right _ _).trans (le_of_eq_of_le ?_
      (mul_sub_sq_mul_addEnergy_div_le ht (by positivity) hcase))
    field_simp
    ring
  · rw [not_le, lt_div_iff₀ (by exact_mod_cast hE)] at hcase
    have hst : √((t : ℝ) * (t - 1)) < t := by nlinarith [Real.sqrt_nonneg ((t : ℝ) * (t - 1))]
    refine (min_le_left _ _).trans ?_
    calc (t : ℝ) * (#A * #B / (t + √(t * (t - 1))))
        = (t - √(t * (t - 1))) * (#A * #B) := by
          rw [mul_div_assoc', div_eq_iff (by positivity)]
          linear_combination (#A * #B : ℝ) * hs
      _ ≤ 2 * (t - √(t * (t - 1))) * (#A * #B) -
          (2 * (t - √(t * (t - 1)))) ^ 2 * E[A, B] / (4 * t) := by
          rw [le_sub_iff_add_le', ← le_sub_iff_add_le, div_le_iff₀ (by positivity)]
          nlinarith [mul_lt_mul_of_pos_left hcase (sub_pos.2 hst)]
      _ ≤ sumCardRepresentableSums t A B := mul_sub_sq_mul_addEnergy_div_le ht (by linarith) le_rfl

/-- The first inequality of Lemma 2.1:
$\sum_{i=1}^t |A +_i B| \ge t \min\left(\frac{|A||B|}{t + \sqrt{t(t-1)}},
\frac{|A|^2|B|}{|T|(|B|-k) + k|A|}\right)$. -/
lemma mul_min_div_le_sumCardRepresentableSums (hkB : k ≤ #B) (ht : 1 ≤ t)
    (hr : ∀ x ∉ T, A.addConvolution (-B) x ≤ k) :
    t * min ((#A * #B : ℝ) / (t + √(t * (t - 1))))
        ((#A ^ 2 * #B : ℝ) / (#T * (#B - k : ℝ) + k * #A)) ≤
      (sumCardRepresentableSums t A B : ℝ) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp
  have hE := addEnergy_pos hA hB
  refine le_trans ?_ (mul_min_div_addEnergy_le ht hE)
  gcongr _ * min _ ?_
  rw [← mul_div_mul_left _ _ (by positivity : (#B : ℝ) ≠ 0),
    (by ring : (#B : ℝ) * (#A ^ 2 * #B) = (#A * #B) ^ 2)]
  gcongr
  exact_mod_cast addEnergy_le_of_addConvolution_neg_le hkB hr

/-- The second inequality of Lemma 2.1: since $\sqrt{t(t-1)} \le t$,
$\min(N/2, t y) \le t \min(N / (t + \sqrt{t(t-1)}), y)$. -/
lemma min_div_two_mul_le_mul_min {N y : ℝ} (ht : 1 ≤ t) (hN : 0 ≤ N) :
    min (N / 2) (t * y) ≤ t * min (N / (t + √(t * (t - 1)))) y := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  rw [mul_min_of_nonneg _ _ (by positivity)]
  gcongr
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  nlinarith [Real.sqrt_le_sqrt (by nlinarith : (t : ℝ) * (t - 1) ≤ t ^ 2),
    Real.sqrt_sq (by positivity : (0 : ℝ) ≤ t)]

/-- **Lemma 2.1.** If every element of `G` outside `T` has at most `k ≤ |B|` representations as
`a - b` with `a ∈ A` and `b ∈ B`, then
$\sum_{i=1}^t |A +_i B| \ge t \min\left(\frac{|A||B|}{t + \sqrt{t(t-1)}},
\frac{|A|^2|B|}{|T|(|B|-k) + k|A|}\right) \ge \min\left(\frac{|A||B|}{2},
t \frac{|A|^2|B|}{|T|(|B|-k) + k|A|}\right)$. -/
theorem mul_min_le_sumCardRepresentableSums (hkB : k ≤ #B) (ht : 1 ≤ t)
    (hr : ∀ x ∉ T, A.addConvolution (-B) x ≤ k) :
    t * min ((#A * #B : ℝ) / (t + √(t * (t - 1))))
        ((#A ^ 2 * #B : ℝ) / (#T * (#B - k : ℝ) + k * #A)) ≤
      (sumCardRepresentableSums t A B : ℝ) ∧
    min ((#A * #B : ℝ) / 2) (t * ((#A ^ 2 * #B : ℝ) / (#T * (#B - k : ℝ) + k * #A))) ≤
      t * min ((#A * #B : ℝ) / (t + √(t * (t - 1))))
        ((#A ^ 2 * #B : ℝ) / (#T * (#B - k : ℝ) + k * #A)) :=
  ⟨mul_min_div_le_sumCardRepresentableSums hkB ht hr,
    min_div_two_mul_le_mul_min ht (by positivity)⟩

end ExtendingPollard
