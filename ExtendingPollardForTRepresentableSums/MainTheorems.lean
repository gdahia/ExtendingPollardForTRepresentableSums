/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ExtendingPollardForTRepresentableSums.SubsetSumset
public import Mathlib.Data.Set.Card
import ExtendingPollardForTRepresentableSums.Induction
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Linarith

/-!
# Theorems 1.1 and 1.2 and Corollary 1.3

This file states the main results of the paper in terms of the stabilizer
`AddAction.stabilizer G (A +_t B)` of Mathlib and the number of holes `numHoles`.

* Theorem 1.1 (`mul_card_add_mul_card_le_or_exists_add_eq_representableSums`): for
  $|A|, |B| \ge t \ge 1$, either $\sum_{i=1}^t |A +_i B| \ge t|A| + t|B| - 2t^2 + 1$, or
  $A +_t B = A' + B'$ for large subsets `A' ⊆ A`, `B' ⊆ B` and a Kneser-type bound holds.
* Theorem 1.2 (`mul_card_add_mul_card_le_or_exists_add_eq_representableSums_two`): the case
  `t = 2`, with the optimal bound $|A + B| + |A +_2 B| \ge 2|A| + 2|B| - 4$.
* The remark ending the introduction of the paper
  (`mul_card_add_mul_card_le_or_exists_add_eq_representableSums_two_mul`,
  `mul_card_add_mul_card_le_or_exists_add_eq_representableSums_three`).
* Corollary 1.3 (`mul_card_add_mul_card_le_or_exists_vadd_subset_representableSums_two`).
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace ExtendingPollard

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The number $|A + H| - |A|$ of `H`-holes of `A`, the elements of $(A + H) \setminus A$. -/
noncomputable def numHoles (H : AddSubgroup G) (A : Finset G) : ℕ :=
  ((A : Set G) + (H : Set G)).ncard - #A

variable {A A' B B' C : Finset G} {t k : ℕ} {H : AddSubgroup G}

/-! ### The stabilizer of Mathlib -/

lemma natCard_stabilizer (hC : C.Nonempty) :
    Nat.card (AddAction.stabilizer G (C : Set G)) = #C.addStab := by
  rw [← SetLike.coe_sort_coe, ← coe_addStab hC, Nat.card_coe_set_eq, Set.ncard_coe_finset]

lemma numHoles_stabilizer (hC : C.Nonempty) (A : Finset G) :
    numHoles (AddAction.stabilizer G (C : Set G)) A = holes C.addStab A := by
  rw [numHoles, ← coe_addStab hC, ← coe_add, Set.ncard_coe_finset, holes]

/-! ### Saturated witnesses -/

/-- If the theorem fails, `A +_t B` has a saturated witness with $|H| - \rho \ge t + 1$. -/
lemma exists_saturatedWitness_of_not_sumLowerBound (ht : 1 ≤ t) (hA : t ≤ #A) (hB : t ≤ #B)
    (h : ¬SumLowerBound t A B) :
    ∃ A' B', SaturatedWitness t A B A' B' ∧ (t + 1 : ℤ) ≤
      #(A' + B').addStab - (holes (A' + B').addStab A' + holes (A' + B').addStab B') := by
  refine ((sumLowerBound_or_subsetSumsetEq ht A B hA hB).resolve_left h).exists_saturatedWitness
    ht hA hB ?_
  unfold SumLowerBound at h
  grind [sq_le_deficit t]

lemma SaturatedWitness.nonempty_add (ht : 1 ≤ t) (hA : t ≤ #A) (hB : t ≤ #B)
    (h : SaturatedWitness t A B A' B') : (A' + B').Nonempty := by
  obtain ⟨hA', hB'⟩ := h.nonempty ht hA hB
  exact hA'.add hB'

/-- The bound (9a) and $\sum_{i=1}^t |A +_i B| + 2t^2 \le t|A| + t|B|$ give
$|H| - \rho \ge 2t$. -/
lemma SaturatedWitness.two_mul_le_card_addStab_sub_holes (ht : 1 ≤ t) (hA : t ≤ #A)
    (hB : t ≤ #B) (h : SaturatedWitness t A B A' B')
    (hS : sumCardRepresentableSums t A B + 2 * t ^ 2 ≤ t * #A + t * #B) :
    (2 * t : ℤ) ≤
      #(A' + B').addStab - (holes (A' + B').addStab A' + holes (A' + B').addStab B') := by
  have h₁ := h.mul_card_add_mul_card_le ht hA hB
  obtain ⟨-, -, hl, -⟩ := h
  have hL : (#(A \ A') + #(B \ B') + 1 : ℤ) ≤ t := by
    exact_mod_cast (by grind : #(A \ A') + #(B \ B') + 1 ≤ t)
  zify at hS
  by_contra! hX
  nlinarith

/-- If $|H| - \rho \ge k \ge t$ for a saturated witness, then
$A' +_k B' = A' + B' = A +_k B = A +_t B$. -/
lemma SaturatedWitness.representableSums_eq (h : SaturatedWitness t A B A' B') (htk : t ≤ k)
    (hk : (k : ℤ) ≤
      #(A' + B').addStab - (holes (A' + B').addStab A' + holes (A' + B').addStab B')) :
    representableSums k A' B' = A' + B' ∧ A' + B' = representableSums k A B ∧
      representableSums k A B = representableSums t A B := by
  obtain ⟨hA', hB', -, -, heq, -⟩ := h
  have hk' : representableSums k A' B' = A' + B' := by
    refine subset_antisymm representableSums_subset_add ?_
    intro x hx
    rw [mem_representableSums]
    exact ⟨hx, by linarith [card_addStab_sub_holes_le_addConvolution hx]⟩
  have h₁ : A' + B' ⊆ representableSums k A B := hk' ▸ representableSums_mono hA' hB'
  have h₂ : representableSums k A B ⊆ A' + B' := heq ▸ representableSums_anti htk
  exact ⟨hk', subset_antisymm h₁ h₂, by rw [← heq, subset_antisymm h₂ h₁]⟩

/-! ### Theorems 1.1 and 1.2 -/

/-- Theorems 1.1 and 1.2 with the bound `SumLowerBound`. -/
lemma sumLowerBound_or_exists_add_eq_representableSums (ht : 1 ≤ t) (A B : Finset G)
    (hA : t ≤ #A) (hB : t ≤ #B)
    (hH : AddAction.stabilizer G (representableSums t A B : Set G) = H) :
    SumLowerBound t A B ∨ ∃ A' ⊆ A, ∃ B' ⊆ B, #(A \ A') + #(B \ B') ≤ t - 1 ∧
      representableSums t A' B' = A' + B' ∧ A' + B' = representableSums t A B ∧ H ≠ ⊥ ∧
      (t * #A + t * #B : ℤ) ≤ sumCardRepresentableSums t A B +
        (t - (#(A \ A') + #(B \ B'))) * (Nat.card H - (numHoles H A' + numHoles H B')) +
        t * (#(A \ A') + #(B \ B')) ∧
      t * #A + t * #B ≤ sumCardRepresentableSums t A B + t * Nat.card H := by
  by_cases h : SumLowerBound t A B
  · exact Or.inl h
  right
  obtain ⟨A', B', hW, hX⟩ := exists_saturatedWitness_of_not_sumLowerBound ht hA hB h
  have h9 := hW.mul_card_add_mul_card_le ht hA hB
  have hne := hW.nonempty_add ht hA hB
  obtain ⟨hA', hB', hl, hrep, heq, -⟩ := hW
  subst hH
  rw [heq] at hne
  refine ⟨A', hA', B', hB', hl, hrep, heq, ?_, ?_, ?_⟩
  · intro hbot
    have := natCard_stabilizer hne
    rw [hbot, AddSubgroup.card_bot, ← heq] at this
    grind
  · rw [natCard_stabilizer hne, numHoles_stabilizer hne, numHoles_stabilizer hne, ← heq]
    linarith
  · rw [natCard_stabilizer hne, ← heq]
    have hL : (#(A \ A') + #(B \ B') : ℤ) ≤ t := by
      exact_mod_cast hl.trans (Nat.sub_le t 1)
    zify
    nlinarith [mul_le_mul_of_nonneg_left (by grind : (#(A' + B').addStab -
        (holes (A' + B').addStab A' + holes (A' + B').addStab B') : ℤ) ≤ #(A' + B').addStab)
        (by linarith : (0 : ℤ) ≤ t - (#(A \ A') + #(B \ B'))),
      mul_le_mul_of_nonneg_left (by linarith : (t : ℤ) ≤ #(A' + B').addStab)
        (by positivity : (0 : ℤ) ≤ #(A \ A') + #(B \ B'))]

/-- **Theorem 1.1.** Let $|A|, |B| \ge t \ge 1$ and let `H` be the stabilizer of `A +_t B`. Either
$\sum_{i=1}^t |A +_i B| \ge t|A| + t|B| - 2t^2 + 1$, or there are `A' ⊆ A` and `B' ⊆ B` with
$l = |A \setminus A'| + |B \setminus B'| \le t - 1$, $A' +_t B' = A' + B' = A +_t B$, `H`
nontrivial, and
$\sum_{i=1}^t |A +_i B| \ge t|A| + t|B| - (t - l)(|H| - \rho) - tl \ge t|A| + t|B| - t|H|$, where
$\rho = |A' + H| - |A'| + |B' + H| - |B'|$. -/
theorem mul_card_add_mul_card_le_or_exists_add_eq_representableSums (ht : 1 ≤ t)
    (A B : Finset G) (hA : t ≤ #A) (hB : t ≤ #B)
    (hH : AddAction.stabilizer G (representableSums t A B : Set G) = H) :
    t * #A + t * #B ≤ sumCardRepresentableSums t A B + (2 * t ^ 2 - 1) ∨
      ∃ A' ⊆ A, ∃ B' ⊆ B, #(A \ A') + #(B \ B') ≤ t - 1 ∧
        representableSums t A' B' = A' + B' ∧ A' + B' = representableSums t A B ∧ H ≠ ⊥ ∧
        (t * #A + t * #B : ℤ) ≤ sumCardRepresentableSums t A B +
          (t - (#(A \ A') + #(B \ B'))) * (Nat.card H - (numHoles H A' + numHoles H B')) +
          t * (#(A \ A') + #(B \ B')) ∧
        t * #A + t * #B ≤ sumCardRepresentableSums t A B + t * Nat.card H := by
  rcases sumLowerBound_or_exists_add_eq_representableSums ht A B hA hB hH with h | h
  · exact Or.inl (h.trans (Nat.add_le_add_left (deficit_le t) _))
  · exact Or.inr h

/-- **Theorem 1.2.** Let $|A|, |B| \ge 2$ and let `H` be the stabilizer of `A +_2 B`. Either
$|A + B| + |A +_2 B| \ge 2|A| + 2|B| - 4$, or there are `A' ⊆ A` and `B' ⊆ B` with
$l = |A \setminus A'| + |B \setminus B'| \le 1$, $A' +_2 B' = A' + B' = A +_2 B$, `H` nontrivial,
and $|A + B| + |A +_2 B| \ge 2|A| + 2|B| - (2 - l)(|H| - \rho) - 2l \ge 2|A| + 2|B| - 2|H|$,
where $\rho = |A' + H| - |A'| + |B' + H| - |B'|$. -/
theorem mul_card_add_mul_card_le_or_exists_add_eq_representableSums_two (A B : Finset G)
    (hA : 2 ≤ #A) (hB : 2 ≤ #B)
    (hH : AddAction.stabilizer G (representableSums 2 A B : Set G) = H) :
    2 * #A + 2 * #B ≤ #(A + B) + #(representableSums 2 A B) + 4 ∨
      ∃ A' ⊆ A, ∃ B' ⊆ B, #(A \ A') + #(B \ B') ≤ 1 ∧
        representableSums 2 A' B' = A' + B' ∧ A' + B' = representableSums 2 A B ∧ H ≠ ⊥ ∧
        (2 * #A + 2 * #B : ℤ) ≤ #(A + B) + #(representableSums 2 A B) +
          (2 - (#(A \ A') + #(B \ B'))) * (Nat.card H - (numHoles H A' + numHoles H B')) +
          2 * (#(A \ A') + #(B \ B')) ∧
        2 * #A + 2 * #B ≤ #(A + B) + #(representableSums 2 A B) + 2 * Nat.card H := by
  have := sumLowerBound_or_exists_add_eq_representableSums (by norm_num) A B hA hB hH
  simpa [SumLowerBound, sumCardRepresentableSums_two, deficit] using this

/-! ### The remark ending the introduction -/

/-- **Remark.** Let $|A|, |B| \ge t \ge 1$ and let `H` be the stabilizer of `A +_t B`. Either
$\sum_{i=1}^t |A +_i B| \ge t|A| + t|B| - 2t^2 + 1$, or there are `A' ⊆ A` and `B' ⊆ B` with
$|A \setminus A'| + |B \setminus B'| \le t - 1$, $A' +_{2t} B' = A' + B' = A +_{2t} B = A +_t B$
and $|H| \ge 2t + \rho$. In particular, every element with at least `t` representations has at
least `2t`. -/
theorem mul_card_add_mul_card_le_or_exists_add_eq_representableSums_two_mul (ht : 1 ≤ t)
    (A B : Finset G) (hA : t ≤ #A) (hB : t ≤ #B)
    (hH : AddAction.stabilizer G (representableSums t A B : Set G) = H) :
    t * #A + t * #B ≤ sumCardRepresentableSums t A B + (2 * t ^ 2 - 1) ∨
      ∃ A' ⊆ A, ∃ B' ⊆ B, #(A \ A') + #(B \ B') ≤ t - 1 ∧
        representableSums (2 * t) A' B' = A' + B' ∧ A' + B' = representableSums (2 * t) A B ∧
        representableSums (2 * t) A B = representableSums t A B ∧
        2 * t + (numHoles H A' + numHoles H B') ≤ Nat.card H := by
  by_cases h : t * #A + t * #B ≤ sumCardRepresentableSums t A B + (2 * t ^ 2 - 1)
  · exact Or.inl h
  right
  obtain ⟨A', B', hW, -⟩ := exists_saturatedWitness_of_not_sumLowerBound ht hA hB
    (fun h' ↦ h (h'.trans (Nat.add_le_add_left (deficit_le t) _)))
  have hne := hW.nonempty_add ht hA hB
  have hX := hW.two_mul_le_card_addStab_sub_holes ht hA hB (by grind [Nat.one_le_pow 2 t ht])
  obtain ⟨hk, heq, heq'⟩ := hW.representableSums_eq (by grind) hX
  obtain ⟨hA', hB', hl, -, heq₀, -⟩ := hW
  subst hH
  rw [heq₀] at hne
  refine ⟨A', hA', B', hB', hl, hk, heq, heq', ?_⟩
  rw [natCard_stabilizer hne, numHoles_stabilizer hne, numHoles_stabilizer hne, ← heq₀]
  zify
  linarith

/-- **Remark for `t = 2`.** Let $|A|, |B| \ge 2$ and let `H` be the stabilizer of `A +_2 B`.
Either $|A + B| + |A +_2 B| \ge 2|A| + 2|B| - 4$, or there are `A' ⊆ A` and `B' ⊆ B` with
$|A \setminus A'| + |B \setminus B'| \le 1$, $A' +_3 B' = A' + B' = A +_3 B = A +_2 B$ and
$|H| \ge 3 + \rho$. -/
theorem mul_card_add_mul_card_le_or_exists_add_eq_representableSums_three (A B : Finset G)
    (hA : 2 ≤ #A) (hB : 2 ≤ #B)
    (hH : AddAction.stabilizer G (representableSums 2 A B : Set G) = H) :
    2 * #A + 2 * #B ≤ #(A + B) + #(representableSums 2 A B) + 4 ∨
      ∃ A' ⊆ A, ∃ B' ⊆ B, #(A \ A') + #(B \ B') ≤ 1 ∧
        representableSums 3 A' B' = A' + B' ∧ A' + B' = representableSums 3 A B ∧
        representableSums 3 A B = representableSums 2 A B ∧
        3 + (numHoles H A' + numHoles H B') ≤ Nat.card H := by
  by_cases h : SumLowerBound 2 A B
  · left
    simpa [SumLowerBound, sumCardRepresentableSums_two, deficit] using h
  right
  obtain ⟨A', B', hW, hX⟩ := exists_saturatedWitness_of_not_sumLowerBound (by norm_num) hA hB h
  have hne := hW.nonempty_add (by norm_num) hA hB
  obtain ⟨hk, heq, heq'⟩ := hW.representableSums_eq (by norm_num) hX
  obtain ⟨hA', hB', hl, -, heq₀, -⟩ := hW
  subst hH
  rw [heq₀] at hne
  refine ⟨A', hA', B', hB', hl, hk, heq, heq', ?_⟩
  rw [natCard_stabilizer hne, numHoles_stabilizer hne, numHoles_stabilizer hne, ← heq₀]
  zify
  push_cast at hX
  linarith

/-! ### Corollary 1.3 -/

/-- **Corollary 1.3.** If $|A|, |B| \ge 2$, then either $|A + B| + |A +_2 B| \ge 2|A| + 2|B| - 4$
or `A +_2 B` contains a coset `x + H` of a subgroup with $|H| \ge 3$. -/
theorem mul_card_add_mul_card_le_or_exists_vadd_subset_representableSums_two (A B : Finset G)
    (hA : 2 ≤ #A) (hB : 2 ≤ #B) :
    2 * #A + 2 * #B ≤ #(A + B) + #(representableSums 2 A B) + 4 ∨
      ∃ x : G, ∃ H : AddSubgroup G, 3 ≤ Nat.card H ∧
        x +ᵥ (H : Set G) ⊆ (representableSums 2 A B : Set G) := by
  rcases mul_card_add_mul_card_le_or_exists_add_eq_representableSums_three A B hA hB rfl with
    h | ⟨A', hA', B', hB', hl, -, heq, heq', hH⟩
  · exact Or.inl h
  right
  obtain ⟨x, hx⟩ : (representableSums 2 A B).Nonempty := by
    rw [← heq', ← heq]
    exact (nonempty_of_card_sdiff_le (t := 2) (by norm_num) hA' (le_self_add.trans hl) hA).add
      (nonempty_of_card_sdiff_le (t := 2) (by norm_num) hB' (le_add_self.trans hl) hB)
  refine ⟨x, AddAction.stabilizer G (representableSums 2 A B : Set G), by grind, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  rw [← AddAction.mem_stabilizer_iff.1 hh]
  simp only [vadd_eq_add]
  rw [add_comm]
  exact Set.vadd_mem_vadd_set hx

end ExtendingPollard
