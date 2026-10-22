/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ExtendingPollardForTRepresentableSums.InductionHypothesis
import ExtendingPollardForTRepresentableSums.DysonTransform
import ExtendingPollardForTRepresentableSums.IntersectionLowerBound

/-!
# The induction

This file assembles Steps 1 to 4 of the paper into the induction proving the main dichotomy
`sumLowerBound_or_subsetSumsetEq`: for $|A|, |B| \ge t \ge 1$, either
$\sum_{i=1}^t |A +_i B| \ge t|A| + t|B| - 2t^2 + 1$ (or $\ge 2|A| + 2|B| - 4$ when `t = 2`), or
`A +_t B` is the sumset `A' + B'` of large subsets with $A' +_t B' = A' + B'$.

The induction is on $\sum_{i=1}^t |A +_i B|$, then on $|A| + |B|$ in decreasing order, then on
$\min(|A|, |B|)$.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace ExtendingPollard

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {A B : Finset G} {t : ℕ}

/-- **The induction step.** The theorem for all smaller pairs implies the theorem for `A` and
`B`. -/
lemma sumLowerBound_or_subsetSumsetEq_of_inductionHypothesis (ht : 1 ≤ t)
    (hIH : InductionHypothesis t A B) (hA : t ≤ #A) (hB : t ≤ #B) :
    SumLowerBound t A B ∨ SubsetSumsetEq t A B := by
  wlog hBA : #B ≤ #A generalizing A B
  · rw [sumLowerBound_comm, subsetSumsetEq_comm]
    exact this hIH.symm hB hA (by grind)
  by_contra! h
  obtain ⟨hgood, hsse⟩ := h
  rcases hB.eq_or_lt with hBt | hBt
  · refine hgood ?_
    rw [SumLowerBound, sumCardRepresentableSums_eq_card_mul_card hBt.ge, ← hBt]
    grind [sq_le_deficit t, sq t]
  have hCb := fun b (hb : b ∈ B) ↦
    card_filter_addConvolution_le_of_mem_right ht hIH hA hBt hgood hsse hb
  obtain ⟨x, hAB, hlt, hmax⟩ := exists_max_card_inter_vadd (card_pos.1 (by grind) : A.Nonempty)
    (card_pos.1 (by grind) : B.Nonempty) (by grind [card_addStab_le ht hsse hCb])
  rw [← sumLowerBound_vadd_right (x := x)] at hgood
  rw [← subsetSumsetEq_vadd_right (x := x)] at hsse
  have hIH' := hIH.vadd_right x
  rw [← card_vadd_finset x B] at hBA hBt hlt
  have hmax' : ∀ y : G, #(A ∩ (y +ᵥ x +ᵥ B)) < #(x +ᵥ B) →
      #(A ∩ (y +ᵥ x +ᵥ B)) ≤ #(A ∩ (x +ᵥ B)) := by
    intro y hy
    rw [vadd_vadd] at hy ⊢
    rw [card_vadd_finset] at hy
    exact hmax _ hy
  exact false_of_le_card_inter ht hIH' hBA hBt hgood hsse
    (le_card_inter ht hIH' hBA hBt hgood hsse hAB hmax') hlt hmax'

/-- **The main dichotomy.** For $|A|, |B| \ge t \ge 1$, either
$\sum_{i=1}^t |A +_i B| \ge t|A| + t|B| - 2t^2 + 1$ (or $\ge 2|A| + 2|B| - 4$ when `t = 2`), or
there are `A' ⊆ A` and `B' ⊆ B` missing at most `t - 1` elements in total with
$A' +_t B' = A' + B' = A +_t B$. -/
theorem sumLowerBound_or_subsetSumsetEq (ht : 1 ≤ t) (A B : Finset G) (hA : t ≤ #A)
    (hB : t ≤ #B) : SumLowerBound t A B ∨ SubsetSumsetEq t A B :=
  sumLowerBound_or_subsetSumsetEq_of_inductionHypothesis ht
    (fun A₁ B₁ hA₁ hB₁ _ ↦ sumLowerBound_or_subsetSumsetEq ht A₁ B₁ hA₁ hB₁) hA hB
termination_by (sumCardRepresentableSums t A B,
  2 * sumCardRepresentableSums t A B - (#A + #B), min #A #B)
decreasing_by
  rw [Prod.lex_def, Prod.lex_def]
  grind [mul_card_le_sumCardRepresentableSums (A := A₁) hB₁,
    mul_card_le_sumCardRepresentableSums (A := B₁) hA₁, sumCardRepresentableSums_comm t B₁ A₁,
    mul_card_le_sumCardRepresentableSums (A := A) hB,
    mul_card_le_sumCardRepresentableSums (A := B) hA, sumCardRepresentableSums_comm t B A,
    Nat.le_mul_of_pos_left #A₁ ht, Nat.le_mul_of_pos_left #B₁ ht, Nat.le_mul_of_pos_left #A ht,
    Nat.le_mul_of_pos_left #B ht]

end ExtendingPollard
