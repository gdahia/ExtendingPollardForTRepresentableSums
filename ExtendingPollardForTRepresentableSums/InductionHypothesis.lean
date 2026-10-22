/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ExtendingPollardForTRepresentableSums.SubsetSumset
import ExtendingPollardForTRepresentableSums.KneserConsequences
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# The induction hypothesis and Step 2

The main theorem is proved by a triple induction: on $\sum_{i=1}^t |A +_i B|$, then on
`-(|A| + |B|)`, then on `min |A| |B|`. This file defines the induction hypothesis and proves the
reductions available from it:

* Step 2 of the paper (`sumLowerBound_or_subsetSumsetEq_of_erase`): removing an element that
  decreases the sum by at least `t` reduces to a smaller pair. Consequently, when the theorem
  fails for `A` and `B`, each element of `B` has at most `t - 1` sums with at most `t`
  representations, and each element of `A` as well;
* the bound (33) of the paper, `|H(A)| ≤ t - 1`;
* the choice of the Dyson transform: a translate `x + B` maximizing $|A \cap (x + B)|$ among those
  with $|A \cap (x + B)| < |B|$;
* adding an element whose sums are already `t`-representable reduces to a larger pair.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace ExtendingPollard

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {A A' B B' : Finset G} {t : ℕ}
  {a h x y α : G}

/-! ### Translation -/

lemma sumLowerBound_vadd_right : SumLowerBound t A (x +ᵥ B) ↔ SumLowerBound t A B := by
  simp [SumLowerBound, sumCardRepresentableSums_vadd_right]

lemma SubsetSumsetEq.vadd_right (h : SubsetSumsetEq t A B) (x : G) :
    SubsetSumsetEq t A (x +ᵥ B) := by
  obtain ⟨A', hA', B', hB', hl, hrep, heq⟩ := h
  refine ⟨A', hA', x +ᵥ B', vadd_finset_subset_vadd_finset hB', ?_, ?_, ?_⟩
  · rwa [← vadd_finset_sdiff, card_vadd_finset]
  · rw [representableSums_vadd_right, hrep, add_vadd_comm]
  · rw [representableSums_vadd_right, ← heq, add_vadd_comm]

lemma subsetSumsetEq_vadd_right : SubsetSumsetEq t A (x +ᵥ B) ↔ SubsetSumsetEq t A B :=
  ⟨fun h ↦ by simpa using h.vadd_right (-x), fun h ↦ h.vadd_right x⟩

/-! ### The induction hypothesis -/

/-- The theorem holds for all pairs `A₁`, `B₁` with `|A₁|, |B₁| ≥ t` that are smaller than `A`, `B`:
either $\sum_{i=1}^t |A_1 +_i B_1|$ is smaller, or it is equal and $|A_1| + |B_1|$ is larger, or
both are equal and `min |A₁| |B₁|` is smaller. -/
def InductionHypothesis (t : ℕ) (A B : Finset G) : Prop :=
  ∀ A₁ B₁ : Finset G, t ≤ #A₁ → t ≤ #B₁ →
    (sumCardRepresentableSums t A₁ B₁ < sumCardRepresentableSums t A B ∨
      sumCardRepresentableSums t A₁ B₁ = sumCardRepresentableSums t A B ∧ #A + #B < #A₁ + #B₁ ∨
      sumCardRepresentableSums t A₁ B₁ = sumCardRepresentableSums t A B ∧
        #A₁ + #B₁ = #A + #B ∧ min #A₁ #B₁ < min #A #B) →
    SumLowerBound t A₁ B₁ ∨ SubsetSumsetEq t A₁ B₁

lemma InductionHypothesis.symm (h : InductionHypothesis t A B) : InductionHypothesis t B A := by
  intro A₁ B₁ hA₁ hB₁ hlt
  rw [sumCardRepresentableSums_comm t B A, add_comm #B, min_comm #B] at hlt
  exact h A₁ B₁ hA₁ hB₁ hlt

lemma InductionHypothesis.vadd_right (h : InductionHypothesis t A B) (x : G) :
    InductionHypothesis t A (x +ᵥ B) := by
  intro A₁ B₁ hA₁ hB₁ hlt
  rw [sumCardRepresentableSums_vadd_right, card_vadd_finset] at hlt
  exact h A₁ B₁ hA₁ hB₁ hlt

/-! ### Step 2 -/

/-- Removing `y` from `B` loses at most one representation. -/
lemma addConvolution_le_addConvolution_erase_add_one (A B : Finset G) (y x : G) :
    A.addConvolution B x ≤ A.addConvolution (B.erase y) x + 1 := by
  by_cases hy : y ∈ B
  · conv_lhs => rw [← insert_erase hy]
    rw [addConvolution_insert (notMem_erase y B)]
    grind
  · rw [erase_eq_of_notMem hy]
    grind

/-- If `A' + B' = A +_t (B \ {y})` and `y` lies in `B' + H`, where `H` is the stabilizer of
`A' + B'`, then every `a ∈ A'` has `a + y` with at least `t + 1` representations in `A + B`. -/
lemma filter_addConvolution_le_subset_sdiff (ht : 1 ≤ t) (hy : y ∈ B)
    (heq : A' + B' = representableSums t A (B.erase y)) (hyH : y ∈ B' + (A' + B').addStab) :
    {a ∈ A | A.addConvolution B (a + y) ≤ t} ⊆ A \ A' := by
  intro a ha
  rw [mem_filter] at ha
  obtain ⟨haA, hle⟩ := ha
  refine mem_sdiff.2 ⟨haA, ?_⟩
  intro haA'
  have hmem : a + y ∈ representableSums t A (B.erase y) := by
    rw [← heq, ← add_addStab (A' + B'), add_assoc]
    exact add_mem_add haA' hyH
  rw [mem_representableSums_of_one_le ht] at hmem
  have := addConvolution_insert (A := A) (notMem_erase y B) (a + y)
  rw [insert_erase hy] at this
  simp only [add_sub_cancel_right, haA, ↓reduceIte] at this
  grind

/-- If a saturated witness `A', B'` for `A` and `B \ {y}` with `y ∉ B' + H` misses `t` elements
of `A` and `B`, then the bound (9a) for `A` and `B` gives `SumLowerBound t A B`. -/
lemma SaturatedWitness.sumLowerBound_of_erase (ht : 1 ≤ t) (hA : t ≤ #A) (hBe : t ≤ #(B.erase y))
    (hy : y ∈ B) (h : SaturatedWitness t A (B.erase y) A' B')
    (hyH : y ∉ B' + (A' + B').addStab) (hL : t - 1 < #(A \ A') + #(B \ B')) :
    SumLowerBound t A B := by
  obtain ⟨hA'ne, hB'ne⟩ := h.nonempty ht hA hBe
  obtain ⟨hA', hB', hl, hrep, -, hsatA, hsatB, hdef⟩ := h
  have hLt : #(A \ A') + #(B \ B') = t := by
    grind [card_sdiff_add_card_eq_card (hB'.trans (erase_subset y B)),
      card_sdiff_add_card_eq_card hB', card_erase_add_one hy]
  have := mul_card_add_mul_card_add_mul_card_le (D := ∅) ht hA' (hB'.trans (erase_subset y B))
    hA'ne hB'ne hLt.le hrep hdef hsatA (fun b hb hbH ↦ hsatB b (by grind) hbH)
    (fun _ ↦ le_rfl) (empty_subset _) (disjoint_empty_right _)
  rw [(by exact_mod_cast hLt : ((#(A \ A') : ℤ) + #(B \ B')) = t)] at this
  unfold SumLowerBound
  zify
  nlinarith [(by exact_mod_cast sq_le_deficit t : (t : ℤ) ^ 2 ≤ deficit t)]

/-- **Step 2.** If removing `y ∈ B` decreases $\sum_{i=1}^t |A +_i B|$ by at least `t`, then the
theorem for `A` and `B \ {y}` implies the theorem for `A` and `B`. -/
lemma sumLowerBound_or_subsetSumsetEq_of_erase (ht : 1 ≤ t) (hIH : InductionHypothesis t A B)
    (hA : t ≤ #A) (hB : t + 1 ≤ #B) (hy : y ∈ B)
    (hS : sumCardRepresentableSums t A (B.erase y) + t ≤ sumCardRepresentableSums t A B) :
    SumLowerBound t A B ∨ SubsetSumsetEq t A B := by
  have hBe : t ≤ #(B.erase y) := by grind [card_erase_add_one hy]
  rcases hIH A (B.erase y) hA hBe (Or.inl (by grind)) with hgood | hsse
  · left
    unfold SumLowerBound at *
    rw [← card_erase_add_one hy, mul_add_one]
    grind
  by_cases hS' : sumCardRepresentableSums t A (B.erase y) + t ^ 2 < t * #A + t * #(B.erase y)
  swap
  · left
    unfold SumLowerBound
    rw [← card_erase_add_one hy, mul_add_one]
    grind [sq_le_deficit t]
  obtain ⟨A', B', hW, -⟩ := hsse.exists_saturatedWitness ht hA hBe hS'
  by_cases hyH : y ∈ B' + (A' + B').addStab
  · obtain ⟨hA', -, hl, -, heq, -⟩ := hW
    grind [card_le_card (filter_addConvolution_le_subset_sdiff ht hy heq hyH),
      sumCardRepresentableSums_erase (t := t) (A := A) hy]
  by_cases hL : #(A \ A') + #(B \ B') ≤ t - 1
  · obtain ⟨hA', hB', -, hrep, -⟩ := hW
    exact Or.inr (subsetSumsetEq_of_subset ht hA' (hB'.trans (erase_subset y B)) hL hrep)
  · exact Or.inl (hW.sumLowerBound_of_erase ht hA hBe hy hyH (not_le.1 hL))

/-- If the theorem fails for `A` and `B`, every `y ∈ B` has at most `t - 1` sums `a + y` with at
most `t` representations. -/
lemma card_filter_addConvolution_le_of_mem_right (ht : 1 ≤ t) (hIH : InductionHypothesis t A B)
    (hA : t ≤ #A) (hB : t + 1 ≤ #B) (hgood : ¬SumLowerBound t A B)
    (hsse : ¬SubsetSumsetEq t A B) (hy : y ∈ B) :
    #{a ∈ A | A.addConvolution B (a + y) ≤ t} ≤ t - 1 := by
  by_contra! h
  have := sumCardRepresentableSums_erase (t := t) (A := A) hy
  rcases sumLowerBound_or_subsetSumsetEq_of_erase ht hIH hA hB hy (by grind) with h | h <;>
    contradiction

/-- If the theorem fails for `A` and `B`, every `y ∈ A` has at most `t - 1` sums `y + b` with at
most `t` representations. -/
lemma card_filter_addConvolution_le_of_mem_left (ht : 1 ≤ t) (hIH : InductionHypothesis t A B)
    (hA : t + 1 ≤ #A) (hB : t ≤ #B) (hgood : ¬SumLowerBound t A B)
    (hsse : ¬SubsetSumsetEq t A B) (hy : y ∈ A) :
    #{b ∈ B | A.addConvolution B (y + b) ≤ t} ≤ t - 1 := by
  rw [sumLowerBound_comm] at hgood
  rw [subsetSumsetEq_comm] at hsse
  simpa [addConvolution_comm B A, add_comm] using
    card_filter_addConvolution_le_of_mem_right ht hIH.symm hB hA hgood hsse hy

/-! ### The bound (33) -/

/-- The number of representations is invariant under the stabilizer of `A`. -/
lemma addConvolution_add_of_mem_addStab (hh : h ∈ A.addStab) (B : Finset G) (x : G) :
    A.addConvolution B (x + h) = A.addConvolution B x := by
  have hA : A.Nonempty := Nonempty.of_addStab ⟨h, hh⟩
  have := vadd_addConvolution_eq_addConvolution_neg_add A B h (x + h)
  rw [(mem_addStab hA).1 hh] at this
  rw [this]
  congr 1
  abel

/-- **The bound (33).** If every `y ∈ B` has at most `t - 1` sums `a + y` with at most `t`
representations and `A +_t B ≠ A + B`, then $|H(A)| \le t - 1$. -/
lemma card_addStab_le (ht : 1 ≤ t) (hsse : ¬SubsetSumsetEq t A B)
    (hC : ∀ y ∈ B, #{a ∈ A | A.addConvolution B (a + y) ≤ t} ≤ t - 1) : #A.addStab ≤ t - 1 := by
  by_cases hall : ∀ a ∈ A, ∀ b ∈ B, t + 1 ≤ A.addConvolution B (a + b)
  · refine absurd (subsetSumsetEq_of_representableSums_eq ?_) hsse
    refine subset_antisymm representableSums_subset_add ?_
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hx
    rw [mem_representableSums_of_one_le ht]
    grind
  push Not at hall
  obtain ⟨a, ha, b, hb, hab⟩ := hall
  refine le_trans ?_ (hC b hb)
  rw [← card_image_of_injective _ (add_right_injective a)]
  apply card_le_card
  intro x hx
  obtain ⟨h, hh, rfl⟩ := mem_image.1 hx
  refine mem_filter.2 ⟨add_mem_of_mem_addStab ha hh, ?_⟩
  rw [add_right_comm, addConvolution_add_of_mem_addStab hh]
  grind

/-! ### The choice of the Dyson transform -/

/-- If $|H(A)| < |B|$, some translate `x + B` meets `A`, is not contained in `A`, and maximizes
$|A \cap (x + B)|$ among the translates not contained in `A`. -/
lemma exists_max_card_inter_vadd (hA : A.Nonempty) (hB : B.Nonempty) (hstab : #A.addStab < #B) :
    ∃ x : G, (A ∩ (x +ᵥ B)).Nonempty ∧ #(A ∩ (x +ᵥ B)) < #B ∧
      ∀ y : G, #(A ∩ (y +ᵥ B)) < #B → #(A ∩ (y +ᵥ B)) ≤ #(A ∩ (x +ᵥ B)) := by
  have hmem : ∀ y : G, (A ∩ (y +ᵥ B)).Nonempty → y ∈ A - B := by
    rintro y ⟨c, hc⟩
    obtain ⟨hcA, hcB⟩ := mem_inter.1 hc
    obtain ⟨b, hb, rfl⟩ := mem_vadd_finset.1 hcB
    exact mem_sub.2 ⟨y + b, hcA, b, hb, by simp⟩
  have hU : ({y ∈ A - B | #(A ∩ (y +ᵥ B)) < #B}).Nonempty := by
    by_contra! hU
    obtain ⟨b₀, hb₀⟩ := hB
    refine hstab.not_ge ?_
    rw [← card_image_of_injective _ (sub_left_injective : Function.Injective fun b : G ↦ b - b₀)]
    apply card_le_card
    intro z hz
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hz
    rw [mem_addStab_iff_vadd_finset_subset hA]
    intro c hc
    obtain ⟨a, ha, rfl⟩ := mem_vadd_finset.1 hc
    have hcard : #((a - b₀) +ᵥ B) ≤ #(A ∩ ((a - b₀) +ᵥ B)) := by
      rw [card_vadd_finset]
      simpa using filter_eq_empty_iff.1 hU (sub_mem_sub ha hb₀)
    have hsub := inter_eq_right.1 (eq_of_subset_of_card_le inter_subset_right hcard)
    convert hsub (vadd_mem_vadd_finset hb (a := a - b₀)) using 1
    rw [vadd_eq_add, vadd_eq_add]
    abel
  obtain ⟨x, hx, hmax⟩ := exists_max_image _ (fun y ↦ #(A ∩ (y +ᵥ B))) hU
  obtain ⟨hxAB, hxB⟩ := mem_filter.1 hx
  refine ⟨x, ?_, hxB, ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_sub.1 hxAB
    exact ⟨a, mem_inter.2 ⟨ha, mem_vadd_finset.2 ⟨b, hb, by simp⟩⟩⟩
  · intro y hy
    by_cases hne : (A ∩ (y +ᵥ B)).Nonempty
    · exact hmax y (mem_filter.2 ⟨hmem y hne, hy⟩)
    · simp [not_nonempty_iff_eq_empty.1 hne]

/-! ### The Dyson transform -/

/-- The Dyson transform `(A ∪ B, A ∩ B)` has pointwise fewer representations. -/
lemma addConvolution_union_inter_le (A B : Finset G) (x : G) :
    (A ∪ B).addConvolution (A ∩ B) x ≤ A.addConvolution B x := by
  refine card_le_card_of_injOn (fun (a, b) ↦ if a ∈ A then (a, b) else (b, a)) ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [coe_filter, mem_product, mem_union, mem_inter, Set.mem_ofPred_eq] at hp ⊢
    grind
  · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hq hpq
    simp only [coe_filter, mem_product, mem_union, mem_inter, Set.mem_ofPred_eq] at hp hq hpq
    grind

/-! ### Adding an element -/

/-- **Adding an element.** If the theorem fails for `A` and `B` and `α ∉ B` has all its sums
`a + α`, `a ∈ A`, in `A +_t B`, then the theorem for `A` and `B ∪ {α}` gives a contradiction. -/
lemma false_of_insert_right (ht : 1 ≤ t) (hIH : InductionHypothesis t A B) (hA : t ≤ #A)
    (hB : t ≤ #B) (hgood : ¬SumLowerBound t A B) (hsse : ¬SubsetSumsetEq t A B) (hα : α ∉ B)
    (hrep : ∀ a ∈ A, a + α ∈ representableSums t A B) : False := by
  have hS : sumCardRepresentableSums t A (insert α B) = sumCardRepresentableSums t A B := by
    rw [sumCardRepresentableSums_insert hα, filter_false_of_mem, card_empty, add_zero]
    intro a ha
    rw [addConvolution_insert hα]
    simp only [add_sub_cancel_right, ha, ↓reduceIte]
    grind [(mem_representableSums_of_one_le ht).1 (hrep a ha)]
  have hcard := card_insert_of_notMem hα
  unfold SumLowerBound at hgood
  rcases hIH A (insert α B) hA (by grind) (Or.inr (Or.inl ⟨hS, by grind⟩)) with hgood' | hsse'
  · unfold SumLowerBound at hgood'
    rw [hS, hcard] at hgood'
    grind
  obtain ⟨A', Y, hW, hX⟩ := hsse'.exists_saturatedWitness ht hA (by grind) (by
    rw [hS, hcard]
    grind [sq_le_deficit t])
  obtain ⟨hA', hY, hl, -⟩ := hW
  refine hsse (subsetSumsetEq_of_subset ht hA' (B' := Y.erase α) ?_ ?_ ?_)
  · intro b hb
    obtain ⟨hbα, hbY⟩ := mem_erase.1 hb
    exact (mem_insert.1 (hY hbY)).resolve_left hbα
  · refine le_trans (Nat.add_le_add_left (card_le_card ?_) _) hl
    intro b hb
    simp only [mem_sdiff, mem_insert, mem_erase] at hb ⊢
    grind
  · refine subset_antisymm representableSums_subset_add ?_
    intro x hx
    have hxY : x ∈ A' + Y := add_subset_add_left (erase_subset α Y) hx
    rw [mem_representableSums_of_one_le ht]
    grind [hX.trans (card_addStab_sub_holes_le_addConvolution hxY),
      addConvolution_le_addConvolution_erase_add_one A' Y α x]

/-- **Adding an element**, to `A`. -/
lemma false_of_insert_left (ht : 1 ≤ t) (hIH : InductionHypothesis t A B) (hA : t ≤ #A)
    (hB : t ≤ #B) (hgood : ¬SumLowerBound t A B) (hsse : ¬SubsetSumsetEq t A B) (hα : α ∉ A)
    (hrep : ∀ b ∈ B, α + b ∈ representableSums t A B) : False := by
  rw [sumLowerBound_comm] at hgood
  rw [subsetSumsetEq_comm] at hsse
  refine false_of_insert_right ht hIH.symm hB hA hgood hsse hα ?_
  intro b hb
  rw [representableSums_comm, add_comm]
  exact hrep b hb

end ExtendingPollard
