/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ExtendingPollardForTRepresentableSums.InductionHypothesis
import ExtendingPollardForTRepresentableSums.IntersectionLowerBound
import ExtendingPollardForTRepresentableSums.KneserConsequences
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Finset

/-!
# Step 4: the theorem for the Dyson transform

After translating `B`, the Dyson transform of the paper is `(A ∪ B, A ∩ B)`. It has pointwise fewer
representations than `A + B` and the same total size, so the induction hypothesis applies to it
once $t \le |A \cap B| < |B|$. This file proves Step 4 of the paper: the structure given by the
theorem for `(A ∪ B, A ∩ B)` contradicts the failure of the theorem for `A` and `B`.

* Case 4.1, `l ≥ 1`: an element of `A ∪ B` or `A ∩ B` outside the witnesses gives many sums
  outside `A' + B'` with at least `t + 1` representations in `A + B`
  (`mul_card_add_mul_card_le_of_mem_union_sdiff`, `mul_card_add_mul_card_le_of_mem_inter_sdiff`).
* Case 4.2, `l = 0`: then `A ∩ B` is periodic with respect to the stabilizer `H` of
  $C = (A \cup B) + (A \cap B)$, and every sum `a + b` outside `C` lies in a coset sum of two
  `H`-cosets meeting both `A \ B` and `B \ A`. Counting the sums outside `C` shows that all the
  sums of `A + B` are `t`-representable (`false_of_representableSums_union_inter_eq`). This
  replaces the three subcases of the paper.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace ExtendingPollard

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {A A' B B' C D X' : Finset G} {t k : ℕ}
  {a a' b d e g x : G}

lemma mem_vadd_finset_iff_sub_mem {s : Finset G} : x ∈ g +ᵥ s ↔ x - g ∈ s := by
  rw [← neg_vadd_mem_iff, vadd_eq_add, neg_add_eq_sub]

lemma sub_mem_addStab_comm (hC : C.Nonempty) : a - b ∈ C.addStab ↔ b - a ∈ C.addStab := by
  constructor <;> intro h <;> simpa using neg_mem_addStab hC h

/-! ### Sums outside a set of popular sums -/

/-- If `C ⊆ A +_t B` and `Z ⊆ A + B` are disjoint, then
$\sum_{i=1}^t |A +_i B| \ge t|C| + \sum_{z \in Z} \min(r_{A,B}(z), t)$. -/
lemma mul_card_add_sum_min_le {Z : Finset G} (hC : C ⊆ representableSums t A B)
    (hZ : Z ⊆ A + B) (hCZ : Disjoint C Z) :
    t * #C + ∑ z ∈ Z, min (A.addConvolution B z) t ≤ sumCardRepresentableSums t A B := by
  rw [sumCardRepresentableSums_eq_sum_min]
  refine le_trans ?_
    (sum_le_sum_of_subset (union_subset (hC.trans representableSums_subset_add) hZ))
  rw [sum_union hCZ, sum_const_nat fun x hx ↦ min_eq_right (mem_representableSums.1 (hC hx)).2,
    mul_comm]

/-- **Sums with one element of `B` outside a set of popular sums.** Let `X' ⊆ A` have all its sums
`a + b` outside `C ⊆ A +_t B`, each with at least `k ≤ t` representations. If at most `t - 1`
elements `a ∈ A` have `a + b` with at most `t` representations, then
$t|C| + t|X'| \le \sum_{i=1}^t |A +_i B| + (t - k)(t - 1)$. -/
lemma mul_card_add_mul_card_le_of_forall_add_notMem (hC : C ⊆ representableSums t A B)
    (hb : b ∈ B) (hX' : X' ⊆ A) (hdisj : ∀ a ∈ X', a + b ∉ C)
    (hlow : ∀ a ∈ X', k ≤ A.addConvolution B (a + b)) (hkt : k ≤ t)
    (hCb : #{a ∈ A | A.addConvolution B (a + b) ≤ t} ≤ t - 1) :
    t * #C + t * #X' ≤ sumCardRepresentableSums t A B + (t - k) * (t - 1) := by
  have h₁ := mul_card_add_sum_min_le (Z := X'.image (· + b)) hC
    (image_subset_iff.2 fun a ha ↦ add_mem_add (hX' ha) hb)
    (disjoint_right.2 ((forall_mem_image (p := (· ∉ C))).2 hdisj))
  rw [sum_image fun x _ y _ h ↦ add_right_cancel h] at h₁
  have h₂ : t * #X' ≤ ∑ a ∈ X', min (A.addConvolution B (a + b)) t +
      (t - k) * #{a ∈ X' | A.addConvolution B (a + b) ≤ t} := by
    rw [card_filter, mul_sum, ← sum_add_distrib, mul_comm, ← smul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro a ha
    grind [hlow a ha]
  linarith [Nat.mul_le_mul_left (t - k) ((card_le_card (filter_subset_filter _ hX')).trans hCb)]

/-! ### Case 4.1 -/

/-- The bound of Case 4.1 from a set `D ⊆ A +_t B` of sums outside `A' + B'` with
$|H| - \rho \le |D| + c$. -/
lemma mul_card_add_mul_card_le_of_card_addStab_sub_holes_le (ht : 1 ≤ t) (hA' : A' ⊆ A ∪ B)
    (hB' : B' ⊆ A ∩ B) (hA'ne : A'.Nonempty) (hB'ne : B'.Nonempty)
    (hL : #((A ∪ B) \ A') + #((A ∩ B) \ B') ≤ t)
    (hrep : representableSums t A' B' = A' + B') (hdef : #(A' + B') < #A' + #B')
    (hsatA : ∀ a ∈ A ∪ B, a ∈ A' + (A' + B').addStab → a ∈ A')
    (hsatB : ∀ b ∈ A ∩ B, b ∈ B' + (A' + B').addStab → b ∈ B')
    (hD : D ⊆ representableSums t A B) (hD' : Disjoint (A' + B') D) {c : ℤ}
    (hX : (#(A' + B').addStab - (holes (A' + B').addStab A' + holes (A' + B').addStab B') : ℤ) ≤
      #D + c) :
    (t * #A + t * #B : ℤ) ≤ sumCardRepresentableSums t A B +
      t * (#((A ∪ B) \ A') + #((A ∩ B) \ B')) +
        (t - (#((A ∪ B) \ A') + #((A ∩ B) \ B'))) * c := by
  have hcore := mul_card_add_mul_card_add_mul_card_le ht hA' hB' hA'ne hB'ne hL hrep hdef hsatA
    hsatB (addConvolution_union_inter_le A B) hD hD'
  have hU := card_union_add_card_inter A B
  zify at hU hL
  nlinarith [mul_le_mul_of_nonneg_left hX
    (by linarith : (0 : ℤ) ≤ t - (#((A ∪ B) \ A') + #((A ∩ B) \ B')))]

/-- An element `a ∈ A ∪ B` outside `A' + H` gives at least $|H| - \rho - (t - 1)$ sums `a + b`,
`b ∈ B'`, outside `A' + B'` with more than `t` representations. -/
lemma card_addStab_sub_holes_le_card_filter_add_left (ht : 1 ≤ t) (hB' : B' ⊆ A ∩ B)
    (hA'ne : A'.Nonempty) (hB'ne : B'.Nonempty) (hdef : #(A' + B') < #A' + #B')
    (hCa : ∀ a ∈ A, #{b ∈ B | A.addConvolution B (a + b) ≤ t} ≤ t - 1)
    (hCb : ∀ b ∈ B, #{a ∈ A | A.addConvolution B (a + b) ≤ t} ≤ t - 1)
    (haU : a ∈ A ∪ B) (ha : a ∉ A' + (A' + B').addStab) :
    (#(A' + B').addStab - (holes (A' + B').addStab A' + holes (A' + B').addStab B') : ℤ) ≤
      #{b ∈ B' | a + b ∉ A' + B' ∧ t < A.addConvolution B (a + b)} + (t - 1) := by
  have hcontr := card_addStab_sub_holes_sub_card_le_left hA'ne hB'ne hdef ha ∅
  have hbad : #{b ∈ B' | a + b ∉ A' + B' ∧ A.addConvolution B (a + b) ≤ t} ≤ t - 1 := by
    rcases mem_union.1 haU with haA | haB
    · refine le_trans (card_le_card ?_) (hCa a haA)
      intro b hb
      simp only [mem_filter] at hb ⊢
      obtain ⟨hb, -, hab⟩ := hb
      exact ⟨mem_of_mem_inter_right (hB' hb), hab⟩
    · refine le_trans (card_le_card ?_) (hCb a haB)
      intro b hb
      simp only [mem_filter] at hb ⊢
      obtain ⟨hb, -, hab⟩ := hb
      rw [add_comm]
      exact ⟨mem_of_mem_inter_left (hB' hb), hab⟩
  have hsplit := card_filter_add_card_filter_not (s := {b ∈ B' | a + b ∉ A' + B'})
    (fun b ↦ t < A.addConvolution B (a + b))
  simp only [filter_filter, not_lt] at hsplit
  simp only [union_empty, card_empty, Nat.cast_zero, sub_zero] at hcontr
  have h := (Nat.cast_le (α := ℤ)).2 (by grind : #{b ∈ B' | a + b ∉ A' + B'} ≤
    #{b ∈ B' | a + b ∉ A' + B' ∧ t < A.addConvolution B (a + b)} + (t - 1))
  push_cast [ht] at h
  linarith

/-- An element `b ∈ A ∩ B` outside `B' + H` gives at least $|H| - \rho - (2t - 2)$ sums `a + b`,
`a ∈ A'`, outside `A' + B'` with more than `t` representations. -/
lemma card_addStab_sub_holes_le_card_filter_add_right (ht : 1 ≤ t) (hA' : A' ⊆ A ∪ B)
    (hA'ne : A'.Nonempty) (hB'ne : B'.Nonempty) (hdef : #(A' + B') < #A' + #B')
    (hCa : ∀ a ∈ A, #{b ∈ B | A.addConvolution B (a + b) ≤ t} ≤ t - 1)
    (hCb : ∀ b ∈ B, #{a ∈ A | A.addConvolution B (a + b) ≤ t} ≤ t - 1)
    (hbI : b ∈ A ∩ B) (hb : b ∉ B' + (A' + B').addStab) :
    (#(A' + B').addStab - (holes (A' + B').addStab A' + holes (A' + B').addStab B') : ℤ) ≤
      #{a ∈ A' | a + b ∉ A' + B' ∧ t < A.addConvolution B (a + b)} + (2 * t - 2) := by
  obtain ⟨hbA, hbB⟩ := mem_inter.1 hbI
  have hcontr := card_addStab_sub_holes_sub_card_le_right hA'ne hB'ne hdef hb ∅
  have hbad : #{a ∈ A' | a + b ∉ A' + B' ∧ A.addConvolution B (a + b) ≤ t} ≤ 2 * t - 2 := by
    refine le_trans (card_le_card (t := {a ∈ A | A.addConvolution B (a + b) ≤ t} ∪
      {a ∈ B | A.addConvolution B (b + a) ≤ t}) ?_)
      ((card_union_le _ _).trans (by grind [hCb b hbB, hCa b hbA]))
    intro a ha
    simp only [mem_filter, mem_union] at ha ⊢
    obtain ⟨ha, -, hab⟩ := ha
    rcases mem_union.1 (hA' ha) with haA | haB
    · exact Or.inl ⟨haA, hab⟩
    · rw [add_comm] at hab
      exact Or.inr ⟨haB, hab⟩
  have hsplit := card_filter_add_card_filter_not (s := {a ∈ A' | a + b ∉ A' + B'})
    (fun a ↦ t < A.addConvolution B (a + b))
  simp only [filter_filter, not_lt] at hsplit
  simp only [union_empty, card_empty, Nat.cast_zero, sub_zero] at hcontr
  have h := (Nat.cast_le (α := ℤ)).2 (by grind : #{a ∈ A' | a + b ∉ A' + B'} ≤
    #{a ∈ A' | a + b ∉ A' + B' ∧ t < A.addConvolution B (a + b)} + (2 * t - 2))
  push_cast [(by grind : 2 ≤ 2 * t)] at h
  linarith

/-- **Case 4.1, an element of `A ∪ B` outside `A'`.** -/
lemma mul_card_add_mul_card_le_of_mem_union_sdiff (ht : 1 ≤ t) (hA' : A' ⊆ A ∪ B)
    (hB' : B' ⊆ A ∩ B) (hA'ne : A'.Nonempty) (hB'ne : B'.Nonempty)
    (hL : #((A ∪ B) \ A') + #((A ∩ B) \ B') ≤ t)
    (hrep : representableSums t A' B' = A' + B') (hdef : #(A' + B') < #A' + #B')
    (hsatA : ∀ a ∈ A ∪ B, a ∈ A' + (A' + B').addStab → a ∈ A')
    (hsatB : ∀ b ∈ A ∩ B, b ∈ B' + (A' + B').addStab → b ∈ B')
    (hCa : ∀ a ∈ A, #{b ∈ B | A.addConvolution B (a + b) ≤ t} ≤ t - 1)
    (hCb : ∀ b ∈ B, #{a ∈ A | A.addConvolution B (a + b) ≤ t} ≤ t - 1)
    (ha : a ∈ (A ∪ B) \ A') :
    (t * #A + t * #B : ℤ) ≤ sumCardRepresentableSums t A B +
      t * (#((A ∪ B) \ A') + #((A ∩ B) \ B')) +
        (t - (#((A ∪ B) \ A') + #((A ∩ B) \ B'))) * (t - 1) := by
  obtain ⟨haU, haA'⟩ := mem_sdiff.1 ha
  refine mul_card_add_mul_card_le_of_card_addStab_sub_holes_le ht hA' hB' hA'ne hB'ne hL hrep
    hdef hsatA hsatB
    (D := {b ∈ B' | a + b ∉ A' + B' ∧ t < A.addConvolution B (a + b)}.image (a + ·)) ?_ ?_ ?_
  · intro x hx
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hx
    obtain ⟨-, -, hab⟩ := mem_filter.1 hb
    rw [mem_representableSums']
    grind
  · rw [disjoint_right]
    intro x hx
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hx
    obtain ⟨-, hab, -⟩ := mem_filter.1 hb
    exact hab
  · rw [card_image_of_injective _ (add_right_injective a)]
    exact card_addStab_sub_holes_le_card_filter_add_left ht hB' hA'ne hB'ne hdef hCa hCb haU
      fun h ↦ haA' (hsatA a haU h)

/-- **Case 4.1, an element of `A ∩ B` outside `B'`.** -/
lemma mul_card_add_mul_card_le_of_mem_inter_sdiff (ht : 1 ≤ t) (hA' : A' ⊆ A ∪ B)
    (hB' : B' ⊆ A ∩ B) (hA'ne : A'.Nonempty) (hB'ne : B'.Nonempty)
    (hL : #((A ∪ B) \ A') + #((A ∩ B) \ B') ≤ t)
    (hrep : representableSums t A' B' = A' + B') (hdef : #(A' + B') < #A' + #B')
    (hsatA : ∀ a ∈ A ∪ B, a ∈ A' + (A' + B').addStab → a ∈ A')
    (hsatB : ∀ b ∈ A ∩ B, b ∈ B' + (A' + B').addStab → b ∈ B')
    (hCa : ∀ a ∈ A, #{b ∈ B | A.addConvolution B (a + b) ≤ t} ≤ t - 1)
    (hCb : ∀ b ∈ B, #{a ∈ A | A.addConvolution B (a + b) ≤ t} ≤ t - 1)
    (hb : b ∈ (A ∩ B) \ B') :
    (t * #A + t * #B : ℤ) ≤ sumCardRepresentableSums t A B +
      t * (#((A ∪ B) \ A') + #((A ∩ B) \ B')) +
        (t - (#((A ∪ B) \ A') + #((A ∩ B) \ B'))) * (2 * t - 2) := by
  obtain ⟨hbI, hbB'⟩ := mem_sdiff.1 hb
  refine mul_card_add_mul_card_le_of_card_addStab_sub_holes_le ht hA' hB' hA'ne hB'ne hL hrep
    hdef hsatA hsatB
    (D := {a ∈ A' | a + b ∉ A' + B' ∧ t < A.addConvolution B (a + b)}.image (· + b)) ?_ ?_ ?_
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
    obtain ⟨-, -, hab⟩ := mem_filter.1 ha
    rw [mem_representableSums']
    grind
  · rw [disjoint_right]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
    obtain ⟨-, hab, -⟩ := mem_filter.1 ha
    exact hab
  · rw [card_image_of_injective _ (add_left_injective b)]
    exact card_addStab_sub_holes_le_card_filter_add_right ht hA' hA'ne hB'ne hdef hCa hCb hbI
      fun h ↦ hbB' (hsatB b hbI h)

/-! ### Case 4.2 -/

/-- An element of `A ∩ B` shifted by the stabilizer stays in `A ∩ B` when `A ∩ B` is periodic. -/
lemma mem_inter_of_sub_mem (hC : C.Nonempty)
    (hper : ∀ c ∈ A ∩ B, ∀ h ∈ C.addStab, c + h ∈ A ∩ B) (hx : x ∈ A ∩ B)
    (h : x - g ∈ C.addStab) : g ∈ A ∩ B := by
  simpa using hper x hx _ (neg_mem_addStab hC h)

/-- If `A ∩ B` is periodic, the coset of an element outside `A ∩ B` does not meet `A ∩ B`. -/
lemma notMem_inter_of_mem_vadd (hC : C.Nonempty)
    (hper : ∀ c ∈ A ∩ B, ∀ h ∈ C.addStab, c + h ∈ A ∩ B) (hg : g ∉ A ∩ B)
    (hx : x ∈ g +ᵥ C.addStab) : x ∉ A ∩ B :=
  fun h ↦ hg (mem_inter_of_sub_mem hC hper h (mem_vadd_finset_iff_sub_mem.1 hx))

/-- A sum `a + b` outside $(A \cup B) + (A \cap B)$ has `a ∉ B` and `b ∉ A`. -/
lemma notMem_and_notMem_of_add_notMem (hC : (A ∪ B) + (A ∩ B) ⊆ C) (ha : a ∈ A) (hb : b ∈ B)
    (hab : a + b ∉ C) : a ∉ B ∧ b ∉ A := by
  refine ⟨fun h ↦ hab (hC ?_), fun h ↦ hab (hC ?_)⟩
  · rw [add_comm a b]
    exact add_mem_add (mem_union_right _ hb) (mem_inter.2 ⟨ha, h⟩)
  · exact add_mem_add (mem_union_left _ ha) (mem_inter.2 ⟨h, hb⟩)

/-- If `a + b ∉ C`, then no element of the coset `a + H` gives a sum with `b` in `C`. -/
lemma add_notMem_of_mem_vadd_addStab (hC : C.Nonempty) (hab : a + b ∉ C)
    (ha' : a' ∈ a +ᵥ C.addStab) : a' + b ∉ C := by
  intro h
  apply hab
  convert add_mem_of_mem_addStab h (neg_mem_addStab hC (mem_vadd_finset_iff_sub_mem.1 ha'))
    using 1
  abel

/-- **The maximality of the Dyson transform.** If `A ∩ B` is periodic, `x ∈ A \ B` and `d ∈ B \ A`
lie in the same coset, then `x - d + B ⊆ A`. -/
lemma sub_add_mem_of_sub_mem
    (hmax : ∀ y : G, #(A ∩ (y +ᵥ B)) < #B → #(A ∩ (y +ᵥ B)) ≤ #(A ∩ B)) (hC : C.Nonempty)
    (hper : ∀ c ∈ A ∩ B, ∀ h ∈ C.addStab, c + h ∈ A ∩ B) (hx : x ∈ A) (hxB : x ∉ B)
    (hd : d ∈ B) (hxd : x - d ∈ C.addStab) (hb : b ∈ B) : x - d + b ∈ A := by
  refine vadd_finset_subset_of_card_inter_lt hmax ?_ (vadd_mem_vadd_finset hb)
  refine card_lt_card ((ssubset_iff_of_subset ?_).2 ⟨x, ?_, ?_⟩)
  · intro c hc
    refine mem_inter.2 ⟨mem_of_mem_inter_left hc, mem_vadd_finset_iff_sub_mem.2 ?_⟩
    rw [sub_eq_add_neg]
    exact mem_of_mem_inter_right (hper c hc _ (neg_mem_addStab hC hxd))
  · exact mem_inter.2 ⟨hx, mem_vadd_finset_iff_sub_mem.2 (by simpa using hd)⟩
  · exact fun h ↦ hxB (mem_of_mem_inter_right h)

/-- In two cosets meeting both `A \ B` and `B \ A`, every sum `a + b` has at least as many
representations as `b + H` has elements of `B`. -/
lemma card_inter_vadd_le_addConvolution
    (hmax : ∀ y : G, #(A ∩ (y +ᵥ B)) < #B → #(A ∩ (y +ᵥ B)) ≤ #(A ∩ B)) (hC : C.Nonempty)
    (hper : ∀ c ∈ A ∩ B, ∀ h ∈ C.addStab, c + h ∈ A ∩ B) (ha : a ∈ A) (haB : a ∉ B)
    (hd : d ∈ B) (had : a - d ∈ C.addStab) (hb : b ∈ B) (hbA : b ∉ A) :
    #(B ∩ (b +ᵥ C.addStab)) ≤ A.addConvolution B (a + b) := by
  have hx₁ := sub_add_mem_of_sub_mem hmax hC hper ha haB hd had hb
  have hx₁B : a - d + b ∉ B := fun h ↦ hbA (mem_of_mem_inter_left (mem_inter_of_sub_mem hC hper
    (mem_inter.2 ⟨hx₁, h⟩) (by rwa [add_sub_cancel_right])))
  refine card_le_card_of_injOn (fun d' ↦ (a + b - d', d')) ?_
    fun d₁ _ d₂ _ h ↦ congrArg Prod.snd h
  intro d' hd'
  obtain ⟨hd'B, hd'H⟩ := mem_inter.1 hd'
  have hx₂ := sub_add_mem_of_sub_mem hmax hC hper hx₁ hx₁B hd'B (by
    convert add_mem_addStab hC had (neg_mem_addStab hC (mem_vadd_finset_iff_sub_mem.1 hd'H))
      using 1
    abel) hd
  simp only [coe_filter, mem_product, Set.mem_ofPred_eq]
  refine ⟨⟨?_, hd'B⟩, by abel⟩
  convert hx₂ using 1
  abel

/-- The cosets meeting both `A \ B` and `B \ A` meet `A` in the same number of elements. -/
lemma card_inter_vadd_le_card_inter_vadd
    (hmax : ∀ y : G, #(A ∩ (y +ᵥ B)) < #B → #(A ∩ (y +ᵥ B)) ≤ #(A ∩ B)) (hC : C.Nonempty)
    (hper : ∀ c ∈ A ∩ B, ∀ h ∈ C.addStab, c + h ∈ A ∩ B) (hd : d ∈ B)
    (had : a - d ∈ C.addStab) (hb : b ∈ B) (hbA : b ∉ A) :
    #(A ∩ (b +ᵥ C.addStab)) ≤ #(A ∩ (a +ᵥ C.addStab)) := by
  refine card_le_card_of_injOn (fun x ↦ x - b + d) ?_ fun x _ y _ h ↦ by simpa using h
  intro x hx
  obtain ⟨hxA, hxH⟩ := mem_inter.1 hx
  rw [mem_vadd_finset_iff_sub_mem] at hxH
  have hxB : x ∉ B := fun h ↦ hbA (mem_of_mem_inter_left (mem_inter_of_sub_mem hC hper
    (mem_inter.2 ⟨hxA, h⟩) hxH))
  refine mem_inter.2 ⟨sub_add_mem_of_sub_mem hmax hC hper hxA hxB hb hxH hd,
    mem_vadd_finset_iff_sub_mem.2 ?_⟩
  beta_reduce
  convert sub_mem_addStab hC hxH had using 1
  abel

/-- **Case 4.2, a coset without elements of `B`.** If `a + b ∉ C` for some `a ∈ A`, `b ∈ B`, then
the coset `a + H` meets `B`. -/
lemma exists_sub_mem_addStab_of_add_notMem_left (ht : 1 ≤ t)
    (hS : sumCardRepresentableSums t A B + t ^ 2 < t * #A + t * #B)
    (hC : C ⊆ representableSums t A B) (hCne : C.Nonempty) {X : ℤ}
    (hKn : (#A + #B : ℤ) ≤ #C + X) (hhole : X ≤ #((A ∪ B) ∩ (a +ᵥ C.addStab)))
    (hb : b ∈ B) (hCb : #{a ∈ A | A.addConvolution B (a + b) ≤ t} ≤ t - 1) (hab : a + b ∉ C) :
    ∃ d ∈ B, a - d ∈ C.addStab := by
  by_contra! hBa
  have hX' : (A ∪ B) ∩ (a +ᵥ C.addStab) = A ∩ (a +ᵥ C.addStab) := by
    ext x
    simp only [mem_inter, mem_union, mem_vadd_finset_iff_sub_mem]
    grind [hBa x, sub_mem_addStab_comm hCne (a := x) (b := a)]
  have := mul_card_add_mul_card_le_of_forall_add_notMem (k := 1) hC hb inter_subset_left
    (fun a' ha' ↦ add_notMem_of_mem_vadd_addStab hCne hab (mem_of_mem_inter_right ha'))
    (fun a' ha' ↦ Nat.one_le_iff_ne_zero.2 (Finset.addConvolution_ne_zero.2
      (add_mem_add (mem_of_mem_inter_left ha') hb))) ht hCb
  rw [hX'] at hhole
  zify [ht] at this hS
  nlinarith [mul_le_mul_of_nonneg_left hKn (by positivity : (0 : ℤ) ≤ t),
    mul_le_mul_of_nonneg_left hhole (by positivity : (0 : ℤ) ≤ t)]

/-- **Case 4.2, a coset without elements of `A`.** If `a + b ∉ C` for some `a ∈ A`, `b ∈ B`, then
the coset `b + H` meets `A`. -/
lemma exists_sub_mem_addStab_of_add_notMem_right (ht : 1 ≤ t)
    (hS : sumCardRepresentableSums t A B + t ^ 2 < t * #A + t * #B)
    (hC : C ⊆ representableSums t A B) (hCne : C.Nonempty) {X : ℤ}
    (hKn : (#A + #B : ℤ) ≤ #C + X) (hhole : X ≤ #((A ∪ B) ∩ (b +ᵥ C.addStab)))
    (ha : a ∈ A) (hCa : #{b ∈ B | A.addConvolution B (a + b) ≤ t} ≤ t - 1) (hab : a + b ∉ C) :
    ∃ e ∈ A, b - e ∈ C.addStab := by
  refine exists_sub_mem_addStab_of_add_notMem_left (A := B) (B := A) ht ?_ ?_ hCne (X := X) ?_ ?_
    ha ?_ ?_
  · rwa [sumCardRepresentableSums_comm, add_comm (t * #B)]
  · rwa [representableSums_comm]
  · linarith
  · rwa [union_comm]
  · simpa [addConvolution_comm B A, add_comm] using hCa
  · rwa [add_comm]

/-- **Case 4.2, two cosets meeting both `A \ B` and `B \ A`.** If `a + b ∉ C`, where the cosets of
`a ∈ A` and `b ∈ B` meet both `A \ B` and `B \ A`, then `b + H` has at least `t` elements of
`B`. -/
lemma le_card_inter_vadd_of_add_notMem (ht : 1 ≤ t)
    (hS : sumCardRepresentableSums t A B + t ^ 2 < t * #A + t * #B)
    (hC : C ⊆ representableSums t A B) (hCne : C.Nonempty) {X : ℤ}
    (hKn : (#A + #B : ℤ) ≤ #C + X) (hb : b ∈ B)
    (hhole : X ≤ #((A ∪ B) ∩ (b +ᵥ C.addStab)))
    (hcoset : ∀ x ∈ b +ᵥ C.addStab, x ∈ A → x ∉ B)
    (hlow : ∀ a' ∈ A ∩ (a +ᵥ C.addStab), #(B ∩ (b +ᵥ C.addStab)) ≤ A.addConvolution B (a' + b))
    (hcard : #(A ∩ (b +ᵥ C.addStab)) ≤ #(A ∩ (a +ᵥ C.addStab))) (hab : a + b ∉ C)
    (hCb : #{a ∈ A | A.addConvolution B (a + b) ≤ t} ≤ t - 1) :
    t ≤ #(B ∩ (b +ᵥ C.addStab)) := by
  by_contra! hlt
  have := mul_card_add_mul_card_le_of_forall_add_notMem hC hb inter_subset_left
    (fun a' ha' ↦ add_notMem_of_mem_vadd_addStab hCne hab (mem_of_mem_inter_right ha')) hlow
    hlt.le hCb
  have hsplit : #((A ∪ B) ∩ (b +ᵥ C.addStab)) =
      #(A ∩ (b +ᵥ C.addStab)) + #(B ∩ (b +ᵥ C.addStab)) := by
    rw [union_inter_distrib_right, card_union_of_disjoint]
    rw [disjoint_left]
    intro x hxA hxB
    obtain ⟨hxA, hxH⟩ := mem_inter.1 hxA
    exact hcoset x hxH hxA (mem_of_mem_inter_left hxB)
  rw [hsplit] at hhole
  zify [ht, hlt.le] at this hS hlt hcard
  push_cast at hhole
  nlinarith [mul_le_mul_of_nonneg_left hKn (by positivity : (0 : ℤ) ≤ t),
    mul_le_mul_of_nonneg_left hhole (by positivity : (0 : ℤ) ≤ t),
    mul_le_mul_of_nonneg_left hcard (by positivity : (0 : ℤ) ≤ t)]

/-- **Case 4.2, the periodicity of `A ∩ B`.** If the theorem fails for `A` and `B` and
$(A \cup B) + (A \cap B) \subseteq A +_t B$, then `A ∩ B` is periodic with respect to the stabilizer
of $(A \cup B) + (A \cap B)$. -/
lemma add_mem_inter_of_mem_addStab (ht : 1 ≤ t) (hIH : InductionHypothesis t A B)
    (hA : t + 1 ≤ #A) (hB : t + 1 ≤ #B) (hgood : ¬SumLowerBound t A B)
    (hsse : ¬SubsetSumsetEq t A B) (hC : (A ∪ B) + (A ∩ B) ⊆ representableSums t A B)
    {c h : G} (hc : c ∈ A ∩ B) (hh : h ∈ ((A ∪ B) + (A ∩ B)).addStab) : c + h ∈ A ∩ B := by
  by_contra hα
  by_cases hαA : c + h ∈ A
  · refine false_of_insert_right ht hIH (by grind) (by grind) hgood hsse
      (fun h' ↦ hα (mem_inter.2 ⟨hαA, h'⟩)) ?_
    intro a ha
    apply hC
    rw [← add_assoc]
    exact add_mem_of_mem_addStab (add_mem_add (mem_union_left _ ha) hc) hh
  · refine false_of_insert_left ht hIH (by grind) (by grind) hgood hsse hαA ?_
    intro b hb
    apply hC
    rw [(by abel : c + h + b = b + c + h)]
    exact add_mem_of_mem_addStab (add_mem_add (mem_union_right _ hb) hc) hh

/-- Every coset `g + H` with `g ∈ A` meets `A` in at least $|H| - \rho$ elements, where `H` is the
stabilizer of `A + B` and `ρ` the number of `H`-holes of `A` and `B`. -/
lemma card_addStab_sub_holes_le_card_inter_vadd (hA : A.Nonempty) (hB : B.Nonempty) (hg : g ∈ A) :
    (#(A + B).addStab - (holes (A + B).addStab A + holes (A + B).addStab B) : ℤ) ≤
      #(A ∩ (g +ᵥ (A + B).addStab)) := by
  have h₁ := card_add_card_inter_vadd_le (hA.add hB) hg
  rw [holes_eq (hA.add hB)]
  zify at h₁
  linarith [(by positivity : (0 : ℤ) ≤ holes (A + B).addStab B)]

/-- Kneser's theorem for the Dyson transform: $|A| + |B| \le |C| + |H| - \rho$, where `H` is the
stabilizer of $C = (A \cup B) + (A \cap B)$ and `ρ` the number of `H`-holes of `A ∪ B` and
`A ∩ B`. -/
lemma card_add_card_le_card_union_add_inter_add (hU : (A ∪ B).Nonempty)
    (hI : (A ∩ B).Nonempty) :
    (#A + #B : ℤ) ≤ #((A ∪ B) + (A ∩ B)) + (#((A ∪ B) + (A ∩ B)).addStab -
      (holes ((A ∪ B) + (A ∩ B)).addStab (A ∪ B) + holes ((A ∪ B) + (A ∩ B)).addStab (A ∩ B))) := by
  have hU' := card_union_add_card_inter A B
  zify at hU'
  linarith [card_add_sub_card_addStab_add_holes_le (A ∪ B) (A ∩ B) hU hI]

/-- **Case 4.2, a coset of `B \ A` meeting `A`.** If `b ∈ B \ A` and its coset `b + H` meets `A`,
then `b + H` has at least `t` elements of `B`. -/
lemma le_card_inter_vadd_of_sub_mem (ht : 1 ≤ t) (hIH : InductionHypothesis t A B)
    (hA : t + 1 ≤ #A) (hB : t + 1 ≤ #B) (hgood : ¬SumLowerBound t A B)
    (hsse : ¬SubsetSumsetEq t A B)
    (hmax : ∀ y : G, #(A ∩ (y +ᵥ B)) < #B → #(A ∩ (y +ᵥ B)) ≤ #(A ∩ B))
    (hS : sumCardRepresentableSums t A B + t ^ 2 < t * #A + t * #B)
    (hC : C ⊆ representableSums t A B) (hCne : C.Nonempty) (hUC : (A ∪ B) + (A ∩ B) ⊆ C)
    {X : ℤ} (hKn : (#A + #B : ℤ) ≤ #C + X)
    (hhole : ∀ g ∈ A ∪ B, X ≤ #((A ∪ B) ∩ (g +ᵥ C.addStab)))
    (hper : ∀ c ∈ A ∩ B, ∀ h ∈ C.addStab, c + h ∈ A ∩ B)
    (hCb : ∀ b ∈ B, #{a ∈ A | A.addConvolution B (a + b) ≤ t} ≤ t - 1) (hb : b ∈ B)
    (hbA : b ∉ A) (he : e ∈ A) (heb : e - b ∈ C.addStab) :
    t ≤ #(B ∩ (b +ᵥ C.addStab)) := by
  have hbI : b ∉ A ∩ B := fun h ↦ hbA (mem_of_mem_inter_left h)
  by_cases hall : ∀ a ∈ A, a + b ∈ C
  · refine (false_of_insert_right ht hIH (by grind) (by grind) hgood hsse (fun h ↦
      notMem_inter_of_mem_vadd hCne hper hbI (mem_vadd_finset_iff_sub_mem.2 heb)
        (mem_inter.2 ⟨he, h⟩)) ?_).elim
    intro a ha
    apply hC
    convert add_mem_of_mem_addStab (hall a ha) heb using 1
    abel
  push Not at hall
  obtain ⟨a, ha, hab⟩ := hall
  obtain ⟨haB, -⟩ := notMem_and_notMem_of_add_notMem hUC ha hb hab
  obtain ⟨d, hd, had⟩ := exists_sub_mem_addStab_of_add_notMem_left ht hS hC hCne hKn
    (hhole a (mem_union_left _ ha)) hb (hCb b hb) hab
  refine le_card_inter_vadd_of_add_notMem ht hS hC hCne hKn hb (hhole b (mem_union_right _ hb))
    ?_ ?_ (card_inter_vadd_le_card_inter_vadd hmax hCne hper hd had hb hbA) hab (hCb b hb)
  · intro x hx hxA hxB
    exact notMem_inter_of_mem_vadd hCne hper hbI hx (mem_inter.2 ⟨hxA, hxB⟩)
  · intro a' ha'
    obtain ⟨ha'A, ha'H⟩ := mem_inter.1 ha'
    refine card_inter_vadd_le_addConvolution hmax hCne hper ha'A ?_ hd ?_ hb hbA
    · intro h
      exact notMem_inter_of_mem_vadd hCne hper (fun h ↦ haB (mem_of_mem_inter_right h)) ha'H
        (mem_inter.2 ⟨ha'A, h⟩)
    · convert add_mem_addStab hCne (mem_vadd_finset_iff_sub_mem.1 ha'H) had using 1
      abel

/-- **Case 4.2.** If the theorem fails for `A` and `B` and every sum of the Dyson transform
`(A ∪ B, A ∩ B)` is `t`-representable in it, then all the sums of `A + B` are `t`-representable,
a contradiction. -/
lemma false_of_representableSums_union_inter_eq (ht : 1 ≤ t) (hIH : InductionHypothesis t A B)
    (hA : t + 1 ≤ #A) (hB : t + 1 ≤ #B) (hgood : ¬SumLowerBound t A B)
    (hsse : ¬SubsetSumsetEq t A B)
    (hmax : ∀ y : G, #(A ∩ (y +ᵥ B)) < #B → #(A ∩ (y +ᵥ B)) ≤ #(A ∩ B))
    (hABne : (A ∩ B).Nonempty)
    (hrep : representableSums t (A ∪ B) (A ∩ B) = (A ∪ B) + (A ∩ B)) : False := by
  have hS : sumCardRepresentableSums t A B + t ^ 2 < t * #A + t * #B := by
    unfold SumLowerBound at hgood
    grind [sq_le_deficit t]
  have hUne : (A ∪ B).Nonempty := (hABne.mono inter_subset_left).mono subset_union_left
  have hCrep : (A ∪ B) + (A ∩ B) ⊆ representableSums t A B := by
    rw [← hrep]
    intro x hx
    rw [mem_representableSums_of_one_le ht] at hx ⊢
    exact hx.trans (addConvolution_union_inter_le A B x)
  have hper := fun c (hc : c ∈ A ∩ B) h (hh : h ∈ ((A ∪ B) + (A ∩ B)).addStab) ↦
    add_mem_inter_of_mem_addStab ht hIH hA hB hgood hsse hCrep hc hh
  have hKn := card_add_card_le_card_union_add_inter_add hUne hABne
  have hhole (g : G) (hg : g ∈ A ∪ B) := card_addStab_sub_holes_le_card_inter_vadd hUne hABne hg
  refine hsse (subsetSumsetEq_of_representableSums_eq
    (subset_antisymm representableSums_subset_add ?_))
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hx
  by_cases hab : a + b ∈ (A ∪ B) + (A ∩ B)
  · exact hCrep hab
  obtain ⟨haB, hbA⟩ := notMem_and_notMem_of_add_notMem subset_rfl ha hb hab
  obtain ⟨e, he, hbe⟩ := exists_sub_mem_addStab_of_add_notMem_right ht hS hCrep (hUne.add hABne)
    hKn (hhole b (mem_union_right _ hb)) ha
    (card_filter_addConvolution_le_of_mem_left ht hIH hA (by grind) hgood hsse ha) hab
  obtain ⟨d, hd, had⟩ := exists_sub_mem_addStab_of_add_notMem_left ht hS hCrep (hUne.add hABne)
    hKn (hhole a (mem_union_left _ ha)) hb
    (card_filter_addConvolution_le_of_mem_right ht hIH (by grind) hB hgood hsse hb) hab
  rw [mem_representableSums_of_one_le ht]
  exact (le_card_inter_vadd_of_sub_mem ht hIH hA hB hgood hsse hmax hS hCrep (hUne.add hABne)
    subset_rfl hKn hhole hper
    (fun b hb ↦ card_filter_addConvolution_le_of_mem_right ht hIH (by grind) hB hgood hsse hb)
    hb hbA he ((sub_mem_addStab_comm (hUne.add hABne)).1 hbe)).trans
    (card_inter_vadd_le_addConvolution hmax (hUne.add hABne) hper ha haB hd had hb hbA)

/-! ### Step 4 -/

/-- **Step 4.** If the theorem fails for `A` and `B` and $t \le |A \cap B| < |B|$, the theorem
for the Dyson transform `(A ∪ B, A ∩ B)` gives a contradiction. -/
lemma false_of_le_card_inter (ht : 1 ≤ t) (hIH : InductionHypothesis t A B) (hBA : #B ≤ #A)
    (hB : t + 1 ≤ #B) (hgood : ¬SumLowerBound t A B) (hsse : ¬SubsetSumsetEq t A B)
    (hAB : t ≤ #(A ∩ B)) (hlt : #(A ∩ B) < #B)
    (hmax : ∀ y : G, #(A ∩ (y +ᵥ B)) < #B → #(A ∩ (y +ᵥ B)) ≤ #(A ∩ B)) : False := by
  have hCa (a : G) (ha : a ∈ A) :=
    card_filter_addConvolution_le_of_mem_left ht hIH (by grind) (by grind) hgood hsse ha
  have hCb (b : G) (hb : b ∈ B) :=
    card_filter_addConvolution_le_of_mem_right ht hIH (by grind) hB hgood hsse hb
  have hU := card_union_add_card_inter A B
  have hS : sumCardRepresentableSums t (A ∪ B) (A ∩ B) ≤ sumCardRepresentableSums t A B :=
    sumCardRepresentableSums_le_of_forall fun x _ ↦ addConvolution_union_inter_le A B x
  rcases hIH (A ∪ B) (A ∩ B) (by grind [card_le_card (subset_union_left (s₁ := A) (s₂ := B))])
    hAB (by grind [card_le_card (subset_union_left (s₁ := A) (s₂ := B))]) with hgood' | hsse'
  · unfold SumLowerBound at hgood hgood'
    grind [congrArg (t * ·) hU]
  obtain ⟨A', B', hW, -⟩ := hsse'.exists_saturatedWitness ht
    (by grind [card_le_card (subset_union_left (s₁ := A) (s₂ := B))]) hAB (by
      unfold SumLowerBound at hgood
      grind [sq_le_deficit t, congrArg (t * ·) hU])
  obtain ⟨hA'ne, hB'ne⟩ := hW.nonempty ht
    (by grind [card_le_card (subset_union_left (s₁ := A) (s₂ := B))]) hAB
  obtain ⟨hA', hB', hl, hrep', -, hsatA, hsatB, hdef⟩ := hW
  unfold SumLowerBound at hgood
  rcases ((A ∪ B) \ A').eq_empty_or_nonempty with hAe | ⟨a, ha⟩
  · rcases ((A ∩ B) \ B').eq_empty_or_nonempty with hBe | ⟨b, hb⟩
    · rw [subset_antisymm hA' (sdiff_eq_empty_iff_subset.1 hAe),
        subset_antisymm hB' (sdiff_eq_empty_iff_subset.1 hBe)] at hrep'
      exact false_of_representableSums_union_inter_eq ht hIH (by grind) hB
        (by unfold SumLowerBound; exact hgood) hsse hmax (card_pos.1 (by grind)) hrep'
    · have := mul_card_add_mul_card_le_of_mem_inter_sdiff ht hA' hB' hA'ne hB'ne (by grind) hrep'
        hdef hsatA hsatB hCa hCb hb
      have hl₁ : 1 ≤ #((A ∩ B) \ B') := card_pos.2 ⟨b, hb⟩
      have hd := Nat.sub_le_iff_le_add.1 (two_mul_sq_sub_le_deficit ht)
      rw [hAe, card_empty] at this hl
      have ht₂ : 2 ≤ t := by grind
      zify [ht] at this hl hl₁ hgood hd
      nlinarith
  · have := mul_card_add_mul_card_le_of_mem_union_sdiff ht hA' hB' hA'ne hB'ne (by grind) hrep'
      hdef hsatA hsatB hCa hCb ha
    have hd := sq_le_deficit t
    zify [ht] at this hl hgood hd
    nlinarith

end ExtendingPollard
