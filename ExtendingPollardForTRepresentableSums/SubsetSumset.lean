/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ExtendingPollardForTRepresentableSums.Kneser.MulStab
public import ExtendingPollardForTRepresentableSums.RepresentableSums
import ExtendingPollardForTRepresentableSums.Kneser.Kneser
import ExtendingPollardForTRepresentableSums.KneserConsequences
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Representable sums as the sumset of large subsets

The main theorem states that either $\sum_{i=1}^t |A +_i B|$ is large, or there are `A' ⊆ A` and
`B' ⊆ B` missing at most `t - 1` elements in total with $A' +_t B' = A' + B' = A +_t B$. This file
defines the two alternatives, `SumLowerBound` and `SubsetSumsetEq`, and proves Step 1 of the paper:
the second alternative yields subsets satisfying the bound (9) of the paper, unless
$\sum_{i=1}^t |A +_i B| \ge t|A| + t|B| - t^2$.

The counting behind Step 1 is in `mul_card_add_mul_card_add_card_le` and
`card_sdiff_mul_le_card_filter`: every element of `A` outside `A'` and of `B` outside `B'` gives at
least `|H| - ρ` sums outside `A' + B'`, where `H` is the stabilizer of `A' + B'` and `ρ` is the
number of `H`-holes of `A'` and `B'`.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace ExtendingPollard

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {A A' A₀ A₁ B B' B₀ B₁ C D E : Finset G}
  {t : ℕ} {a b x : G}

/-! ### The two alternatives -/

/-- The deficit $2t^2 - 1$ of the bound (6) of Theorem 1.1, or `4` in the bound (10) of
Theorem 1.2 when `t = 2`. -/
def deficit (t : ℕ) : ℕ := if t = 2 then 4 else 2 * t ^ 2 - 1

/-- The bound (6) of Theorem 1.1, or (10) of Theorem 1.2 when `t = 2`. -/
def SumLowerBound (t : ℕ) (A B : Finset G) : Prop :=
  t * #A + t * #B ≤ sumCardRepresentableSums t A B + deficit t

/-- Conditions (7) and (8) of Theorem 1.1: `A +_t B` is the sumset of subsets `A' ⊆ A` and
`B' ⊆ B` missing at most `t - 1` elements in total, with $A' +_t B' = A' + B'$. -/
def SubsetSumsetEq (t : ℕ) (A B : Finset G) : Prop :=
  ∃ A' ⊆ A, ∃ B' ⊆ B, #(A \ A') + #(B \ B') ≤ t - 1 ∧
    representableSums t A' B' = A' + B' ∧ A' + B' = representableSums t A B

lemma sq_le_deficit (t : ℕ) : t ^ 2 ≤ deficit t := by
  unfold deficit
  grind [sq]

lemma deficit_le (t : ℕ) : deficit t ≤ 2 * t ^ 2 - 1 := by
  unfold deficit
  grind

lemma two_mul_sq_sub_le_deficit (ht : 1 ≤ t) : 2 * t ^ 2 - 2 * t ≤ deficit t := by
  unfold deficit
  grind [(by nlinarith : t ≤ t ^ 2)]

lemma deficit_of_ne_two (ht : t ≠ 2) : deficit t = 2 * t ^ 2 - 1 := by
  simp [deficit, ht]

lemma sumLowerBound_comm : SumLowerBound t A B ↔ SumLowerBound t B A := by
  rw [SumLowerBound, SumLowerBound, sumCardRepresentableSums_comm]
  grind

lemma SubsetSumsetEq.symm (h : SubsetSumsetEq t A B) : SubsetSumsetEq t B A := by
  obtain ⟨A', hA', B', hB', hl, h₁, h₂⟩ := h
  exact ⟨B', hB', A', hA', by grind, by rw [representableSums_comm, h₁, add_comm],
    by rw [add_comm, h₂, representableSums_comm]⟩

lemma subsetSumsetEq_comm : SubsetSumsetEq t A B ↔ SubsetSumsetEq t B A :=
  ⟨SubsetSumsetEq.symm, SubsetSumsetEq.symm⟩

/-- If every element of `A + B` has at least `t` representations, then `SubsetSumsetEq` holds with
`A' = A` and `B' = B`. -/
lemma subsetSumsetEq_of_representableSums_eq (h : representableSums t A B = A + B) :
    SubsetSumsetEq t A B :=
  ⟨A, subset_rfl, B, subset_rfl, by simp, h, h.symm⟩

/-! ### Counting the sums outside `A' + B'` -/

/-- An element outside `A' + B'` has at most `|A \ A'| + |B \ B'|` representations in `A + B`. -/
lemma addConvolution_le_of_notMem_add (hx : x ∉ A' + B') :
    A.addConvolution B x ≤ #(A \ A') + #(B \ B') := by
  have hsub : {p ∈ A ×ˢ B | p.1 + p.2 = x} ⊆
      {p ∈ A ×ˢ B | p.1 + p.2 = x ∧ p.1 ∉ A'} ∪ {p ∈ A ×ˢ B | p.1 + p.2 = x ∧ p.2 ∉ B'} := by
    rintro ⟨a, b⟩ hp
    simp only [mem_filter, mem_product, mem_union] at hp ⊢
    grind [add_mem_add]
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (add_le_add ?_ ?_))
  · refine card_le_card_of_injOn Prod.fst ?_ ?_
    · rintro ⟨a, b⟩ hp
      simp only [coe_filter, mem_product, Set.mem_ofPred_eq, coe_sdiff, Set.mem_sdiff,
        mem_coe] at hp ⊢
      grind
    · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hq (rfl : a = a')
      simp only [coe_filter, mem_product, Set.mem_ofPred_eq] at hp hq
      grind
  · refine card_le_card_of_injOn Prod.snd ?_ ?_
    · rintro ⟨a, b⟩ hp
      simp only [coe_filter, mem_product, Set.mem_ofPred_eq, coe_sdiff, Set.mem_sdiff,
        mem_coe] at hp ⊢
      grind
    · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hq (rfl : b = b')
      simp only [coe_filter, mem_product, Set.mem_ofPred_eq] at hp hq
      grind

/-- The number of pairs with sum outside `E`, as a sum of numbers of representations. -/
lemma card_filter_add_notMem_eq_sum (A B E : Finset G) :
    #{p ∈ A ×ˢ B | p.1 + p.2 ∉ E} = ∑ x ∈ (A + B) \ E, A.addConvolution B x := by
  rw [card_eq_sum_card_fiberwise (f := fun p ↦ p.1 + p.2) (t := (A + B) \ E)]
  · apply sum_congr rfl
    intro x hx
    rw [filter_filter, Finset.addConvolution]
    congr 1
    apply filter_congr
    grind
  · rintro ⟨a, b⟩ hp
    simp only [coe_filter, mem_product, Set.mem_ofPred_eq, coe_sdiff, Set.mem_sdiff,
      mem_coe] at hp ⊢
    obtain ⟨⟨ha, hb⟩, hab⟩ := hp
    exact ⟨add_mem_add ha hb, hab⟩

/-- **The sum outside a set of popular sums.** Let `C` and `D` be disjoint sets of elements with
at least `t` representations in `A + B`, and let `A₁ + B₁` have pointwise fewer representations
than `A + B` and at most `t` outside `C`. Then
$\sum_{i=1}^t |A +_i B| \ge t|C| + t|D|$ plus the number of pairs of `A₁ × B₁` with sum outside
`C ∪ D`. -/
lemma mul_card_add_mul_card_add_card_le (ht : 1 ≤ t) (hCD : Disjoint C D)
    (hC : C ⊆ representableSums t A B) (hD : D ⊆ representableSums t A B)
    (hr : ∀ x, A₁.addConvolution B₁ x ≤ A.addConvolution B x)
    (hr₁ : ∀ x ∉ C, A₁.addConvolution B₁ x ≤ t) :
    t * #C + t * #D + #{p ∈ A₁ ×ˢ B₁ | p.1 + p.2 ∉ C ∪ D} ≤ sumCardRepresentableSums t A B := by
  have hA₁B₁ : A₁ + B₁ ⊆ A + B := by
    intro x hx
    rw [← Finset.addConvolution_pos] at hx ⊢
    exact hx.trans_le (hr x)
  have hmin : ∀ x ∈ C ∪ D, min (A.addConvolution B x) t = t := fun x hx ↦
    min_eq_right ((mem_representableSums_of_one_le ht).1 ((mem_union.1 hx).elim (hC ·) (hD ·)))
  rw [sumCardRepresentableSums_eq_sum_min,
    ← sum_sdiff (union_subset (hC.trans representableSums_subset_add)
      (hD.trans representableSums_subset_add)), sum_union hCD, card_filter_add_notMem_eq_sum,
    sum_const_nat fun x hx ↦ hmin x (mem_union_left _ hx),
    sum_const_nat fun x hx ↦ hmin x (mem_union_right _ hx), mul_comm #C, mul_comm #D]
  have : ∑ x ∈ (A₁ + B₁) \ (C ∪ D), A₁.addConvolution B₁ x ≤
      ∑ x ∈ (A + B) \ (C ∪ D), min (A.addConvolution B x) t := by
    refine (sum_le_sum_of_subset (sdiff_subset_sdiff hA₁B₁ subset_rfl)).trans ?_
    gcongr with x hx
    exact le_min (hr x) (hr₁ x (by grind))
  grind

/-- Pairs of `A₁ × B₁` with sum outside `E`, counted through the elements of `A₁ \ A'` and
`B₁ \ B'`. -/
lemma sum_card_filter_add_le_card_filter (hA' : A' ⊆ A₁) (hB' : B' ⊆ B₁) (E : Finset G) :
    ∑ a ∈ A₁ \ A', #{b ∈ B' | a + b ∉ E} + ∑ b ∈ B₁ \ B', #{a ∈ A' | a + b ∉ E} ≤
      #{p ∈ A₁ ×ˢ B₁ | p.1 + p.2 ∉ E} := by
  rw [(by simp_rw [card_filter, sum_product] : ∑ a ∈ A₁ \ A', #{b ∈ B' | a + b ∉ E} =
      #{p ∈ (A₁ \ A') ×ˢ B' | p.1 + p.2 ∉ E}),
    (by simp_rw [card_filter, sum_product_right] : ∑ b ∈ B₁ \ B', #{a ∈ A' | a + b ∉ E} =
      #{p ∈ A' ×ˢ (B₁ \ B') | p.1 + p.2 ∉ E}), ← card_union_of_disjoint]
  · apply card_le_card
    intro p hp
    simp only [mem_union, mem_filter, mem_product, mem_sdiff] at hp ⊢
    grind
  · rw [disjoint_left]
    intro p hp hp'
    simp only [mem_filter, mem_product, mem_sdiff] at hp hp'
    grind

/-! ### Holes and the contribution of the outside elements -/

/-- The number `#(A + H) - #A` of `H`-holes of `A`, the elements of `(A + H) \ A`. -/
def holes (H A : Finset G) : ℕ := #(A + H) - #A

lemma holes_eq (hC : C.Nonempty) (A : Finset G) :
    (holes C.addStab A : ℤ) = #(A + C.addStab) - #A := by
  rw [holes, Nat.cast_sub (card_le_card (subset_add_addStab hC A))]

/-- Kneser's theorem in terms of holes:
$|A + B| \ge |A| + |B| - |H| + \rho$. -/
lemma card_add_sub_card_addStab_add_holes_le (A B : Finset G) (hA : A.Nonempty)
    (hB : B.Nonempty) :
    (#A + #B - #(A + B).addStab + (holes (A + B).addStab A + holes (A + B).addStab B) : ℤ) ≤
      #(A + B) := by
  have := add_kneser A B
  zify at this
  rw [holes_eq (hA.add hB), holes_eq (hA.add hB)]
  linarith

/-- Kneser's theorem bounds the part of `B` in each coset of the stabilizer `H` of `A + B`:
$|B \cap (b + H)| \ge |A| + |B| - |A + B|$. -/
lemma card_add_card_le_card_add_add_card_inter_vadd (hA : A.Nonempty) (hb : b ∈ B) :
    #A + #B ≤ #(A + B) + #(B ∩ (b +ᵥ (A + B).addStab)) := by
  have h₁ := card_add_card_inter_vadd_le (hA.add ⟨b, hb⟩) hb
  have h₂ := card_add_sub_card_addStab_add_holes_le A B hA ⟨b, hb⟩
  have h₃ := card_le_card (subset_add_addStab (hA.add ⟨b, hb⟩) A)
  rw [holes_eq (hA.add ⟨b, hb⟩), holes_eq (hA.add ⟨b, hb⟩)] at h₂
  zify at h₁ h₃ ⊢
  linarith

/-- Every element of `A' + B'` has at least `|H| - ρ` representations, where `H` is the
stabilizer of `A' + B'` and `ρ` the number of `H`-holes of `A'` and `B'`. -/
lemma card_addStab_sub_holes_le_addConvolution (hx : x ∈ A' + B') :
    (#(A' + B').addStab - (holes (A' + B').addStab A' + holes (A' + B').addStab B') : ℤ) ≤
      A'.addConvolution B' x := by
  have := card_addStab_add_le_addConvolution hx
  zify at this
  rw [holes_eq ⟨x, hx⟩, holes_eq ⟨x, hx⟩]
  linarith

/-- An element `a ∉ A' + H` of a deficient sumset gives at least `|H| - ρ - |D|` sums `a + b` with
`b ∈ B'` outside `(A' + B') ∪ D`. -/
lemma card_addStab_sub_holes_sub_card_le_left (hA' : A'.Nonempty) (hB' : B'.Nonempty)
    (hdef : #(A' + B') < #A' + #B') (ha : a ∉ A' + (A' + B').addStab) (D : Finset G) :
    (#(A' + B').addStab - (holes (A' + B').addStab A' + holes (A' + B').addStab B') - #D : ℤ) ≤
      #{b ∈ B' | a + b ∉ A' + B' ∪ D} := by
  have h₁ := card_addStab_add_card_le_card_filter_add_notMem hA' hB' hdef ha
  have h₂ : #{b ∈ B' | a + b ∉ A' + B'} ≤ #{b ∈ B' | a + b ∉ A' + B' ∪ D} + #D := by
    refine (card_le_card (t := {b ∈ B' | a + b ∉ A' + B' ∪ D} ∪ {b ∈ B' | a + b ∈ D})
      ?_).trans ((card_union_le _ _).trans ?_)
    · intro b hb
      simp only [mem_filter, mem_union] at hb ⊢
      tauto
    · apply Nat.add_le_add_left
      refine card_le_card_of_injOn (a + ·) ?_ (add_right_injective a).injOn
      intro b hb
      simp only [coe_filter, Set.mem_ofPred_eq] at hb
      grind
  zify at h₁ h₂
  rw [holes_eq (hA'.add hB') B']
  linarith [(by positivity : (0 : ℤ) ≤ holes (A' + B').addStab A')]

/-- An element `b ∉ B' + H` of a deficient sumset gives at least `|H| - ρ - |D|` sums `a + b` with
`a ∈ A'` outside `(A' + B') ∪ D`. -/
lemma card_addStab_sub_holes_sub_card_le_right (hA' : A'.Nonempty) (hB' : B'.Nonempty)
    (hdef : #(A' + B') < #A' + #B') (hb : b ∉ B' + (A' + B').addStab) (D : Finset G) :
    (#(A' + B').addStab - (holes (A' + B').addStab A' + holes (A' + B').addStab B') - #D : ℤ) ≤
      #{a ∈ A' | a + b ∉ A' + B' ∪ D} := by
  have := card_addStab_sub_holes_sub_card_le_left (a := b) hB' hA'
    (by rwa [add_comm, add_comm #B']) (by rwa [add_comm B' A']) D
  simp only [add_comm B' A', add_comm b] at this
  linarith

/-- **The contribution of the outside elements.** If `A' ⊆ A₁` and `B' ⊆ B₁` contain every element
of `A₁` and `B₁` in their `H`-cosets, where `H` is the stabilizer of the deficient sumset
`A' + B'`, then each element of `A₁ \ A'` and `B₁ \ B'` gives at least `|H| - ρ - |D|` pairs of
`A₁ × B₁` with sum outside `(A' + B') ∪ D`. -/
lemma card_sdiff_mul_le_card_filter (hA' : A' ⊆ A₁) (hB' : B' ⊆ B₁) (hA'ne : A'.Nonempty)
    (hB'ne : B'.Nonempty) (hdef : #(A' + B') < #A' + #B')
    (hsatA : ∀ a ∈ A₁, a ∈ A' + (A' + B').addStab → a ∈ A')
    (hsatB : ∀ b ∈ B₁, b ∈ B' + (A' + B').addStab → b ∈ B') (D : Finset G) :
    ((#(A₁ \ A') + #(B₁ \ B') : ℕ) : ℤ) *
        (#(A' + B').addStab - (holes (A' + B').addStab A' + holes (A' + B').addStab B') - #D) ≤
      #{p ∈ A₁ ×ˢ B₁ | p.1 + p.2 ∉ A' + B' ∪ D} := by
  refine le_trans ?_ (Nat.cast_le.2 (sum_card_filter_add_le_card_filter hA' hB' (A' + B' ∪ D)))
  push_cast
  rw [add_mul, ← nsmul_eq_mul, ← nsmul_eq_mul]
  gcongr ?_ + ?_
  · apply card_nsmul_le_sum
    intro a ha
    obtain ⟨haA, haA'⟩ := mem_sdiff.1 ha
    exact card_addStab_sub_holes_sub_card_le_left hA'ne hB'ne hdef
      (fun h ↦ haA' (hsatA a haA h)) D
  · apply card_nsmul_le_sum
    intro b hb
    obtain ⟨hbB, hbB'⟩ := mem_sdiff.1 hb
    exact card_addStab_sub_holes_sub_card_le_right hA'ne hB'ne hdef
      (fun h ↦ hbB' (hsatB b hbB h)) D

/-- If `A' ⊆ A` and `B' ⊆ B` miss at most `t - 1` elements and every element of `A' + B'` has at
least `t` representations in `A' + B'`, then `SubsetSumsetEq t A B` holds: the sums outside
`A' + B'` have too few representations to lie in `A +_t B`. -/
lemma subsetSumsetEq_of_subset (ht : 1 ≤ t) (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    (hl : #(A \ A') + #(B \ B') ≤ t - 1) (hrep : representableSums t A' B' = A' + B') :
    SubsetSumsetEq t A B := by
  refine ⟨A', hA', B', hB', hl, hrep, subset_antisymm ?_ ?_⟩
  · rw [← hrep]
    exact representableSums_mono hA' hB'
  · intro x hx
    by_contra hx'
    rw [mem_representableSums_of_one_le ht] at hx
    grind [addConvolution_le_of_notMem_add (A := A) (B := B) hx']

/-- **The core inequality of Step 1.** Let `A' ⊆ A₁` and `B' ⊆ B₁` miss `L ≤ t` elements, with
$A' +_t B' = A' + B'$ deficient and containing every element of `A₁` and `B₁` in their `H`-cosets,
where `H` is the stabilizer of `A' + B'` and `ρ` the number of `H`-holes of `A'` and `B'`. If
`A₁ + B₁` has pointwise fewer representations than `A + B` and `D ⊆ A +_t B` is disjoint from
`A' + B'`, then
$t|A_1| + t|B_1| + (t - L)|D| \le \sum_{i=1}^t |A +_i B| + tL + (t - L)(|H| - \rho)$. -/
lemma mul_card_add_mul_card_add_mul_card_le (ht : 1 ≤ t) (hA' : A' ⊆ A₁) (hB' : B' ⊆ B₁)
    (hA'ne : A'.Nonempty) (hB'ne : B'.Nonempty) (hL : #(A₁ \ A') + #(B₁ \ B') ≤ t)
    (hrep : representableSums t A' B' = A' + B') (hdef : #(A' + B') < #A' + #B')
    (hsatA : ∀ a ∈ A₁, a ∈ A' + (A' + B').addStab → a ∈ A')
    (hsatB : ∀ b ∈ B₁, b ∈ B' + (A' + B').addStab → b ∈ B')
    (hr : ∀ x, A₁.addConvolution B₁ x ≤ A.addConvolution B x)
    (hD : D ⊆ representableSums t A B) (hCD : Disjoint (A' + B') D) :
    (t * #A₁ + t * #B₁ + (t - (#(A₁ \ A') + #(B₁ \ B'))) * #D : ℤ) ≤
      sumCardRepresentableSums t A B + t * (#(A₁ \ A') + #(B₁ \ B')) +
        (t - (#(A₁ \ A') + #(B₁ \ B'))) *
          (#(A' + B').addStab - (holes (A' + B').addStab A' + holes (A' + B').addStab B')) := by
  have hC : A' + B' ⊆ representableSums t A B := by
    intro x hx
    rw [← hrep, mem_representableSums_of_one_le ht] at hx
    rw [mem_representableSums_of_one_le ht]
    exact hx.trans ((addConvolution_mono hA' hB' x).trans (hr x))
  have h₁ := mul_card_add_mul_card_add_card_le ht hCD hC hD hr
    fun x hx ↦ (addConvolution_le_of_notMem_add hx).trans hL
  have h₂ := card_sdiff_mul_le_card_filter hA' hB' hA'ne hB'ne hdef hsatA hsatB D
  rw [← card_sdiff_add_card_eq_card hA', ← card_sdiff_add_card_eq_card hB']
  zify at h₁
  push_cast at h₂ ⊢
  linarith [mul_le_mul_of_nonneg_left (card_add_sub_card_addStab_add_holes_le A' B' hA'ne hB'ne)
    (by positivity : (0 : ℤ) ≤ t)]

/-! ### Step 1 -/

/-- `A' ⊆ A` and `B' ⊆ B` witness `SubsetSumsetEq t A B`, the sumset `A' + B'` is deficient, and
`A'` and `B'` contain every element of `A` and `B` in their cosets of the stabilizer of
`A' + B'`. -/
def SaturatedWitness (t : ℕ) (A B A' B' : Finset G) : Prop :=
  A' ⊆ A ∧ B' ⊆ B ∧ #(A \ A') + #(B \ B') ≤ t - 1 ∧ representableSums t A' B' = A' + B' ∧
    A' + B' = representableSums t A B ∧
    (∀ a ∈ A, a ∈ A' + (A' + B').addStab → a ∈ A') ∧
    (∀ b ∈ B, b ∈ B' + (A' + B').addStab → b ∈ B') ∧ #(A' + B') < #A' + #B'

omit [AddCommGroup G] in
lemma nonempty_of_card_sdiff_le (ht : 1 ≤ t) (hA' : A' ⊆ A) (hl : #(A \ A') ≤ t - 1)
    (hA : t ≤ #A) : A'.Nonempty := by
  rw [← card_pos]
  grind [card_sdiff_add_card_eq_card hA']

/-- If `A' ⊆ A` and `B' ⊆ B` miss at most `t - 1` elements, $A' + B' = A +_t B$ and
$\sum_{i=1}^t |A +_i B| < t|A| + t|B| - t^2$, then `A' + B'` is deficient. -/
lemma card_add_lt_of_add_eq_representableSums (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    (hl : #(A \ A') + #(B \ B') ≤ t - 1) (heq : A' + B' = representableSums t A B)
    (hS : sumCardRepresentableSums t A B + t ^ 2 < t * #A + t * #B) :
    #(A' + B') < #A' + #B' := by
  by_contra! hdef
  have h := mul_card_representableSums_le t A B
  rw [← heq] at h
  rw [← card_sdiff_add_card_eq_card hA', ← card_sdiff_add_card_eq_card hB'] at hS
  nlinarith [Nat.mul_le_mul_left t hdef, Nat.mul_le_mul_left t hl,
    Nat.mul_le_mul_left t (Nat.sub_le t 1)]

/-- The elements of `A` and `B` in the cosets of the stabilizer of `A₀ + B₀` meeting `A₀` and `B₀`
have sumset `A₀ + B₀`. -/
lemma inter_add_addStab_add_inter_add_addStab (hA₀ : A₀ ⊆ A) (hB₀ : B₀ ⊆ B)
    (hne : (A₀ + B₀).Nonempty) :
    A ∩ (A₀ + (A₀ + B₀).addStab) + B ∩ (B₀ + (A₀ + B₀).addStab) = A₀ + B₀ := by
  refine subset_antisymm ((add_subset_add inter_subset_right inter_subset_right).trans ?_)
    (add_subset_add (subset_inter hA₀ (subset_add_addStab hne A₀))
      (subset_inter hB₀ (subset_add_addStab hne B₀)))
  rw [add_add_add_comm, addStab_add_addStab, add_addStab]

/-- Enlarging a witness `A₀, B₀` of `SubsetSumsetEq t A B` by the elements of `A` and `B` in its
cosets of the stabilizer of `A₀ + B₀` gives a saturated witness, provided
$\sum_{i=1}^t |A +_i B| < t|A| + t|B| - t^2$. -/
lemma saturatedWitness_inter_add_addStab (hA₀ : A₀ ⊆ A) (hB₀ : B₀ ⊆ B)
    (hne : (A₀ + B₀).Nonempty) (hl : #(A \ A₀) + #(B \ B₀) ≤ t - 1)
    (hrep : representableSums t A₀ B₀ = A₀ + B₀) (heq : A₀ + B₀ = representableSums t A B)
    (hS : sumCardRepresentableSums t A B + t ^ 2 < t * #A + t * #B) :
    SaturatedWitness t A B (A ∩ (A₀ + (A₀ + B₀).addStab)) (B ∩ (B₀ + (A₀ + B₀).addStab)) := by
  have hA₀A := subset_inter hA₀ (subset_add_addStab hne A₀)
  have hB₀B := subset_inter hB₀ (subset_add_addStab hne B₀)
  have hsum := inter_add_addStab_add_inter_add_addStab hA₀ hB₀ hne
  have hl' : #(A \ (A ∩ (A₀ + (A₀ + B₀).addStab))) + #(B \ (B ∩ (B₀ + (A₀ + B₀).addStab))) ≤
      t - 1 :=
    (add_le_add (card_le_card (sdiff_subset_sdiff subset_rfl hA₀A))
      (card_le_card (sdiff_subset_sdiff subset_rfl hB₀B))).trans hl
  refine ⟨inter_subset_left, inter_subset_left, hl', ?_, by rw [hsum, heq], ?_, ?_,
    card_add_lt_of_add_eq_representableSums inter_subset_left inter_subset_left hl'
      (by rw [hsum, heq]) hS⟩
  · refine subset_antisymm representableSums_subset_add ?_
    rw [hsum]
    exact hrep.symm.subset.trans (representableSums_mono hA₀A hB₀B)
  · intro a ha ha'
    rw [hsum] at ha'
    refine mem_inter.2 ⟨ha, ?_⟩
    rw [← add_addStab_add_addStab]
    exact add_subset_add_right inter_subset_right ha'
  · intro b hb hb'
    rw [hsum] at hb'
    refine mem_inter.2 ⟨hb, ?_⟩
    rw [← add_addStab_add_addStab]
    exact add_subset_add_right inter_subset_right hb'

/-- The subsets of a saturated witness are nonempty. -/
lemma SaturatedWitness.nonempty (ht : 1 ≤ t) (hA : t ≤ #A) (hB : t ≤ #B)
    (h : SaturatedWitness t A B A' B') : A'.Nonempty ∧ B'.Nonempty := by
  obtain ⟨hA', hB', hl, -⟩ := h
  exact ⟨nonempty_of_card_sdiff_le ht hA' (le_self_add.trans hl) hA,
    nonempty_of_card_sdiff_le ht hB' (le_add_self.trans hl) hB⟩

/-- The bound (9a) of Step 1:
$t|A| + t|B| \le \sum_{i=1}^t |A +_i B| + tl + (t - l)(|H| - \rho)$. -/
lemma SaturatedWitness.mul_card_add_mul_card_le (ht : 1 ≤ t) (hA : t ≤ #A) (hB : t ≤ #B)
    (h : SaturatedWitness t A B A' B') :
    (t * #A + t * #B : ℤ) ≤ sumCardRepresentableSums t A B + t * (#(A \ A') + #(B \ B')) +
      (t - (#(A \ A') + #(B \ B'))) *
        (#(A' + B').addStab - (holes (A' + B').addStab A' + holes (A' + B').addStab B')) := by
  obtain ⟨hA'ne, hB'ne⟩ := h.nonempty ht hA hB
  obtain ⟨hA', hB', hl, hrep, -, hsatA, hsatB, hdef⟩ := h
  simpa using mul_card_add_mul_card_add_mul_card_le (D := ∅) ht hA' hB' hA'ne hB'ne (by grind)
    hrep hdef hsatA hsatB (fun _ ↦ le_rfl) (empty_subset _) (disjoint_empty_right _)

/-- The bound (9a) and $\sum_{i=1}^t |A +_i B| < t|A| + t|B| - t^2$ give $|H| - \rho \ge t + 1$. -/
lemma SaturatedWitness.add_one_le_card_addStab_sub_holes (ht : 1 ≤ t) (hA : t ≤ #A)
    (hB : t ≤ #B) (h : SaturatedWitness t A B A' B')
    (hS : sumCardRepresentableSums t A B + t ^ 2 < t * #A + t * #B) :
    (t + 1 : ℤ) ≤
      #(A' + B').addStab - (holes (A' + B').addStab A' + holes (A' + B').addStab B') := by
  have h₁ := h.mul_card_add_mul_card_le ht hA hB
  obtain ⟨-, -, hl, -⟩ := h
  have hL : (#(A \ A') + #(B \ B') : ℤ) ≤ t := by exact_mod_cast hl.trans (Nat.sub_le t 1)
  zify at hS
  nlinarith

/-- **Step 1.** If `SubsetSumsetEq t A B` holds and
$\sum_{i=1}^t |A +_i B| < t|A| + t|B| - t^2$, then there is a saturated witness with
$|H| - \rho \ge t + 1$. -/
lemma SubsetSumsetEq.exists_saturatedWitness (ht : 1 ≤ t) (hA : t ≤ #A) (hB : t ≤ #B)
    (h : SubsetSumsetEq t A B) (hS : sumCardRepresentableSums t A B + t ^ 2 < t * #A + t * #B) :
    ∃ A' B', SaturatedWitness t A B A' B' ∧ (t + 1 : ℤ) ≤
      #(A' + B').addStab - (holes (A' + B').addStab A' + holes (A' + B').addStab B') := by
  obtain ⟨A₀, hA₀, B₀, hB₀, hl, hrep, heq⟩ := h
  have hW := saturatedWitness_inter_add_addStab hA₀ hB₀
    ((nonempty_of_card_sdiff_le ht hA₀ (le_self_add.trans hl) hA).add
      (nonempty_of_card_sdiff_le ht hB₀ (le_add_self.trans hl) hB)) hl hrep heq hS
  exact ⟨_, _, hW, hW.add_one_le_card_addStab_sub_holes ht hA hB hS⟩

/-- A saturated witness with $|H| - \rho \ge t + 1$ either has $A +_t B = A + B$, or gives an
element of `A` or `B` with at least `t + 1` sums having fewer than `t` representations. -/
lemma SaturatedWitness.eq_add_or_exists (ht : 1 ≤ t) (hA : t ≤ #A) (hB : t ≤ #B)
    (h : SaturatedWitness t A B A' B')
    (hX : (t + 1 : ℤ) ≤
      #(A' + B').addStab - (holes (A' + B').addStab A' + holes (A' + B').addStab B')) :
    representableSums t A B = A + B ∨
      (∃ a ∈ A, t + 1 ≤ #{b ∈ B | A.addConvolution B (a + b) < t}) ∨
      ∃ b ∈ B, t + 1 ≤ #{a ∈ A | A.addConvolution B (a + b) < t} := by
  obtain ⟨hA'ne, hB'ne⟩ := h.nonempty ht hA hB
  obtain ⟨hA', hB', -, -, heq, hsatA, hsatB, hdef⟩ := h
  have hlt : ∀ a ∈ A, ∀ b ∈ B, a + b ∉ A' + B' → A.addConvolution B (a + b) < t := by
    intro a ha b hb hab
    rw [heq, mem_representableSums] at hab
    grind [add_mem_add ha hb]
  rcases (A \ A').eq_empty_or_nonempty with hAe | ⟨a, ha⟩
  · rcases (B \ B').eq_empty_or_nonempty with hBe | ⟨b, hb⟩
    · left
      rw [← heq, subset_antisymm hA' (sdiff_eq_empty_iff_subset.1 hAe),
        subset_antisymm hB' (sdiff_eq_empty_iff_subset.1 hBe)]
    · right; right
      obtain ⟨hbB, hbB'⟩ := mem_sdiff.1 hb
      refine ⟨b, hbB, ?_⟩
      have := card_addStab_sub_holes_sub_card_le_right hA'ne hB'ne hdef
        (fun h ↦ hbB' (hsatB b hbB h)) ∅
      have hsub : {a ∈ A' | a + b ∉ A' + B'} ⊆ {a ∈ A | A.addConvolution B (a + b) < t} := by
        intro a ha
        rw [mem_filter] at ha ⊢
        obtain ⟨ha, hab⟩ := ha
        exact ⟨hA' ha, hlt a (hA' ha) b hbB hab⟩
      simp only [union_empty, card_empty, Nat.cast_zero, sub_zero] at this
      grind [card_le_card hsub]
  · right; left
    obtain ⟨haA, haA'⟩ := mem_sdiff.1 ha
    refine ⟨a, haA, ?_⟩
    have := card_addStab_sub_holes_sub_card_le_left hA'ne hB'ne hdef
      (fun h ↦ haA' (hsatA a haA h)) ∅
    have hsub : {b ∈ B' | a + b ∉ A' + B'} ⊆ {b ∈ B | A.addConvolution B (a + b) < t} := by
      intro b hb
      rw [mem_filter] at hb ⊢
      obtain ⟨hb, hab⟩ := hb
      exact ⟨hB' hb, hlt a haA b (hB' hb) hab⟩
    simp only [union_empty, card_empty, Nat.cast_zero, sub_zero] at this
    grind [card_le_card hsub]

end ExtendingPollard
