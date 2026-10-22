/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.Additive.Convolution
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-!
# Representable sums

For finite subsets `A` and `B` of an abelian group, `A.addConvolution B x` is the number
$r_{A,B}(x)$ of representations of `x` as `a + b` with `a ∈ A` and `b ∈ B`, and
`representableSums i A B` is the set $A +_i B$ of the elements with at least `i` representations.

This file proves $\sum_{i=1}^t |A +_i B| = \sum_x \min(r_{A,B}(x), t)$ and the elementary
properties of this sum: monotonicity, the effect of adding or removing one element, and the
trivial bounds.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace ExtendingPollard

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The set $A +_i B$ of `i`-representable sums: the elements of `A + B` with at least `i`
representations as `a + b` with `a ∈ A` and `b ∈ B`. -/
def representableSums (i : ℕ) (A B : Finset G) : Finset G :=
  {x ∈ A + B | i ≤ A.addConvolution B x}

/-- The sum $\sum_{i=1}^t |A +_i B|$. -/
def sumCardRepresentableSums (t : ℕ) (A B : Finset G) : ℕ :=
  ∑ i ∈ Icc 1 t, #(representableSums i A B)

variable {A A' B B' U : Finset G} {i j t : ℕ} {x y : G}

/-! ### The representation function -/

lemma addConvolution_mono (hA : A ⊆ A') (hB : B ⊆ B') (x : G) :
    A.addConvolution B x ≤ A'.addConvolution B' x :=
  card_le_card (filter_subset_filter _ (product_subset_product hA hB))

lemma addConvolution_comm (A B : Finset G) (x : G) :
    A.addConvolution B x = B.addConvolution A x :=
  card_nbij' Prod.swap Prod.swap (by grind [Set.MapsTo, add_comm])
    (by grind [Set.MapsTo, add_comm]) (by simp [Set.LeftInvOn]) (by simp [Set.LeftInvOn])

lemma addConvolution_insert (hy : y ∉ B) (x : G) :
    A.addConvolution (insert y B) x = A.addConvolution B x + if x - y ∈ A then 1 else 0 := by
  have hsplit : {p ∈ A ×ˢ insert y B | p.1 + p.2 = x} =
      {p ∈ A ×ˢ B | p.1 + p.2 = x} ∪ ({a ∈ ({x - y} : Finset G) | a ∈ A} ×ˢ {y}) := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product, mem_insert, mem_union, mem_singleton]
    grind
  rw [Finset.addConvolution, Finset.addConvolution, hsplit, card_union_of_disjoint]
  · simp [filter_singleton, apply_ite card]
  · rw [disjoint_left]
    rintro ⟨a, b⟩ h₁ h₂
    simp only [mem_filter, mem_product, mem_singleton] at h₁ h₂
    grind

lemma addConvolution_le_of_forall (h : ∀ x ∈ A + B, A.addConvolution B x ≤ A'.addConvolution B' x)
    (x : G) : A.addConvolution B x ≤ A'.addConvolution B' x := by
  by_cases hx : x ∈ A + B
  · exact h x hx
  · simp [Finset.addConvolution_eq_zero.2 hx]

lemma sum_addConvolution (A B : Finset G) : ∑ x ∈ A + B, A.addConvolution B x = #A * #B := by
  rw [← card_product]
  refine (card_eq_sum_card_fiberwise (f := fun p : G × G ↦ p.1 + p.2) ?_).symm
  rintro ⟨a, b⟩ hp
  obtain ⟨ha, hb⟩ := mem_product.1 hp
  exact add_mem_add ha hb

/-! ### Representable sums -/

lemma mem_representableSums :
    x ∈ representableSums i A B ↔ x ∈ A + B ∧ i ≤ A.addConvolution B x :=
  mem_filter

lemma mem_representableSums' :
    x ∈ representableSums i A B ↔ 0 < A.addConvolution B x ∧ i ≤ A.addConvolution B x := by
  rw [mem_representableSums, Finset.addConvolution_pos]

lemma mem_representableSums_of_one_le (hi : 1 ≤ i) :
    x ∈ representableSums i A B ↔ i ≤ A.addConvolution B x := by
  rw [mem_representableSums, ← Finset.addConvolution_pos]
  grind

lemma representableSums_subset_add : representableSums i A B ⊆ A + B :=
  filter_subset _ _

lemma representableSums_one : representableSums 1 A B = A + B := by
  ext x
  rw [mem_representableSums_of_one_le le_rfl, Nat.one_le_iff_ne_zero,
    Finset.addConvolution_ne_zero]

lemma representableSums_anti (h : i ≤ j) : representableSums j A B ⊆ representableSums i A B :=
  monotone_filter_right _ fun _ _ hx ↦ h.trans hx

lemma representableSums_mono (hA : A ⊆ A') (hB : B ⊆ B') :
    representableSums i A B ⊆ representableSums i A' B' := by
  intro x hx
  rw [mem_representableSums] at hx ⊢
  obtain ⟨hx, hi⟩ := hx
  exact ⟨add_subset_add hA hB hx, hi.trans (addConvolution_mono hA hB x)⟩

lemma representableSums_comm : representableSums i A B = representableSums i B A := by
  ext x
  simp [mem_representableSums, add_comm A B, addConvolution_comm A B]

/-! ### The sum of the sizes of the representable sums -/

lemma sum_ite_le_eq_min (r t : ℕ) : ∑ i ∈ Icc 1 t, (if i ≤ r then 1 else 0) = min r t := by
  have : {i ∈ Icc 1 t | i ≤ r} = Icc 1 (min r t) := by
    ext
    simp only [mem_filter, mem_Icc, le_min_iff]
    grind
  rw [sum_boole, Nat.cast_id, this, Nat.card_Icc, Nat.add_sub_cancel]

lemma sumCardRepresentableSums_eq_sum_min (t : ℕ) (A B : Finset G) :
    sumCardRepresentableSums t A B = ∑ x ∈ A + B, min (A.addConvolution B x) t := by
  simp_rw [sumCardRepresentableSums, representableSums, card_filter]
  rw [sum_comm]
  congr with x
  exact sum_ite_le_eq_min _ _

lemma sum_min_addConvolution_of_subset (h : A + B ⊆ U) :
    ∑ x ∈ U, min (A.addConvolution B x) t = ∑ x ∈ A + B, min (A.addConvolution B x) t := by
  refine (sum_subset h ?_).symm
  intro x _ hx
  simp [Finset.addConvolution_eq_zero.2 hx]

lemma sumCardRepresentableSums_eq_sum_min_of_subset (h : A + B ⊆ U) :
    sumCardRepresentableSums t A B = ∑ x ∈ U, min (A.addConvolution B x) t := by
  rw [sumCardRepresentableSums_eq_sum_min, sum_min_addConvolution_of_subset h]

lemma sumCardRepresentableSums_comm (t : ℕ) (A B : Finset G) :
    sumCardRepresentableSums t A B = sumCardRepresentableSums t B A := by
  simp [sumCardRepresentableSums, representableSums_comm (A := A)]

lemma sumCardRepresentableSums_le_of_forall
    (h : ∀ x ∈ A + B, A.addConvolution B x ≤ A'.addConvolution B' x) :
    sumCardRepresentableSums t A B ≤ sumCardRepresentableSums t A' B' := by
  have hsub : A + B ⊆ A' + B' := by
    intro x hx
    rw [← Finset.addConvolution_pos] at hx ⊢
    exact hx.trans_le (h x (Finset.addConvolution_pos.1 hx))
  rw [sumCardRepresentableSums_eq_sum_min, sumCardRepresentableSums_eq_sum_min]
  refine (sum_le_sum_of_subset hsub).trans' ?_
  gcongr with x hx
  exact h x hx

lemma sumCardRepresentableSums_mono (hA : A ⊆ A') (hB : B ⊆ B') :
    sumCardRepresentableSums t A B ≤ sumCardRepresentableSums t A' B' :=
  sumCardRepresentableSums_le_of_forall fun x _ ↦ addConvolution_mono hA hB x

lemma sumCardRepresentableSums_one (A B : Finset G) :
    sumCardRepresentableSums 1 A B = #(A + B) := by
  simp [sumCardRepresentableSums, representableSums_one]

lemma sumCardRepresentableSums_two (A B : Finset G) :
    sumCardRepresentableSums 2 A B = #(A + B) + #(representableSums 2 A B) := by
  rw [← representableSums_one]
  rfl

/-- Two parts `P` and `Q` of `A` with disjoint sumsets with `B` contribute separately. -/
lemma sumCardRepresentableSums_add_le {P Q : Finset G} (hP : P ⊆ A) (hQ : Q ⊆ A)
    (h : Disjoint (P + B) (Q + B)) :
    sumCardRepresentableSums t P B + sumCardRepresentableSums t Q B ≤
      sumCardRepresentableSums t A B := by
  rw [sumCardRepresentableSums_eq_sum_min, sumCardRepresentableSums_eq_sum_min,
    sumCardRepresentableSums_eq_sum_min]
  refine le_trans ?_ ((sum_union h).symm.le.trans (sum_le_sum_of_subset
    (union_subset (add_subset_add_right hP) (add_subset_add_right hQ))))
  gcongr with x _ x _
  · exact addConvolution_mono hP subset_rfl x
  · exact addConvolution_mono hQ subset_rfl x

/-- The bound $\sum_{i=1}^t |A +_i B| \ge t |A +_t B|$. -/
lemma mul_card_representableSums_le (t : ℕ) (A B : Finset G) :
    t * #(representableSums t A B) ≤ sumCardRepresentableSums t A B := by
  refine le_of_eq_of_le ?_
    (card_nsmul_le_sum (Icc 1 t) (fun i ↦ #(representableSums i A B))
      #(representableSums t A B) ?_)
  · simp
  · intro i hi
    obtain ⟨-, hit⟩ := mem_Icc.1 hi
    exact card_le_card (representableSums_anti hit)

/-- When every element has at most `t` representations, the sum is `|A| |B|`. -/
lemma sumCardRepresentableSums_eq_card_mul_card (hB : #B ≤ t) :
    sumCardRepresentableSums t A B = #A * #B := by
  rw [sumCardRepresentableSums_eq_sum_min, ← sum_addConvolution]
  congr with x
  exact min_eq_left ((Finset.addConvolution_le_card_right).trans hB)

/-- The trivial bound $\sum_{i=1}^t |A +_i B| \ge t |A|$ for $|B| \ge t$. -/
lemma mul_card_le_sumCardRepresentableSums (htB : t ≤ #B) :
    t * #A ≤ sumCardRepresentableSums t A B := by
  obtain ⟨B₀, hB₀B, hB₀⟩ := exists_subset_card_eq htB
  have := sumCardRepresentableSums_mono (t := t) (subset_refl A) hB₀B
  rwa [sumCardRepresentableSums_eq_card_mul_card hB₀.le, hB₀, mul_comm] at this

/-- An element with `|B|` representations lies in every translate `b + A` with `b ∈ B`. -/
lemma mem_vadd_finset_of_addConvolution_eq_card {b : G} (hx : A.addConvolution B x = #B)
    (hb : b ∈ B) : x ∈ b +ᵥ A := by
  have himage : {p ∈ A ×ˢ B | p.1 + p.2 = x}.image Prod.snd = B := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro c hc
      obtain ⟨⟨a, c⟩, hp, rfl⟩ := mem_image.1 hc
      simp only [mem_filter, mem_product] at hp
      obtain ⟨⟨-, hc⟩, -⟩ := hp
      exact hc
    · rw [card_image_of_injOn, ← hx, Finset.addConvolution]
      intro p hp q hq hpq
      grind
  obtain ⟨⟨a, b⟩, hp, rfl⟩ := mem_image.1 (himage ▸ hb)
  simp only [mem_filter, mem_product] at hp
  obtain ⟨⟨ha, -⟩, rfl⟩ := hp
  exact mem_vadd_finset.2 ⟨a, ha, add_comm _ _⟩

/-- The trivial bound is strict when two translates `b + A` and `b' + A` with `b, b' ∈ B` differ
and $|B| > t$. -/
lemma mul_card_lt_sumCardRepresentableSums {b b' : G} (ht : 1 ≤ t) (htB : t + 1 ≤ #B)
    (hb : b ∈ B) (hb' : b' ∈ B) (hne : b +ᵥ A ≠ b' +ᵥ A) :
    t * #A < sumCardRepresentableSums t A B := by
  obtain ⟨B₀, hpair, hB₀B, hB₀⟩ :=
    exists_subsuperset_card_eq (insert_subset hb (singleton_subset_iff.2 hb'))
      ((card_insert_le _ _).trans (by simpa)) htB
  refine lt_of_lt_of_le ?_ (sumCardRepresentableSums_mono (subset_refl A) hB₀B)
  have hfull : {x ∈ A + B₀ | A.addConvolution B₀ x = t + 1} ⊆ (b +ᵥ A) ∩ (b' +ᵥ A) := by
    intro x hx
    rw [mem_filter, ← hB₀] at hx
    obtain ⟨-, hx⟩ := hx
    exact mem_inter.2 ⟨mem_vadd_finset_of_addConvolution_eq_card hx (hpair (mem_insert_self _ _)),
      mem_vadd_finset_of_addConvolution_eq_card hx
        (hpair (mem_insert_of_mem (mem_singleton_self _)))⟩
  have hinter : #((b +ᵥ A) ∩ (b' +ᵥ A)) < #A := by
    rw [← card_vadd_finset b A]
    refine card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_left, ?_⟩)
    intro h
    exact hne (eq_of_subset_of_card_le (inter_eq_left.1 h) (by simp))
  have hsum : sumCardRepresentableSums t A B₀ + #{x ∈ A + B₀ | A.addConvolution B₀ x = t + 1} =
      (t + 1) * #A := by
    rw [sumCardRepresentableSums_eq_sum_min, card_filter, ← sum_add_distrib, ← hB₀, mul_comm,
      ← sum_addConvolution]
    congr with x
    grind [(Finset.addConvolution_le_card_right : A.addConvolution B₀ x ≤ #B₀)]
  grind [card_le_card hfull]

/-- Adding `y` to `B` increases the sum by the number of `a ∈ A` for which `a + y` has at most `t`
representations in the new sumset. -/
lemma sumCardRepresentableSums_insert (hy : y ∉ B) :
    sumCardRepresentableSums t A (insert y B) = sumCardRepresentableSums t A B +
      #{a ∈ A | A.addConvolution (insert y B) (a + y) ≤ t} := by
  have hcard : #{a ∈ A | A.addConvolution (insert y B) (a + y) ≤ t} =
      #{x ∈ A + insert y B | x - y ∈ A ∧ A.addConvolution (insert y B) x ≤ t} := by
    refine card_nbij' (· + y) (· - y) ?_ ?_ (by simp [Set.LeftInvOn]) (by simp [Set.LeftInvOn])
    · intro a ha
      simp only [coe_filter, Set.mem_ofPred_eq] at ha ⊢
      obtain ⟨ha, hr⟩ := ha
      exact ⟨add_mem_add ha (mem_insert_self _ _), by simpa using ha, hr⟩
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx ⊢
      obtain ⟨-, hx, hr⟩ := hx
      exact ⟨hx, by simpa using hr⟩
  rw [hcard, sumCardRepresentableSums_eq_sum_min,
    sumCardRepresentableSums_eq_sum_min_of_subset (add_subset_add_left (subset_insert y B)),
    card_filter, ← sum_add_distrib]
  congr with x
  rw [addConvolution_insert hy]
  grind

/-- Removing `y` from `B` decreases the sum by the number of `a ∈ A` for which `a + y` has at most
`t` representations in `A + B`. -/
lemma sumCardRepresentableSums_erase (hy : y ∈ B) :
    sumCardRepresentableSums t A B = sumCardRepresentableSums t A (B.erase y) +
      #{a ∈ A | A.addConvolution B (a + y) ≤ t} := by
  simpa [insert_erase hy] using sumCardRepresentableSums_insert (A := A) (t := t)
    (notMem_erase y B)

/-! ### Translation -/

lemma addConvolution_vadd_right (A B : Finset G) (y x : G) :
    A.addConvolution (y +ᵥ B) x = A.addConvolution B (x - y) := by
  refine card_nbij' (fun (a, b) ↦ (a, b - y)) (fun (a, b) ↦ (a, b + y)) ?_ ?_ ?_ ?_
  · rintro ⟨a, c⟩ hp
    simp only [coe_filter, mem_product, Set.mem_ofPred_eq, mem_vadd_finset, vadd_eq_add] at hp ⊢
    obtain ⟨⟨ha, b, hb, rfl⟩, rfl⟩ := hp
    refine ⟨⟨ha, by simpa⟩, by abel⟩
  · rintro ⟨a, b⟩ hp
    simp only [coe_filter, mem_product, Set.mem_ofPred_eq, mem_vadd_finset, vadd_eq_add] at hp ⊢
    obtain ⟨⟨ha, hb⟩, hab⟩ := hp
    exact ⟨⟨ha, b, hb, add_comm _ _⟩, by rw [← add_assoc, hab, sub_add_cancel]⟩
  · simp [Set.LeftInvOn]
  · simp [Set.LeftInvOn]

lemma representableSums_vadd_right (i : ℕ) (A B : Finset G) (y : G) :
    representableSums i A (y +ᵥ B) = y +ᵥ representableSums i A B := by
  ext x
  rw [← neg_vadd_mem_iff, mem_representableSums', mem_representableSums',
    addConvolution_vadd_right, vadd_eq_add, neg_add_eq_sub]

lemma sumCardRepresentableSums_vadd_right (t : ℕ) (A B : Finset G) (y : G) :
    sumCardRepresentableSums t A (y +ᵥ B) = sumCardRepresentableSums t A B := by
  simp [sumCardRepresentableSums, representableSums_vadd_right, card_vadd_finset]

end ExtendingPollard
