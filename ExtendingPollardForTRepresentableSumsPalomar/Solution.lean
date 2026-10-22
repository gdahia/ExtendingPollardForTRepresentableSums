/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib
public import ExtendingPollardForTRepresentableSums

/-!
# Pollard's theorem for $t$-representable sums

The statements of `Challenge.lean`, which are the results of the library with the same names
without the prime.
-/

public section

open Finset
open scoped Pointwise

namespace ExtendingPollard

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem mul_card_add_mul_card_le_or_exists_add_eq_representableSums' {t : ℕ} (ht : 1 ≤ t)
    (A B : Finset G) (hA : t ≤ #A) (hB : t ≤ #B) {H : AddSubgroup G}
    (hH : AddAction.stabilizer G (representableSums t A B : Set G) = H) :
    t * #A + t * #B ≤ ∑ i ∈ Icc 1 t, #(representableSums i A B) + (2 * t ^ 2 - 1) ∨
      ∃ A' ⊆ A, ∃ B' ⊆ B, #(A \ A') + #(B \ B') ≤ t - 1 ∧
        representableSums t A' B' = A' + B' ∧ A' + B' = representableSums t A B ∧ H ≠ ⊥ ∧
        (t * #A + t * #B : ℤ) ≤ ((∑ i ∈ Icc 1 t, #(representableSums i A B) : ℕ) : ℤ) +
          (t - (#(A \ A') + #(B \ B'))) * (Nat.card H - (numHoles H A' + numHoles H B')) +
          t * (#(A \ A') + #(B \ B')) ∧
        t * #A + t * #B ≤ ∑ i ∈ Icc 1 t, #(representableSums i A B) + t * Nat.card H :=
  mul_card_add_mul_card_le_or_exists_add_eq_representableSums ht A B hA hB hH

theorem mul_card_add_mul_card_le_or_exists_add_eq_representableSums_two' (A B : Finset G)
    (hA : 2 ≤ #A) (hB : 2 ≤ #B) {H : AddSubgroup G}
    (hH : AddAction.stabilizer G (representableSums 2 A B : Set G) = H) :
    2 * #A + 2 * #B ≤ #(A + B) + #(representableSums 2 A B) + 4 ∨
      ∃ A' ⊆ A, ∃ B' ⊆ B, #(A \ A') + #(B \ B') ≤ 1 ∧
        representableSums 2 A' B' = A' + B' ∧ A' + B' = representableSums 2 A B ∧ H ≠ ⊥ ∧
        (2 * #A + 2 * #B : ℤ) ≤ #(A + B) + #(representableSums 2 A B) +
          (2 - (#(A \ A') + #(B \ B'))) * (Nat.card H - (numHoles H A' + numHoles H B')) +
          2 * (#(A \ A') + #(B \ B')) ∧
        2 * #A + 2 * #B ≤ #(A + B) + #(representableSums 2 A B) + 2 * Nat.card H :=
  mul_card_add_mul_card_le_or_exists_add_eq_representableSums_two A B hA hB hH

theorem mul_card_add_mul_card_le_or_exists_vadd_subset_representableSums_two' (A B : Finset G)
    (hA : 2 ≤ #A) (hB : 2 ≤ #B) :
    2 * #A + 2 * #B ≤ #(A + B) + #(representableSums 2 A B) + 4 ∨
      ∃ x : G, ∃ H : AddSubgroup G, 3 ≤ Nat.card H ∧
        x +ᵥ (H : Set G) ⊆ (representableSums 2 A B : Set G) :=
  mul_card_add_mul_card_le_or_exists_vadd_subset_representableSums_two A B hA hB

theorem mul_card_add_mul_card_le_or_exists_add_eq_representableSums_two_mul' {t : ℕ}
    (ht : 1 ≤ t) (A B : Finset G) (hA : t ≤ #A) (hB : t ≤ #B) {H : AddSubgroup G}
    (hH : AddAction.stabilizer G (representableSums t A B : Set G) = H) :
    t * #A + t * #B ≤ ∑ i ∈ Icc 1 t, #(representableSums i A B) + (2 * t ^ 2 - 1) ∨
      ∃ A' ⊆ A, ∃ B' ⊆ B, #(A \ A') + #(B \ B') ≤ t - 1 ∧
        representableSums (2 * t) A' B' = A' + B' ∧ A' + B' = representableSums (2 * t) A B ∧
        representableSums (2 * t) A B = representableSums t A B ∧
        2 * t + (numHoles H A' + numHoles H B') ≤ Nat.card H :=
  mul_card_add_mul_card_le_or_exists_add_eq_representableSums_two_mul ht A B hA hB hH

theorem mul_card_add_mul_card_le_or_exists_add_eq_representableSums_three' (A B : Finset G)
    (hA : 2 ≤ #A) (hB : 2 ≤ #B) {H : AddSubgroup G}
    (hH : AddAction.stabilizer G (representableSums 2 A B : Set G) = H) :
    2 * #A + 2 * #B ≤ #(A + B) + #(representableSums 2 A B) + 4 ∨
      ∃ A' ⊆ A, ∃ B' ⊆ B, #(A \ A') + #(B \ B') ≤ 1 ∧
        representableSums 3 A' B' = A' + B' ∧ A' + B' = representableSums 3 A B ∧
        representableSums 3 A B = representableSums 2 A B ∧
        3 + (numHoles H A' + numHoles H B') ≤ Nat.card H :=
  mul_card_add_mul_card_le_or_exists_add_eq_representableSums_three A B hA hB hH

theorem mul_min_le_sumCardRepresentableSums' {A B T : Finset G} {k t : ℕ} (hkB : k ≤ #B)
    (ht : 1 ≤ t) (hr : ∀ x ∉ T, A.addConvolution (-B) x ≤ k) :
    t * min ((#A * #B : ℝ) / (t + √(t * (t - 1))))
        ((#A ^ 2 * #B : ℝ) / (#T * (#B - k : ℝ) + k * #A)) ≤
      ((∑ i ∈ Icc 1 t, #(representableSums i A B) : ℕ) : ℝ) ∧
    min ((#A * #B : ℝ) / 2) (t * ((#A ^ 2 * #B : ℝ) / (#T * (#B - k : ℝ) + k * #A))) ≤
      t * min ((#A * #B : ℝ) / (t + √(t * (t - 1))))
        ((#A ^ 2 * #B : ℝ) / (#T * (#B - k : ℝ) + k * #A)) :=
  mul_min_le_sumCardRepresentableSums hkB ht hr

theorem card_add_lt_card_add_insert' {A B : Finset G} {b : G} (hA : A.Nonempty)
    (hB : B.Nonempty) (hAB : #(A + B) = #A + #B - 1)
    (hper : AddAction.stabilizer G ((A + B : Finset G) : Set G) = ⊥) (hb : b ∉ B) :
    #(A + B) < #(A + insert b B) :=
  card_add_lt_card_add_insert hA hB hAB hper hb

end ExtendingPollard
