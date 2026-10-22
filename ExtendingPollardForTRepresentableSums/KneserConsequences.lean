/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ExtendingPollardForTRepresentableSums.Kneser.MulStab
public import Mathlib.Combinatorics.Additive.Convolution
import ExtendingPollardForTRepresentableSums.Kneser.Kneser
import Mathlib.Tactic.NormNum.Pow

/-!
# Consequences of Kneser's theorem

Let `H` be the stabilizer `(A + B).addStab` of a sumset. An element of `(A + H) \ A` is an
`H`-hole of `A`, so `#(A + H) - #A` is the number of `H`-holes of `A`.

This file proves the consequences of Kneser's theorem that the proof of the main theorem uses:

* `le_addConvolution_of_card_add_le`: Proposition E(i) of the paper. If
  $|A + B| \le |A| + |B| - k$, every element of `A + B` has at least `k` representations.
* `add_eq_univ_of_card_lt_card_add_card`: Proposition E(ii), the pigeonhole principle.
* `card_add_lt_card_add_insert`: Lemma 2.2 of the paper.
* `card_addStab_add_card_le_card_filter_add_notMem`: in the deficient case of Kneser's theorem,
  each element `a` outside `A + H` has at least `|H|` minus the number of `H`-holes of `B`
  partners `b ∈ B` with `a + b ∉ A + B`.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace ExtendingPollard

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {A B C H : Finset G} {a b x : G}

/-! ### The stabilizer of a finset -/

lemma neg_mem_addStab (hC : C.Nonempty) (ha : a ∈ C.addStab) : -a ∈ C.addStab := by
  rw [← mem_coe, coe_addStab hC] at ha ⊢
  exact neg_mem ha

lemma add_mem_addStab (hC : C.Nonempty) (ha : a ∈ C.addStab) (hb : b ∈ C.addStab) :
    a + b ∈ C.addStab := by
  rw [← mem_coe, coe_addStab hC] at ha hb ⊢
  exact add_mem ha hb

lemma sub_mem_addStab (hC : C.Nonempty) (ha : a ∈ C.addStab) (hb : b ∈ C.addStab) :
    a - b ∈ C.addStab := by
  rw [sub_eq_add_neg]
  exact add_mem_addStab hC ha (neg_mem_addStab hC hb)

lemma add_mem_of_mem_addStab (hx : x ∈ C) (ha : a ∈ C.addStab) : x + a ∈ C := by
  rw [← add_addStab C]
  exact add_mem_add hx ha

lemma subset_add_addStab (hC : C.Nonempty) (A : Finset G) : A ⊆ A + C.addStab := by
  intro a ha
  simpa using add_mem_add ha hC.zero_mem_addStab

lemma add_addStab_add_addStab (A C : Finset G) :
    A + C.addStab + C.addStab = A + C.addStab := by
  rw [add_assoc, addStab_add_addStab]

/-- An element of `C` translated by an element of the stabilizer of `C` stays in `C`, also
backwards. -/
lemma add_mem_iff_of_mem_addStab (hC : C.Nonempty) (ha : a ∈ C.addStab) : x + a ∈ C ↔ x ∈ C :=
  ⟨fun h ↦ by simpa using add_mem_of_mem_addStab h (neg_mem_addStab hC ha),
    fun h ↦ add_mem_of_mem_addStab h ha⟩

lemma vadd_finset_addStab_subset_add (ha : a ∈ A) :
    a +ᵥ C.addStab ⊆ A + C.addStab := by
  intro x hx
  obtain ⟨h, hh, rfl⟩ := mem_vadd_finset.1 hx
  exact add_mem_add ha hh

/-! ### Holes -/

/-- A translate `a + H` with `a ∈ A` contains at most as many `H`-holes as `A` has. -/
lemma card_add_card_inter_vadd_le (hC : C.Nonempty) (ha : a ∈ A) :
    #C.addStab + #A ≤ #(A ∩ (a +ᵥ C.addStab)) + #(A + C.addStab) := by
  have h := card_le_card (sdiff_subset_sdiff (vadd_finset_addStab_subset_add (C := C) ha)
    (subset_refl A))
  rw [card_sdiff_of_subset (subset_add_addStab hC A), card_sdiff, card_vadd_finset,
    inter_comm] at h
  grind [card_le_card (inter_subset_right (s₁ := A) (s₂ := a +ᵥ C.addStab)),
    card_vadd_finset a C.addStab, card_le_card (subset_add_addStab hC A)]

/-- The elements of a translate `a + H` in `A` correspond to the `h ∈ H` with `a + h ∈ A`. -/
lemma card_inter_vadd_eq_card_filter (A H : Finset G) (a : G) :
    #(A ∩ (a +ᵥ H)) = #{h ∈ H | a + h ∈ A} := by
  refine card_nbij' (· - a) (a + ·) ?_ ?_ (by simp [Set.LeftInvOn]) (by simp [Set.LeftInvOn])
  · intro x hx
    obtain ⟨hxA, hxH⟩ := mem_inter.1 hx
    obtain ⟨h, hh, rfl⟩ := mem_vadd_finset.1 hxH
    simpa [hh] using hxA
  · intro h hh
    simp only [coe_filter, Set.mem_ofPred_eq] at hh
    obtain ⟨hh, hA⟩ := hh
    simp only [coe_inter, Set.mem_inter_iff, mem_coe]
    exact ⟨hA, vadd_mem_vadd_finset hh⟩

/-- The elements of a coset `b + H` of the stabilizer in `B` correspond to the `h ∈ H` with
`b - h ∈ B`. -/
lemma card_inter_vadd_addStab_eq_card_filter_sub (hC : C.Nonempty) (B : Finset G) (b : G) :
    #(B ∩ (b +ᵥ C.addStab)) = #{h ∈ C.addStab | b - h ∈ B} := by
  refine card_nbij' (b - ·) (b - ·) ?_ ?_ (by simp [Set.LeftInvOn]) (by simp [Set.LeftInvOn])
  · intro x hx
    obtain ⟨hxB, hxH⟩ := mem_inter.1 hx
    obtain ⟨h, hh, rfl⟩ := mem_vadd_finset.1 hxH
    simp only [coe_filter, Set.mem_ofPred_eq, vadd_eq_add, sub_add_cancel_left]
    exact ⟨neg_mem_addStab hC hh, by simpa using hxB⟩
  · intro h hh
    simp only [coe_filter, Set.mem_ofPred_eq] at hh
    obtain ⟨hh, hB⟩ := hh
    simp only [coe_inter, Set.mem_inter_iff, mem_coe]
    exact ⟨hB, mem_vadd_finset.2 ⟨-h, neg_mem_addStab hC hh, by simp [sub_eq_add_neg]⟩⟩

/-- An element `a + b` has at least `|A ∩ (a + H)| + |B ∩ (b + H)| - |H|` representations, where
`H` is the stabilizer of a nonempty finset. -/
lemma card_inter_add_card_inter_le (hC : C.Nonempty) (a b : G) :
    #(A ∩ (a +ᵥ C.addStab)) + #(B ∩ (b +ᵥ C.addStab)) ≤
      A.addConvolution B (a + b) + #C.addStab := by
  rw [card_inter_vadd_eq_card_filter, card_inter_vadd_addStab_eq_card_filter_sub hC]
  have hinter : #{h ∈ C.addStab | a + h ∈ A ∧ b - h ∈ B} ≤ A.addConvolution B (a + b) := by
    refine card_le_card_of_injOn (fun h ↦ (a + h, b - h)) ?_ ?_
    · intro h hh
      simp only [coe_filter, Set.mem_ofPred_eq] at hh
      obtain ⟨-, hA, hB⟩ := hh
      simp only [coe_filter, mem_product, Set.mem_ofPred_eq]
      exact ⟨⟨hA, hB⟩, by abel⟩
    · intro h _ h' _ hhh'
      simpa using congrArg Prod.fst hhh'
  have hunion := card_union_add_card_inter {h ∈ C.addStab | a + h ∈ A}
    {h ∈ C.addStab | b - h ∈ B}
  rw [← filter_or, ← filter_and] at hunion
  grind [card_le_card (filter_subset (fun h ↦ a + h ∈ A ∨ b - h ∈ B) C.addStab)]

/-- The number of representations of an element of `A + B` is at least `|H|` minus the number of
`H`-holes of `A` and `B`, where `H` is the stabilizer of `A + B`. -/
lemma card_addStab_add_le_addConvolution (hx : x ∈ A + B) :
    #(A + B).addStab + #A + #B ≤
      A.addConvolution B x + #(A + (A + B).addStab) + #(B + (A + B).addStab) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hx
  have hC : (A + B).Nonempty := ⟨_, hx⟩
  grind [card_inter_add_card_inter_le (A := A) (B := B) hC a b, card_add_card_inter_vadd_le hC ha,
    card_add_card_inter_vadd_le hC hb]

/-! ### Proposition E -/

/-- **Proposition E(i).** If $|A + B| \le |A| + |B| - k$, then every element of `A + B` has at
least `k` representations. -/
lemma le_addConvolution_of_card_add_le {k : ℕ} (hk : #(A + B) + k ≤ #A + #B) (hx : x ∈ A + B) :
    k ≤ A.addConvolution B x := by
  grind [card_addStab_add_le_addConvolution hx, add_kneser A B]

/-- **Proposition E(ii).** In a finite group, if $|A| + |B| > |G|$, then `A + B` is the whole
group. -/
lemma add_eq_univ_of_card_lt_card_add_card [Fintype G] (h : Fintype.card G < #A + #B) :
    A + B = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨y, hy⟩ := inter_nonempty_of_card_lt_card_add_card (subset_univ A)
    (subset_univ (x +ᵥ -B)) (by simpa [card_neg] using h)
  obtain ⟨hyA, hyB⟩ := mem_inter.1 hy
  obtain ⟨c, hc, rfl⟩ := mem_vadd_finset.1 hyB
  obtain ⟨d, hd, rfl⟩ := mem_neg.1 hc
  exact mem_add.2 ⟨_, hyA, d, hd, by simp⟩

/-! ### Lemma 2.2 -/

/-- **Lemma 2.2.** If $|A + B| = |A| + |B| - 1$ and `A + B` is aperiodic, then adding any new
element to `B` enlarges `A + B`. -/
theorem card_add_lt_card_add_insert (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : #(A + B) = #A + #B - 1) (hper : AddAction.stabilizer G ((A + B : Finset G) : Set G) = ⊥)
    (hb : b ∉ B) : #(A + B) < #(A + insert b B) := by
  replace hper : (A + B).addStab = {0} := by
    rw [← coe_inj, coe_addStab (hA.add hB), hper, AddSubgroup.coe_bot, coe_singleton]
  by_contra! h
  have heq : A + insert b B = A + B :=
    (eq_of_subset_of_card_le (add_subset_add_left (subset_insert b B)) h).symm
  have := add_kneser A (insert b B)
  rw [heq, hper, card_singleton, singleton_zero, add_zero, add_zero,
    card_insert_of_notMem hb] at this
  grind [hA.card_pos]

/-! ### The contribution of an element outside a deficient sumset -/

/-- If $|A + B| < |A| + |B|$ and `a ∉ A + H`, where `H` is the stabilizer of `A + B`, then
`a + b ∉ A + B` for some `b ∈ B`. -/
lemma exists_add_notMem_add (hA : A.Nonempty) (hB : B.Nonempty) (hAB : #(A + B) < #A + #B)
    (ha : a ∉ A + (A + B).addStab) : ∃ b ∈ B, a + b ∉ A + B := by
  by_contra! hsub
  set H := (A + B).addStab
  have hC : (A + B).Nonempty := hA.add hB
  have hdisj : Disjoint (A + H) (a +ᵥ H) := by
    rw [disjoint_right]
    intro x hx hxA
    obtain ⟨h, hh, rfl⟩ := mem_vadd_finset.1 hx
    apply ha
    have := add_mem_add hxA (neg_mem_addStab hC hh)
    rwa [add_addStab_add_addStab, vadd_eq_add, add_neg_cancel_right] at this
  have hsum : (A + H ∪ (a +ᵥ H)) + (B + H) = A + B := by
    refine subset_antisymm ?_ ?_
    · rw [union_add]
      refine union_subset ?_ ?_
      · rw [add_add_add_comm, addStab_add_addStab, add_addStab]
      · intro x hx
        obtain ⟨y, hy, z, hz, rfl⟩ := mem_add.1 hx
        obtain ⟨h, hh, rfl⟩ := mem_vadd_finset.1 hy
        obtain ⟨c, hc, h', hh', rfl⟩ := mem_add.1 hz
        rw [vadd_eq_add, (by abel : a + h + (c + h') = a + c + (h + h'))]
        exact add_mem_of_mem_addStab (hsub c hc) (add_mem_addStab hC hh hh')
    · exact add_subset_add (subset_union_left.trans' (subset_add_addStab hC A))
        (subset_add_addStab hC B)
  have hkneser := add_kneser (A + H ∪ (a +ᵥ H)) (B + H)
  rw [hsum] at hkneser
  grind [card_le_card (subset_add_addStab hC (A + H ∪ (a +ᵥ H))),
    card_le_card (subset_add_addStab hC (B + H)), card_union_of_disjoint hdisj,
    card_vadd_finset a H, card_le_card (subset_add_addStab hC A),
    card_le_card (subset_add_addStab hC B)]

/-- **The contribution of an element outside a deficient sumset.** If $|A + B| < |A| + |B|$ and
`a ∉ A + H`, where `H` is the stabilizer of `A + B`, then at least `|H|` minus the number of
`H`-holes of `B` elements `b ∈ B` have `a + b ∉ A + B`. -/
lemma card_addStab_add_card_le_card_filter_add_notMem (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : #(A + B) < #A + #B) (ha : a ∉ A + (A + B).addStab) :
    #(A + B).addStab + #B ≤ #{b ∈ B | a + b ∉ A + B} + #(B + (A + B).addStab) := by
  obtain ⟨b₀, hb₀, hab₀⟩ := exists_add_notMem_add hA hB hAB ha
  have hC : (A + B).Nonempty := hA.add hB
  have hsub : B ∩ (b₀ +ᵥ (A + B).addStab) ⊆ {b ∈ B | a + b ∉ A + B} := by
    intro b hb
    obtain ⟨hbB, hbH⟩ := mem_inter.1 hb
    obtain ⟨h, hh, rfl⟩ := mem_vadd_finset.1 hbH
    refine mem_filter.2 ⟨hbB, ?_⟩
    intro hmem
    apply hab₀
    rwa [vadd_eq_add, ← add_assoc, add_mem_iff_of_mem_addStab hC hh] at hmem
  grind [card_le_card hsub, card_add_card_inter_vadd_le hC hb₀ (A := B)]

end ExtendingPollard
