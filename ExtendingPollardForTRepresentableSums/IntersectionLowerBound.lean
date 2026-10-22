/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ExtendingPollardForTRepresentableSums.InductionHypothesis
public import Mathlib.Basic.Real.Basic
import ExtendingPollardForTRepresentableSums.EnergyBound
import ExtendingPollardForTRepresentableSums.KneserConsequences
import Mathlib.Data.Finset.Sym
import Mathlib.Tactic.Rify

/-!
# Step 3: the Dyson transform keeps at least `t` elements

After translating `B`, the Dyson transform of the paper is `(A ∪ B, A ∩ B)`, where `A ∩ B` is
nonempty, $|A \cap B| < |B|$, and $|A \cap (y + B)| \le |A \cap B|$ for every translate `y + B`
not contained in `A` (hypothesis `hmax`). This file proves Step 3 of the paper: if the theorem
fails for `A` and `B`, then $|A \cap B| \ge t$.

The proof bounds the size of the set $T = \{y : y + B \subseteq A\}$ and applies Lemma 2.1
(`mul_min_le_sumCardRepresentableSums`), since every `y ∉ T` has at most $|A \cap B|$
representations in `A - B`. The case `t = 2` uses that `B` is then a Sidon set.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace ExtendingPollard

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {A B C T : Finset G} {t : ℕ}
  {a b b₀ c p y : G}

/-! ### The translates of `B` inside `A` -/

lemma filter_vadd_finset_subset_add_subset (A B : Finset G) :
    {y ∈ A - B | y +ᵥ B ⊆ A} + B ⊆ A := by
  intro x hx
  obtain ⟨y, hy, b, hb, rfl⟩ := mem_add.1 hx
  obtain ⟨-, hyA⟩ := mem_filter.1 hy
  exact hyA (vadd_mem_vadd_finset hb)

lemma mem_filter_vadd_finset_subset (hB : B.Nonempty) (h : y +ᵥ B ⊆ A) :
    y ∈ {y ∈ A - B | y +ᵥ B ⊆ A} := by
  obtain ⟨b, hb⟩ := hB
  exact mem_filter.2 ⟨mem_sub.2 ⟨y + b, h (vadd_mem_vadd_finset hb), b, hb, by simp⟩, h⟩

/-- A translate `y + B` meeting `A` in more than $|A \cap B|$ elements lies in `A`. -/
lemma vadd_finset_subset_of_card_inter_lt
    (hmax : ∀ y : G, #(A ∩ (y +ᵥ B)) < #B → #(A ∩ (y +ᵥ B)) ≤ #(A ∩ B))
    (hy : #(A ∩ B) < #(A ∩ (y +ᵥ B))) : y +ᵥ B ⊆ A := by
  by_contra h
  refine hy.not_ge (hmax y ?_)
  rw [← card_vadd_finset y B]
  exact card_lt_card (inter_subset_right.ssubset_of_not_subset
    fun h' ↦ h (h'.trans inter_subset_left))

/-- Every `y ∉ T` has at most $|A \cap B|$ representations in `A - B`. -/
lemma addConvolution_neg_le_of_notMem (hB : B.Nonempty)
    (hmax : ∀ y : G, #(A ∩ (y +ᵥ B)) < #B → #(A ∩ (y +ᵥ B)) ≤ #(A ∩ B))
    (hy : y ∉ {y ∈ A - B | y +ᵥ B ⊆ A}) : A.addConvolution (-B) y ≤ #(A ∩ B) := by
  rw [← card_inter_vadd]
  by_contra! h
  exact hy (mem_filter_vadd_finset_subset hB (vadd_finset_subset_of_card_inter_lt hmax h))

/-- If every `b ∈ B` has at most `t - 1` sums `a + b` with at most `t` representations, then
$|A + B| \le |A +_t B| + (t - 1)|B|$. -/
lemma card_add_le_card_representableSums_add
    (hC : ∀ b ∈ B, #{a ∈ A | A.addConvolution B (a + b) ≤ t} ≤ t - 1) :
    #(A + B) ≤ #(representableSums t A B) + (t - 1) * #B := by
  rw [← card_sdiff_add_card_eq_card (representableSums_subset_add (i := t) (A := A) (B := B)),
    add_comm, mul_comm, ← smul_eq_mul]
  gcongr
  refine le_trans ?_ (sum_le_card_nsmul B _ (t - 1) hC)
  rw [(by simp_rw [card_filter, sum_product_right] :
    ∑ b ∈ B, #{a ∈ A | A.addConvolution B (a + b) ≤ t} =
      #{p ∈ A ×ˢ B | A.addConvolution B (p.1 + p.2) ≤ t})]
  refine le_trans ?_ (card_le_card (s := {p ∈ A ×ˢ B | p.1 + p.2 ∉ representableSums t A B}) ?_)
  · rw [card_filter_add_notMem_eq_sum, card_eq_sum_ones]
    gcongr with x hx
    exact Nat.one_le_iff_ne_zero.2 (Finset.addConvolution_ne_zero.2 (sdiff_subset hx))
  · rintro ⟨a, b⟩ hp
    simp only [mem_filter, mem_product, mem_representableSums] at hp ⊢
    grind [add_mem_add]

/-! ### Case 3.1: `t = 2` -/

/-- Two distinct representations of `c` give `c ∈ A +₂ B`. -/
lemma two_le_addConvolution {a a' b b' : G} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B)
    (hb' : b' ∈ B) (h : a + b = c) (h' : a' + b' = c) (hne : (a, b) ≠ (a', b')) :
    2 ≤ A.addConvolution B c :=
  one_lt_card.2 ⟨(a, b), mem_filter.2 ⟨mem_product.2 ⟨ha, hb⟩, h⟩, (a', b'),
    mem_filter.2 ⟨mem_product.2 ⟨ha', hb'⟩, h'⟩, hne⟩

/-- If $|A \cap B| = 1$ and every `a ∈ A` has at most one sum `a + b` with at most two
representations, then `A = T + B`. -/
lemma subset_filter_vadd_finset_subset_add (hB : 3 ≤ #B)
    (hmax : ∀ y : G, #(A ∩ (y +ᵥ B)) < #B → #(A ∩ (y +ᵥ B)) ≤ #(A ∩ B))
    (h1 : #(A ∩ B) = 1) (hC : ∀ a ∈ A, #{b ∈ B | A.addConvolution B (a + b) ≤ 2} ≤ 1) :
    A ⊆ {y ∈ A - B | y +ᵥ B ⊆ A} + B := by
  intro a ha
  by_contra haT
  have hkey : ∀ b ∈ B, ∀ p ∈ {p ∈ A ×ˢ B | p.1 + p.2 = a + b}, p = (a, b) := by
    rintro b hb ⟨a', b'⟩ hp
    simp only [mem_filter, mem_product] at hp
    obtain ⟨⟨ha', hb'⟩, h⟩ := hp
    by_cases hne : a' = a
    · subst hne
      simp [add_left_cancel h]
    have h2 : 1 < #(A ∩ ((a - b') +ᵥ B)) := by
      refine one_lt_card.2 ⟨a, mem_inter.2 ⟨ha, mem_vadd_finset.2 ⟨b', hb', by simp⟩⟩, a',
        mem_inter.2 ⟨ha', mem_vadd_finset.2 ⟨b, hb, ?_⟩⟩, Ne.symm hne⟩
      rw [vadd_eq_add, eq_sub_of_add_eq h]
      abel
    exact (haT (mem_add.2 ⟨a - b', mem_filter_vadd_finset_subset ⟨b, hb⟩
      (vadd_finset_subset_of_card_inter_lt hmax (by rwa [h1])), b', hb', by simp⟩)).elim
  have hsub : B ⊆ {b ∈ B | A.addConvolution B (a + b) ≤ 2} := by
    intro b hb
    refine mem_filter.2 ⟨hb, le_trans ?_ one_le_two⟩
    apply card_le_one.2
    intro p hp q hq
    rw [hkey b hb p hp, hkey b hb q hq]
  grind [card_le_card hsub, hC a ha]

/-- If $|A \cap B| = 1$, $A = T + B$ and $|H(A)| \le 1$, then `B` is a Sidon set. -/
lemma eq_or_eq_and_eq_of_add_eq
    (hmax : ∀ y : G, #(A ∩ (y +ᵥ B)) < #B → #(A ∩ (y +ᵥ B)) ≤ #(A ∩ B))
    (h1 : #(A ∩ B) = 1) (hstab : #A.addStab ≤ 1) (hAT : A ⊆ {y ∈ A - B | y +ᵥ B ⊆ A} + B)
    {b₁ b₂ b₁' b₂' : G} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hb₁' : b₁' ∈ B) (hb₂' : b₂' ∈ B)
    (h : b₁ + b₂' = b₁' + b₂) : b₁ = b₁' ∨ b₁ = b₂ ∧ b₁' = b₂' := by
  set T := {y ∈ A - B | y +ᵥ B ⊆ A}
  have hTA := filter_vadd_finset_subset_add_subset A B
  have hAne : A.Nonempty := (card_pos.1 (by grind : 0 < #(A ∩ B))).mono inter_subset_left
  by_contra! hne
  obtain ⟨hne₁, hne₂⟩ := hne
  have hy : b₁ - b₂ ∈ A.addStab := by
    rw [subset_antisymm hAT hTA]
    refine subset_addStab_add_left ⟨b₁, hb₁⟩
      ((mem_addStab_iff_vadd_finset_subset (hAne.mono hAT).of_add_left).2 ?_)
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_vadd_finset.1 hw
    rw [vadd_eq_add]
    refine mem_filter_vadd_finset_subset ⟨b₁, hb₁⟩ (vadd_finset_subset_of_card_inter_lt hmax ?_)
    rw [h1]
    refine one_lt_card.2 ⟨z + b₁, mem_inter.2 ⟨hTA (add_mem_add hz hb₁),
      mem_vadd_finset.2 ⟨b₂, hb₂, ?_⟩⟩, z + b₁', mem_inter.2 ⟨hTA (add_mem_add hz hb₁'),
      mem_vadd_finset.2 ⟨b₂', hb₂', ?_⟩⟩, fun h ↦ hne₁ (add_left_cancel h)⟩
    · rw [vadd_eq_add]
      abel
    · rw [vadd_eq_add, eq_sub_of_add_eq h.symm]
      abel
  obtain rfl : b₁ = b₂ := sub_eq_zero.1 (card_le_one.1 hstab _ hy _ hAne.zero_mem_addStab)
  exact hne₂ rfl (add_left_cancel (h.trans (add_comm _ _))).symm

/-- A Sidon set `B` has $|B + B| \ge |B|(|B| + 1)/2$. -/
lemma card_mul_card_add_one_le (hB : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ b₁' ∈ B, ∀ b₂' ∈ B,
      b₁ + b₂' = b₁' + b₂ → b₁ = b₁' ∨ b₁ = b₂ ∧ b₁' = b₂') :
    #B * (#B + 1) ≤ 2 * #(B + B) := by
  have hsym : #B.sym2 ≤ #(B + B) := by
    refine card_le_card_of_injOn (Sym2.lift ⟨fun x y ↦ x + y, fun x y ↦ add_comm x y⟩) ?_ ?_
    · intro s hs
      induction s using Sym2.ind with
      | h x y =>
        rw [mem_coe, mk_mem_sym2_iff] at hs
        obtain ⟨hx, hy⟩ := hs
        exact add_mem_add hx hy
    · intro s hs s' hs' hss'
      induction s using Sym2.ind with
      | h x y =>
        induction s' using Sym2.ind with
        | h x' y' =>
          rw [mem_coe, mk_mem_sym2_iff] at hs hs'
          obtain ⟨hx, hy⟩ := hs
          obtain ⟨hx', hy'⟩ := hs'
          simp only [Sym2.lift_mk] at hss'
          rcases hB x hx y' hy' x' hx' y hy (by rw [hss', add_comm x' y']) with rfl | ⟨rfl, rfl⟩
          · rw [add_left_cancel hss']
          · exact Sym2.eq_swap
  rw [card_sym2, Nat.choose_two_right, Nat.add_sub_cancel] at hsym
  grind [Nat.div_mul_cancel (even_iff_two_dvd.1 (Nat.even_mul_succ_self #B))]

/-- Every element with two representations in `T + (B + B)` has two representations in
`A + B`, if `T + B ⊆ A`. -/
lemma two_le_addConvolution_of_add_subset (hTB : T + B ⊆ A)
    (hc : 2 ≤ T.addConvolution (B + B) c) : 2 ≤ A.addConvolution B c := by
  obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.1 hc
  simp only [mem_filter, mem_product] at hp hq
  obtain ⟨⟨hz, hs⟩, hpc⟩ := hp
  obtain ⟨⟨hz', hs'⟩, hqc⟩ := hq
  obtain ⟨b₁, hb₁, b₂, hb₂, hs₁⟩ := mem_add.1 hs
  obtain ⟨b₁', hb₁', b₂', hb₂', hs₁'⟩ := mem_add.1 hs'
  by_cases h₁ : b₁ = b₂
  · by_cases h₂ : b₁' = b₂'
    · subst h₁ h₂
      refine two_le_addConvolution (hTB (add_mem_add hz hb₁)) (hTB (add_mem_add hz' hb₁')) hb₁
        hb₁' (by rw [← hpc, ← hs₁, add_assoc]) (by rw [← hqc, ← hs₁', add_assoc]) ?_
      intro h
      obtain rfl : b₁ = b₁' := congrArg Prod.snd h
      exact hpq (Prod.ext (add_right_cancel (hpc.trans (hqc.symm.trans (by rw [← hs₁, ← hs₁']))))
        (hs₁.symm.trans hs₁'))
    · refine two_le_addConvolution (hTB (add_mem_add hz' hb₁')) (hTB (add_mem_add hz' hb₂'))
        hb₂' hb₁' (by rw [← hqc, ← hs₁', add_assoc]) (by rw [← hqc, ← hs₁', add_assoc,
          add_comm b₂']) fun h ↦ h₂ (congrArg Prod.snd h).symm
  · refine two_le_addConvolution (hTB (add_mem_add hz hb₁)) (hTB (add_mem_add hz hb₂)) hb₂ hb₁
      (by rw [← hpc, ← hs₁, add_assoc]) (by rw [← hpc, ← hs₁, add_assoc, add_comm b₂])
      fun h ↦ h₁ (congrArg Prod.snd h).symm

/-- If `A = T + B` and $A +_2 B \ne A + B$, then $|T| + |B + B| \le |A + B| + 1$. -/
lemma card_add_card_add_le_of_eq_add (hsse : ¬SubsetSumsetEq 2 A B) (hA : A = T + B) :
    #T + #(B + B) ≤ #(A + B) + 1 := by
  by_contra! h
  refine hsse (subsetSumsetEq_of_representableSums_eq
    (subset_antisymm representableSums_subset_add ?_))
  intro x hx
  rw [hA, add_assoc] at hx h
  rw [mem_representableSums_of_one_le one_le_two]
  exact two_le_addConvolution_of_add_subset hA.symm.subset
    (le_addConvolution_of_card_add_le (by grind) hx)

/-- If `A = T + B` with `B` a Sidon set and $A +_2 B \ne A + B$, then
$2|T| + |B|(|B| + 1) \le 2|A + B| + 2$. -/
lemma two_mul_card_add_card_mul_card_add_one_le (hsse : ¬SubsetSumsetEq 2 A B) (hA : A = T + B)
    (hB : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ b₁' ∈ B, ∀ b₂' ∈ B,
      b₁ + b₂' = b₁' + b₂ → b₁ = b₁' ∨ b₁ = b₂ ∧ b₁' = b₂') :
    2 * #T + #B * (#B + 1) ≤ 2 * #(A + B) + 2 := by
  grind [card_mul_card_add_one_le hB, card_add_card_add_le_of_eq_add hsse hA]

/-- The final inequality of Case 3.1. -/
lemma false_of_min_le_of_two_mul_le {a b s T : ℕ} (hb : 3 ≤ b) (hab : b ≤ a)
    (hs : 2 * s + 5 ≤ 2 * a + 3 * b) (hT : 2 * T + b * (b + 1) + 3 ≤ 2 * a + 3 * b)
    (h : (a * b : ℝ) ≤ s ∨ (a ^ 2 * b : ℝ) / (T * (b - 1) + a) ≤ s) : False := by
  rify at hb hab hs hT
  have hT0 : (0 : ℝ) ≤ T := by positivity
  rcases h with h | h
  · nlinarith
  rw [div_le_iff₀ (by nlinarith)] at h
  have hP : 2 * T * (b - 1) + 2 * a ≤ (2 * a - b ^ 2 + 2 * b - 3) * ((b : ℝ) - 1) + 2 * a := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right (by linarith : 2 * (s : ℝ) ≤ 2 * a + 3 * b - 5)
      (by nlinarith : (0 : ℝ) ≤ 2 * T * (b - 1) + 2 * a),
    mul_le_mul_of_nonneg_left hP (by linarith : (0 : ℝ) ≤ 2 * a + 3 * b - 5),
    mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * a) (by linarith : (0 : ℝ) ≤ b - 3))
      (by nlinarith : (0 : ℝ) ≤ b ^ 2 - 3 * b + 1),
    mul_pos (mul_pos (by linarith : (0 : ℝ) < 3 * b - 5) (by linarith : (0 : ℝ) < b - 1))
      (by nlinarith : (0 : ℝ) < b ^ 2 - 2 * b + 3)]

/-- **Case 3.1.** For `t = 2`, the theorem failing for `A` and `B` forces $|A \cap B| \ge 2$. -/
lemma false_of_card_inter_eq_one (hIH : InductionHypothesis 2 A B) (hBA : #B ≤ #A)
    (hB : 3 ≤ #B) (hgood : ¬SumLowerBound 2 A B) (hsse : ¬SubsetSumsetEq 2 A B)
    (hmax : ∀ y : G, #(A ∩ (y +ᵥ B)) < #B → #(A ∩ (y +ᵥ B)) ≤ #(A ∩ B))
    (h1 : #(A ∩ B) = 1) : False := by
  have hC₁ (b : G) (hb : b ∈ B) :=
    card_filter_addConvolution_le_of_mem_right one_le_two hIH (by grind) hB hgood hsse hb
  have hAT := subset_filter_vadd_finset_subset_add hB hmax h1 fun a ha ↦
    card_filter_addConvolution_le_of_mem_left one_le_two hIH (by grind) (by grind) hgood hsse ha
  have hTB := two_mul_card_add_card_mul_card_add_one_le hsse
    (subset_antisymm hAT (filter_vadd_finset_subset_add_subset A B))
    fun b₁ hb₁ b₂ hb₂ b₁' hb₁' b₂' hb₂' h ↦
      eq_or_eq_and_eq_of_add_eq hmax h1 (card_addStab_le one_le_two hsse hC₁) hAT hb₁ hb₂ hb₁'
        hb₂' h
  have hlem := (mul_min_le_sumCardRepresentableSums (k := 1) (by grind) le_rfl fun y hy ↦
    h1 ▸ addConvolution_neg_le_of_notMem (card_pos.1 (by grind)) hmax hy).1
  rw [sumCardRepresentableSums_one] at hlem
  norm_num at hlem
  unfold SumLowerBound deficit at hgood
  rw [sumCardRepresentableSums_two] at hgood
  exact false_of_min_le_of_two_mul_le hB hBA (by grind [card_add_le_card_representableSums_add hC₁])
    (by grind [card_add_le_card_representableSums_add hC₁]) hlem

/-! ### Case 3.2: `t ≥ 3` -/

/-- If $|H(A)| < |B|$, the translates `b + A` with `b ∈ B` are not all equal. -/
lemma exists_vadd_finset_ne (hstab : #A.addStab < #B) (hA : A.Nonempty) (b₀ : G) :
    ∃ b ∈ B, b +ᵥ A ≠ b₀ +ᵥ A := by
  by_contra! h
  refine hstab.not_ge (card_le_card_of_injOn (· - b₀) ?_ sub_left_injective.injOn)
  intro b hb
  simp only [mem_coe, mem_addStab hA]
  rw [sub_eq_neg_add, ← vadd_vadd, h b hb, vadd_vadd, neg_add_cancel, zero_vadd]

/-- If `B` lies in one coset `b₀ + H` of the stabilizer `H` of a nonempty set, then the part `P`
of `A` in a coset of `H` has the same representations of `p + b` in `P + B` as in `A + B`, for
every `p` in that coset and `b ∈ B`. -/
lemma addConvolution_filter_sub_mem_addStab (hC : C.Nonempty)
    (hBH : ∀ b ∈ B, b - b₀ ∈ C.addStab) (a : G) (hp : p - a ∈ C.addStab) (hb : b ∈ B) :
    {a' ∈ A | a' - a ∈ C.addStab}.addConvolution B (p + b) = A.addConvolution B (p + b) := by
  refine le_antisymm (addConvolution_mono (filter_subset _ _) subset_rfl _) ?_
  apply card_le_card
  rintro ⟨q, b'⟩ hq
  simp only [mem_filter, mem_product] at hq ⊢
  obtain ⟨⟨hqA, hb'⟩, hqb⟩ := hq
  refine ⟨⟨⟨hqA, ?_⟩, hb'⟩, hqb⟩
  convert sub_mem_addStab hC (add_mem_addStab hC hp (hBH b hb)) (hBH b' hb') using 1
  rw [eq_sub_of_add_eq hqb]
  abel

/-- If `B` lies in one coset of the stabilizer `H` of a nonempty set, the parts of `A` inside and
outside a coset of `H` have disjoint sumsets with `B`. -/
lemma disjoint_filter_sub_mem_addStab_add (hC : C.Nonempty)
    (hBH : ∀ b ∈ B, b - b₀ ∈ C.addStab) (a : G) :
    Disjoint ({a' ∈ A | a' - a ∈ C.addStab} + B) ({a' ∈ A | a' - a ∉ C.addStab} + B) := by
  rw [disjoint_left]
  intro y hyP hyQ
  obtain ⟨p, hp, b₁, hb₁, rfl⟩ := mem_add.1 hyP
  obtain ⟨q, hq, b₂, hb₂, hq'⟩ := mem_add.1 hyQ
  obtain ⟨-, hp⟩ := mem_filter.1 hp
  obtain ⟨-, hq⟩ := mem_filter.1 hq
  apply hq
  convert sub_mem_addStab hC (add_mem_addStab hC hp (hBH b₁ hb₁)) (hBH b₂ hb₂) using 1
  rw [eq_sub_of_add_eq hq']
  abel

/-- If `A` meets two cosets of `H`, then `A` is not contained in the coset of `a`. -/
lemma filter_sub_notMem_addStab_nonempty (hC : C.Nonempty) {a₁ a₂ : G} (ha₁ : a₁ ∈ A)
    (ha₂ : a₂ ∈ A) (hne : a₂ - a₁ ∉ C.addStab) (a : G) :
    {a' ∈ A | a' - a ∉ C.addStab}.Nonempty := by
  by_cases h₁ : a₁ - a ∈ C.addStab
  · refine ⟨a₂, mem_filter.2 ⟨ha₂, ?_⟩⟩
    intro h₂
    apply hne
    convert sub_mem_addStab hC h₂ h₁ using 1
    abel
  · exact ⟨a₁, mem_filter.2 ⟨ha₁, h₁⟩⟩

/-- If `B` lies in one coset of `H` and `a ∈ A` has at most `t - 1` sums `a + b` with at most `t`
representations, then the part of `A` in the coset of `a` has at least `t` elements. -/
lemma le_card_filter_sub_mem_addStab (hC : C.Nonempty) (hBH : ∀ b ∈ B, b - b₀ ∈ C.addStab)
    (hB : t + 1 ≤ #B)
    (hCa : #{b ∈ B | A.addConvolution B (a + b) ≤ t} ≤ t - 1) :
    t ≤ #{a' ∈ A | a' - a ∈ C.addStab} := by
  by_contra! h
  have hsub : B ⊆ {b ∈ B | A.addConvolution B (a + b) ≤ t} := by
    intro b hb
    refine mem_filter.2 ⟨hb, ?_⟩
    rw [← addConvolution_filter_sub_mem_addStab hC hBH a (by simpa using hC.zero_mem_addStab) hb]
    exact Finset.addConvolution_le_card_left.trans h.le
  grind [card_le_card hsub]

/-- Splitting `A` along a coset of `H`, where `B` lies in one coset of `H`:
$\sum_{i=1}^t |P +_i B| + t|Q| \le \sum_{i=1}^t |A +_i B|$. -/
lemma sumCardRepresentableSums_filter_add_mul_card_le (hC : C.Nonempty)
    (hBH : ∀ b ∈ B, b - b₀ ∈ C.addStab) (hB : t ≤ #B) (a : G) :
    sumCardRepresentableSums t {a' ∈ A | a' - a ∈ C.addStab} B +
        t * #{a' ∈ A | a' - a ∉ C.addStab} ≤ sumCardRepresentableSums t A B := by
  grind [sumCardRepresentableSums_add_le (t := t) (filter_subset _ A) (filter_subset _ A)
      (disjoint_filter_sub_mem_addStab_add hC hBH a),
    mul_card_le_sumCardRepresentableSums (A := {a' ∈ A | a' - a ∉ C.addStab}) (t := t) hB]

/-- If the theorem fails for `A` and `B` and `B` lies in one coset of `H`, then the bound (6)
fails for the part of `A` in a coset of `H`. -/
lemma not_sumLowerBound_filter_sub_mem_addStab (hC : C.Nonempty)
    (hBH : ∀ b ∈ B, b - b₀ ∈ C.addStab) (hB : t ≤ #B) (h : ¬SumLowerBound t A B) (a : G) :
    ¬SumLowerBound t {a' ∈ A | a' - a ∈ C.addStab} B := by
  unfold SumLowerBound at *
  rw [← card_filter_add_card_filter_not (s := A) (fun a' ↦ a' - a ∈ C.addStab), mul_add] at h
  grind [sumCardRepresentableSums_filter_add_mul_card_le (A := A) (t := t) hC hBH hB a]

/-- **The subgroup claim of Case 3.2.** If the theorem fails for `A` and `B`, `B` lies in one
coset of the stabilizer `H` of a nonempty set, and `A` meets two `H`-cosets, then the theorem
for the parts of `A` in each coset gives a contradiction. -/
lemma false_of_forall_sub_mem_addStab (ht : 1 ≤ t) (hIH : InductionHypothesis t A B)
    (hA : t + 1 ≤ #A) (hB : t + 1 ≤ #B) (hgood : ¬SumLowerBound t A B)
    (hsse : ¬SubsetSumsetEq t A B) (hC : C.Nonempty) (hBH : ∀ b ∈ B, b - b₀ ∈ C.addStab)
    {a₁ a₂ : G} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hne : a₂ - a₁ ∉ C.addStab) : False := by
  refine hsse (subsetSumsetEq_of_representableSums_eq
    (subset_antisymm representableSums_subset_add ?_))
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hx
  set P := {a' ∈ A | a' - a ∈ C.addStab}
  have hPt := le_card_filter_sub_mem_addStab hC hBH hB
    (card_filter_addConvolution_le_of_mem_left ht hIH hA (by grind) hgood hsse ha)
  have hgoodP := not_sumLowerBound_filter_sub_mem_addStab hC hBH (by grind) hgood a
  rcases hIH P B hPt (by grind) (Or.inl (by
    nlinarith [sumCardRepresentableSums_filter_add_mul_card_le (A := A) (t := t) hC hBH
        (by grind) a,
      card_pos.2 (filter_sub_notMem_addStab_nonempty hC ha₁ ha₂ hne a)])) with hgP | hsP
  · exact (hgoodP hgP).elim
  unfold SumLowerBound at hgoodP
  obtain ⟨P', B', hW, hX⟩ := hsP.exists_saturatedWitness ht hPt (by grind)
    (by grind [sq_le_deficit t])
  rcases hW.eq_add_or_exists ht hPt (by grind) hX with heq | ⟨p, hp, hcard⟩ | ⟨b', hb', hcard⟩
  · refine representableSums_mono (filter_subset (· - a ∈ C.addStab) A) subset_rfl ?_
    rw [heq]
    exact add_mem_add (mem_filter.2 ⟨ha, by simpa using hC.zero_mem_addStab⟩) hb
  · obtain ⟨hpA, hpH⟩ := mem_filter.1 hp
    have hsub : {b' ∈ B | P.addConvolution B (p + b') < t} ⊆
        {b' ∈ B | A.addConvolution B (p + b') ≤ t} := by
      intro b' hb'
      rw [mem_filter] at hb' ⊢
      obtain ⟨hb', hlt⟩ := hb'
      rw [← addConvolution_filter_sub_mem_addStab hC hBH a hpH hb']
      exact ⟨hb', hlt.le⟩
    grind [card_le_card hsub,
      card_filter_addConvolution_le_of_mem_left ht hIH hA (by grind) hgood hsse hpA]
  · have hsub : {p ∈ P | P.addConvolution B (p + b') < t} ⊆
        {a' ∈ A | A.addConvolution B (a' + b') ≤ t} := by
      intro p hp
      rw [mem_filter] at hp ⊢
      obtain ⟨hp, hlt⟩ := hp
      obtain ⟨hpA, hpH⟩ := mem_filter.1 hp
      rw [← addConvolution_filter_sub_mem_addStab hC hBH a hpH hb']
      exact ⟨hpA, hlt.le⟩
    grind [card_le_card hsub,
      card_filter_addConvolution_le_of_mem_right ht hIH (by grind) hB hgood hsse hb']

/-- If `C ⊆ A` and `A` lies in one coset of the stabilizer of `C`, then `A = C`. -/
lemma eq_of_subset_of_forall_sub_mem_addStab (hCA : C ⊆ A) (hC : C.Nonempty)
    (hA : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₂ - a₁ ∈ C.addStab) : A = C := by
  obtain ⟨c, hc⟩ := hC
  refine subset_antisymm ?_ hCA
  intro a ha
  simpa using add_mem_of_mem_addStab hc (hA c (hCA hc) a ha)

/-- **The bound (47).** If the theorem fails for `A` and `B` and $|A \cap B| \le t - 1$, then
$|T| \le |A| - |B| + t - 1$. -/
lemma card_filter_vadd_finset_subset_add_card_le (ht : 1 ≤ t) (hIH : InductionHypothesis t A B)
    (hBA : #B ≤ #A) (hB : t + 1 ≤ #B) (hgood : ¬SumLowerBound t A B)
    (hsse : ¬SubsetSumsetEq t A B)
    (hmax : ∀ y : G, #(A ∩ (y +ᵥ B)) < #B → #(A ∩ (y +ᵥ B)) ≤ #(A ∩ B))
    (hAB : #(A ∩ B) ≤ t - 1) (hstab : #A.addStab ≤ t - 1) :
    #{y ∈ A - B | y +ᵥ B ⊆ A} + #B ≤ #A + (t - 1) := by
  set T := {y ∈ A - B | y +ᵥ B ⊆ A}
  by_contra! h
  have hTne : T.Nonempty := card_pos.1 (by grind)
  obtain ⟨b₀, hb₀⟩ : B.Nonempty := card_pos.1 (by grind)
  have hTB := filter_vadd_finset_subset_add_subset A B
  by_cases hall : ∀ b ∈ B, b - b₀ ∈ (T + B).addStab
  · by_cases hA₁ : ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₂ - a₁ ∉ (T + B).addStab
    · obtain ⟨a₁, ha₁, a₂, ha₂, hne⟩ := hA₁
      exact false_of_forall_sub_mem_addStab ht hIH (by grind) hB hgood hsse
        (hTne.add ⟨b₀, hb₀⟩) hall ha₁ ha₂ hne
    push Not at hA₁
    rw [eq_of_subset_of_forall_sub_mem_addStab hTB (hTne.add ⟨b₀, hb₀⟩) hA₁] at hstab
    grind [card_le_card_of_injOn (· - b₀) (fun b hb ↦ hall b hb) sub_left_injective.injOn]
  push Not at hall
  obtain ⟨b₁, hb₁, hb₁H⟩ := hall
  apply hb₁H
  refine subset_addStab_add_left ⟨b₀, hb₀⟩ ((mem_addStab_iff_vadd_finset_subset hTne).2 ?_)
  intro w hw
  obtain ⟨z, hz, rfl⟩ := mem_vadd_finset.1 hw
  rw [vadd_eq_add]
  refine mem_filter_vadd_finset_subset ⟨b₀, hb₀⟩ (vadd_finset_subset_of_card_inter_lt hmax ?_)
  refine lt_of_lt_of_le (by grind : #(A ∩ B) < t) ((by
    grind [card_add_card_le_card_add_add_card_inter_vadd hTne hb₀, card_le_card hTB] :
      t ≤ #(B ∩ (b₀ +ᵥ (T + B).addStab))).trans ?_)
  rw [← card_vadd_finset (b₁ - b₀ + z) (B ∩ (b₀ +ᵥ (T + B).addStab))]
  apply card_le_card
  intro w hw
  obtain ⟨c, hc, rfl⟩ := mem_vadd_finset.1 hw
  obtain ⟨hcB, hcH⟩ := mem_inter.1 hc
  obtain ⟨h, hh, rfl⟩ := mem_vadd_finset.1 hcH
  refine mem_inter.2 ⟨?_, vadd_mem_vadd_finset hcB⟩
  convert hTB (add_mem_of_mem_addStab (add_mem_add hz hb₁) hh) using 1
  simp only [vadd_eq_add]
  abel

/-- For `t ≥ 3`, the failure of the bound (6) reads
$\sum_{i=1}^t |A +_i B| + 2t^2 \le t|A| + t|B|$. -/
lemma add_two_mul_sq_le_of_not_sumLowerBound (ht : 3 ≤ t) (h : ¬SumLowerBound t A B) :
    sumCardRepresentableSums t A B + 2 * t ^ 2 ≤ t * #A + t * #B := by
  unfold SumLowerBound at h
  rw [deficit_of_ne_two (by grind)] at h
  grind [(by nlinarith : 1 ≤ 2 * t ^ 2)]

/-- The final inequality of Case 3.2. -/
lemma false_of_min_le_of_le {a b S t T : ℕ} (ht : 3 ≤ t) (hb : 2 * t + 1 ≤ b) (hab : b ≤ a)
    (hT : T + b ≤ a + (t - 1)) (hS : S + 2 * t ^ 2 ≤ t * a + t * b)
    (h : min ((a * b : ℝ) / 2)
      (t * ((a ^ 2 * b : ℝ) / (T * (b - (t - 1 : ℕ) : ℝ) + (t - 1 : ℕ) * a))) ≤ S) : False := by
  have ht1 : 1 ≤ t := by grind
  push_cast [ht1] at h
  rify [ht1] at ht hb hab hT hS
  have hT0 : (0 : ℝ) ≤ T := by positivity
  rcases min_le_iff.1 h with h | h
  · nlinarith
  have hD : 0 < T * (b - (t - 1)) + (t - 1) * (a : ℝ) := by nlinarith
  rw [mul_div_assoc', div_le_iff₀ hD] at h
  have h₂ : S * (T * (b - (t - 1)) + (t - 1) * a) ≤
      t * (a + b - 2 * t) * ((a - b + t - 1) * (b - (t - 1)) + (t - 1) * (a : ℝ)) :=
    (mul_le_mul_of_nonneg_right (by nlinarith) hD.le).trans
      (mul_le_mul_of_nonneg_left (by nlinarith) (by nlinarith))
  have h₅ : (a : ℝ) ^ 2 * b ≤
      (a + b - 2 * t) * ((a - b + t - 1) * (b - (t - 1)) + (t - 1) * a) := by
    rw [mul_assoc] at h₂
    exact le_of_mul_le_mul_left (h.trans h₂) (by linarith)
  nlinarith [mul_pos (by linarith : (0 : ℝ) < a) (by nlinarith : (0 : ℝ) < 2 * b + (t - 1) ^ 2),
    mul_nonneg (by linarith : (0 : ℝ) ≤ b - 2 * t) (sq_nonneg ((b : ℝ) - (t - 1)))]

/-- **Case 3.2.** For `t ≥ 3`, the theorem failing for `A` and `B` forces $|A \cap B| \ge t$. -/
lemma false_of_card_inter_le_sub_one (ht : 3 ≤ t) (hIH : InductionHypothesis t A B)
    (hBA : #B ≤ #A) (hB : t + 1 ≤ #B) (hgood : ¬SumLowerBound t A B)
    (hsse : ¬SubsetSumsetEq t A B) (hAB : (A ∩ B).Nonempty)
    (hmax : ∀ y : G, #(A ∩ (y +ᵥ B)) < #B → #(A ∩ (y +ᵥ B)) ≤ #(A ∩ B))
    (hlt : #(A ∩ B) ≤ t - 1) : False := by
  have ht1 : 1 ≤ t := by grind
  obtain ⟨b₀, hb₀⟩ := hAB.mono inter_subset_right
  have hstab := card_addStab_le ht1 hsse fun b hb ↦
    card_filter_addConvolution_le_of_mem_right ht1 hIH (by grind) hB hgood hsse hb
  obtain ⟨b, hb, hne⟩ := exists_vadd_finset_ne (B := B) (by grind) (hAB.mono inter_subset_left) b₀
  obtain ⟨hsum, hmin⟩ := mul_min_le_sumCardRepresentableSums (k := t - 1) (by grind) ht1 fun y hy ↦
    (addConvolution_neg_le_of_notMem ⟨b₀, hb₀⟩ hmax hy).trans hlt
  exact false_of_min_le_of_le ht (Nat.lt_of_mul_lt_mul_left (a := t) (by
      nlinarith [mul_card_lt_sumCardRepresentableSums ht1 hB hb hb₀ hne,
        add_two_mul_sq_le_of_not_sumLowerBound ht hgood])) hBA
    (card_filter_vadd_finset_subset_add_card_le ht1 hIH hBA hB hgood hsse hmax hlt hstab)
    (add_two_mul_sq_le_of_not_sumLowerBound ht hgood) (hmin.trans hsum)

/-- **Step 3.** If the theorem fails for `A` and `B`, then $|A \cap B| \ge t$. -/
lemma le_card_inter (ht : 1 ≤ t) (hIH : InductionHypothesis t A B) (hBA : #B ≤ #A)
    (hB : t + 1 ≤ #B) (hgood : ¬SumLowerBound t A B) (hsse : ¬SubsetSumsetEq t A B)
    (hAB : (A ∩ B).Nonempty)
    (hmax : ∀ y : G, #(A ∩ (y +ᵥ B)) < #B → #(A ∩ (y +ᵥ B)) ≤ #(A ∩ B)) : t ≤ #(A ∩ B) := by
  by_contra! h
  have := card_pos.2 hAB
  rcases (by grind : t = 2 ∨ 3 ≤ t) with rfl | ht3
  · exact false_of_card_inter_eq_one hIH hBA hB hgood hsse hmax (by grind)
  · exact false_of_card_inter_le_sub_one ht3 hIH hBA hB hgood hsse hAB hmax (by grind)

end ExtendingPollard
