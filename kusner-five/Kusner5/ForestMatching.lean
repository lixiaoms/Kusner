import Kusner5.MatchingArithmetic
import Kusner5.RangeGeometry
import Kusner5.Orders
import Kusner5.CutEnergy

/-!
Actual-label endpoint and finite position estimates.

The threshold lemmas are lower relaxations of an injection into the actual
ordered eleven positions. They never posit independently realizable orders.
In particular, one shared path label is represented once with its combined
weight, even when that weight exceeds the individual edge cap.
-/

namespace Kusner5.ForestMatching

open scoped BigOperators
open Profiles MatchingArithmetic

noncomputable section

def squaredPosition : Fin 11 → ℝ :=
  ![s1, s2, s3, s4, s5, 0, s5, s4, s3, s2, s1]

theorem shiftedVector_sq_eq_position (i : Fin 11) :
    shiftedVector i ^ 2 = squaredPosition i := shiftedVector_sq i

theorem squaredPosition_nonneg (i : Fin 11) : 0 ≤ squaredPosition i := by
  rw [← shiftedVector_sq_eq_position]
  exact sq_nonneg _

def positions {ι : Type*} (p : Equiv.Perm Label) (labels : ι → Label) :
    ι → Fin 11 := fun i => p.symm (labels i)

theorem positions_injective {ι : Type*} (p : Equiv.Perm Label)
    (labels : ι → Label) (hlabels : Function.Injective labels) :
    Function.Injective (positions p labels) := p.symm.injective.comp hlabels

/-- A permutation sends every distinct original label to a distinct position. -/
theorem shifted_original_label_square {ι : Type*} (p : Equiv.Perm Label)
    (labels : ι → Label) (i : ι) :
    shiftedVector (p.symm (labels i)) ^ 2 = squaredPosition (positions p labels i) := by
  exact shiftedVector_sq_eq_position _

theorem sum_comp_le_sum_of_injective {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (hf : Function.Injective f) (g : κ → ℝ)
    (hg : ∀ j, 0 ≤ g j) : (∑ i, g (f i)) ≤ ∑ j, g j := by
  classical
  calc
    (∑ i, g (f i)) = ∑ j ∈ Finset.univ.image f, g j := by
      rw [Finset.sum_image]
      intro i hi j hj hij
      exact hf hij
    _ ≤ ∑ j ∈ Finset.univ, g j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j hj hjnot
      exact hg j

def discount (a q : ℝ) : ℝ := max (a - q) 0

theorem discount_nonneg (a q : ℝ) : 0 ≤ discount a q := le_max_right _ _
theorem sub_le_discount (a q : ℝ) : a - q ≤ discount a q := le_max_left _ _

theorem threshold_sum_lower {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (hf : Function.Injective f) (q : κ → ℝ) (a : ℝ) :
    (Fintype.card ι : ℝ) * a - (∑ j, discount a (q j)) ≤ ∑ i, q (f i) := by
  have hpoint : (∑ i, (a - q (f i))) ≤ ∑ i, discount a (q (f i)) := by
    exact Finset.sum_le_sum fun i _ => sub_le_discount a (q (f i))
  have himage := sum_comp_le_sum_of_injective f hf
    (fun j => discount a (q j)) (fun j => discount_nonneg a (q j))
  have hid : (∑ i, (a - q (f i))) =
      (Fintype.card ι : ℝ) * a - ∑ i, q (f i) := by
    simp [Finset.sum_sub_distrib]
  rw [hid] at hpoint
  linarith

theorem weighted_threshold_sum_lower {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (hf : Function.Injective f) (q : κ → ℝ)
    (w : ι → ℝ) (a M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ M) :
    a * (∑ i, w i) - M * (∑ j, discount a (q j)) ≤
      ∑ i, w i * q (f i) := by
  have hpoint (i : ι) :
      w i * (a - q (f i)) ≤ M * discount a (q (f i)) := by
    calc
      _ ≤ w i * discount a (q (f i)) :=
        mul_le_mul_of_nonneg_left (sub_le_discount _ _) (hw i).1
      _ ≤ _ := mul_le_mul_of_nonneg_right (hw i).2 (discount_nonneg _ _)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hpoint i)
  have hi := sum_comp_le_sum_of_injective f hf
    (fun j => discount a (q j)) (fun j => discount_nonneg a (q j))
  have hm := mul_le_mul_of_nonneg_left hi hM
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum] at hs
  linarith

/-- One exceptional weight represents one shared original label. -/
theorem weighted_threshold_one_large {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (hf : Function.Injective f) (q : κ → ℝ)
    (hq : ∀ j, 0 ≤ q j) (w : ι → ℝ) (i0 : ι) (a M S : ℝ)
    (ha : 0 ≤ a) (hM : 0 ≤ M) (hMS : M ≤ S)
    (hw0 : w i0 ≤ S) (hw : ∀ i, 0 ≤ w i)
    (hwM : ∀ i, i ≠ i0 → w i ≤ M) :
    a * (∑ i, w i) - M * (∑ j, discount a (q j)) - (S - M) * a ≤
      ∑ i, w i * q (f i) := by
  classical
  have hpoint (i : ι) :
      w i * (a - q (f i)) ≤ M * discount a (q (f i)) +
        (if i = i0 then (S - M) * discount a (q (f i)) else 0) := by
    have hfirst := mul_le_mul_of_nonneg_left (sub_le_discount a (q (f i))) (hw i)
    by_cases hi : i = i0
    · subst i
      simp only [ite_true]
      have hlast := mul_le_mul_of_nonneg_right hw0 (discount_nonneg a (q (f i0)))
      nlinarith
    · simp only [hi, ite_false, add_zero]
      exact le_trans hfirst
        (mul_le_mul_of_nonneg_right (hwM i hi) (discount_nonneg a (q (f i))))
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hpoint i)
  have hi := sum_comp_le_sum_of_injective f hf
    (fun j => discount a (q j)) (fun j => discount_nonneg a (q j))
  have hm := mul_le_mul_of_nonneg_left hi hM
  have hd : discount a (q (f i0)) ≤ a := by
    apply max_le
    · linarith [hq (f i0)]
    · exact ha
  have hlarge := mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hMS)
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum] at hs
  have hsingle : (∑ i, if i = i0 then (S - M) * discount a (q (f i)) else 0) =
      (S - M) * discount a (q (f i0)) := by simp
  rw [hsingle] at hs
  linarith

theorem discount_position_sum (a : ℝ) :
    (∑ i : Fin 11, discount a (squaredPosition i)) =
      2 * discount a s1 + 2 * discount a s2 + 2 * discount a s3 +
        2 * discount a s4 + 2 * discount a s5 + discount a 0 := by
  norm_num [squaredPosition, Fin.sum_univ_succ]
  ring

theorem discount_sum_s5 : (∑ i : Fin 11, discount s5 (squaredPosition i)) = s5 := by
  rw [discount_position_sum]
  have h51 : s5 - s1 ≤ 0 := by linarith [s5_lt_s4, s4_lt_s3, s3_lt_s2, s2_lt_s1]
  have h52 : s5 - s2 ≤ 0 := by linarith [s5_lt_s4, s4_lt_s3, s3_lt_s2]
  have h53 : s5 - s3 ≤ 0 := by linarith [s5_lt_s4, s4_lt_s3]
  have h54 : s5 - s4 ≤ 0 := by linarith [s5_lt_s4]
  simp [discount, max_eq_right h51, max_eq_right h52, max_eq_right h53,
    max_eq_right h54, max_eq_left (le_of_lt s5_pos)]

theorem discount_sum_s4 :
    (∑ i : Fin 11, discount s4 (squaredPosition i)) = 3 * s4 - 2 * s5 := by
  rw [discount_position_sum]
  have h41 : s4 - s1 ≤ 0 := by linarith [s4_lt_s3, s3_lt_s2, s2_lt_s1]
  have h42 : s4 - s2 ≤ 0 := by linarith [s4_lt_s3, s3_lt_s2]
  have h43 : s4 - s3 ≤ 0 := by linarith [s4_lt_s3]
  have h45 : 0 ≤ s4 - s5 := by linarith [s5_lt_s4]
  simp [discount, max_eq_right h41, max_eq_right h42, max_eq_right h43,
    max_eq_left h45, max_eq_left (le_of_lt MatchingArithmetic.s4_pos)]
  ring

theorem discount_sum_s3 :
    (∑ i : Fin 11, discount s3 (squaredPosition i)) = 5 * s3 - 2 * s4 - 2 * s5 := by
  rw [discount_position_sum]
  have h31 : s3 - s1 ≤ 0 := by linarith [s3_lt_s2, s2_lt_s1]
  have h32 : s3 - s2 ≤ 0 := by linarith [s3_lt_s2]
  have h34 : 0 ≤ s3 - s4 := by linarith [s4_lt_s3]
  have h35 : 0 ≤ s3 - s5 := by linarith [s5_lt_s4, s4_lt_s3]
  simp [discount, max_eq_right h31, max_eq_right h32,
    max_eq_left h34, max_eq_left h35, max_eq_left (le_of_lt MatchingArithmetic.s3_pos)]
  ring

theorem discount_sum_s2 :
    (∑ i : Fin 11, discount s2 (squaredPosition i)) =
      7 * s2 - 2 * s3 - 2 * s4 - 2 * s5 := by
  rw [discount_position_sum]
  have h21 : s2 - s1 ≤ 0 := by linarith [s2_lt_s1]
  have h23 : 0 ≤ s2 - s3 := by linarith [s3_lt_s2]
  have h24 : 0 ≤ s2 - s4 := by linarith [s4_lt_s3, s3_lt_s2]
  have h25 : 0 ≤ s2 - s5 := by linarith [s5_lt_s4, s4_lt_s3, s3_lt_s2]
  simp [discount, max_eq_right h21, max_eq_left h23,
    max_eq_left h24, max_eq_left h25, max_eq_left (le_of_lt MatchingArithmetic.s2_pos)]
  ring

theorem position_sum_two (f : Fin 2 → Fin 11) (hf : Function.Injective f) :
    s5 ≤ ∑ i, squaredPosition (f i) := by
  have h := threshold_sum_lower f hf squaredPosition s5
  rw [discount_sum_s5] at h
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at h
  linarith

theorem position_sum_four (f : Fin 4 → Fin 11) (hf : Function.Injective f) :
    2 * s5 + s4 ≤ ∑ i, squaredPosition (f i) := by
  have h := threshold_sum_lower f hf squaredPosition s4
  rw [discount_sum_s4] at h
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at h
  linarith

theorem position_sum_six (f : Fin 6 → Fin 11) (hf : Function.Injective f) :
    2 * s5 + 2 * s4 + s3 ≤ ∑ i, squaredPosition (f i) := by
  have h := threshold_sum_lower f hf squaredPosition s3
  rw [discount_sum_s3] at h
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at h
  linarith

theorem position_sum_eight (f : Fin 8 → Fin 11) (hf : Function.Injective f) :
    2 * s5 + 2 * s4 + 2 * s3 + s2 ≤ ∑ i, squaredPosition (f i) := by
  have h := threshold_sum_lower f hf squaredPosition s2
  rw [discount_sum_s2] at h
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at h
  linarith

def firstPositions {m n : ℕ} (h : m ≤ n) (f : Fin n → Fin 11) : Fin m → Fin 11 :=
  fun i => f ⟨i.val, lt_of_lt_of_le i.isLt h⟩

theorem firstPositions_injective {m n : ℕ} (h : m ≤ n) (f : Fin n → Fin 11)
    (hf : Function.Injective f) : Function.Injective (firstPositions h f) := by
  intro i j hij
  have hcast := hf hij
  apply Fin.ext
  exact congrArg (fun r : Fin n => r.val) hcast

theorem weighted_six_positions (f : Fin 6 → Fin 11) (hf : Function.Injective f)
    (x y z : ℝ) (hxy : y ≤ x) (hyz : z ≤ y) (hz : 0 ≤ z) :
    c1 * x + c2 * y + c3 * z ≤
      x * (squaredPosition (f 0) + squaredPosition (f 1)) +
        y * (squaredPosition (f 2) + squaredPosition (f 3)) +
        z * (squaredPosition (f 4) + squaredPosition (f 5)) := by
  have h2 := position_sum_two (firstPositions (by norm_num : 2 ≤ 6) f)
    (firstPositions_injective _ f hf)
  have h4 := position_sum_four (firstPositions (by norm_num : 4 ≤ 6) f)
    (firstPositions_injective _ f hf)
  have h6 := position_sum_six f hf
  norm_num [firstPositions, Fin.sum_univ_succ] at h2 h4 h6
  have hp2 := mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr h2)
  have hp4 := mul_nonneg (sub_nonneg.mpr hyz) (sub_nonneg.mpr h4)
  have hp6 := mul_nonneg hz (sub_nonneg.mpr h6)
  dsimp [c1, c2, c3]
  nlinarith

theorem weighted_eight_positions (f : Fin 8 → Fin 11) (hf : Function.Injective f)
    (x y z w : ℝ) (hxy : y ≤ x) (hyz : z ≤ y) (hzw : w ≤ z) (hw : 0 ≤ w) :
    c1 * x + c2 * y + c3 * z + c4 * w ≤
      x * (squaredPosition (f 0) + squaredPosition (f 1)) +
        y * (squaredPosition (f 2) + squaredPosition (f 3)) +
        z * (squaredPosition (f 4) + squaredPosition (f 5)) +
        w * (squaredPosition (f 6) + squaredPosition (f 7)) := by
  have h2 := position_sum_two (firstPositions (by norm_num : 2 ≤ 8) f)
    (firstPositions_injective _ f hf)
  have h4 := position_sum_four (firstPositions (by norm_num : 4 ≤ 8) f)
    (firstPositions_injective _ f hf)
  have h6 := position_sum_six (firstPositions (by norm_num : 6 ≤ 8) f)
    (firstPositions_injective _ f hf)
  have h8 := position_sum_eight f hf
  norm_num [firstPositions, Fin.sum_univ_succ] at h2 h4 h6 h8
  have hp2 := mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr h2)
  have hp4 := mul_nonneg (sub_nonneg.mpr hyz) (sub_nonneg.mpr h4)
  have hp6 := mul_nonneg (sub_nonneg.mpr hzw) (sub_nonneg.mpr h6)
  have hp8 := mul_nonneg hw (sub_nonneg.mpr h8)
  dsimp [c1, c2, c3, c4]
  nlinarith

theorem seven_capped_threshold_s3 (f : Fin 7 → Fin 11) (hf : Function.Injective f)
    (w : Fin 7 → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1 / 3) :
    s3 * (∑ i, w i) - (5 * s3 - 2 * s5 - 2 * s4) / 3 ≤
      ∑ i, w i * squaredPosition (f i) := by
  have h := weighted_threshold_sum_lower f hf squaredPosition w s3 (1 / 3)
    (by norm_num) hw
  rw [discount_sum_s3] at h
  linarith

theorem seven_capped_threshold_s4 (f : Fin 7 → Fin 11) (hf : Function.Injective f)
    (w : Fin 7 → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1 / 3) :
    s4 * (∑ i, w i) - (3 * s4 - 2 * s5) / 3 ≤
      ∑ i, w i * squaredPosition (f i) := by
  have h := weighted_threshold_sum_lower f hf squaredPosition w s4 (1 / 3)
    (by norm_num) hw
  rw [discount_sum_s4] at h
  linarith

theorem seven_shared_threshold_s4 (f : Fin 7 → Fin 11) (hf : Function.Injective f)
    (w : Fin 7 → ℝ) (shared : Fin 7) (S : ℝ) (hS : 1 / 3 ≤ S)
    (hwS : w shared ≤ S) (hw : ∀ i, 0 ≤ w i)
    (hwCap : ∀ i, i ≠ shared → w i ≤ 1 / 3) :
    s4 * (∑ i, w i) - S * s4 - (2 / 3) * (s4 - s5) ≤
      ∑ i, w i * squaredPosition (f i) := by
  have h := weighted_threshold_one_large f hf squaredPosition squaredPosition_nonneg
    w shared s4 (1 / 3) S (le_of_lt MatchingArithmetic.s4_pos)
    (by norm_num) hS hwS hw hwCap
  rw [discount_sum_s4] at h
  linarith

abbrev ExtremaFamily (x : Configuration) := ∀ k : Coordinate, CoordinateExtrema x k

def IsWide {x : Configuration} (E : ExtremaFamily x) (k : Coordinate) : Prop :=
  1 / 2 < (E k).range

def IsEndpoint {x : Configuration} (E : ExtremaFamily x) (k : Coordinate)
    (i : Label) : Prop := i = (E k).lo ∨ i = (E k).hi

def ShareEndpoint {x : Configuration} (E : ExtremaFamily x) (k l : Coordinate) : Prop :=
  ∃ i : Label, IsEndpoint E k i ∧ IsEndpoint E l i

theorem shareEndpoint_symm {x : Configuration} {E : ExtremaFamily x}
    {k l : Coordinate} (h : ShareEndpoint E k l) : ShareEndpoint E l k := by
  rcases h with ⟨i, hk, hl⟩
  exact ⟨i, hl, hk⟩

def IsNonisolated {x : Configuration} (E : ExtremaFamily x) (k : Coordinate) : Prop :=
  IsWide E k ∧ ∃ l, IsWide E l ∧ l ≠ k ∧ ShareEndpoint E k l

def IsIsolated {x : Configuration} (E : ExtremaFamily x) (k : Coordinate) : Prop :=
  IsWide E k ∧ ¬∃ l, IsWide E l ∧ l ≠ k ∧ ShareEndpoint E k l

def wideCoordinates {x : Configuration} (E : ExtremaFamily x) : Finset Coordinate := by
  classical
  exact Finset.univ.filter (IsWide E)

def isolatedCoordinates {x : Configuration} (E : ExtremaFamily x) : Finset Coordinate := by
  classical
  exact Finset.univ.filter (IsIsolated E)

def nonisolatedCoordinates {x : Configuration} (E : ExtremaFamily x) : Finset Coordinate := by
  classical
  exact Finset.univ.filter (IsNonisolated E)

@[simp] theorem mem_wideCoordinates {x : Configuration} (E : ExtremaFamily x)
    (k : Coordinate) : k ∈ wideCoordinates E ↔ IsWide E k := by
  classical
  simp [wideCoordinates]

@[simp] theorem mem_isolatedCoordinates {x : Configuration} (E : ExtremaFamily x)
    (k : Coordinate) : k ∈ isolatedCoordinates E ↔ IsIsolated E k := by
  classical
  simp [isolatedCoordinates]

@[simp] theorem mem_nonisolatedCoordinates {x : Configuration} (E : ExtremaFamily x)
    (k : Coordinate) : k ∈ nonisolatedCoordinates E ↔ IsNonisolated E k := by
  classical
  simp [nonisolatedCoordinates]

theorem wideCoordinates_partition {x : Configuration} (E : ExtremaFamily x) :
    wideCoordinates E = isolatedCoordinates E ∪ nonisolatedCoordinates E := by
  classical
  ext k
  simp only [mem_wideCoordinates, Finset.mem_union, mem_isolatedCoordinates,
    mem_nonisolatedCoordinates, IsIsolated, IsNonisolated]
  tauto

theorem isolated_nonisolated_disjoint {x : Configuration} (E : ExtremaFamily x) :
    Disjoint (isolatedCoordinates E) (nonisolatedCoordinates E) := by
  classical
  apply Finset.disjoint_left.mpr
  intro k hk hl
  exact (mem_isolatedCoordinates E k |>.mp hk).2
    (mem_nonisolatedCoordinates E k |>.mp hl).2

theorem wide_card_partition {x : Configuration} (E : ExtremaFamily x) :
    (wideCoordinates E).card =
      (isolatedCoordinates E).card + (nonisolatedCoordinates E).card := by
  rw [wideCoordinates_partition, Finset.card_union_of_disjoint
    (isolated_nonisolated_disjoint E)]

theorem nonisolated_has_nonisolated_neighbor {x : Configuration} (E : ExtremaFamily x)
    (k : Coordinate) (hk : k ∈ nonisolatedCoordinates E) :
    ∃ l ∈ nonisolatedCoordinates E, l ≠ k ∧ ShareEndpoint E k l := by
  rcases (mem_nonisolatedCoordinates E k).mp hk with ⟨hwk, l, hwl, hlk, hshare⟩
  refine ⟨l, ?_, hlk, hshare⟩
  apply (mem_nonisolatedCoordinates E l).mpr
  exact ⟨hwl, k, hwk, Ne.symm hlk, shareEndpoint_symm hshare⟩

theorem nonisolated_card_ne_one {x : Configuration} (E : ExtremaFamily x) :
    (nonisolatedCoordinates E).card ≠ 1 := by
  classical
  intro h
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h
  have hkmem : k ∈ nonisolatedCoordinates E := by rw [hk]; simp
  obtain ⟨l, hl, hlk, hshare⟩ := nonisolated_has_nonisolated_neighbor E k hkmem
  have heq : l = k := by simpa [hk] using hl
  exact hlk heq

/-- These are all counts; the actual structural witnesses are proved separately. -/
theorem exhaustive_wide_isolated_counts {x : Configuration} (E : ExtremaFamily x)
    (hWide : 4 ≤ (wideCoordinates E).card)
    (hIsolated : 2 ≤ (isolatedCoordinates E).card) :
    ((wideCoordinates E).card = 4 ∧ (isolatedCoordinates E).card = 2 ∧
      (nonisolatedCoordinates E).card = 2) ∨
    ((wideCoordinates E).card = 4 ∧ (isolatedCoordinates E).card = 4 ∧
      (nonisolatedCoordinates E).card = 0) ∨
    ((wideCoordinates E).card = 5 ∧ (isolatedCoordinates E).card = 2 ∧
      (nonisolatedCoordinates E).card = 3) ∨
    ((wideCoordinates E).card = 5 ∧ (isolatedCoordinates E).card = 3 ∧
      (nonisolatedCoordinates E).card = 2) ∨
    ((wideCoordinates E).card = 5 ∧ (isolatedCoordinates E).card = 5 ∧
      (nonisolatedCoordinates E).card = 0) := by
  have hMax := Finset.card_le_univ (s := wideCoordinates E)
  have hPart := wide_card_partition E
  have hNotOne := nonisolated_card_ne_one E
  norm_num only [Fintype.card_fin] at hMax
  omega

def excess {x : Configuration} (E : ExtremaFamily x) (k : Coordinate) : ℝ :=
  (E k).range - 1 / 2

theorem excess_pos {x : Configuration} (E : ExtremaFamily x)
    (k : Coordinate) (hk : IsWide E k) : 0 < excess E k := sub_pos.mpr hk

theorem nonisolated_mass_lt_of_root_ledger (Hnon Δ : ℝ)
    (hEq : Δ = 5 * rootAlpha - 5) (hLower : (10 / 11) * Hnon ≤ Δ) :
    Hnon < 33 / 80 := by
  linarith [rootAlpha_lt_43_40]

theorem isolated_mass_gt_of_root_ledger (H Hnon Hiso Δ : ℝ)
    (hH : 5 / 6 < H) (hSplit : H = Hnon + Hiso)
    (hEq : Δ = 5 * rootAlpha - 5) (hLower : (10 / 11) * Hnon ≤ Δ) :
    101 / 240 < Hiso := by
  have hN := nonisolated_mass_lt_of_root_ledger Hnon Δ hEq hLower
  linarith

theorem isolated_card_at_least_two {x : Configuration} (E : ExtremaFamily x)
    (hMass : 101 / 240 < ∑ k ∈ isolatedCoordinates E, excess E k)
    (hCap : ∀ k, IsWide E k → excess E k ≤ 1 / 3) :
    2 ≤ (isolatedCoordinates E).card := by
  classical
  have hsum : (∑ k ∈ isolatedCoordinates E, excess E k) ≤
      ((isolatedCoordinates E).card : ℝ) / 3 := by
    calc
      _ ≤ ∑ k ∈ isolatedCoordinates E, (1 / 3 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hCap k ((mem_isolatedCoordinates E k).mp hk).1
      _ = _ := by simp; ring
  by_contra hn
  have hcard : (isolatedCoordinates E).card ≤ 1 := by omega
  have hreal : ((isolatedCoordinates E).card : ℝ) ≤ 1 := by exact_mod_cast hcard
  linarith

theorem extrema_abs_endpoint {n d : ℕ} {x : Fin n → Point d} {k : Fin d}
    (e : CoordinateExtrema x k) : |x e.lo k - x e.hi k| = e.range := by
  rw [abs_sub_comm]
  change |e.range| = e.range
  exact abs_of_nonneg e.range_nonneg

theorem two_coordinate_distance_le {d : ℕ} (a b : Point d) (k l : Fin d)
    (hkl : k ≠ l) : |a k - b k| + |a l - b l| ≤ l1dist a b := by
  classical
  calc
    _ = ∑ j ∈ ({k, l} : Finset (Fin d)), |a j - b j| := by simp [hkl]
    _ ≤ ∑ j ∈ Finset.univ, |a j - b j| := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => abs_nonneg _)

theorem distinct_wide_endpoint_pairs {x : Configuration} (hx : UnitEquilateral x)
    (E : ExtremaFamily x) (k l : Coordinate) (hk : IsWide E k) (hl : IsWide E l)
    (hkl : k ≠ l) :
    ¬(((E k).lo = (E l).lo ∧ (E k).hi = (E l).hi) ∨
      ((E k).lo = (E l).hi ∧ (E k).hi = (E l).lo)) := by
  intro hpair
  have hab := (E k).lo_ne_hi_of_wide hk
  have hkabs := extrema_abs_endpoint (E k)
  have hlabs : |x (E k).lo l - x (E k).hi l| = (E l).range := by
    rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
      exact extrema_abs_endpoint (E l)
    · rw [ha, hb, abs_sub_comm]
      exact extrema_abs_endpoint (E l)
  have hbound := two_coordinate_distance_le (x (E k).lo) (x (E k).hi) k l hkl
  rw [hkabs, hlabs, hx _ _ hab] at hbound
  dsimp [IsWide] at hk hl
  linarith

theorem order_first_eq_wide_lo {x : Configuration} (hx : UnitEquilateral x)
    {k : Coordinate} (e : CoordinateExtrema x k) (hw : 1 / 2 < e.range)
    (p : Equiv.Perm Label) (hp : Monotone (fun i => x (p i) k)) : p 0 = e.lo := by
  apply e.wide_lo_unique hx hw (p 0)
  have hmin : x (p 0) k ≤ x e.lo k := by
    have h := hp (show (0 : Label) ≤ p.symm e.lo by exact Fin.zero_le _)
    simpa using h
  exact le_antisymm hmin (e.bound_all (p 0)).1

theorem order_last_eq_wide_hi {x : Configuration} (hx : UnitEquilateral x)
    {k : Coordinate} (e : CoordinateExtrema x k) (hw : 1 / 2 < e.range)
    (p : Equiv.Perm Label) (hp : Monotone (fun i => x (p i) k)) :
    p (Fin.last 10) = e.hi := by
  apply e.wide_hi_unique hx hw (p (Fin.last 10))
  have hmax : x e.hi k ≤ x (p (Fin.last 10)) k := by
    have hle : p.symm e.hi ≤ Fin.last 10 := by
      change (p.symm e.hi).val ≤ 10
      have := (p.symm e.hi).isLt
      omega
    simpa using hp hle
  exact le_antisymm (e.bound_all (p (Fin.last 10))).2 hmax

theorem wide_range_eq_order_range {x : Configuration} (hx : UnitEquilateral x)
    {k : Coordinate} (e : CoordinateExtrema x k) (hw : 1 / 2 < e.range)
    (p : Equiv.Perm Label) (hp : Monotone (fun i => x (p i) k)) :
    scalarRange (fun i => x i k) p = e.range := by
  unfold scalarRange CoordinateExtrema.range
  rw [order_first_eq_wide_lo hx e hw p hp, order_last_eq_wide_hi hx e hw p hp]

theorem sum_abs_ge_twice_of_sum_zero {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (hd : (∑ i, d i) = 0) (j : ι) :
    2 * |d j| ≤ ∑ i, |d i| := by
  classical
  have hremove : d j + (∑ i ∈ Finset.univ.erase j, d i) = 0 := by
    rw [← Finset.sum_insert (by simp), Finset.insert_erase (Finset.mem_univ j), hd]
  have habssum : |d j| + (∑ i ∈ Finset.univ.erase j, |d i|) = ∑ i, |d i| := by
    calc
      _ = ∑ i ∈ insert j (Finset.univ.erase j), |d i| :=
        (Finset.sum_insert (by simp)).symm
      _ = _ := by rw [Finset.insert_erase (Finset.mem_univ j)]
  have hrest : (∑ i ∈ Finset.univ.erase j, d i) = -d j := by linarith
  have htriangle := Finset.abs_sum_le_sum_abs d (Finset.univ.erase j)
  rw [hrest, abs_neg] at htriangle
  linarith

theorem cyclic_variation_ge_twice {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (s : Equiv.Perm ι) (j : ι) :
    2 * |a j - a (s j)| ≤ ∑ i, |a i - a (s i)| := by
  classical
  have hperm : (∑ i, a (s i)) = ∑ i, a i := by
    apply Finset.sum_bij (fun i _ => s i)
    · intro i hi; exact Finset.mem_univ _
    · intro i hi j hj hij; exact s.injective hij
    · intro i hi; exact ⟨s.symm i, Finset.mem_univ _, by simp⟩
    · intro i hi; rfl
  apply sum_abs_ge_twice_of_sum_zero (fun i => a i - a (s i)) _ j
  rw [Finset.sum_sub_distrib, hperm]
  ring

def cyclicCoordinateVariation {ι : Type*} [Fintype ι] (x : Configuration)
    (v : ι → Label) (s : Equiv.Perm ι) (k : Coordinate) : ℝ :=
  ∑ i, |x (v i) k - x (v (s i)) k|

/-- Every actual cycle would instantiate this theorem; there is no graph premise. -/
theorem no_wide_permutation_cycle {ι : Type*} [Fintype ι] [Nonempty ι]
    {x : Configuration} (hx : UnitEquilateral x) (E : ExtremaFamily x)
    (v : ι → Label) (s : Equiv.Perm ι) (c : ι → Coordinate)
    (hc : Function.Injective c)
    (hnext : ∀ i, v i ≠ v (s i)) (hwide : ∀ i, IsWide E (c i))
    (hends : ∀ i,
      ((E (c i)).lo = v i ∧ (E (c i)).hi = v (s i)) ∨
      ((E (c i)).lo = v (s i) ∧ (E (c i)).hi = v i)) : False := by
  classical
  have hvariation (i : ι) :
      2 * (E (c i)).range ≤ cyclicCoordinateVariation x v s (c i) := by
    have h := cyclic_variation_ge_twice (fun j => x (v j) (c i)) s i
    have heq : |x (v i) (c i) - x (v (s i)) (c i)| = (E (c i)).range := by
      rcases hends i with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [← ha, ← hb]
        exact extrema_abs_endpoint (E (c i))
      · rw [← hb, ← ha, abs_sub_comm]
        exact extrema_abs_endpoint (E (c i))
    simpa only [heq, cyclicCoordinateVariation] using h
  have hsumLower := Finset.sum_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hvariation i)
  have hsumInject := sum_comp_le_sum_of_injective c hc
    (cyclicCoordinateVariation x v s)
    (fun k => Finset.sum_nonneg fun i _ => abs_nonneg _)
  have htotal : (∑ k, cyclicCoordinateVariation x v s k) = (Fintype.card ι : ℝ) := by
    unfold cyclicCoordinateVariation
    rw [Finset.sum_comm]
    change (∑ i, l1dist (x (v i)) (x (v (s i)))) = _
    have hpair (i : ι) : l1dist (x (v i)) (x (v (s i))) = 1 := hx _ _ (hnext i)
    simp_rw [hpair]
    simp
  have hstrict : (Fintype.card ι : ℝ) < ∑ i, 2 * (E (c i)).range := by
    calc
      _ = ∑ _i : ι, (1 : ℝ) := by simp
      _ < _ := by
        apply Finset.sum_lt_sum
        · intro i hi
          have hw := hwide i
          dsimp [IsWide] at hw
          linarith
        · obtain ⟨i⟩ := ‹Nonempty ι›
          refine ⟨i, Finset.mem_univ _, ?_⟩
          have hw := hwide i
          dsimp [IsWide] at hw
          linarith
  rw [htotal] at hsumInject
  linarith

def actualExtrema (x : Configuration) : ExtremaFamily x :=
  fun k => CoordinateExtrema.ofOrder x k (columnOrders x k) (columnOrders_monotone x k)

theorem actualExtrema_range (x : Configuration) (k : Coordinate) :
    (actualExtrema x k).range = scalarRange (fun i => x i k) (columnOrders x k) := rfl

theorem actual_wideCoordinates_eq (x : Configuration) :
    wideCoordinates (actualExtrema x) = Profiles.wideCoordinates x := by
  classical
  ext k
  simp [wideCoordinates, Profiles.wideCoordinates, IsWide, actualExtrema_range]

theorem actual_at_least_four_wide (x : Configuration) (hx : UnitEquilateral x) :
    4 ≤ (wideCoordinates (actualExtrema x)).card := by
  rw [actual_wideCoordinates_eq]
  exact Profiles.at_least_four_wide x hx

theorem actual_wide_excess_eq (x : Configuration) :
    (∑ k ∈ wideCoordinates (actualExtrema x), excess (actualExtrema x) k) =
      Profiles.wideExcess x := by
  rw [actual_wideCoordinates_eq]
  rfl

theorem actual_wide_outer_energy_lower (x : Configuration) (hx : UnitEquilateral x)
    (k : Coordinate) (hk : IsWide (actualExtrema x) k)
    (u : Label → ℝ) (hu : (∑ i, u i) = 0) :
    excess (actualExtrema x) k *
        (u (actualExtrema x k).lo ^ 2 + u (actualExtrema x k).hi ^ 2) ≤
      columnEnergy x (columnOrders x) k u := by
  have hwide : 1 / 2 < scalarRange (fun i => x i k) (columnOrders x k) := hk
  have hg := wide_ordered_outer_gaps x hx k (columnOrders x k)
    (columnOrders_monotone x k) hwide
  exact scalarEnergy_outer_lower (fun i => x i k) (columnOrders x k)
    (columnOrders_monotone x k) u hu (excess (actualExtrema x) k)
    (le_of_lt (excess_pos _ k hk)) hg.1 hg.2

theorem root_actual_endpoint_sq (x : Configuration) (k : Coordinate) (i : Label)
    (hi : IsEndpoint (actualExtrema x) k i) :
    transport (columnOrders x k) rootVector i ^ 2 = 10 / 11 := by
  rcases hi with hlo | hhi
  · rw [hlo]
    exact rootVector_transport_first_sq _
  · rw [hhi]
    exact rootVector_transport_last_sq _

theorem shifted_actual_endpoint_sq (x : Configuration) (k : Coordinate) (i : Label)
    (hi : IsEndpoint (actualExtrema x) k i) :
    transport (columnOrders x k) shiftedVector i ^ 2 = s1 := by
  rcases hi with hlo | hhi
  · rw [hlo]
    change transport (columnOrders x k) shiftedVector (columnOrders x k 0) ^ 2 = s1
    rw [transport_at_order, shiftedVector_first_sq]
  · rw [hhi]
    change transport (columnOrders x k) shiftedVector
      (columnOrders x k (Fin.last 10)) ^ 2 = s1
    rw [transport_at_order, shiftedVector_last_sq]

def directedEnergy (x : Configuration) (v : Label → ℝ)
    (pair : Coordinate × Coordinate) : ℝ :=
  if pair.2 ≠ pair.1 then
    columnEnergy x (columnOrders x) pair.2 (transport (columnOrders x pair.1) v)
  else 0

theorem directedEnergy_nonneg (x : Configuration) (v : Label → ℝ)
    (pair : Coordinate × Coordinate) : 0 ≤ directedEnergy x v pair := by
  unfold directedEnergy
  split_ifs
  · exact scalarEnergy_nonneg _ _ (columnOrders_monotone x pair.2) _
  · exact le_rfl

theorem sum_directedEnergy (x : Configuration) (v : Label → ℝ) :
    (∑ pair : Coordinate × Coordinate, directedEnergy x v pair) =
      crossEnergy x (columnOrders x) v := by
  classical
  rw [Fintype.sum_prod_type]
  unfold crossEnergy
  apply Finset.sum_congr rfl
  intro k hk
  have herase : (Finset.univ : Finset Coordinate).erase k =
      Finset.univ.filter (fun l => l ≠ k) := by
    ext l
    simp
  rw [herase, Finset.sum_filter]
  rfl

theorem root_shared_endpoint_lower (x : Configuration) (hx : UnitEquilateral x)
    (row col : Coordinate) (hrow : IsWide (actualExtrema x) row)
    (hcol : IsWide (actualExtrema x) col)
    (hshare : ShareEndpoint (actualExtrema x) row col) :
    (10 / 11) * excess (actualExtrema x) col ≤
      columnEnergy x (columnOrders x) col (transport (columnOrders x row) rootVector) := by
  obtain ⟨i, hirow, hicol⟩ := hshare
  have hsq := root_actual_endpoint_sq x row i hirow
  have hlower := actual_wide_outer_energy_lower x hx col hcol
    (transport (columnOrders x row) rootVector)
    (by rw [sum_transport, sum_rootVector_zero])
  have ht := le_of_lt (excess_pos (actualExtrema x) col hcol)
  rcases hicol with hlo | hhi
  · rw [hlo] at hsq
    rw [hsq] at hlower
    have hother := mul_nonneg ht
      (sq_nonneg (transport (columnOrders x row) rootVector (actualExtrema x col).hi))
    nlinarith
  · rw [hhi] at hsq
    rw [hsq] at hlower
    have hother := mul_nonneg ht
      (sq_nonneg (transport (columnOrders x row) rootVector (actualExtrema x col).lo))
    nlinarith

theorem sum_subtype_finset {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ) :
    (∑ i : {a // a ∈ S}, f i.val) = ∑ a ∈ S, f a := by
  classical
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi; exact i.property
  · intro i hi j hj hij; exact Subtype.ext hij
  · intro a ha; exact ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩
  · intro i hi; rfl

/-- One chosen neighboring row per column; column indices make the pairs injective. -/
theorem original_root_nonisolated_lower (x : Configuration) (hx : UnitEquilateral x) :
    (10 / 11) * (∑ k ∈ nonisolatedCoordinates (actualExtrema x),
      excess (actualExtrema x) k) ≤ crossEnergy x (columnOrders x) rootVector := by
  classical
  let N := nonisolatedCoordinates (actualExtrema x)
  let I := {k : Coordinate // k ∈ N}
  have hneighbors (k : I) :
      ∃ l ∈ N, l ≠ k.val ∧ ShareEndpoint (actualExtrema x) k.val l :=
    nonisolated_has_nonisolated_neighbor (actualExtrema x) k.val k.property
  choose neighbor hneighbor_mem hneighbor_ne hneighbor_share using hneighbors
  let pair : I → Coordinate × Coordinate := fun k => (neighbor k, k.val)
  have hpair : Function.Injective pair := by
    intro i j hij
    apply Subtype.ext
    exact congrArg Prod.snd hij
  have hterm (k : I) : (10 / 11) * excess (actualExtrema x) k.val ≤
      directedEnergy x rootVector (pair k) := by
    have hwidek := ((mem_nonisolatedCoordinates (actualExtrema x) k.val).mp k.property).1
    have hwider := ((mem_nonisolatedCoordinates (actualExtrema x) (neighbor k)).mp
      (hneighbor_mem k)).1
    have h := root_shared_endpoint_lower x hx (neighbor k) k.val hwider hwidek
      (shareEndpoint_symm (hneighbor_share k))
    simpa [directedEnergy, pair, Ne.symm (hneighbor_ne k)] using h
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset I)) => hterm k)
  have hsub := sum_comp_le_sum_of_injective pair hpair (directedEnergy x rootVector)
    (directedEnergy_nonneg x rootVector)
  rw [← Finset.mul_sum, sum_subtype_finset] at hsum
  rw [sum_directedEnergy] at hsub
  exact le_trans hsum hsub

theorem original_isolated_mass_gt (x : Configuration) (hx : UnitEquilateral x) :
    101 / 240 < ∑ k ∈ isolatedCoordinates (actualExtrema x), excess (actualExtrema x) k := by
  have hsplit : Profiles.wideExcess x =
      (∑ k ∈ nonisolatedCoordinates (actualExtrema x), excess (actualExtrema x) k) +
        ∑ k ∈ isolatedCoordinates (actualExtrema x), excess (actualExtrema x) k := by
    rw [← actual_wide_excess_eq, wideCoordinates_partition,
      Finset.sum_union (isolated_nonisolated_disjoint (actualExtrema x))]
    ring
  exact isolated_mass_gt_of_root_ledger _ _ _ _ (Profiles.wideExcess_gt_five_sixths x hx)
    hsplit (root_crossEnergy x hx) (original_root_nonisolated_lower x hx)

theorem original_excess_le_third (x : Configuration) (hx : UnitEquilateral x)
    (k : Coordinate) : excess (actualExtrema x) k ≤ 1 / 3 := by
  have hcap := coordinate_range_le_five_sixths hx (actualExtrema x k)
  dsimp [excess]
  linarith

theorem original_at_least_two_isolated (x : Configuration) (hx : UnitEquilateral x) :
    2 ≤ (isolatedCoordinates (actualExtrema x)).card :=
  isolated_card_at_least_two (actualExtrema x) (original_isolated_mass_gt x hx)
    (fun k _ => original_excess_le_third x hx k)

theorem original_exhaustive_counts (x : Configuration) (hx : UnitEquilateral x) :
    ((wideCoordinates (actualExtrema x)).card = 4 ∧
      (isolatedCoordinates (actualExtrema x)).card = 2 ∧
      (nonisolatedCoordinates (actualExtrema x)).card = 2) ∨
    ((wideCoordinates (actualExtrema x)).card = 4 ∧
      (isolatedCoordinates (actualExtrema x)).card = 4 ∧
      (nonisolatedCoordinates (actualExtrema x)).card = 0) ∨
    ((wideCoordinates (actualExtrema x)).card = 5 ∧
      (isolatedCoordinates (actualExtrema x)).card = 2 ∧
      (nonisolatedCoordinates (actualExtrema x)).card = 3) ∨
    ((wideCoordinates (actualExtrema x)).card = 5 ∧
      (isolatedCoordinates (actualExtrema x)).card = 3 ∧
      (nonisolatedCoordinates (actualExtrema x)).card = 2) ∨
    ((wideCoordinates (actualExtrema x)).card = 5 ∧
      (isolatedCoordinates (actualExtrema x)).card = 5 ∧
      (nonisolatedCoordinates (actualExtrema x)).card = 0) :=
  exhaustive_wide_isolated_counts (actualExtrema x)
    (actual_at_least_four_wide x hx) (original_at_least_two_isolated x hx)

def IsMatching {x : Configuration} (E : ExtremaFamily x) : Prop :=
  ∀ k l, IsWide E k → IsWide E l → k ≠ l → ¬ShareEndpoint E k l

theorem matching_of_no_nonisolated {x : Configuration} (E : ExtremaFamily x)
    (hNone : (nonisolatedCoordinates E).card = 0) : IsMatching E := by
  classical
  have hempty := Finset.card_eq_zero.mp hNone
  intro k l hk hl hkl hshare
  have hmem : k ∈ nonisolatedCoordinates E := by
    exact (mem_nonisolatedCoordinates E k).mpr ⟨hk, l, hl, Ne.symm hkl, hshare⟩
  rw [hempty] at hmem
  simp at hmem

theorem all_wide_of_card_five {x : Configuration} (E : ExtremaFamily x)
    (hcard : (wideCoordinates E).card = 5) : ∀ k, IsWide E k := by
  classical
  have heq : wideCoordinates E = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa [hcard]
  intro k
  apply (mem_wideCoordinates E k).mp
  rw [heq]
  exact Finset.mem_univ _

def endpointLabel {x : Configuration} (E : ExtremaFamily x)
    (kb : Coordinate × Bool) : Label := if kb.2 then (E kb.1).hi else (E kb.1).lo

theorem endpointLabel_isEndpoint {x : Configuration} (E : ExtremaFamily x)
    (kb : Coordinate × Bool) : IsEndpoint E kb.1 (endpointLabel E kb) := by
  rcases kb with ⟨k, b⟩
  cases b <;> simp [endpointLabel, IsEndpoint]

theorem matching_endpointLabel_injective {x : Configuration} (E : ExtremaFamily x)
    (hWide : ∀ k, IsWide E k) (hMatching : IsMatching E) :
    Function.Injective (endpointLabel E) := by
  intro a b hab
  rcases a with ⟨k, ka⟩
  rcases b with ⟨l, lb⟩
  have hkl : k = l := by
    by_contra hne
    apply hMatching k l (hWide k) (hWide l) hne
    exact ⟨endpointLabel E (k, ka), endpointLabel_isEndpoint E (k, ka),
      hab.symm ▸ endpointLabel_isEndpoint E (l, lb)⟩
  subst l
  cases ka <;> cases lb
  · rfl
  · simp [endpointLabel] at hab
    exact False.elim ((E k).lo_ne_hi_of_wide (hWide k) hab)
  · simp [endpointLabel] at hab
    exact False.elim ((E k).lo_ne_hi_of_wide (hWide k) hab.symm)
  · rfl

def IsCore {x : Configuration} (E : ExtremaFamily x) (i : Label) : Prop :=
  ∀ k, i ≠ (E k).lo ∧ i ≠ (E k).hi

/-- Ten indexed endpoint slots cannot cover the eleven original labels. -/
theorem exists_core {x : Configuration} (E : ExtremaFamily x) : ∃ i, IsCore E i := by
  classical
  have hnot : ¬Function.Surjective (endpointLabel E) := by
    intro hsurj
    have hc := Fintype.card_le_of_surjective (endpointLabel E) hsurj
    norm_num at hc
  change ¬∀ i, ∃ kb, endpointLabel E kb = i at hnot
  push_neg at hnot
  obtain ⟨i, hi⟩ := hnot
  refine ⟨i, fun k => ⟨?_, ?_⟩⟩
  · simpa [endpointLabel] using Ne.symm (hi (k, false))
  · simpa [endpointLabel] using Ne.symm (hi (k, true))

def endpointSet {x : Configuration} (E : ExtremaFamily x) (k : Coordinate) : Finset Label :=
  {(E k).lo, (E k).hi}

@[simp] theorem mem_endpointSet {x : Configuration} (E : ExtremaFamily x)
    (k : Coordinate) (i : Label) : i ∈ endpointSet E k ↔ IsEndpoint E k i := by
  simp [endpointSet, IsEndpoint]

def endpointSupport {x : Configuration} (E : ExtremaFamily x)
    (S : Finset Coordinate) : Finset Label := S.biUnion (endpointSet E)

theorem endpointSet_card_le_two {x : Configuration} (E : ExtremaFamily x)
    (k : Coordinate) : (endpointSet E k).card ≤ 2 := by
  by_cases h : (E k).lo = (E k).hi <;> simp [endpointSet, h]

theorem endpointSupport_card_le_twice {x : Configuration} (E : ExtremaFamily x)
    (S : Finset Coordinate) : (endpointSupport E S).card ≤ 2 * S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [endpointSupport]
  | @insert k S hk ih =>
    have hunion := Finset.card_union_le (endpointSet E k) (endpointSupport E S)
    have hedge := endpointSet_card_le_two E k
    simp only [endpointSupport, Finset.biUnion_insert, Finset.card_insert_of_notMem hk]
    change ((endpointSet E k) ∪ endpointSupport E S).card ≤ 2 * (S.card + 1)
    omega

theorem union_card_le_sum_sub_one {α : Type*} [DecidableEq α] (S T : Finset α)
    (hOverlap : ∃ a, a ∈ S ∧ a ∈ T) : (S ∪ T).card + 1 ≤ S.card + T.card := by
  obtain ⟨a, haS, haT⟩ := hOverlap
  have hmem : a ∈ S ∩ T := Finset.mem_inter.mpr ⟨haS, haT⟩
  have hpos : 1 ≤ (S ∩ T).card := by
    exact Finset.one_le_card.mpr ⟨a, hmem⟩
  have hcard := Finset.card_union_add_card_inter S T
  omega

theorem shared_two_edges_support_le_three {x : Configuration} (E : ExtremaFamily x)
    (k l : Coordinate) (hShare : ShareEndpoint E k l) :
    ((endpointSet E k) ∪ endpointSet E l).card ≤ 3 := by
  obtain ⟨i, hik, hil⟩ := hShare
  have hover := union_card_le_sum_sub_one (endpointSet E k) (endpointSet E l)
    ⟨i, (mem_endpointSet E k i).mpr hik, (mem_endpointSet E l i).mpr hil⟩
  have hk := endpointSet_card_le_two E k
  have hl := endpointSet_card_le_two E l
  omega

theorem nonisolated_three_support_le_four {x : Configuration} (E : ExtremaFamily x)
    (hN : (nonisolatedCoordinates E).card = 3) :
    (endpointSupport E (nonisolatedCoordinates E)).card ≤ 4 := by
  classical
  let N := nonisolatedCoordinates E
  have hNnonempty : N.Nonempty := Finset.card_pos.mp (by simpa [N, hN])
  obtain ⟨k, hk⟩ := hNnonempty
  obtain ⟨l, hl, hlk, hklShare⟩ := nonisolated_has_nonisolated_neighbor E k hk
  have hthird : ∃ m ∈ N, m ≠ k ∧ m ≠ l := by
    by_contra hnone
    push_neg at hnone
    have hsub : N ⊆ ({k, l} : Finset Coordinate) := by
      intro m hm
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hmk : m = k
      · exact Or.inl hmk
      · exact Or.inr (hnone m hm hmk)
    have hc := Finset.card_le_card hsub
    have hp : ({k, l} : Finset Coordinate).card ≤ 2 := by simp [Ne.symm hlk]
    have hNc : N.card = 3 := hN
    omega
  obtain ⟨m, hm, hmk, hml⟩ := hthird
  have hsubset : ({k, l, m} : Finset Coordinate) ⊆ N := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact hk
    · exact hl
    · exact hm
  have htriple : ({k, l, m} : Finset Coordinate).card = 3 := by
    simp [hlk, hmk, hml, Ne.symm hlk, Ne.symm hmk, Ne.symm hml]
  have heq : N = {k, l, m} := by
    symm
    apply Finset.eq_of_subset_of_card_le hsubset
    simpa [N, hN, htriple]
  obtain ⟨n, hn, hnm, hmnShare⟩ := nonisolated_has_nonisolated_neighbor E m hm
  have hn' : n = k ∨ n = l ∨ n = m := by
    have : n ∈ N := hn
    simpa [heq] using this
  have hmShare : ShareEndpoint E m k ∨ ShareEndpoint E m l := by
    rcases hn' with rfl | rfl | rfl
    · exact Or.inl hmnShare
    · exact Or.inr hmnShare
    · exact False.elim (hnm rfl)
  have hkl : ((endpointSet E k) ∪ endpointSet E l).card ≤ 3 :=
    shared_two_edges_support_le_three E k l hklShare
  have hmCard := endpointSet_card_le_two E m
  have hover : ∃ i, i ∈ endpointSet E k ∪ endpointSet E l ∧ i ∈ endpointSet E m := by
    rcases hmShare with hmkShare | hmlShare
    · obtain ⟨i, him, hik⟩ := hmkShare
      exact ⟨i, Finset.mem_union.mpr (Or.inl ((mem_endpointSet E k i).mpr hik)),
        (mem_endpointSet E m i).mpr him⟩
    · obtain ⟨i, him, hil⟩ := hmlShare
      exact ⟨i, Finset.mem_union.mpr (Or.inr ((mem_endpointSet E l i).mpr hil)),
        (mem_endpointSet E m i).mpr him⟩
  have hCard := union_card_le_sum_sub_one ((endpointSet E k) ∪ endpointSet E l)
    (endpointSet E m) hover
  have hSupport : endpointSupport E N = (endpointSet E k ∪ endpointSet E l) ∪
      endpointSet E m := by simp [endpointSupport, heq, Finset.union_assoc]
  change (endpointSupport E N).card ≤ 4
  rw [hSupport]
  omega

theorem two_isolated_three_nonisolated_support_le_eight {x : Configuration}
    (E : ExtremaFamily x) (hI : (isolatedCoordinates E).card = 2)
    (hN : (nonisolatedCoordinates E).card = 3) :
    (endpointSupport E (wideCoordinates E)).card ≤ 8 := by
  have hIso := endpointSupport_card_le_twice E (isolatedCoordinates E)
  have hNon := nonisolated_three_support_le_four E hN
  have hUnion := Finset.card_union_le (endpointSupport E (isolatedCoordinates E))
    (endpointSupport E (nonisolatedCoordinates E))
  have hSupport : endpointSupport E (wideCoordinates E) =
      endpointSupport E (isolatedCoordinates E) ∪ endpointSupport E (nonisolatedCoordinates E) := by
    rw [wideCoordinates_partition]
    ext i
    simp only [endpointSupport, Finset.mem_biUnion, Finset.mem_union]
    constructor
    · rintro ⟨k, hk, hki⟩
      rcases hk with hk | hk
      · exact Or.inl ⟨k, hk, hki⟩
      · exact Or.inr ⟨k, hk, hki⟩
    · rintro (h | h)
      · obtain ⟨k, hk, hki⟩ := h
        exact ⟨k, Or.inl hk, hki⟩
      · obtain ⟨k, hk, hki⟩ := h
        exact ⟨k, Or.inr hk, hki⟩
  rw [hSupport]
  omega

def IsWideCore {x : Configuration} (E : ExtremaFamily x) (i : Label) : Prop :=
  ∀ k, IsWide E k → i ≠ (E k).lo ∧ i ≠ (E k).hi

theorem three_core_labels_of_support_le_eight {x : Configuration} (E : ExtremaFamily x)
    (hSupport : (endpointSupport E (wideCoordinates E)).card ≤ 8) :
    ∃ q : Fin 3 → Label, Function.Injective q ∧ ∀ i, IsWideCore E (q i) := by
  classical
  let C := (endpointSupport E (wideCoordinates E))ᶜ
  have hC : 3 ≤ C.card := by
    dsimp [C]
    rw [Finset.card_compl]
    norm_num only [Fintype.card_fin]
    omega
  obtain ⟨q, hq, hmem⟩ := exists_fin_injection_into_finset C 3 hC
  refine ⟨q, hq, ?_⟩
  intro i k hk
  have hnot : q i ∉ endpointSupport E (wideCoordinates E) := by
    simpa [C] using hmem i
  constructor
  · intro hlo
    apply hnot
    apply Finset.mem_biUnion.mpr
    exact ⟨k, (mem_wideCoordinates E k).mpr hk, by simp [endpointSet, hlo]⟩
  · intro hhi
    apply hnot
    apply Finset.mem_biUnion.mpr
    exact ⟨k, (mem_wideCoordinates E k).mpr hk, by simp [endpointSet, hhi]⟩

def tripleConfiguration (x : Configuration) (q : Fin 3 → Label) : Fin 3 → Point 5 :=
  fun i => x (q i)

def tripleWidth (x : Configuration) (q : Fin 3 → Label) : ℝ :=
  ∑ k, scalarRange (fun i => x (q i) k) (columnOrders (tripleConfiguration x q) k)

theorem trace_three_eq_range (f : Fin 3 → ℝ) (p : Equiv.Perm (Fin 3)) :
    scalarTrace f p = (2 / 3) * scalarRange f p := by
  have hw (r : Fin 2) : prefixWeight (n := 2) r = 2 / 3 := by
    fin_cases r <;> norm_num [prefixWeight]
  unfold scalarTrace
  simp_rw [hw]
  rw [← Finset.sum_mul, sum_gaps]
  ring

theorem original_triple_width (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 3 → Label) (hq : Function.Injective q) : tripleWidth x q = 3 / 2 := by
  have hy : UnitEquilateral (tripleConfiguration x q) := by
    intro i j hij
    exact hx (q i) (q j) (fun heq => hij (hq heq))
  have ht := unit_equilateral_actual_totalTrace (tripleConfiguration x q) hy
  have hs : (∑ k, columnTrace (tripleConfiguration x q)
      (columnOrders (tripleConfiguration x q)) k) = (2 / 3) * tripleWidth x q := by
    unfold columnTrace tripleWidth tripleConfiguration
    simp_rw [trace_three_eq_range]
    rw [Finset.mul_sum]
  rw [hs] at ht
  norm_num only [Nat.cast_ofNat] at ht
  linarith

theorem subconfiguration_range_le_box {m n d : ℕ} (x : Fin n → Point d)
    (q : Fin (m + 1) → Fin n) (k : Fin d) (p : Equiv.Perm (Fin (m + 1)))
    (a b : ℝ) (hbox : ∀ i, a ≤ x (q i) k ∧ x (q i) k ≤ b) :
    scalarRange (fun i => x (q i) k) p ≤ b - a := by
  have hlo := (hbox (p 0)).1
  have hhi := (hbox (p (Fin.last m))).2
  unfold scalarRange
  linarith

theorem three_core_labels_force_excess_le_one (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 3 → Label) (hq : Function.Injective q)
    (hCore : ∀ i, IsWideCore (actualExtrema x) (q i)) : Profiles.wideExcess x ≤ 1 := by
  classical
  have hcol (k : Coordinate) :
      scalarRange (fun i => x (q i) k) (columnOrders (tripleConfiguration x q) k) ≤
        1 / 2 - if IsWide (actualExtrema x) k then excess (actualExtrema x) k else 0 := by
    by_cases hw : IsWide (actualExtrema x) k
    · rw [if_pos hw]
      have hbox (i : Fin 3) :
          x (actualExtrema x k).hi k - 1 / 2 ≤ x (q i) k ∧
            x (q i) k ≤ x (actualExtrema x k).lo k + 1 / 2 :=
        (actualExtrema x k).wide_inner_bounds hx hw (q i)
          (hCore i k hw).1 (hCore i k hw).2
      have h := subconfiguration_range_le_box x q k
        (columnOrders (tripleConfiguration x q) k)
        (x (actualExtrema x k).hi k - 1 / 2)
        (x (actualExtrema x k).lo k + 1 / 2) hbox
      dsimp [excess, CoordinateExtrema.range]
      linarith
    · rw [if_neg hw]
      have h := subconfiguration_range_le_box x q k
        (columnOrders (tripleConfiguration x q) k)
        (x (actualExtrema x k).lo k) (x (actualExtrema x k).hi k)
        (fun i => (actualExtrema x k).bound_all (q i))
      have hn : (actualExtrema x k).range ≤ 1 / 2 := le_of_not_gt hw
      dsimp [CoordinateExtrema.range] at hn
      linarith
  have hsum := Finset.sum_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset Coordinate)) => hcol k)
  have hExcess : (∑ k, if IsWide (actualExtrema x) k then excess (actualExtrema x) k else 0) =
      Profiles.wideExcess x := by
    rw [← actual_wide_excess_eq]
    simp [wideCoordinates, Finset.sum_filter]
  change tripleWidth x q ≤ ∑ k : Coordinate,
    (1 / 2 - if IsWide (actualExtrema x) k then excess (actualExtrema x) k else 0) at hsum
  rw [Finset.sum_sub_distrib, hExcess, original_triple_width x hx q hq] at hsum
  norm_num at hsum
  linarith

end
end Kusner5.ForestMatching
