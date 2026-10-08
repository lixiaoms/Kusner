import Kusner5.QuartetProjection

/-!
Positive physical slots and actual outsider faces. A zero-width coordinate is
excluded from slot counts but is never excluded from original tail equations.
-/

namespace Kusner5

open scoped BigOperators
open QuartetGeometry

noncomputable section

def positiveQuartetSlots (x : Configuration) (q : Fin 4 → Label)
    (t : Fin 3) : Finset Coordinate := by
  classical
  exact Finset.univ.filter (fun k => quartetPartition x q k = t ∧
    0 < quartetHalfWidth x q k)

def allPositiveQuartetSlots (x : Configuration) (q : Fin 4 → Label) :
    Finset Coordinate := by
  classical
  exact Finset.univ.filter (fun k => 0 < quartetHalfWidth x q k)

theorem mem_positiveQuartetSlots (x : Configuration) (q : Fin 4 → Label)
    (t : Fin 3) (k : Coordinate) :
    k ∈ positiveQuartetSlots x q t ↔
      quartetPartition x q k = t ∧ 0 < quartetHalfWidth x q k := by
  classical
  simp only [positiveQuartetSlots, Finset.mem_filter, Finset.mem_univ, true_and]

theorem quartet_type_halfwidth_sum (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q) (t : Fin 3) :
    (∑ k, if quartetPartition x q k = t then quartetHalfWidth x q k else 0) =
      1 / 4 - quartetSingletonWidth x q 0 / 2 := by
  have hs : (∑ k, if quartetPartition x q k = t then quartetHalfWidth x q k else 0) =
      quartetBalancedWidth x q t / 2 := by
    unfold quartetBalancedWidth
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hkt : quartetPartition x q k = t
    · simp only [if_pos hkt, quartetHalfWidth_gap, div_eq_mul_inv]
    · simp only [if_neg hkt, zero_mul]
  rw [hs, (quartet_equal_cut_totals x hx q hq).2 t]
  ring

theorem sum_positive_quartet_halfwidths (x : Configuration)
    (q : Fin 4 → Label) (t : Fin 3) :
    (∑ k ∈ positiveQuartetSlots x q t, quartetHalfWidth x q k) =
      ∑ k, if quartetPartition x q k = t then quartetHalfWidth x q k else 0 := by
  classical
  simp only [positiveQuartetSlots, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases ht : quartetPartition x q k = t
  · by_cases hp : 0 < quartetHalfWidth x q k
    · simp only [ht, hp, and_self, ite_true]
    · have hz : quartetHalfWidth x q k = 0 :=
        le_antisymm (le_of_not_gt hp) (quartetHalfWidth_nonneg x q k)
      simp only [hz, ite_self]
  · simp only [ht, false_and, ite_false]

/-- All three balanced types contain a true positive physical slot under the
contradiction assumption. -/
theorem positive_quartet_type_nonempty (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q)
    (hb : quartetSingletonWidth x q 0 < 1 / 24) (t : Fin 3) :
    (positiveQuartetSlots x q t).Nonempty := by
  classical
  have hs := quartet_type_halfwidth_sum x hx q hq t
  rw [← sum_positive_quartet_halfwidths] at hs
  have hp : 0 < ∑ k ∈ positiveQuartetSlots x q t, quartetHalfWidth x q k := by
    linarith
  by_contra hn
  have he : positiveQuartetSlots x q t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  rw [he, Finset.sum_empty] at hp
  linarith

/-- This is a count of the original five physical slots, not feature cuts. -/
theorem sum_positive_quartet_type_cards (x : Configuration) (q : Fin 4 → Label) :
    (∑ t : Fin 3, (positiveQuartetSlots x q t).card) =
      (allPositiveQuartetSlots x q).card := by
  classical
  have hc (t : Fin 3) : (positiveQuartetSlots x q t).card =
      ∑ k : Coordinate, if quartetPartition x q k = t ∧
        0 < quartetHalfWidth x q k then (1 : ℕ) else 0 := by
    simp [positiveQuartetSlots, Finset.sum_filter]
  have hca : (allPositiveQuartetSlots x q).card =
      ∑ k : Coordinate, if 0 < quartetHalfWidth x q k then (1 : ℕ) else 0 := by
    simp [allPositiveQuartetSlots, Finset.sum_filter]
  simp_rw [hc]
  rw [hca, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hp : 0 < quartetHalfWidth x q k
  · simp only [hp, and_true]
    simp
  · simp only [hp, and_false, ite_false, Finset.sum_const_zero]

theorem positive_quartet_slot_total_le_five (x : Configuration) (q : Fin 4 → Label) :
    (∑ t : Fin 3, (positiveQuartetSlots x q t).card) ≤ 5 := by
  rw [sum_positive_quartet_type_cards]
  have h := Finset.card_le_card (Finset.subset_univ (allPositiveQuartetSlots x q))
  simpa only [Finset.card_univ, Fintype.card_fin] using h

/-- In the 311 and 221 allocations every physical coordinate has positive
width, so touching an active box face is a genuine section-boundary condition. -/
theorem quartet_all_halfwidths_pos_of_five_slots (x : Configuration)
    (q : Fin 4 → Label)
    (hfive : (∑ t : Fin 3, (positiveQuartetSlots x q t).card) = 5) :
    ∀ k, 0 < quartetHalfWidth x q k := by
  classical
  have hc : (allPositiveQuartetSlots x q).card = 5 := by
    rw [← sum_positive_quartet_type_cards]
    exact hfive
  have he : allPositiveQuartetSlots x q = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa only [hc, Finset.card_univ, Fintype.card_fin] using (le_refl 5)
  intro k
  have hk : k ∈ allPositiveQuartetSlots x q := by rw [he]; exact Finset.mem_univ _
  exact (Finset.mem_filter.mp hk).2

theorem quartet_outsider_type_sum_abs_le_singleton (x : Configuration)
    (hx : UnitEquilateral x) (q : Fin 4 → Label) (hq : Function.Injective q)
    (j : Label) (hj : ∀ i, j ≠ q i) (t : Fin 3) :
    |quartetTypeSum x q j t| ≤ quartetSingletonWidth x q 0 := by
  have hA0 := quartetAgreement_bounds x hx q hq j 0
  have hA1 := quartetAgreement_bounds x hx q hq j 1
  have hA2 := quartetAgreement_bounds x hx q hq j 2
  have hA3 := quartetAgreement_bounds x hx q hq j 3
  rw [(quartet_outsider_equations x hx q hq j hj).2 t]
  apply abs_le.mpr
  fin_cases t <;> norm_num [tetrahedralSign, Fin.sum_univ_succ] <;>
    constructor <;> linarith [hA0.1, hA0.2, hA1.1, hA1.2,
      hA2.1, hA2.2, hA3.1, hA3.2]

theorem quartet_outsider_tail_mass_pos (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q) (j : Label)
    (hj : ∀ i, j ≠ q i) : 0 < l1mass (quartetTail x q j) := by
  have hA0 := (quartetAgreement_bounds x hx q hq j 0).1
  have hA1 := (quartetAgreement_bounds x hx q hq j 1).1
  have hA2 := (quartetAgreement_bounds x hx q hq j 2).1
  have hA3 := (quartetAgreement_bounds x hx q hq j 3).1
  rw [(quartet_outsider_equations x hx q hq j hj).1]
  dsimp [agreementMass]
  linarith [quartetSingletonWidth_nonneg x q 0]

theorem quartet_nonzero_tail_reflected_face (x : Configuration)
    (q : Fin 4 → Label) (j : Label) (k : Coordinate)
    (ht : quartetTail x q j k ≠ 0) :
    |quartetReflectedClamp x q j k| = quartetHalfWidth x q k := by
  unfold quartetReflectedClamp
  rw [abs_mul, quartetReflection_abs, one_mul]
  rcases lt_or_gt_of_ne ht with hn | hp
  · rw [quartetTail_neg_face x q j k hn, abs_neg,
      abs_of_nonneg (quartetHalfWidth_nonneg x q k)]
  · rw [quartetTail_pos_face x q j k hp,
      abs_of_nonneg (quartetHalfWidth_nonneg x q k)]

/-- Sorting the three actual slot counts yields the complete four possible
positive allocations. The physical coordinate total remains five. -/
theorem original_quartet_positive_slot_classification (x : Configuration)
    (hx : UnitEquilateral x) (q : Fin 4 → Label) (hq : Function.Injective q)
    (hb : quartetSingletonWidth x q 0 < 1 / 24) :
    ∃ p : Equiv.Perm (Fin 3),
      ((positiveQuartetSlots x q (p 0)).card = 1 ∧
       (positiveQuartetSlots x q (p 1)).card = 1 ∧
       (positiveQuartetSlots x q (p 2)).card = 1) ∨
      ((positiveQuartetSlots x q (p 0)).card = 1 ∧
       (positiveQuartetSlots x q (p 1)).card = 1 ∧
       (positiveQuartetSlots x q (p 2)).card = 2) ∨
      ((positiveQuartetSlots x q (p 0)).card = 1 ∧
       (positiveQuartetSlots x q (p 1)).card = 1 ∧
       (positiveQuartetSlots x q (p 2)).card = 3) ∨
      ((positiveQuartetSlots x q (p 0)).card = 1 ∧
       (positiveQuartetSlots x q (p 1)).card = 2 ∧
       (positiveQuartetSlots x q (p 2)).card = 2) := by
  classical
  let f : Fin 3 → ℝ := fun t => ((positiveQuartetSlots x q t).card : ℝ)
  let p := actualOrder f
  have h01 : (positiveQuartetSlots x q (p 0)).card ≤
      (positiveQuartetSlots x q (p 1)).card := by
    have h := actualOrder_monotone f (by decide : (0 : Fin 3) ≤ 1)
    change ((positiveQuartetSlots x q (p 0)).card : ℝ) ≤
      ((positiveQuartetSlots x q (p 1)).card : ℝ) at h
    exact_mod_cast h
  have h12 : (positiveQuartetSlots x q (p 1)).card ≤
      (positiveQuartetSlots x q (p 2)).card := by
    have h := actualOrder_monotone f (by decide : (1 : Fin 3) ≤ 2)
    change ((positiveQuartetSlots x q (p 1)).card : ℝ) ≤
      ((positiveQuartetSlots x q (p 2)).card : ℝ) at h
    exact_mod_cast h
  have hpositive (t : Fin 3) : 1 ≤ (positiveQuartetSlots x q t).card := by
    have hp := Finset.card_pos.mpr (positive_quartet_type_nonempty x hx q hq hb t)
    omega
  have hsum := positive_quartet_slot_total_le_five x q
  have hperm := sum_perm p (fun t => (positiveQuartetSlots x q t).card)
  rw [← hperm] at hsum
  norm_num [Fin.sum_univ_succ] at hsum
  refine ⟨p, ?_⟩
  have hp0 := hpositive (p 0)
  have hp1 := hpositive (p 1)
  have hp2 := hpositive (p 2)
  omega

theorem sum_positive_quartet_reflected_clamp (x : Configuration)
    (q : Fin 4 → Label) (j : Label) (t : Fin 3) :
    (∑ k ∈ positiveQuartetSlots x q t, quartetReflectedClamp x q j k) =
      quartetTypeSum x q j t := by
  classical
  change (∑ k ∈ positiveQuartetSlots x q t, quartetReflectedClamp x q j k) =
    ∑ k, if quartetPartition x q k = t then quartetReflectedClamp x q j k else 0
  simp only [positiveQuartetSlots, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases ht : quartetPartition x q k = t
  · by_cases hp : 0 < quartetHalfWidth x q k
    · simp only [ht, hp, and_self, ite_true]
    · have hz : quartetHalfWidth x q k = 0 :=
        le_antisymm (le_of_not_gt hp) (quartetHalfWidth_nonneg x q k)
      have hv := quartetReflectedClamp_bounds x q j k
      have hv0 : quartetReflectedClamp x q j k = 0 := by rw [hz] at hv; linarith [hv.1, hv.2]
      simp only [ht, hp, hv0, and_false, ite_false, ite_true]
  · simp only [ht, false_and, ite_false]

/-- A positive singleton-type slot cannot carry a true outsider tail under
the small-b assumption. No claim is made about zero-width tail coordinates. -/
theorem quartet_singleton_slot_tail_zero (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q)
    (hb : quartetSingletonWidth x q 0 < 1 / 24) (j : Label)
    (hj : ∀ i, j ≠ q i) (t : Fin 3)
    (hcard : (positiveQuartetSlots x q t).card = 1)
    (k : Coordinate) (hk : k ∈ positiveQuartetSlots x q t) :
    quartetTail x q j k = 0 := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have hak : k = a := by rw [ha] at hk; exact Finset.mem_singleton.mp hk
  have hQ : quartetTypeSum x q j t = quartetReflectedClamp x q j k := by
    rw [← sum_positive_quartet_reflected_clamp, ha]
    simpa only [Finset.sum_singleton, hak]
  have hL : quartetHalfWidth x q k = 1 / 4 - quartetSingletonWidth x q 0 / 2 := by
    have hs := quartet_type_halfwidth_sum x hx q hq t
    rw [← sum_positive_quartet_halfwidths, ha, Finset.sum_singleton] at hs
    simpa only [hak] using hs
  by_contra ht
  have hface := quartet_nonzero_tail_reflected_face x q j k ht
  have hbound := quartet_outsider_type_sum_abs_le_singleton x hx q hq j hj t
  rw [hQ, hface, hL] at hbound
  linarith

/-- In the two full five-slot allocations, every outsider has a genuine face
on an active double/triple type. Its positive tail mass is original evidence. -/
theorem original_quartet_outsider_active_face (x : Configuration)
    (hx : UnitEquilateral x) (q : Fin 4 → Label) (hq : Function.Injective q)
    (hb : quartetSingletonWidth x q 0 < 1 / 24)
    (hfive : (∑ t : Fin 3, (positiveQuartetSlots x q t).card) = 5)
    (j : Label) (hj : ∀ i, j ≠ q i) :
    ∃ k : Coordinate,
      k ∈ positiveQuartetSlots x q (quartetPartition x q k) ∧
      2 ≤ (positiveQuartetSlots x q (quartetPartition x q k)).card ∧
      |quartetReflectedClamp x q j k| = quartetHalfWidth x q k := by
  classical
  have hmass := quartet_outsider_tail_mass_pos x hx q hq j hj
  have hex : ∃ k, quartetTail x q j k ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hz : l1mass (quartetTail x q j) = 0 := by simp [l1mass, hn]
    linarith
  obtain ⟨k, ht⟩ := hex
  have hk : k ∈ positiveQuartetSlots x q (quartetPartition x q k) :=
    (mem_positiveQuartetSlots x q _ k).mpr
      ⟨rfl, quartet_all_halfwidths_pos_of_five_slots x q hfive k⟩
  have hcpos : 1 ≤ (positiveQuartetSlots x q (quartetPartition x q k)).card := by
    have hp : 0 < (positiveQuartetSlots x q (quartetPartition x q k)).card :=
      Finset.card_pos.mpr ⟨k, hk⟩
    omega
  have hcne : (positiveQuartetSlots x q (quartetPartition x q k)).card ≠ 1 := by
    intro hc
    exact ht (quartet_singleton_slot_tail_zero x hx q hq hb j hj _ hc k hk)
  exact ⟨k, hk, by omega, quartet_nonzero_tail_reflected_face x q j k ht⟩

private theorem exists_other_finset_member {α : Type*} [DecidableEq α]
    (S : Finset α) (i : S) (hS : 2 ≤ S.card) : ∃ j : S, j ≠ i := by
  classical
  have hcard : 0 < (S.erase i.val).card := by
    rw [Finset.card_erase_of_mem i.property]
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
  refine ⟨⟨j, (Finset.mem_erase.mp hj).2⟩, ?_⟩
  intro heq
  exact (Finset.mem_erase.mp hj).1 (congrArg Subtype.val heq)

private theorem extension_sum {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (f : S → ℝ) :
    (∑ k, if hk : k ∈ S then f ⟨k, hk⟩ else 0) = ∑ k : S, f k := by
  classical
  let g : α → ℝ := fun k => if hk : k ∈ S then f ⟨k, hk⟩ else 0
  have hsub : (∑ k ∈ S, g k) = ∑ k, g k := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro k _ hnot
    exact dif_neg hnot
  calc
    _ = ∑ k, g k := rfl
    _ = ∑ k ∈ S, g k := hsub.symm
    _ = ∑ k : S, g k.val := (sum_over_finset S g).symm
    _ = ∑ k : S, f k := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [g, dif_pos k.property]

private theorem supported_partition_sum {α τ : Type*} [Fintype α] [Fintype τ]
    (tag : α → τ) (f : τ → α → ℝ)
    (hsupport : ∀ t k, tag k ≠ t → f t k = 0) :
    (∑ k, f (tag k) k) = ∑ t, ∑ k, f t k := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  symm
  apply Finset.sum_eq_single (tag k)
  · intro t _ hne
    exact hsupport t k (Ne.symm hne)
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ (tag k)))

/-- Exact paid projections on a genuine active type face in the 311/221
allocations. The alternative vertex in the dominant-width case belongs to
the SAME positive slot subtype; a zero-width or foreign slot cannot certify
this boundary. -/
theorem exists_original_quartet_face_projection (x : Configuration)
    (hx : UnitEquilateral x) (q : Fin 4 → Label) (hq : Function.Injective q)
    (hb : quartetSingletonWidth x q 0 < 1 / 24)
    (hfive : (∑ t : Fin 3, (positiveQuartetSlots x q t).card) = 5)
    (j : Label) (hj : ∀ i, j ≠ q i) :
    ∃ z : Point 5,
      (∀ k, -quartetHalfWidth x q k ≤ z k ∧ z k ≤ quartetHalfWidth x q k) ∧
      (∀ t : Fin 3, (∑ k, if quartetPartition x q k = t then z k else 0) = 0) ∧
      l1dist z (quartetReflectedClamp x q j) =
        agreementDisplacement (quartetAgreement x q j) ∧
      ∃ k : Coordinate, 0 < quartetHalfWidth x q k ∧
        2 ≤ (positiveQuartetSlots x q (quartetPartition x q k)).card ∧
        |z k| = quartetHalfWidth x q k := by
  classical
  obtain ⟨k0, hk0, hc0, hface0⟩ :=
    original_quartet_outsider_active_face x hx q hq hb hfive j hj
  let tag := quartetPartition x q
  let S := positiveQuartetSlots x q
  let L (t : Fin 3) : S t → ℝ := fun k => quartetHalfWidth x q k.val
  let v (t : Fin 3) : S t → ℝ := fun k => quartetReflectedClamp x q j k.val
  let t0 := tag k0
  let i0 : S t0 := ⟨k0, hk0⟩
  have hL (t : Fin 3) (k : S t) : 0 ≤ L t k := quartetHalfWidth_nonneg x q k.val
  have hv (t : Fin 3) : InSymmetricBox (L t) (v t) :=
    fun k => quartetReflectedClamp_bounds x q j k.val
  have hp (t : Fin 3) :
      ∃ a : S t → ℝ, InSymmetricBox (L t) a ∧ (∑ k, a k) = 0 ∧
        (∑ k, |a k - v t k|) = |∑ k, v t k| ∧
        (t = t0 → ∃ k : S t, |a k| = L t k) := by
    by_cases ht : t = t0
    · subst t
      have hother : ∃ k : S t0, k ≠ i0 := exists_other_finset_member (S t0) i0 hc0
      obtain ⟨a, ha, hs, hd, hf⟩ :=
        zero_sum_face_projection (L t0) (v t0) (hL t0) (hv t0) i0 hface0 hother
      exact ⟨a, ha, hs, hd, fun _ => hf⟩
    · obtain ⟨a, ha, hs, hd⟩ := zero_sum_box_projection (L t) (v t) (hL t) (hv t)
      exact ⟨a, ha, hs, hd, fun heq => False.elim (ht heq)⟩
  choose a ha hs hd hf using hp
  let A : Fin 3 → Coordinate → ℝ := fun t k =>
    if hk : k ∈ S t then a t ⟨k, hk⟩ else 0
  have hpos := quartet_all_halfwidths_pos_of_five_slots x q hfive
  have hmem (t : Fin 3) (k : Coordinate) : k ∈ S t ↔ tag k = t := by
    rw [mem_positiveQuartetSlots]
    constructor
    · exact And.left
    · intro ht
      exact ⟨ht, hpos k⟩
  have hAzero (t : Fin 3) (k : Coordinate) (hne : tag k ≠ t) : A t k = 0 := by
    have hk : k ∉ S t := fun h => hne ((hmem t k).mp h)
    exact dif_neg hk
  have hAbounds (k : Coordinate) :
      -quartetHalfWidth x q k ≤ A (tag k) k ∧ A (tag k) k ≤ quartetHalfWidth x q k := by
    have hk : k ∈ S (tag k) := (hmem _ k).mpr rfl
    simpa only [A, dif_pos hk, L] using ha (tag k) ⟨k, hk⟩
  have hAsum (t : Fin 3) : (∑ k, A t k) = 0 := by
    change (∑ k, if hk : k ∈ S t then a t ⟨k, hk⟩ else 0) = 0
    rw [extension_sum]
    exact hs t
  have hvsum (t : Fin 3) : (∑ k : S t, v t k) = quartetTypeSum x q j t := by
    rw [sum_over_finset (S t) (quartetReflectedClamp x q j)]
    exact sum_positive_quartet_reflected_clamp x q j t
  let V : Fin 3 → Coordinate → ℝ := fun t k =>
    if tag k = t then quartetReflectedClamp x q j k else 0
  have hDsum (t : Fin 3) : (∑ k, |A t k - V t k|) =
      |quartetTypeSum x q j t| := by
    have hpoint (k : Coordinate) : |A t k - V t k| =
        if hk : k ∈ S t then |a t ⟨k, hk⟩ - v t ⟨k, hk⟩| else 0 := by
      by_cases hk : k ∈ S t
      · have ht := (hmem t k).mp hk
        simp only [A, V, dif_pos hk, if_pos ht, v]
      · have ht : tag k ≠ t := fun heq => hk ((hmem t k).mpr heq)
        simp only [A, V, dif_neg hk, if_neg ht, sub_self, abs_zero]
    simp_rw [hpoint]
    rw [extension_sum (S t) (fun k : S t => |a t k - v t k|), hd t, hvsum t]
  let z : Point 5 := fun k => A (tag k) k
  refine ⟨z, hAbounds, ?_, ?_, ?_⟩
  · intro t
    have hpoint (k : Coordinate) : (if quartetPartition x q k = t then z k else 0) = A t k := by
      by_cases ht : tag k = t
      · change (if tag k = t then A (tag k) k else 0) = A t k
        rw [if_pos ht, ht]
      · change (if tag k = t then A (tag k) k else 0) = A t k
        rw [if_neg ht, hAzero t k ht]
    simp_rw [hpoint]
    exact hAsum t
  · have hsupport (t : Fin 3) (k : Coordinate) (hne : tag k ≠ t) :
        |A t k - V t k| = 0 := by
      rw [hAzero t k hne]
      simp only [V, if_neg hne, sub_self, abs_zero]
    have hsplit := supported_partition_sum tag (fun t k => |A t k - V t k|) hsupport
    calc
      l1dist z (quartetReflectedClamp x q j) = ∑ k, |A (tag k) k - V (tag k) k| := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [z, V, ite_true]
      _ = ∑ t, ∑ k, |A t k - V t k| := hsplit
      _ = ∑ t, |quartetTypeSum x q j t| := by simp_rw [hDsum]
      _ = agreementDisplacement (quartetAgreement x q j) :=
        quartet_outsider_displacement x hx q hq j hj
  · obtain ⟨k, hkface⟩ := hf t0 rfl
    have hkt : tag k.val = t0 := (hmem t0 k.val).mp k.property
    refine ⟨k.val, hpos k.val, ?_, ?_⟩
    · change 2 ≤ (S (tag k.val)).card
      rw [hkt]
      exact hc0
    · change |A (tag k.val) k.val| = L t0 k
      rw [hkt]
      simpa only [A, dif_pos k.property] using hkface

end
end Kusner5
