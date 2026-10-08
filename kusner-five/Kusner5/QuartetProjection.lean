import Kusner5.QuartetOutsiders

/-!
Literal coordinate reflections, exact paid type-wise projection, and
same-original-outsider pair and cycle estimates. A projection is never
asserted to be equilateral or to preserve the original full point distances.
-/

namespace Kusner5

open scoped BigOperators
open QuartetGeometry

noncomputable section

def quartetReflectedClamp (x : Configuration) (q : Fin 4 → Label) (j : Label) :
    Point 5 := fun k => quartetReflection x q k * quartetClamp x q j k

theorem quartetReflection_abs (x : Configuration) (q : Fin 4 → Label)
    (k : Coordinate) : |quartetReflection x q k| = 1 :=
  quartetOwnerSign_abs x q k 0

/-- An actual coordinate sign reflection preserves the explicit physical
distance, without an arbitrary plane isometry premise. -/
theorem quartet_reflection_isometry (x : Configuration) (q : Fin 4 → Label)
    (p r : Point 5) :
    l1dist (fun k => quartetReflection x q k * p k)
      (fun k => quartetReflection x q k * r k) = l1dist p r := by
  unfold l1dist
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_sub, abs_mul, quartetReflection_abs, one_mul]

theorem quartetReflectedClamp_bounds (x : Configuration) (q : Fin 4 → Label)
    (j : Label) (k : Coordinate) :
    -quartetHalfWidth x q k ≤ quartetReflectedClamp x q j k ∧
      quartetReflectedClamp x q j k ≤ quartetHalfWidth x q k := by
  apply abs_le.mp
  unfold quartetReflectedClamp
  rw [abs_mul, quartetReflection_abs, one_mul]
  exact abs_le.mpr (quartetClamp_bounds x q j k)

private theorem sum_partition_supported {ι τ : Type*} [Fintype ι] [Fintype τ]
    (tag : ι → τ) (f : τ → ι → ℝ)
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

/-- The box projection is constructed for each actual balanced type. Slots
of zero width have zero auxiliary coordinates but their tails remain in the
original agreement and co-occurrence ledgers. -/
theorem exists_quartet_type_projection (x : Configuration) (q : Fin 4 → Label)
    (j : Label) :
    ∃ z : Point 5,
      (∀ k, -quartetHalfWidth x q k ≤ z k ∧ z k ≤ quartetHalfWidth x q k) ∧
      (∀ t : Fin 3, (∑ k, if quartetPartition x q k = t then z k else 0) = 0) ∧
      l1dist z (quartetReflectedClamp x q j) =
        ∑ t, |quartetTypeSum x q j t| := by
  classical
  let tag := quartetPartition x q
  let L : Fin 3 → Coordinate → ℝ := fun t k =>
    if tag k = t then quartetHalfWidth x q k else 0
  let v : Fin 3 → Coordinate → ℝ := fun t k =>
    if tag k = t then quartetReflectedClamp x q j k else 0
  have hL (t : Fin 3) (k : Coordinate) : 0 ≤ L t k := by
    dsimp [L]
    split_ifs
    · exact quartetHalfWidth_nonneg x q k
    · exact le_rfl
  have hv (t : Fin 3) : InSymmetricBox (L t) (v t) := by
    intro k
    dsimp [L, v]
    split_ifs
    · exact quartetReflectedClamp_bounds x q j k
    · constructor <;> norm_num
  have hp (t : Fin 3) := zero_sum_box_projection (L t) (v t) (hL t) (hv t)
  choose a ha hs hd using hp
  have hzoutside (t : Fin 3) (k : Coordinate) (hne : tag k ≠ t) : a t k = 0 := by
    have h := ha t k
    simp only [L, if_neg hne, neg_zero] at h
    linarith [h.1, h.2]
  let z : Point 5 := fun k => a (tag k) k
  refine ⟨z, ?_, ?_, ?_⟩
  · intro k
    simpa only [L, z, ite_true] using ha (tag k) k
  · intro t
    have hpoint (k : Coordinate) :
        (if quartetPartition x q k = t then z k else 0) = a t k := by
      by_cases hkt : tag k = t
      · simp only [tag] at hkt
        simp only [hkt, ite_true, z, show tag k = t from hkt]
      · have hz := hzoutside t k hkt
        change (if tag k = t then z k else 0) = a t k
        rw [if_neg hkt, hz]
    simp_rw [hpoint]
    exact hs t
  · have hsupport (t : Fin 3) (k : Coordinate) (hne : tag k ≠ t) :
        |a t k - v t k| = 0 := by
      rw [hzoutside t k hne]
      simp only [v, if_neg hne, sub_self, abs_zero]
    have hsplit := sum_partition_supported tag
      (fun t k => |a t k - v t k|) hsupport
    have hvsum (t : Fin 3) : (∑ k, v t k) = quartetTypeSum x q j t := rfl
    calc
      l1dist z (quartetReflectedClamp x q j) =
          ∑ k, |a (tag k) k - v (tag k) k| := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [z, v, ite_true]
      _ = ∑ t, ∑ k, |a t k - v t k| := hsplit
      _ = ∑ t, |quartetTypeSum x q j t| := by
        simp_rw [hd, hvsum]

theorem exists_original_quartet_projection (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q) (j : Label)
    (hj : ∀ i, j ≠ q i) :
    ∃ z : Point 5,
      (∀ k, -quartetHalfWidth x q k ≤ z k ∧ z k ≤ quartetHalfWidth x q k) ∧
      (∀ t : Fin 3, (∑ k, if quartetPartition x q k = t then z k else 0) = 0) ∧
      l1dist z (quartetReflectedClamp x q j) =
        agreementDisplacement (quartetAgreement x q j) := by
  obtain ⟨z, hb, hs, hp⟩ := exists_quartet_type_projection x q j
  exact ⟨z, hb, hs, hp.trans (quartet_outsider_displacement x hx q hq j hj)⟩

def quartetOutsiderSet (q : Fin 4 → Label) : Finset Label :=
  (Finset.univ.image q)ᶜ

/-- Exactly seven other ORIGINAL labels are extracted from the same array. -/
theorem exists_seven_original_outsiders (q : Fin 4 → Label)
    (hq : Function.Injective q) :
    ∃ r : Fin 7 → Label, Function.Injective r ∧ ∀ j i, r j ≠ q i := by
  classical
  have himage : (Finset.univ.image q).card = 4 := by
    rw [Finset.card_image_of_injective _ hq]
    simp
  have hcard : (quartetOutsiderSet q).card = 7 := by
    unfold quartetOutsiderSet
    rw [Finset.card_compl, himage]
    norm_num
  obtain ⟨r, hr, hmem⟩ := exists_fin_injection_into_finset (quartetOutsiderSet q) 7
    (by rw [hcard])
  refine ⟨r, hr, ?_⟩
  intro j i hij
  have hnot : r j ∉ Finset.univ.image q := by
    simpa only [quartetOutsiderSet, Finset.mem_compl] using hmem j
  apply hnot
  rw [hij]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- Original pair separation after paying the two actual projection moves.
The supplied moves are intermediate geometric obligations, never final
Kusner theorem hypotheses. -/
theorem quartet_projected_pair_lower (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q) (j l : Label)
    (hj : ∀ i, j ≠ q i) (hl : ∀ i, l ≠ q i) (hjl : j ≠ l)
    (zj zl : Point 5)
    (hpj : l1dist zj (quartetReflectedClamp x q j) ≤
      agreementDisplacement (quartetAgreement x q j))
    (hpl : l1dist zl (quartetReflectedClamp x q l) ≤
      agreementDisplacement (quartetAgreement x q l))
    (p s : Bool) (i h : Fin 4)
    (hformj : formValue p i (quartetAgreement x q j) =
      agreementBudget (quartetAgreement x q j))
    (hforml : formValue s h (quartetAgreement x q l) =
      agreementBudget (quartetAgreement x q l)) :
    1 / 2 - quartetSingletonWidth x q 0 -
      quartetSingletonWidth x q 0 * formPairCap p s i h ≤ l1dist zj zl := by
  have hsplit := quartet_pair_split x q j l
  rw [hx j l hjl,
    l1dist_overlap_identity (quartetTail x q j) (quartetTail x q l)] at hsplit
  have hmj := (quartet_outsider_equations x hx q hq j hj).1
  have hml := (quartet_outsider_equations x hx q hq l hl).1
  have href : l1dist (quartetClamp x q j) (quartetClamp x q l) =
      l1dist (quartetReflectedClamp x q j) (quartetReflectedClamp x q l) :=
    (quartet_reflection_isometry x q (quartetClamp x q j) (quartetClamp x q l)).symm
  have ht1 := physical_triangle (quartetReflectedClamp x q j) zj
    (quartetReflectedClamp x q l)
  have ht2 := physical_triangle zj zl (quartetReflectedClamp x q l)
  rw [l1dist_comm (quartetReflectedClamp x q j) zj] at ht1
  have hco := quartet_original_cooccurrence x hx q hq j l
  have htable := form_pair_bound (quartetSingletonWidth_nonneg x q 0)
    (quartetAgreement x q j) (quartetAgreement x q l)
    (quartetAgreement_bounds x hx q hq j) (quartetAgreement_bounds x hx q hq l)
    p s i h
  rw [hformj, hforml] at htable
  rw [href] at hsplit
  dsimp [agreementBudget] at htable
  linarith

theorem formPairCap_le_five (p s : Bool) (i h : Fin 4) :
    formPairCap p s i h ≤ 5 := by
  unfold formPairCap
  split_ifs <;> norm_num

/-- The paid original projections retain a strict positive pair separation
when the original singleton total is below the contradiction threshold. -/
theorem quartet_projected_pair_separation (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q) (j l : Label)
    (hj : ∀ i, j ≠ q i) (hl : ∀ i, l ≠ q i) (hjl : j ≠ l)
    (zj zl : Point 5)
    (hpj : l1dist zj (quartetReflectedClamp x q j) ≤
      agreementDisplacement (quartetAgreement x q j))
    (hpl : l1dist zl (quartetReflectedClamp x q l) ≤
      agreementDisplacement (quartetAgreement x q l)) :
    1 / 2 - 6 * quartetSingletonWidth x q 0 ≤ l1dist zj zl := by
  obtain ⟨p, i, hfi⟩ := agreementBudget_has_form (quartetAgreement x q j)
  obtain ⟨s, ih, hfh⟩ := agreementBudget_has_form (quartetAgreement x q l)
  have hLower := quartet_projected_pair_lower x hx q hq j l hj hl hjl zj zl
    hpj hpl p s i ih hfi hfh
  have hc := mul_le_mul_of_nonneg_left (formPairCap_le_five p s i ih)
    (quartetSingletonWidth_nonneg x q 0)
  linarith

theorem nextSeven_ne_self (i : Fin 7) : i ≠ nextSeven i := by
  fin_cases i <;> decide

/-- Any cyclic order of the SAME seven actual outsiders has the lower chord
budget. One indexed form is chosen consistently per node, including ties. -/
theorem original_projected_seven_cycle_lower (x : Configuration)
    (hx : UnitEquilateral x) (q : Fin 4 → Label) (hq : Function.Injective q)
    (r : Fin 7 → Label) (hr : Function.Injective r) (hout : ∀ j i, r j ≠ q i)
    (z : Fin 7 → Point 5)
    (hpaid : ∀ j, l1dist (z j) (quartetReflectedClamp x q (r j)) ≤
      agreementDisplacement (quartetAgreement x q (r j))) :
    7 / 2 - 40 * quartetSingletonWidth x q 0 ≤
      ∑ j, l1dist (z j) (z (nextSeven j)) := by
  classical
  let b := quartetSingletonWidth x q 0
  have hb : 0 ≤ b := quartetSingletonWidth_nonneg x q 0
  have hf (j : Fin 7) := agreementBudget_has_form (quartetAgreement x q (r j))
  choose p u hform using hf
  let w : Fin 7 → ℝ := fun j =>
    b * formPairCap (p j) (p (nextSeven j)) (u j) (u (nextSeven j))
  have hbase (j : Fin 7) : w j ≤ 5 * b := by
    have h := mul_le_mul_of_nonneg_left
      (formPairCap_le_five (p j) (p (nextSeven j)) (u j) (u (nextSeven j))) hb
    simpa only [w, mul_comm] using h
  have hagree (j : Fin 7) (hp : p j = p (nextSeven j))
      (hu : u j = u (nextSeven j)) : w j ≤ 3 * b := by
    have hc : formPairCap (p j) (p (nextSeven j)) (u j) (u (nextSeven j)) ≤ 3 := by
      rw [hp, hu]
      cases p (nextSeven j) <;> norm_num [formPairCap]
    have h := mul_le_mul_of_nonneg_left hc hb
    simpa only [w, mul_comm] using h
  have hchange (j : Fin 7) (hu : u j ≠ u (nextSeven j)) : w j ≤ 4 * b := by
    simp only [w, formPairCap, if_neg hu]
    rw [mul_comm]
  have hcycle := odd_cycle_cap33 hb p u w hbase hagree hchange
  have hpoint (j : Fin 7) : 1 / 2 - b - w j ≤
      l1dist (z j) (z (nextSeven j)) := by
    exact quartet_projected_pair_lower x hx q hq (r j) (r (nextSeven j))
      (hout j) (hout (nextSeven j))
      (fun hij => nextSeven_ne_self j (hr hij)) (z j) (z (nextSeven j))
      (hpaid j) (hpaid (nextSeven j)) (p j) (p (nextSeven j))
      (u j) (u (nextSeven j)) (hform j) (hform (nextSeven j))
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 7))) =>
    hpoint j)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hs
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat] at hs
  change 7 / 2 - 40 * b ≤ _
  linarith

end
end Kusner5
