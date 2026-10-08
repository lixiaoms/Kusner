import Kusner5.Quartet
import Kusner5.CutEnergy

/-!
The seven outsiders remain actual original labels. All agreements and type
sums below are computed from the literal physical clamp and tail functions.
In particular zero-middle-width coordinates retain their original tails.
-/

namespace Kusner5

open scoped BigOperators
open QuartetGeometry

noncomputable section

theorem scalarOverlap_le_abs_left (a b : ℝ) : scalarOverlap a b ≤ |a| := by
  have h : |b| ≤ |a - b| + |a| := by
    simpa only [sub_zero, abs_sub_comm] using abs_sub_le b a 0
  dsimp [scalarOverlap]
  linarith

theorem scalarOverlap_le_abs_right (a b : ℝ) : scalarOverlap a b ≤ |b| := by
  rw [scalarOverlap_comm]
  exact scalarOverlap_le_abs_left b a

@[simp] theorem scalarOverlap_neg_neg (a b : ℝ) :
    scalarOverlap (-a) (-b) = scalarOverlap a b := by
  unfold scalarOverlap
  rw [show -a - -b = -(a - b) by ring]
  simp only [abs_neg]

theorem scalarOverlap_double_min_lower (u a b : ℝ) :
    scalarOverlap u a + scalarOverlap u b - |u| ≤
      min (scalarOverlap u a) (scalarOverlap u b) := by
  apply le_min
  · linarith [scalarOverlap_le_abs_left u b]
  · linarith [scalarOverlap_le_abs_left u a]

private theorem disjoint_owner_min_sum_nonneg {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (hu : ∀ i j, i ≠ j → u i * u j ≤ 0)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∑ i, min (scalarOverlap (u i) a) (scalarOverlap (u i) b)) ≤
      scalarOverlap a b := by
  classical
  by_cases hp : ∃ i, 0 < u i
  · obtain ⟨i0, hi0⟩ := hp
    have hn (i : ι) (hine : i ≠ i0) : u i ≤ 0 := by
      nlinarith [hu i i0 hine]
    have hsum : (∑ i, min (scalarOverlap (u i) a) (scalarOverlap (u i) b)) =
        min (scalarOverlap (u i0) a) (scalarOverlap (u i0) b) := by
      apply Finset.sum_eq_single i0
      · intro i _ hine
        rw [scalarOverlap_eq_zero_of_opposite (hn i hine) ha]
        exact min_eq_left (scalarOverlap_nonneg (u i) b)
      · intro hi
        exact False.elim (hi (Finset.mem_univ i0))
    rw [hsum, scalarOverlap_eq_min_nonneg ha hb]
    have hA : scalarOverlap (u i0) a ≤ a := by
      simpa only [abs_of_nonneg ha] using scalarOverlap_le_abs_right (u i0) a
    have hB : scalarOverlap (u i0) b ≤ b := by
      simpa only [abs_of_nonneg hb] using scalarOverlap_le_abs_right (u i0) b
    exact le_min
      ((min_le_left _ _).trans hA) ((min_le_right _ _).trans hB)
  · have hn : ∀ i, u i ≤ 0 := by
      intro i
      exact le_of_not_gt (fun hi => hp ⟨i, hi⟩)
    have hzero : (∑ i, min (scalarOverlap (u i) a) (scalarOverlap (u i) b)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [scalarOverlap_eq_zero_of_opposite (hn i) ha]
      exact min_eq_left (scalarOverlap_nonneg (u i) b)
    rw [hzero]
    exact scalarOverlap_nonneg a b

private theorem owner_min_zero_of_opposite (u a b : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 0) :
    min (scalarOverlap u a) (scalarOverlap u b) = 0 := by
  rcases le_total u 0 with hu | hu
  · rw [scalarOverlap_eq_zero_of_opposite hu ha]
    exact min_eq_left (scalarOverlap_nonneg u b)
  · have hz : scalarOverlap u b = 0 := by
      rw [scalarOverlap_comm]
      exact scalarOverlap_eq_zero_of_opposite hb hu
    rw [hz]
    exact min_eq_right (scalarOverlap_nonneg u a)

/-- Signed supports may occupy opposite rays of one physical coordinate.
The same physical overlap is counted only once. -/
theorem disjoint_owner_min_sum {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (hu : ∀ i j, i ≠ j → u i * u j ≤ 0) (a b : ℝ) :
    (∑ i, min (scalarOverlap (u i) a) (scalarOverlap (u i) b)) ≤
      scalarOverlap a b := by
  classical
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · exact disjoint_owner_min_sum_nonneg u hu a b ha hb
  · have hzero : (∑ i, min (scalarOverlap (u i) a) (scalarOverlap (u i) b)) = 0 := by
      simp only [owner_min_zero_of_opposite _ _ _ ha hb, Finset.sum_const_zero]
    rw [hzero]
    exact scalarOverlap_nonneg a b
  · have hzero : (∑ i, min (scalarOverlap (u i) a) (scalarOverlap (u i) b)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [min_comm]
      exact owner_min_zero_of_opposite (u i) b a hb ha
    rw [hzero]
    exact scalarOverlap_nonneg a b
  · have hun : ∀ i j, i ≠ j → (-u i) * (-u j) ≤ 0 := by
      intro i j hij
      simpa only [neg_mul_neg] using hu i j hij
    have h := disjoint_owner_min_sum_nonneg (fun i => -u i) hun (-a) (-b)
      (neg_nonneg.mpr ha) (neg_nonneg.mpr hb)
    simpa only [scalarOverlap_neg_neg] using h

/-- Co-occurrence is derived from actual disjoint signed owner supports and
their literal masses, with no independent cut or projected-distance premise. -/
theorem disjoint_owner_cooccurrence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → κ → ℝ) (a b : κ → ℝ) (B : ℝ)
    (hMass : ∀ i, l1mass (u i) = B)
    (hDisjoint : ∀ i j, i ≠ j → ∀ k, u i k * u j k ≤ 0) :
    (∑ i, max 0 (l1overlap (u i) a + l1overlap (u i) b - B)) ≤
      l1overlap a b := by
  let T : ι → ℝ := fun i => ∑ k,
    min (scalarOverlap (u i k) (a k)) (scalarOverlap (u i k) (b k))
  have hT0 (i : ι) : 0 ≤ T i := by
    apply Finset.sum_nonneg
    intro k _
    exact le_min (scalarOverlap_nonneg _ _) (scalarOverlap_nonneg _ _)
  have hT (i : ι) : l1overlap (u i) a + l1overlap (u i) b - B ≤ T i := by
    have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset κ)) =>
      scalarOverlap_double_min_lower (u i k) (a k) (b k))
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at h
    change l1overlap (u i) a + l1overlap (u i) b - l1mass (u i) ≤ T i at h
    rw [hMass i] at h
    exact h
  calc
    _ ≤ ∑ i, T i :=
      Finset.sum_le_sum (fun i _ => max_le (hT0 i) (hT i))
    _ = ∑ k, ∑ i,
        min (scalarOverlap (u i k) (a k)) (scalarOverlap (u i k) (b k)) :=
      Finset.sum_comm
    _ ≤ l1overlap a b := by
      apply Finset.sum_le_sum
      intro k _
      exact disjoint_owner_min_sum (fun i => u i k)
        (fun i j hij => hDisjoint i j hij k) (a k) (b k)

def quartetAgreement (x : Configuration) (q : Fin 4 → Label) (j : Label) :
    Fin 4 → ℝ := fun i => l1overlap (quartetTail x q (q i)) (quartetTail x q j)

def quartetTypeSum (x : Configuration) (q : Fin 4 → Label) (j : Label) :
    Fin 3 → ℝ := fun t => ∑ k,
      if quartetPartition x q k = t then
        quartetReflection x q k * quartetClamp x q j k else 0

theorem quartetAgreement_bounds (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q) (j : Label) (i : Fin 4) :
    0 ≤ quartetAgreement x q j i ∧
      quartetAgreement x q j i ≤ quartetSingletonWidth x q 0 := by
  constructor
  · unfold quartetAgreement l1overlap
    exact Finset.sum_nonneg (fun k _ => scalarOverlap_nonneg _ _)
  · have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset Coordinate)) =>
      scalarOverlap_le_abs_left (quartetTail x q (q i) k) (quartetTail x q j k))
    change quartetAgreement x q j i ≤ l1mass (quartetTail x q (q i)) at h
    rw [quartetTail_selected_mass, (quartet_equal_cut_totals x hx q hq).1 i] at h
    exact h

theorem quartet_original_cooccurrence (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q) (j l : Label) :
    (∑ i, max 0 (quartetAgreement x q j i + quartetAgreement x q l i -
      quartetSingletonWidth x q 0)) ≤
      l1overlap (quartetTail x q j) (quartetTail x q l) := by
  apply disjoint_owner_cooccurrence
    (fun i => quartetTail x q (q i)) (quartetTail x q j) (quartetTail x q l)
    (quartetSingletonWidth x q 0)
  · intro i
    rw [quartetTail_selected_mass, (quartet_equal_cut_totals x hx q hq).1 i]
  · exact fun i h hij k => quartetTail_owner_signed_disjoint x q i h hij k

private theorem abs_signed_box_difference (s L y : ℝ) (hs : |s| = 1)
    (hy : -L ≤ y ∧ y ≤ L) : |s * L - y| = L - s * y := by
  by_cases hp : 0 ≤ s
  · have hs1 : s = 1 := by simpa only [abs_of_nonneg hp] using hs
    rw [hs1, one_mul, one_mul, abs_of_nonneg (sub_nonneg.mpr hy.2)]
  · have hs1 : s = -1 := by
      rw [abs_of_nonpos (le_of_not_ge hp)] at hs
      linarith
    rw [hs1]
    have hneg : -1 * L - y ≤ 0 := by linarith [hy.1]
    rw [abs_of_nonpos hneg]
    ring

theorem quartet_owner_clamp_distance (x : Configuration) (q : Fin 4 → Label)
    (j : Label) (i : Fin 4) :
    l1dist (quartetClamp x q (q i)) (quartetClamp x q j) =
      (∑ k, quartetHalfWidth x q k) -
        ∑ t, (tetrahedralSign i t : ℝ) * quartetTypeSum x q j t := by
  have hpoint (k : Coordinate) :
      |quartetClamp x q (q i) k - quartetClamp x q j k| =
        quartetHalfWidth x q k - quartetOwnerSign x q k i * quartetClamp x q j k := by
    rw [quartetClamp_selected]
    exact abs_signed_box_difference _ _ _ (quartetOwnerSign_abs x q k i)
      (quartetClamp_bounds x q j k)
  have hgroup : (∑ t, (tetrahedralSign i t : ℝ) * quartetTypeSum x q j t) =
      ∑ k, quartetOwnerSign x q k i * quartetClamp x q j k := by
    simp only [quartetTypeSum, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [quartetOwnerSign_tetrahedral]
    simp only [mul_ite, mul_zero]
    simp
    ring
  unfold l1dist
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, hgroup]

theorem quartet_total_halfwidth (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q) :
    (∑ k, quartetHalfWidth x q k) = 3 / 4 -
      3 * quartetSingletonWidth x q 0 / 2 := by
  have hsum : (∑ t, quartetBalancedWidth x q t) =
      ∑ k, quartetGap x q k 1 := by
    unfold quartetBalancedWidth
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simp
  have heq := (quartet_equal_cut_totals x hx q hq).2
  simp_rw [heq] at hsum
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat] at hsum
  have hdiv : (∑ k, quartetHalfWidth x q k) =
      (∑ k, quartetGap x q k 1) / 2 := by
    simp only [quartetHalfWidth_gap, div_eq_mul_inv, ← Finset.sum_mul]
  rw [hdiv]
  linarith

/-- Each equation here is one of the actual four owner/outsider unit pairs. -/
theorem quartet_original_cross_equation (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q) (j : Label)
    (hj : ∀ i, j ≠ q i) (i : Fin 4) :
    1 = quartetSingletonWidth x q 0 + (∑ k, quartetHalfWidth x q k) +
      l1mass (quartetTail x q j) -
        (∑ t, (tetrahedralSign i t : ℝ) * quartetTypeSum x q j t) -
      2 * quartetAgreement x q j i := by
  have hp := quartet_pair_split x q (q i) j
  rw [hx (q i) j (Ne.symm (hj i)), quartet_owner_clamp_distance,
    l1dist_overlap_identity, quartetTail_selected_mass,
    (quartet_equal_cut_totals x hx q hq).1 i] at hp
  change 1 = _ + (_ + _ - 2 * quartetAgreement x q j i) at hp
  linarith

/-- The original cross equations force the tail mass and each signed type
sum. There is no common original norm or circumcenter hypothesis. -/
theorem quartet_outsider_equations (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q) (j : Label)
    (hj : ∀ i, j ≠ q i) :
    l1mass (quartetTail x q j) = 1 / 4 + quartetSingletonWidth x q 0 / 2 +
      agreementMass (quartetAgreement x q j) / 2 ∧
    ∀ t, quartetTypeSum x q j t =
      -(∑ i, (tetrahedralSign i t : ℝ) * quartetAgreement x q j i) / 2 := by
  have h0 := quartet_original_cross_equation x hx q hq j hj 0
  have h1 := quartet_original_cross_equation x hx q hq j hj 1
  have h2 := quartet_original_cross_equation x hx q hq j hj 2
  have h3 := quartet_original_cross_equation x hx q hq j hj 3
  have hL := quartet_total_halfwidth x hx q hq
  rw [hL] at h0 h1 h2 h3
  norm_num [tetrahedralSign, Fin.sum_univ_succ] at h0 h1 h2 h3
  constructor
  · unfold agreementMass
    linarith
  · intro t
    fin_cases t <;> norm_num [tetrahedralSign, Fin.sum_univ_succ] <;> linarith

theorem tetrahedral_displacement_identity (A : Fin 4 → ℝ) :
    (∑ t : Fin 3, |-(∑ i, (tetrahedralSign i t : ℝ) * A i) / 2|) =
      agreementDisplacement A := by
  have h0 : -(∑ i, (tetrahedralSign i 0 : ℝ) * A i) =
      -(A 0 + A 1 - A 2 - A 3) := by
    norm_num [tetrahedralSign, Fin.sum_univ_succ]
    ring
  have h1 : -(∑ i, (tetrahedralSign i 1 : ℝ) * A i) =
      -(A 0 - A 1 + A 2 - A 3) := by
    norm_num [tetrahedralSign, Fin.sum_univ_succ]
    ring
  have h2 : -(∑ i, (tetrahedralSign i 2 : ℝ) * A i) =
      -(A 0 - A 1 - A 2 + A 3) := by
    norm_num [tetrahedralSign, Fin.sum_univ_succ]
    ring
  have hs : (∑ t : Fin 3, |-(∑ i, (tetrahedralSign i t : ℝ) * A i) / 2|) =
      |-(∑ i, (tetrahedralSign i 0 : ℝ) * A i) / 2| +
      |-(∑ i, (tetrahedralSign i 1 : ℝ) * A i) / 2| +
      |-(∑ i, (tetrahedralSign i 2 : ℝ) * A i) / 2| := by
    have hthree (f : Fin 3 → ℝ) : (∑ t, f t) = f 0 + f 1 + f 2 := by
      simp [Fin.sum_univ_succ] <;> ring
    exact hthree (fun t => |-(∑ i, (tetrahedralSign i t : ℝ) * A i) / 2|)
  rw [hs, h0, h1, h2]
  simp only [abs_div, abs_neg]
  norm_num [agreementDisplacement]
  ring

theorem quartet_outsider_displacement (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q) (j : Label)
    (hj : ∀ i, j ≠ q i) :
    (∑ t, |quartetTypeSum x q j t|) =
      agreementDisplacement (quartetAgreement x q j) := by
  simp_rw [(quartet_outsider_equations x hx q hq j hj).2]
  exact tetrahedral_displacement_identity _

end
end Kusner5
