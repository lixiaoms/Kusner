import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Kusner5.CutEnergy
import Kusner5.RangeGeometry

/-!
Exact eleven-label prefix profiles for the original five-dimensional argument.
All entries below are indexed ordered positions, never new geometric labels.
The actual-label transport and original-distance energy bridge live in CutEnergy.
-/

namespace Kusner5.Profiles

open scoped BigOperators

noncomputable section

def s1 : ℝ := 9 / 22
def s2 : ℝ := 2 / 11
def s3 : ℝ := (62 - 10 * Real.sqrt 37) / 22
def s4 : ℝ := (82 - 6 * Real.sqrt 185) / 22
def s5 : ℝ := (94 - 42 * Real.sqrt 5) / 22

def shiftedAlpha : ℝ := s1 + s2 + s3 + s4 + s5
def rootAlpha : ℝ :=
  (190 - 12 * Real.sqrt 5 - 24 * Real.sqrt 3 -
    8 * Real.sqrt 42 - 4 * Real.sqrt 210) / 11
def modifiedAlpha : ℝ :=
  (204 - 6 * Real.sqrt 14 - 4 * Real.sqrt 91 -
    4 * Real.sqrt 221 - 4 * Real.sqrt 323) / 22
def modifiedBeta : ℝ := 1 / 2 + modifiedAlpha
def nonwideAlpha : ℝ := (260 - 20 * Real.sqrt 31 - 4 * Real.sqrt 1054) / 33
def nonwideCap : ℝ := nonwideAlpha + 1 / 3

theorem shiftedAlpha_eq_sum : shiftedAlpha = s1 + s2 + s3 + s4 + s5 := rfl

theorem shiftedAlpha_eq_radicals :
    shiftedAlpha = (251 - 10 * Real.sqrt 37 - 6 * Real.sqrt 185 -
      42 * Real.sqrt 5) / 22 := by
  unfold shiftedAlpha s1 s2 s3 s4 s5
  ring

theorem modifiedBeta_eq_radicals :
    modifiedBeta = (215 - 6 * Real.sqrt 14 - 4 * Real.sqrt 91 -
      4 * Real.sqrt 221 - 4 * Real.sqrt 323) / 22 := by
  unfold modifiedBeta modifiedAlpha
  ring

theorem nonwideCap_eq_radicals :
    nonwideCap = (271 - 20 * Real.sqrt 31 - 4 * Real.sqrt 1054) / 33 := by
  unfold nonwideCap nonwideAlpha
  ring

/-- Strict root comparisons use only ordered-field arithmetic and `sq_sqrt`. -/
theorem sqrt_gt_rat {a b : ℝ} (hb : 0 ≤ b) (hba : b ^ 2 < a) :
    b < Real.sqrt a := by
  have ha : 0 ≤ a := le_trans (sq_nonneg b) (le_of_lt hba)
  have hs := Real.sq_sqrt ha
  have hn := Real.sqrt_nonneg a
  nlinarith

theorem sqrt_lt_rat {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : a < b ^ 2) :
    Real.sqrt a < b := by
  have hs := Real.sq_sqrt ha
  have hn := Real.sqrt_nonneg a
  nlinarith

theorem sq_lt_sq_of_nonneg_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    a ^ 2 < b ^ 2 := by
  have h₁ : 0 < b - a := by linarith
  have h₂ : 0 < b + a := by linarith
  have hp := mul_pos h₁ h₂
  nlinarith

/-- A kernel arithmetic helper for exact products of nonnegative radicals. -/
theorem sqrt_product_eq_of_sq {a b c f : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf : 0 ≤ f)
    (h : a * b = f ^ 2 * c) :
    Real.sqrt a * Real.sqrt b = f * Real.sqrt c := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hsc := Real.sq_sqrt hc
  have hL : (Real.sqrt a * Real.sqrt b) ^ 2 = a * b := by
    rw [mul_pow, hsa, hsb]
  have hR : (f * Real.sqrt c) ^ 2 = f ^ 2 * c := by
    rw [mul_pow, hsc]
  have hLP : 0 ≤ Real.sqrt a * Real.sqrt b :=
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have hRP : 0 ≤ f * Real.sqrt c := mul_nonneg hf (Real.sqrt_nonneg c)
  have heq : (Real.sqrt a * Real.sqrt b) ^ 2 = (f * Real.sqrt c) ^ 2 := by
    rw [hL, hR, h]
  have hz : (Real.sqrt a * Real.sqrt b - f * Real.sqrt c) *
      (Real.sqrt a * Real.sqrt b + f * Real.sqrt c) = 0 := by
    nlinarith [heq]
  rcases mul_eq_zero.mp hz with hd | hs
  · linarith
  · linarith

theorem sqrt37_lower : (608276 / 100000 : ℝ) < Real.sqrt 37 := by
  exact sqrt_gt_rat (by norm_num) (by norm_num)
theorem sqrt185_lower : (1360147 / 100000 : ℝ) < Real.sqrt 185 := by
  exact sqrt_gt_rat (by norm_num) (by norm_num)
theorem sqrt5_lower : (223606 / 100000 : ℝ) < Real.sqrt 5 := by
  exact sqrt_gt_rat (by norm_num) (by norm_num)

theorem shiftedAlpha_lt_two_thirds : shiftedAlpha < 2 / 3 := by
  rw [shiftedAlpha_eq_radicals]
  nlinarith [sqrt37_lower, sqrt185_lower, sqrt5_lower]

theorem rootAlpha_lt_43_40 : rootAlpha < 43 / 40 := by
  have h5 : (2236 / 1000 : ℝ) < Real.sqrt 5 :=
    sqrt_gt_rat (by norm_num) (by norm_num)
  have h3 : (1732 / 1000 : ℝ) < Real.sqrt 3 :=
    sqrt_gt_rat (by norm_num) (by norm_num)
  have h42 : (6480 / 1000 : ℝ) < Real.sqrt 42 :=
    sqrt_gt_rat (by norm_num) (by norm_num)
  have h210 : (14491 / 1000 : ℝ) < Real.sqrt 210 :=
    sqrt_gt_rat (by norm_num) (by norm_num)
  unfold rootAlpha
  nlinarith

theorem modifiedBeta_lt_21_20 : modifiedBeta < 21 / 20 := by
  have h14 : (37416 / 10000 : ℝ) < Real.sqrt 14 :=
    sqrt_gt_rat (by norm_num) (by norm_num)
  have h91 : (95393 / 10000 : ℝ) < Real.sqrt 91 :=
    sqrt_gt_rat (by norm_num) (by norm_num)
  have h221 : (148660 / 10000 : ℝ) < Real.sqrt 221 :=
    sqrt_gt_rat (by norm_num) (by norm_num)
  have h323 : (179722 / 10000 : ℝ) < Real.sqrt 323 :=
    sqrt_gt_rat (by norm_num) (by norm_num)
  rw [modifiedBeta_eq_radicals]
  nlinarith

theorem nonwideCap_lt_10_11 : nonwideCap < 10 / 11 := by
  have h31 : (139 / 25 : ℝ) < Real.sqrt 31 :=
    sqrt_gt_rat (by norm_num) (by norm_num)
  have h1054 : (1623 / 50 : ℝ) < Real.sqrt 1054 :=
    sqrt_gt_rat (by norm_num) (by norm_num)
  rw [nonwideCap_eq_radicals]
  nlinarith

theorem s3_eq_sq : s3 = (Real.sqrt 37 - 5) ^ 2 / 22 := by
  have hs := Real.sq_sqrt (by norm_num : 0 ≤ (37 : ℝ))
  unfold s3
  nlinarith

theorem sqrt37_mul_sqrt5 : Real.sqrt 37 * Real.sqrt 5 = Real.sqrt 185 := by
  simpa using (sqrt_product_eq_of_sq
    (a := 37) (b := 5) (c := 185) (f := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

theorem s4_eq_sq : s4 = (3 * Real.sqrt 5 - Real.sqrt 37) ^ 2 / 22 := by
  have h37 := Real.sq_sqrt (by norm_num : 0 ≤ (37 : ℝ))
  have h5 := Real.sq_sqrt (by norm_num : 0 ≤ (5 : ℝ))
  unfold s4
  nlinarith [sqrt37_mul_sqrt5]

theorem s5_eq_sq : s5 = (7 - 3 * Real.sqrt 5) ^ 2 / 22 := by
  have h5 := Real.sq_sqrt (by norm_num : 0 ≤ (5 : ℝ))
  unfold s5
  nlinarith

theorem shifted_third_increment_pos : 0 < Real.sqrt 37 - 5 := by
  have h : (6 : ℝ) < Real.sqrt 37 := sqrt_gt_rat (by norm_num) (by norm_num)
  linarith

theorem shifted_fourth_increment_gt : (5 / 8 : ℝ) < 3 * Real.sqrt 5 - Real.sqrt 37 := by
  have h5 : (559 / 250 : ℝ) < Real.sqrt 5 :=
    sqrt_gt_rat (by norm_num) (by norm_num)
  have h37 : Real.sqrt 37 < (6083 / 1000 : ℝ) :=
    sqrt_lt_rat (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem shifted_fifth_increment_pos : 0 < 7 - 3 * Real.sqrt 5 := by
  have h : Real.sqrt 5 < (7 / 3 : ℝ) :=
    sqrt_lt_rat (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem s3_lt_121_2200 : s3 < 121 / 2200 := by
  have h37 : Real.sqrt 37 < (61 / 10 : ℝ) :=
    sqrt_lt_rat (by norm_num) (by norm_num) (by norm_num)
  have hd : Real.sqrt 37 - 5 < (11 / 10 : ℝ) := by linarith
  have hs := sq_lt_sq_of_nonneg_lt (le_of_lt shifted_third_increment_pos) hd
  rw [s3_eq_sq]
  nlinarith

theorem s4_lt_9_352 : s4 < 9 / 352 := by
  have h37 : (6 : ℝ) < Real.sqrt 37 := sqrt_gt_rat (by norm_num) (by norm_num)
  have h5 : Real.sqrt 5 < (9 / 4 : ℝ) :=
    sqrt_lt_rat (by norm_num) (by norm_num) (by norm_num)
  have hd : 3 * Real.sqrt 5 - Real.sqrt 37 < (3 / 4 : ℝ) := by linarith
  have hp : 0 ≤ 3 * Real.sqrt 5 - Real.sqrt 37 := by
    linarith [shifted_fourth_increment_gt]
  have hs := sq_lt_sq_of_nonneg_lt hp hd
  rw [s4_eq_sq]
  nlinarith

theorem s5_lt_2_275 : s5 < 2 / 275 := by
  have h5 : (11 / 5 : ℝ) < Real.sqrt 5 := sqrt_gt_rat (by norm_num) (by norm_num)
  have hd : 7 - 3 * Real.sqrt 5 < (2 / 5 : ℝ) := by linarith
  have hs := sq_lt_sq_of_nonneg_lt (le_of_lt shifted_fifth_increment_pos) hd
  rw [s5_eq_sq]
  nlinarith

theorem s3_gt_one_twentieth : (1 / 20 : ℝ) < s3 := by
  have h37 : (121 / 20 : ℝ) < Real.sqrt 37 :=
    sqrt_gt_rat (by norm_num) (by norm_num)
  have hd : (21 / 20 : ℝ) < Real.sqrt 37 - 5 := by linarith
  have hs := sq_lt_sq_of_nonneg_lt (by norm_num : 0 ≤ (21 / 20 : ℝ)) hd
  rw [s3_eq_sq]
  nlinarith

theorem s4_gt_one_sixtieth : (1 / 60 : ℝ) < s4 := by
  have hs := sq_lt_sq_of_nonneg_lt (by norm_num : 0 ≤ (5 / 8 : ℝ))
    shifted_fourth_increment_gt
  rw [s4_eq_sq]
  nlinarith

theorem s5_pos : 0 < s5 := by
  rw [s5_eq_sq]
  exact div_pos (pow_pos shifted_fifth_increment_pos 2) (by norm_num)

theorem s5_lt_s4 : s5 < s4 := by
  linarith [s5_lt_2_275, s4_gt_one_sixtieth]
theorem s4_lt_s3 : s4 < s3 := by
  linarith [s4_lt_9_352, s3_gt_one_twentieth]
theorem s3_lt_s2 : s3 < s2 := by
  unfold s2
  linarith [s3_lt_121_2200]
theorem s2_lt_s1 : s2 < s1 := by norm_num [s2, s1]

theorem s3_lt_one_sixteenth : s3 < 1 / 16 := by linarith [s3_lt_121_2200]
theorem s4_lt_one_thirtysecond : s4 < 1 / 32 := by linarith [s4_lt_9_352]
theorem s5_lt_one_128 : s5 < 1 / 128 := by linarith [s5_lt_2_275]

/-- The position before a cut is 0-based; a cut r contains positions 0,...,r. -/
def cutWeight (r : Fin 10) : ℝ :=
  ((r.val + 1 : ℕ) : ℝ) * ((10 - r.val : ℕ) : ℝ) / 11

def profileIncrement (h : Fin 12 → ℝ) (i : Fin 11) : ℝ :=
  h i.succ - h i.castSucc

theorem sum_profileIncrement (h : Fin 12 → ℝ) :
    (∑ i : Fin 11, profileIncrement h i) = h (Fin.last 11) - h 0 := by
  simpa [profileIncrement, gap, scalarRange] using
    (sum_gaps (n := 11) h (Equiv.refl (Fin 12)))

def orderedPrefix (v : Fin 11 → ℝ) (r : Fin 10) : ℝ :=
  ∑ i : Fin 11, if i.val ≤ r.val then v i else 0

def halfSquaredNorm (v : Fin 11 → ℝ) : ℝ := (1 / 2) * ∑ i, (v i) ^ 2

def shiftedHeightNumerator : Fin 12 → ℝ :=
  ![0, 3, 5, Real.sqrt 37, 3 * Real.sqrt 5, 7, 7,
    3 * Real.sqrt 5, Real.sqrt 37, 5, 3, 0]
def shiftedHeight (i : Fin 12) : ℝ := shiftedHeightNumerator i / Real.sqrt 22
def shiftedVector (i : Fin 11) : ℝ :=
  (shiftedHeightNumerator i.succ - shiftedHeightNumerator i.castSucc) / Real.sqrt 22

theorem shiftedVector_eq_increment (i : Fin 11) :
    shiftedVector i = profileIncrement shiftedHeight i := by
  simp [shiftedVector, profileIncrement, shiftedHeight, sub_div]

theorem sum_shiftedVector_zero : (∑ i : Fin 11, shiftedVector i) = 0 := by
  simp_rw [shiftedVector_eq_increment]
  rw [sum_profileIncrement]
  norm_num [shiftedHeight, shiftedHeightNumerator]

theorem orderedPrefix_shiftedVector (r : Fin 10) :
    orderedPrefix shiftedVector r = shiftedHeight r.castSucc.succ := by
  fin_cases r <;>
    norm_num [orderedPrefix, shiftedVector, shiftedHeight, shiftedHeightNumerator,
      Fin.sum_univ_succ] <;> ring

theorem shiftedHeight_sq (r : Fin 10) :
    shiftedHeight r.castSucc.succ ^ 2 = cutWeight r - 1 / 2 := by
  have h37 := Real.sq_sqrt (by norm_num : 0 ≤ (37 : ℝ))
  have h5 := Real.sq_sqrt (by norm_num : 0 ≤ (5 : ℝ))
  have h22 := Real.sq_sqrt (by norm_num : 0 ≤ (22 : ℝ))
  fin_cases r <;>
    norm_num [shiftedHeight, shiftedHeightNumerator, cutWeight, div_pow, mul_pow,
      h37, h5, h22]

theorem shiftedVector_sq (i : Fin 11) :
    shiftedVector i ^ 2 = ![s1, s2, s3, s4, s5, 0, s5, s4, s3, s2, s1] i := by
  have h37 := Real.sq_sqrt (by norm_num : 0 ≤ (37 : ℝ))
  have h5 := Real.sq_sqrt (by norm_num : 0 ≤ (5 : ℝ))
  have h22 := Real.sq_sqrt (by norm_num : 0 ≤ (22 : ℝ))
  fin_cases i <;>
    norm_num [shiftedVector, shiftedHeightNumerator, s1, s2, s3, s4, s5,
      div_pow, h22] <;> nlinarith [sqrt37_mul_sqrt5]

theorem shiftedVector_halfSquaredNorm : halfSquaredNorm shiftedVector = shiftedAlpha := by
  unfold halfSquaredNorm
  simp_rw [shiftedVector_sq]
  norm_num [Fin.sum_univ_succ, shiftedAlpha]
  ring

def profileEnergy (g : Fin 10 → ℝ) (h : Fin 12 → ℝ) : ℝ :=
  ∑ r, g r * h r.castSucc.succ ^ 2
def profileTrace (g : Fin 10 → ℝ) : ℝ := ∑ r, g r * cutWeight r
def profileRange (g : Fin 10 → ℝ) : ℝ := ∑ r, g r

theorem shifted_profileEnergy (g : Fin 10 → ℝ) :
    profileEnergy g shiftedHeight = profileTrace g - profileRange g / 2 := by
  unfold profileEnergy profileTrace profileRange
  simp_rw [shiftedHeight_sq, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

theorem shifted_trace_le (g : Fin 10 → ℝ)
    (hcap : profileEnergy g shiftedHeight ≤ shiftedAlpha) :
    profileTrace g ≤ profileRange g / 2 + shiftedAlpha := by
  rw [shifted_profileEnergy] at hcap
  linarith

def rootHeightNumerator : Fin 12 → ℝ :=
  ![0, Real.sqrt 10, Real.sqrt 18, Real.sqrt 24, Real.sqrt 28, Real.sqrt 30,
    Real.sqrt 30, Real.sqrt 28, Real.sqrt 24, Real.sqrt 18, Real.sqrt 10, 0]
def rootHeight (i : Fin 12) : ℝ := rootHeightNumerator i / Real.sqrt 11
def rootVector (i : Fin 11) : ℝ :=
  (rootHeightNumerator i.succ - rootHeightNumerator i.castSucc) / Real.sqrt 11

theorem rootVector_eq_increment (i : Fin 11) :
    rootVector i = profileIncrement rootHeight i := by
  simp [rootVector, profileIncrement, rootHeight, sub_div]

theorem sum_rootVector_zero : (∑ i : Fin 11, rootVector i) = 0 := by
  simp_rw [rootVector_eq_increment]
  rw [sum_profileIncrement]
  norm_num [rootHeight, rootHeightNumerator]

theorem orderedPrefix_rootVector (r : Fin 10) :
    orderedPrefix rootVector r = rootHeight r.castSucc.succ := by
  fin_cases r <;>
    norm_num [orderedPrefix, rootVector, rootHeight, rootHeightNumerator,
      Fin.sum_univ_succ] <;> ring

theorem rootHeight_sq (r : Fin 10) :
    rootHeight r.castSucc.succ ^ 2 = cutWeight r := by
  have h10 := Real.sq_sqrt (by norm_num : 0 ≤ (10 : ℝ))
  have h18 := Real.sq_sqrt (by norm_num : 0 ≤ (18 : ℝ))
  have h24 := Real.sq_sqrt (by norm_num : 0 ≤ (24 : ℝ))
  have h28 := Real.sq_sqrt (by norm_num : 0 ≤ (28 : ℝ))
  have h30 := Real.sq_sqrt (by norm_num : 0 ≤ (30 : ℝ))
  have h11 := Real.sq_sqrt (by norm_num : 0 ≤ (11 : ℝ))
  fin_cases r <;>
    norm_num [rootHeight, rootHeightNumerator, cutWeight, div_pow,
      h10, h18, h24, h28, h30, h11]

theorem rootVector_halfSquaredNorm : halfSquaredNorm rootVector = rootAlpha := by
  have h10 := Real.sq_sqrt (by norm_num : 0 ≤ (10 : ℝ))
  have h18 := Real.sq_sqrt (by norm_num : 0 ≤ (18 : ℝ))
  have h24 := Real.sq_sqrt (by norm_num : 0 ≤ (24 : ℝ))
  have h28 := Real.sq_sqrt (by norm_num : 0 ≤ (28 : ℝ))
  have h30 := Real.sq_sqrt (by norm_num : 0 ≤ (30 : ℝ))
  have h11 := Real.sq_sqrt (by norm_num : 0 ≤ (11 : ℝ))
  have h1018 : Real.sqrt 10 * Real.sqrt 18 = 6 * Real.sqrt 5 :=
    sqrt_product_eq_of_sq (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have h1824 : Real.sqrt 18 * Real.sqrt 24 = 12 * Real.sqrt 3 :=
    sqrt_product_eq_of_sq (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have h2428 : Real.sqrt 24 * Real.sqrt 28 = 4 * Real.sqrt 42 :=
    sqrt_product_eq_of_sq (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have h2830 : Real.sqrt 28 * Real.sqrt 30 = 2 * Real.sqrt 210 :=
    sqrt_product_eq_of_sq (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  norm_num [halfSquaredNorm, rootVector, rootHeightNumerator, rootAlpha,
    Fin.sum_univ_succ, div_pow, h11]
  nlinarith [h1018, h1824, h2428, h2830]

theorem rootVector_first_sq : rootVector 0 ^ 2 = 10 / 11 := by
  norm_num [rootVector, rootHeightNumerator, div_pow, Real.sq_sqrt]

theorem rootVector_last_sq : rootVector (Fin.last 10) ^ 2 = 10 / 11 := by
  norm_num [rootVector, rootHeightNumerator, div_pow, Real.sq_sqrt]

theorem root_profileEnergy (g : Fin 10 → ℝ) :
    profileEnergy g rootHeight = profileTrace g := by
  simp only [profileEnergy, rootHeight_sq, profileTrace]

def modifiedHeightNumerator : Fin 12 → ℝ :=
  ![0, 3, Real.sqrt 14, Real.sqrt 26, Real.sqrt 34, Real.sqrt 38,
    Real.sqrt 38, Real.sqrt 34, Real.sqrt 26, Real.sqrt 14, 3, 0]
def modifiedHeight (i : Fin 12) : ℝ := modifiedHeightNumerator i / Real.sqrt 22
def modifiedVector (i : Fin 11) : ℝ :=
  (modifiedHeightNumerator i.succ - modifiedHeightNumerator i.castSucc) / Real.sqrt 22

theorem modifiedVector_eq_increment (i : Fin 11) :
    modifiedVector i = profileIncrement modifiedHeight i := by
  simp [modifiedVector, profileIncrement, modifiedHeight, sub_div]

theorem sum_modifiedVector_zero : (∑ i : Fin 11, modifiedVector i) = 0 := by
  simp_rw [modifiedVector_eq_increment]
  rw [sum_profileIncrement]
  norm_num [modifiedHeight, modifiedHeightNumerator]

theorem orderedPrefix_modifiedVector (r : Fin 10) :
    orderedPrefix modifiedVector r = modifiedHeight r.castSucc.succ := by
  fin_cases r <;>
    norm_num [orderedPrefix, modifiedVector, modifiedHeight, modifiedHeightNumerator,
      Fin.sum_univ_succ] <;> ring

theorem modifiedHeight_sq (r : Fin 10) :
    modifiedHeight r.castSucc.succ ^ 2 = cutWeight r - 1 +
      if r = 0 ∨ r = 9 then 1 / 2 else 0 := by
  have h14 := Real.sq_sqrt (by norm_num : 0 ≤ (14 : ℝ))
  have h26 := Real.sq_sqrt (by norm_num : 0 ≤ (26 : ℝ))
  have h34 := Real.sq_sqrt (by norm_num : 0 ≤ (34 : ℝ))
  have h38 := Real.sq_sqrt (by norm_num : 0 ≤ (38 : ℝ))
  have h22 := Real.sq_sqrt (by norm_num : 0 ≤ (22 : ℝ))
  fin_cases r <;>
    norm_num [modifiedHeight, modifiedHeightNumerator, cutWeight, div_pow,
      h14, h26, h34, h38, h22]

theorem modifiedVector_halfSquaredNorm : halfSquaredNorm modifiedVector = modifiedAlpha := by
  have h14 := Real.sq_sqrt (by norm_num : 0 ≤ (14 : ℝ))
  have h26 := Real.sq_sqrt (by norm_num : 0 ≤ (26 : ℝ))
  have h34 := Real.sq_sqrt (by norm_num : 0 ≤ (34 : ℝ))
  have h38 := Real.sq_sqrt (by norm_num : 0 ≤ (38 : ℝ))
  have h22 := Real.sq_sqrt (by norm_num : 0 ≤ (22 : ℝ))
  have h1426 : Real.sqrt 14 * Real.sqrt 26 = 2 * Real.sqrt 91 :=
    sqrt_product_eq_of_sq (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have h2634 : Real.sqrt 26 * Real.sqrt 34 = 2 * Real.sqrt 221 :=
    sqrt_product_eq_of_sq (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have h3438 : Real.sqrt 34 * Real.sqrt 38 = 2 * Real.sqrt 323 :=
    sqrt_product_eq_of_sq (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  norm_num [halfSquaredNorm, modifiedVector, modifiedHeightNumerator, modifiedAlpha,
    Fin.sum_univ_succ, div_pow, h22]
  nlinarith [h1426, h2634, h3438]

theorem modified_profileEnergy (g : Fin 10 → ℝ) :
    profileEnergy g modifiedHeight = profileTrace g - profileRange g +
      (g 0 + g 9) / 2 := by
  unfold profileEnergy profileTrace profileRange
  simp_rw [modifiedHeight_sq]
  norm_num [Fin.sum_univ_succ]
  ring

def nonwideHeightNumerator : Fin 12 → ℝ :=
  ![0, Real.sqrt 8, Real.sqrt 32, Real.sqrt 50, Real.sqrt 62, Real.sqrt 68,
    Real.sqrt 68, Real.sqrt 62, Real.sqrt 50, Real.sqrt 32, Real.sqrt 8, 0]
def nonwideHeight (i : Fin 12) : ℝ := nonwideHeightNumerator i / Real.sqrt 33
def nonwideVector (i : Fin 11) : ℝ :=
  (nonwideHeightNumerator i.succ - nonwideHeightNumerator i.castSucc) / Real.sqrt 33

theorem nonwideVector_eq_increment (i : Fin 11) :
    nonwideVector i = profileIncrement nonwideHeight i := by
  simp [nonwideVector, profileIncrement, nonwideHeight, sub_div]

theorem sum_nonwideVector_zero : (∑ i : Fin 11, nonwideVector i) = 0 := by
  simp_rw [nonwideVector_eq_increment]
  rw [sum_profileIncrement]
  norm_num [nonwideHeight, nonwideHeightNumerator]

theorem orderedPrefix_nonwideVector (r : Fin 10) :
    orderedPrefix nonwideVector r = nonwideHeight r.castSucc.succ := by
  fin_cases r <;>
    norm_num [orderedPrefix, nonwideVector, nonwideHeight, nonwideHeightNumerator,
      Fin.sum_univ_succ] <;> ring

theorem nonwideHeight_sq (r : Fin 10) :
    nonwideHeight r.castSucc.succ ^ 2 = cutWeight r - 2 / 3 := by
  have h8 := Real.sq_sqrt (by norm_num : 0 ≤ (8 : ℝ))
  have h32 := Real.sq_sqrt (by norm_num : 0 ≤ (32 : ℝ))
  have h50 := Real.sq_sqrt (by norm_num : 0 ≤ (50 : ℝ))
  have h62 := Real.sq_sqrt (by norm_num : 0 ≤ (62 : ℝ))
  have h68 := Real.sq_sqrt (by norm_num : 0 ≤ (68 : ℝ))
  have h33 := Real.sq_sqrt (by norm_num : 0 ≤ (33 : ℝ))
  fin_cases r <;>
    norm_num [nonwideHeight, nonwideHeightNumerator, cutWeight, div_pow,
      h8, h32, h50, h62, h68, h33]

theorem nonwideVector_halfSquaredNorm : halfSquaredNorm nonwideVector = nonwideAlpha := by
  have h8 := Real.sq_sqrt (by norm_num : 0 ≤ (8 : ℝ))
  have h32 := Real.sq_sqrt (by norm_num : 0 ≤ (32 : ℝ))
  have h50 := Real.sq_sqrt (by norm_num : 0 ≤ (50 : ℝ))
  have h62 := Real.sq_sqrt (by norm_num : 0 ≤ (62 : ℝ))
  have h68 := Real.sq_sqrt (by norm_num : 0 ≤ (68 : ℝ))
  have h33 := Real.sq_sqrt (by norm_num : 0 ≤ (33 : ℝ))
  have h832 : Real.sqrt 8 * Real.sqrt 32 = 16 := by
    simpa using (sqrt_product_eq_of_sq (a := 8) (b := 32) (c := 1) (f := 16)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h3250 : Real.sqrt 32 * Real.sqrt 50 = 40 := by
    simpa using (sqrt_product_eq_of_sq (a := 32) (b := 50) (c := 1) (f := 40)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h5062 : Real.sqrt 50 * Real.sqrt 62 = 10 * Real.sqrt 31 :=
    sqrt_product_eq_of_sq (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have h6268 : Real.sqrt 62 * Real.sqrt 68 = 2 * Real.sqrt 1054 :=
    sqrt_product_eq_of_sq (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  norm_num [halfSquaredNorm, nonwideVector, nonwideHeightNumerator, nonwideAlpha,
    Fin.sum_univ_succ, div_pow, h33]
  nlinarith [h832, h3250, h5062, h6268]

theorem nonwide_profileEnergy (g : Fin 10 → ℝ) :
    profileEnergy g nonwideHeight = profileTrace g - (2 / 3) * profileRange g := by
  unfold profileEnergy profileTrace profileRange
  simp_rw [nonwideHeight_sq, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

theorem cutWeight_eq_prefixWeight (r : Fin 10) :
    cutWeight r = prefixWeight (n := 10) r := by
  unfold cutWeight prefixWeight
  have h : r.val ≤ 10 := by
    have := r.isLt
    omega
  rw [Nat.cast_sub h]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  norm_num

theorem profileTrace_gaps (f : Fin 11 → ℝ) (p : Equiv.Perm (Fin 11)) :
    profileTrace (gap f p) = scalarTrace f p := by
  simp only [profileTrace, scalarTrace, cutWeight_eq_prefixWeight]

theorem profileRange_gaps (f : Fin 11 → ℝ) (p : Equiv.Perm (Fin 11)) :
    profileRange (gap f p) = scalarRange f p := sum_gaps f p

/-- Own energy is evaluated after transporting the ordered vector to the
same original labels on which every physical column acts. -/
theorem scalarEnergy_shifted (f : Fin 11 → ℝ) (p : Equiv.Perm (Fin 11)) :
    scalarEnergy f p (transport p shiftedVector) =
      scalarTrace f p - scalarRange f p / 2 := by
  rw [scalarEnergy_transport_eq f p shiftedVector
    (fun r => shiftedHeight r.castSucc.succ) orderedPrefix_shiftedVector]
  change profileEnergy (gap f p) shiftedHeight = _
  rw [shifted_profileEnergy, profileTrace_gaps, profileRange_gaps]

theorem scalarEnergy_root (f : Fin 11 → ℝ) (p : Equiv.Perm (Fin 11)) :
    scalarEnergy f p (transport p rootVector) = scalarTrace f p := by
  rw [scalarEnergy_transport_eq f p rootVector
    (fun r => rootHeight r.castSucc.succ) orderedPrefix_rootVector]
  change profileEnergy (gap f p) rootHeight = _
  rw [root_profileEnergy, profileTrace_gaps]

theorem scalarEnergy_modified (f : Fin 11 → ℝ) (p : Equiv.Perm (Fin 11)) :
    scalarEnergy f p (transport p modifiedVector) = scalarTrace f p -
      scalarRange f p + (gap f p 0 + gap f p 9) / 2 := by
  rw [scalarEnergy_transport_eq f p modifiedVector
    (fun r => modifiedHeight r.castSucc.succ) orderedPrefix_modifiedVector]
  change profileEnergy (gap f p) modifiedHeight = _
  rw [modified_profileEnergy, profileTrace_gaps, profileRange_gaps]

theorem scalarEnergy_nonwide (f : Fin 11 → ℝ) (p : Equiv.Perm (Fin 11)) :
    scalarEnergy f p (transport p nonwideVector) =
      scalarTrace f p - (2 / 3) * scalarRange f p := by
  rw [scalarEnergy_transport_eq f p nonwideVector
    (fun r => nonwideHeight r.castSucc.succ) orderedPrefix_nonwideVector]
  change profileEnergy (gap f p) nonwideHeight = _
  rw [nonwide_profileEnergy, profileTrace_gaps, profileRange_gaps]

theorem shiftedVector_first_sq : shiftedVector 0 ^ 2 = s1 := by
  simpa using shiftedVector_sq (0 : Fin 11)
theorem shiftedVector_last_sq : shiftedVector (Fin.last 10) ^ 2 = s1 := by
  simpa using shiftedVector_sq (Fin.last 10)

theorem rootVector_transport_first_sq (p : Equiv.Perm (Fin 11)) :
    transport p rootVector (p 0) ^ 2 = 10 / 11 := by
  rw [transport_at_order, rootVector_first_sq]
theorem rootVector_transport_last_sq (p : Equiv.Perm (Fin 11)) :
    transport p rootVector (p (Fin.last 10)) ^ 2 = 10 / 11 := by
  rw [transport_at_order, rootVector_last_sq]

theorem profile_columnEnergy_le {d : ℕ} (x : Fin 11 → Point d)
    (hx : UnitEquilateral x) (orders : Fin d → Equiv.Perm (Fin 11))
    (horders : ∀ k, Monotone (fun i => x (orders k i) k))
    (v : Fin 11 → ℝ) (hv : (∑ i, v i) = 0) (a : ℝ)
    (ha : halfSquaredNorm v = a) (k : Fin d) :
    columnEnergy x orders k (transport (orders k) v) ≤ a := by
  have hu : (∑ i, transport (orders k) v i) = 0 := by rw [sum_transport, hv]
  have hc := unit_equilateral_columnEnergy_le x hx orders horders
    (transport (orders k) v) hu k
  rw [sum_transport_sq] at hc
  change columnEnergy x orders k (transport (orders k) v) ≤ halfSquaredNorm v at hc
  rwa [ha] at hc

theorem shifted_columnEnergy {d : ℕ} (x : Fin 11 → Point d)
    (orders : Fin d → Equiv.Perm (Fin 11)) (k : Fin d) :
    columnEnergy x orders k (transport (orders k) shiftedVector) =
      columnTrace x orders k - scalarRange (fun i => x i k) (orders k) / 2 :=
  scalarEnergy_shifted _ _

theorem root_columnEnergy {d : ℕ} (x : Fin 11 → Point d)
    (orders : Fin d → Equiv.Perm (Fin 11)) (k : Fin d) :
    columnEnergy x orders k (transport (orders k) rootVector) =
      columnTrace x orders k := scalarEnergy_root _ _

theorem shifted_columnTrace_le {d : ℕ} (x : Fin 11 → Point d)
    (hx : UnitEquilateral x) (orders : Fin d → Equiv.Perm (Fin 11))
    (horders : ∀ k, Monotone (fun i => x (orders k i) k)) (k : Fin d) :
    columnTrace x orders k ≤ scalarRange (fun i => x i k) (orders k) / 2 +
      shiftedAlpha := by
  have hc := profile_columnEnergy_le x hx orders horders shiftedVector
    sum_shiftedVector_zero shiftedAlpha shiftedVector_halfSquaredNorm k
  rw [shifted_columnEnergy] at hc
  linarith

theorem nonwide_columnTrace_lt {d : ℕ} (x : Fin 11 → Point d)
    (hx : UnitEquilateral x) (orders : Fin d → Equiv.Perm (Fin 11))
    (horders : ∀ k, Monotone (fun i => x (orders k i) k)) (k : Fin d)
    (hw : scalarRange (fun i => x i k) (orders k) ≤ 1 / 2) :
    columnTrace x orders k < 10 / 11 := by
  have hc := profile_columnEnergy_le x hx orders horders nonwideVector
    sum_nonwideVector_zero nonwideAlpha nonwideVector_halfSquaredNorm k
  change scalarEnergy (fun i => x i k) (orders k)
    (transport (orders k) nonwideVector) ≤ nonwideAlpha at hc
  rw [scalarEnergy_nonwide] at hc
  have ht : columnTrace x orders k ≤ nonwideCap := by
    unfold columnTrace nonwideCap
    linarith
  exact lt_of_le_of_lt ht nonwideCap_lt_10_11

/-- The auxiliary outer-bound premise is discharged by RangeGeometry's
original triple lemma in the actual-column wrapper. -/
theorem modified_columnTrace_le_of_outer_bound {d : ℕ} (x : Fin 11 → Point d)
    (hx : UnitEquilateral x) (orders : Fin d → Equiv.Perm (Fin 11))
    (horders : ∀ k, Monotone (fun i => x (orders k i) k)) (k : Fin d)
    (ho : scalarRange (fun i => x i k) (orders k) -
      (gap (fun i => x i k) (orders k) 0 + gap (fun i => x i k) (orders k) 9) / 2 ≤
        1 / 2) : columnTrace x orders k ≤ modifiedBeta := by
  have hc := profile_columnEnergy_le x hx orders horders modifiedVector
    sum_modifiedVector_zero modifiedAlpha modifiedVector_halfSquaredNorm k
  change scalarEnergy (fun i => x i k) (orders k)
    (transport (orders k) modifiedVector) ≤ modifiedAlpha at hc
  rw [scalarEnergy_modified] at hc
  unfold columnTrace modifiedBeta
  linarith

def totalWidth (x : Configuration) : ℝ :=
  ∑ k, scalarRange (fun i => x i k) (columnOrders x k)

theorem sum_div_const {V : Type*} [Fintype V] (f : V → ℝ) (b : ℝ) :
    (∑ i, f i / b) = (∑ i, f i) / b := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]

theorem shifted_crossEnergy (x : Configuration) (hx : UnitEquilateral x) :
    crossEnergy x (columnOrders x) shiftedVector =
      5 * shiftedAlpha + totalWidth x / 2 - 5 := by
  rw [crossEnergy_actual_eq_deficit x hx shiftedVector sum_shiftedVector_zero]
  change 5 * halfSquaredNorm shiftedVector -
    (∑ k, columnEnergy x (columnOrders x) k
      (transport (columnOrders x k) shiftedVector)) = _
  rw [shiftedVector_halfSquaredNorm]
  simp_rw [shifted_columnEnergy]
  rw [Finset.sum_sub_distrib, sum_div_const, unit_equilateral_five_totalTrace x hx]
  change 5 * shiftedAlpha - (5 - totalWidth x / 2) = _
  ring

theorem root_crossEnergy (x : Configuration) (hx : UnitEquilateral x) :
    crossEnergy x (columnOrders x) rootVector = 5 * rootAlpha - 5 := by
  rw [crossEnergy_actual_eq_deficit x hx rootVector sum_rootVector_zero]
  change 5 * halfSquaredNorm rootVector -
    (∑ k, columnEnergy x (columnOrders x) k
      (transport (columnOrders x k) rootVector)) = _
  rw [rootVector_halfSquaredNorm]
  simp_rw [root_columnEnergy]
  rw [unit_equilateral_five_totalTrace x hx]

theorem totalWidth_gt_ten_thirds (x : Configuration) (hx : UnitEquilateral x) :
    (10 / 3 : ℝ) < totalWidth x := by
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset Coordinate)) =>
    shifted_columnTrace_le x hx (columnOrders x) (columnOrders_monotone x) k)
  rw [Finset.sum_add_distrib, sum_div_const,
    unit_equilateral_five_totalTrace x hx] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  change 5 ≤ totalWidth x / 2 + 5 * shiftedAlpha at hs
  nlinarith [shiftedAlpha_lt_two_thirds]

def wideCoordinates (x : Configuration) : Finset Coordinate := by
  classical
  exact Finset.univ.filter (fun k => (1 / 2 : ℝ) <
    scalarRange (fun i => x i k) (columnOrders x k))

def wideExcess (x : Configuration) : ℝ :=
  ∑ k ∈ wideCoordinates x, (scalarRange (fun i => x i k) (columnOrders x k) - 1 / 2)

theorem totalWidth_le_base_add_wideExcess (x : Configuration) :
    totalWidth x ≤ 5 / 2 + wideExcess x := by
  classical
  have hk (k : Coordinate) : scalarRange (fun i => x i k) (columnOrders x k) ≤
      1 / 2 + if (1 / 2 : ℝ) < scalarRange (fun i => x i k) (columnOrders x k)
        then scalarRange (fun i => x i k) (columnOrders x k) - 1 / 2 else 0 := by
    split_ifs <;> linarith
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset Coordinate)) => hk k)
  rw [Finset.sum_add_distrib] at hs
  have he : (∑ k : Coordinate,
      if (1 / 2 : ℝ) < scalarRange (fun i => x i k) (columnOrders x k)
        then scalarRange (fun i => x i k) (columnOrders x k) - 1 / 2 else 0) =
      wideExcess x := by
    classical
    have hsub : (wideCoordinates x) ≤ (Finset.univ : Finset Coordinate) :=
      Finset.subset_univ _
    have hgt_of_mem : ∀ k ∈ wideCoordinates x,
        (1 / 2 : ℝ) < scalarRange (fun i => x i k) (columnOrders x k) := by
      intro k hk
      have hk' : k ∈ Finset.univ.filter (fun k => (1 / 2 : ℝ) <
          scalarRange (fun i => x i k) (columnOrders x k)) := hk
      exact (Finset.mem_filter.mp hk').2
    have hcongr : (∑ k : Coordinate,
        if (1 / 2 : ℝ) < scalarRange (fun i => x i k) (columnOrders x k)
          then scalarRange (fun i => x i k) (columnOrders x k) - 1 / 2 else 0) =
        ∑ k ∈ Finset.univ,
          if k ∈ wideCoordinates x then
            scalarRange (fun i => x i k) (columnOrders x k) - 1 / 2 else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k ∈ wideCoordinates x
      · rw [if_pos hk, if_pos (hgt_of_mem k hk)]
      · rw [if_neg hk]
        have hnot : ¬((1 / 2 : ℝ) < scalarRange (fun i => x i k) (columnOrders x k)) := by
          intro hgt
          exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hgt⟩)
        rw [if_neg hnot]
    have hout : (∑ k : Coordinate,
        if k ∈ wideCoordinates x then
          scalarRange (fun i => x i k) (columnOrders x k) - 1 / 2 else 0) =
        ∑ k ∈ wideCoordinates x,
          (scalarRange (fun i => x i k) (columnOrders x k) - 1 / 2) := by
      have hzero : ∀ k ∈ (Finset.univ : Finset Coordinate), k ∉ wideCoordinates x →
          (if k ∈ wideCoordinates x then
            scalarRange (fun i => x i k) (columnOrders x k) - 1 / 2 else 0)
            = (0 : ℝ) := by
        intro k _ hknot
        have hk : k ∉ wideCoordinates x := hknot
        rw [if_neg hk]
      have hSS : (∑ k ∈ wideCoordinates x,
          (if k ∈ wideCoordinates x then
            scalarRange (fun i => x i k) (columnOrders x k) - 1 / 2 else 0)) =
          (∑ k ∈ (Finset.univ : Finset Coordinate),
            (if k ∈ wideCoordinates x then
              scalarRange (fun i => x i k) (columnOrders x k) - 1 / 2 else 0)) :=
        Finset.sum_subset hsub hzero
      have hEq : ∀ k ∈ wideCoordinates x,
          (if k ∈ wideCoordinates x then
            scalarRange (fun i => x i k) (columnOrders x k) - 1 / 2 else 0) =
            (scalarRange (fun i => x i k) (columnOrders x k) - 1 / 2) := by
        intro k hk
        exact if_pos hk
      rw [← hSS]
      exact Finset.sum_congr rfl hEq
    exact hcongr.trans hout
  rw [he] at hs
  norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  exact hs

theorem wideExcess_gt_five_sixths (x : Configuration) (hx : UnitEquilateral x) :
    (5 / 6 : ℝ) < wideExcess x := by
  linarith [totalWidth_gt_ten_thirds x hx, totalWidth_le_base_add_wideExcess x]

theorem modified_actual_columnTrace_le {d : ℕ} (x : Fin 11 → Point d)
    (hx : UnitEquilateral x) (k : Fin d) :
    columnTrace x (columnOrders x) k ≤ modifiedBeta :=
  modified_columnTrace_le_of_outer_bound x hx (columnOrders x)
    (columnOrders_monotone x) k (actual_outer_gap_range_inequality x hx k)

/-- Counts actual PHYSICAL columns, including true constant columns. -/
theorem at_least_four_wide (x : Configuration) (hx : UnitEquilateral x) :
    4 ≤ (wideCoordinates x).card := by
  classical
  by_contra hn
  have hc : (wideCoordinates x).card ≤ 3 := by omega
  have hcR : ((wideCoordinates x).card : ℝ) ≤ 3 := by exact_mod_cast hc
  have hk (k : Coordinate) : columnTrace x (columnOrders x) k ≤
      10 / 11 + (31 / 220) *
        (if (1 / 2 : ℝ) < scalarRange (fun i => x i k) (columnOrders x k)
          then (1 : ℝ) else 0) := by
    split_ifs with hw
    · have hm := modified_actual_columnTrace_le x hx k
      have hb := modifiedBeta_lt_21_20
      norm_num
      linarith
    · have hnon := nonwide_columnTrace_lt x hx (columnOrders x)
        (columnOrders_monotone x) k (le_of_not_gt hw)
      norm_num
      linarith
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset Coordinate)) => hk k)
  have hcount : (∑ k : Coordinate,
      if (1 / 2 : ℝ) < scalarRange (fun i => x i k) (columnOrders x k)
        then (1 : ℝ) else 0) = ((wideCoordinates x).card : ℝ) := by
    simpa [wideCoordinates, Finset.sum_filter] using
      (show (∑ k ∈ wideCoordinates x, (1 : ℝ)) = ((wideCoordinates x).card : ℝ) by simp)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcount,
    unit_equilateral_five_totalTrace x hx] at hs
  norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  nlinarith

theorem shifted_row_deficit {d : ℕ} (x : Fin 11 → Point d) (hx : UnitEquilateral x)
    (k : Fin d) :
    (∑ l ∈ Finset.univ.erase k,
      columnEnergy x (columnOrders x) l (transport (columnOrders x k) shiftedVector)) =
      shiftedAlpha + scalarRange (fun i => x i k) (columnOrders x k) / 2 -
        columnTrace x (columnOrders x) k := by
  have hr := crossEnergy_row x hx (columnOrders x) (columnOrders_monotone x)
    shiftedVector sum_shiftedVector_zero k
  change _ = halfSquaredNorm shiftedVector - _ at hr
  rw [shiftedVector_halfSquaredNorm, shifted_columnEnergy] at hr
  linarith

theorem root_row_deficit {d : ℕ} (x : Fin 11 → Point d) (hx : UnitEquilateral x)
    (k : Fin d) :
    (∑ l ∈ Finset.univ.erase k,
      columnEnergy x (columnOrders x) l (transport (columnOrders x k) rootVector)) =
      rootAlpha - columnTrace x (columnOrders x) k := by
  have hr := crossEnergy_row x hx (columnOrders x) (columnOrders_monotone x)
    rootVector sum_rootVector_zero k
  change _ = halfSquaredNorm rootVector - _ at hr
  rw [rootVector_halfSquaredNorm, root_columnEnergy] at hr
  exact hr

/-- The modified profile has its own slack; it is never identified with the
unmodified or shifted directed deficit. -/
theorem modified_row_slack {d : ℕ} (x : Fin 11 → Point d) (hx : UnitEquilateral x)
    (k : Fin d) :
    modifiedBeta - columnTrace x (columnOrders x) k =
      (∑ l ∈ Finset.univ.erase k,
        columnEnergy x (columnOrders x) l (transport (columnOrders x k) modifiedVector)) +
      (1 / 2 - scalarRange (fun i => x i k) (columnOrders x k) +
        (gap (fun i => x i k) (columnOrders x k) 0 +
          gap (fun i => x i k) (columnOrders x k) 9) / 2) := by
  have hr := crossEnergy_row x hx (columnOrders x) (columnOrders_monotone x)
    modifiedVector sum_modifiedVector_zero k
  change _ = halfSquaredNorm modifiedVector -
    scalarEnergy (fun i => x i k) (columnOrders x k)
      (transport (columnOrders x k) modifiedVector) at hr
  rw [modifiedVector_halfSquaredNorm, scalarEnergy_modified] at hr
  unfold modifiedBeta columnTrace
  linarith

theorem shiftedHeight_nonneg (i : Fin 12) : 0 ≤ shiftedHeight i := by
  fin_cases i <;> norm_num [shiftedHeight, shiftedHeightNumerator] <;> positivity
theorem rootHeight_nonneg (i : Fin 12) : 0 ≤ rootHeight i := by
  fin_cases i <;> norm_num [rootHeight, rootHeightNumerator] <;> positivity
theorem modifiedHeight_nonneg (i : Fin 12) : 0 ≤ modifiedHeight i := by
  fin_cases i <;> norm_num [modifiedHeight, modifiedHeightNumerator] <;> positivity
theorem nonwideHeight_nonneg (i : Fin 12) : 0 ≤ nonwideHeight i := by
  fin_cases i <;> norm_num [nonwideHeight, nonwideHeightNumerator] <;> positivity

theorem eq_sqrt_of_nonneg_sq {a b : ℝ} (ha : 0 ≤ a) (he : a ^ 2 = b) :
    a = Real.sqrt b := by
  have hb : 0 ≤ b := by nlinarith [sq_nonneg a]
  have hs := Real.sq_sqrt hb
  have hn := Real.sqrt_nonneg b
  have hp : (a - Real.sqrt b) * (a + Real.sqrt b) = 0 := by nlinarith
  rcases mul_eq_zero.mp hp with hm | hp
  · linarith
  · linarith

theorem shiftedHeight_eq_sqrt (r : Fin 10) :
    shiftedHeight r.castSucc.succ = Real.sqrt (cutWeight r - 1 / 2) :=
  eq_sqrt_of_nonneg_sq (shiftedHeight_nonneg _) (shiftedHeight_sq r)

theorem rootHeight_eq_sqrt (r : Fin 10) :
    rootHeight r.castSucc.succ = Real.sqrt (cutWeight r) :=
  eq_sqrt_of_nonneg_sq (rootHeight_nonneg _) (rootHeight_sq r)

theorem modifiedHeight_eq_sqrt (r : Fin 10) :
    modifiedHeight r.castSucc.succ = Real.sqrt
      (cutWeight r - 1 + if r = 0 ∨ r = 9 then 1 / 2 else 0) :=
  eq_sqrt_of_nonneg_sq (modifiedHeight_nonneg _) (modifiedHeight_sq r)

theorem nonwideHeight_eq_sqrt (r : Fin 10) :
    nonwideHeight r.castSucc.succ = Real.sqrt (cutWeight r - 2 / 3) :=
  eq_sqrt_of_nonneg_sq (nonwideHeight_nonneg _) (nonwideHeight_sq r)

end
end Kusner5.Profiles
