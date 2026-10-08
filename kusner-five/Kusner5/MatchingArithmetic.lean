import Kusner5.Profiles

/-!
Exact arithmetic for the shifted-prefix forest and matching arguments.

The lemmas in this module are scalar consequences of the geometric ledgers.
They do not assert that an arbitrary original input satisfies those ledgers;
that bridge belongs to ForestMatching and the final composition.
-/

namespace Kusner5.MatchingArithmetic

open Profiles

noncomputable section

def alpha : ℝ := s1 + s2 + s3 + s4 + s5
def c1 : ℝ := s5
def c2 : ℝ := s5 + s4
def c3 : ℝ := s4 + s3
def c4 : ℝ := s3 + s2
def b1 : ℝ := 4 * c1
def b2 : ℝ := c1 + 3 * c2
def b3 : ℝ := 2 * c2 + 2 * c3
def b4 : ℝ := 3 * c3 + c4
def b5 : ℝ := 4 * c4
def gamma : ℝ := 1 / 2 - b3

def G1 : ℝ := (b1 + b2 + b3) / 3 - 5 * alpha + 13 / 4
def G4 : ℝ := (b1 + b2 + b3 + b4) / 3 - 5 * alpha + 37 / 12

theorem s4_pos : 0 < s4 := lt_trans s5_pos s5_lt_s4
theorem s3_pos : 0 < s3 := lt_trans s4_pos s4_lt_s3
theorem s2_pos : 0 < s2 := lt_trans s3_pos s3_lt_s2

theorem b1_lt_b2 : b1 < b2 := by
  dsimp [b1, b2, c1, c2]
  linarith [s4_pos]

theorem b2_lt_b3 : b2 < b3 := by
  dsimp [b2, b3, c1, c2, c3]
  linarith [s5_lt_s4, s4_lt_s3, s4_pos]

theorem b3_lt_b4 : b3 < b4 := by
  dsimp [b3, b4, c2, c3, c4]
  linarith [s5_lt_s4, s4_lt_s3, s3_lt_s2]

theorem b4_lt_b5 : b4 < b5 := by
  dsimp [b4, b5, c3, c4]
  linarith [s4_lt_s3, s3_lt_s2]

theorem b3_lt_seventeen_sixtyfourths : b3 < 17 / 64 := by
  have h3 : s3 < 1 / 16 := lt_trans s3_lt_121_2200 (by norm_num)
  have h4 : s4 < 1 / 32 := lt_trans s4_lt_9_352 (by norm_num)
  have h5 : s5 < 1 / 128 := lt_trans s5_lt_2_275 (by norm_num)
  dsimp [b3, c2, c3]
  linarith

theorem b4_lt_half : b4 < 1 / 2 := by
  have hs2 : s2 = 2 / 11 := by norm_num [Profiles.s2]
  dsimp [b4, c3, c4]
  linarith [s3_lt_121_2200, s4_lt_9_352]

theorem b5_add_b3_gt_one : 1 < b5 + b3 := by
  have hs2 : s2 = 2 / 11 := by norm_num [Profiles.s2]
  dsimp [b5, b3, c2, c3, c4]
  linarith [s3_gt_one_twentieth, s4_pos, s5_pos]

theorem gamma_gt_fifteen_sixtyfourths : 15 / 64 < gamma := by
  dsimp [gamma]
  linarith [b3_lt_seventeen_sixtyfourths]

theorem gamma_pos : 0 < gamma := by
  linarith [gamma_gt_fifteen_sixtyfourths]

theorem G1_radical :
    G1 = (-3825 + 260 * Real.sqrt 37 + 96 * Real.sqrt 185 +
      420 * Real.sqrt 5) / 132 := by
  dsimp [G1, b1, b2, b3, c1, c2, c3, alpha,
    Profiles.s1, Profiles.s2, Profiles.s3, Profiles.s4, Profiles.s5]
  ring

theorem G4_radical :
    G4 = (-2851 + 180 * Real.sqrt 37 + 60 * Real.sqrt 185 +
      420 * Real.sqrt 5) / 132 := by
  dsimp [G4, b1, b2, b3, b4, c1, c2, c3, c4, alpha,
    Profiles.s1, Profiles.s2, Profiles.s3, Profiles.s4, Profiles.s5]
  ring

theorem G1_gt_certificate : 17549 / 1650000 < G1 := by
  rw [G1_radical]
  linarith [sqrt37_lower, sqrt185_lower, sqrt5_lower]

theorem G1_pos : 0 < G1 := by
  linarith [G1_gt_certificate]

theorem G4_gt_negative_certificate : -(4349 / 660000) < G4 := by
  rw [G4_radical]
  linarith [sqrt37_lower, sqrt185_lower, sqrt5_lower]

theorem final_certificate_positive : (0 : ℝ) < 33541 / 10560000 := by
  norm_num

theorem four_wide_path_contradiction (W Δ : ℝ)
    (hW : W ≤ 23 / 6)
    (hLower : (9 / 22) * (W - 19 / 6) ≤ Δ)
    (hUpper : Δ < W / 2 - 5 / 3) : False := by
  linarith

theorem five_wide_two_isolated_contradiction (H Δ : ℝ)
    (hH : H ≤ 1)
    (hLower : (9 / 22) * (H - 2 / 3) ≤ Δ)
    (hUpper : Δ < H / 2 - 5 / 12) : False := by
  linarith

theorem four_matching_capped_lower (t1 t2 t3 t4 : ℝ)
    (ht1 : t1 ≤ 1 / 3) (ht2 : t2 ≤ 1 / 3) (ht4 : 0 ≤ t4) :
    (b1 + b2) / 3 + b3 * (t1 + t2 + t3 + t4 - 2 / 3) ≤
      b1 * t1 + b2 * t2 + b3 * t3 + b4 * t4 := by
  have h31 : 0 ≤ b3 - b1 := by linarith [b1_lt_b2, b2_lt_b3]
  have h32 : 0 ≤ b3 - b2 := by linarith [b2_lt_b3]
  have h43 : 0 ≤ b4 - b3 := by linarith [b3_lt_b4]
  have h1 := mul_nonneg h31 (sub_nonneg.mpr ht1)
  have h2 := mul_nonneg h32 (sub_nonneg.mpr ht2)
  have h4 := mul_nonneg h43 ht4
  nlinarith

theorem four_matching_contradiction (t1 t2 t3 t4 Δ : ℝ)
    (ht1 : t1 ≤ 1 / 3) (ht2 : t2 ≤ 1 / 3) (ht4 : 0 ≤ t4)
    (hH : t1 + t2 + t3 + t4 ≤ 1)
    (hLower : b1 * t1 + b2 * t2 + b3 * t3 + b4 * t4 ≤ Δ)
    (hUpper : Δ ≤ 5 * alpha - 15 / 4 + (t1 + t2 + t3 + t4) / 2) : False := by
  have hCap := four_matching_capped_lower t1 t2 t3 t4 ht1 ht2 ht4
  have hc : 0 ≤ 1 / 2 - b3 := by linarith [b3_lt_seventeen_sixtyfourths]
  have hp := mul_nonneg hc (sub_nonneg.mpr hH)
  have hG : G1 ≤
      (b1 + b2) / 3 + b3 * (t1 + t2 + t3 + t4 - 2 / 3) -
        (5 * alpha - 15 / 4 + (t1 + t2 + t3 + t4) / 2) := by
    dsimp [G1]
    nlinarith
  linarith [G1_pos]

def pathSmall (U S : ℝ) : ℝ :=
  4 * (s3 + s4) * U + (s1 + s3 + 6 * s4) * S -
    (5 * s4 + 10 * s3 - 10 * s5) / 3

def pathLarge (U S : ℝ) : ℝ :=
  4 * (s3 + s4) * U + (s1 + s3 + 3 * s4) * S -
    (2 * s4 + 10 * s3 - 10 * s5) / 3

theorem path_bounds_agree_at_third (U : ℝ) :
    pathSmall U (1 / 3) = pathLarge U (1 / 3) := by
  dsimp [pathSmall, pathLarge]
  ring

theorem path_U_coefficient_negative : 4 * (s3 + s4) - 1 / 2 < 0 := by
  have h3 : s3 < 1 / 16 := lt_trans s3_lt_121_2200 (by norm_num)
  have h4 : s4 < 1 / 32 := lt_trans s4_lt_9_352 (by norm_num)
  linarith

theorem path_large_S_coefficient_positive : 0 < s1 + s3 + 3 * s4 - 1 / 2 := by
  have hs1 : s1 = 9 / 22 := by norm_num [Profiles.s1]
  linarith [s3_gt_one_twentieth, s4_gt_one_sixtieth]

theorem path_small_S_coefficient_positive : 0 < s1 + s3 + 6 * s4 - 1 / 2 := by
  linarith [path_large_S_coefficient_positive, s4_pos]

theorem path_small_gap (U S : ℝ) (hU : U ≤ 1) (hS : 0 ≤ S) :
    G1 ≤ pathSmall U S - (5 * alpha - 15 / 4 + (U + S) / 2) := by
  have hpU := mul_nonneg
    (le_of_lt (neg_pos.mpr path_U_coefficient_negative)) (sub_nonneg.mpr hU)
  have hpS := mul_nonneg (le_of_lt path_small_S_coefficient_positive) hS
  dsimp [pathSmall, G1, b1, b2, b3, c1, c2, c3]
  nlinarith

theorem path_large_gap (U S : ℝ) (hU : U ≤ 1) (hS : 1 / 3 ≤ S) :
    G1 ≤ pathLarge U S - (5 * alpha - 15 / 4 + (U + S) / 2) := by
  have hpU := mul_nonneg
    (le_of_lt (neg_pos.mpr path_U_coefficient_negative)) (sub_nonneg.mpr hU)
  have hpS := mul_nonneg (le_of_lt path_large_S_coefficient_positive)
    (sub_nonneg.mpr hS)
  have hcoef := path_small_S_coefficient_positive
  dsimp [pathLarge, G1, b1, b2, b3, c1, c2, c3]
  nlinarith

theorem path_small_contradiction (U S Δ : ℝ) (hU : U ≤ 1) (hS : 0 ≤ S)
    (hEq : Δ = 5 * alpha - 15 / 4 + (U + S) / 2)
    (hLower : pathSmall U S ≤ Δ) : False := by
  have hGap := path_small_gap U S hU hS
  rw [← hEq] at hGap
  linarith [G1_pos]

theorem path_large_contradiction (U S Δ : ℝ) (hU : U ≤ 1) (hS : 1 / 3 ≤ S)
    (hEq : Δ = 5 * alpha - 15 / 4 + (U + S) / 2)
    (hLower : pathLarge U S ≤ Δ) : False := by
  have hGap := path_large_gap U S hU hS
  rw [← hEq] at hGap
  linarith [G1_pos]

theorem matching_slack_from_quartet (t1 t2 t3 t5 : ℝ)
    (hWidth : 37 / 24 ≤ (1 / 2 + t5) + 1 / 2 +
      (1 - (1 / 2 + t1)) + (1 - (1 / 2 + t2)) + (1 - (1 / 2 + t3))) :
    1 / 24 ≤ (1 / 3 - t1) + (1 / 3 - t2) + (1 / 3 - t3) + t5 := by
  linarith

theorem matching_slack_identity (t1 t2 t3 t4 t5 : ℝ) :
    b1 * t1 + b2 * t2 + b3 * t3 + b4 * t4 + b5 * t5 -
        (5 * alpha - 15 / 4 + (t1 + t2 + t3 + t4 + t5) / 2) =
      G4 + (1 / 2 - b1) * (1 / 3 - t1) +
        (1 / 2 - b2) * (1 / 3 - t2) +
        (1 / 2 - b3) * (1 / 3 - t3) +
        (1 / 2 - b4) * (1 / 3 - t4) + (b5 - 1 / 2) * t5 := by
  dsimp [G4]
  ring

theorem matching_gap (t1 t2 t3 t4 t5 : ℝ)
    (ht1 : t1 ≤ 1 / 3) (ht2 : t2 ≤ 1 / 3)
    (ht3 : t3 ≤ 1 / 3) (ht4 : t4 ≤ 1 / 3) (ht5 : 0 ≤ t5)
    (hSlack : 1 / 24 ≤ (1 / 3 - t1) + (1 / 3 - t2) + (1 / 3 - t3) + t5) :
    33541 / 10560000 <
      b1 * t1 + b2 * t2 + b3 * t3 + b4 * t4 + b5 * t5 -
        (5 * alpha - 15 / 4 + (t1 + t2 + t3 + t4 + t5) / 2) := by
  rw [matching_slack_identity]
  have hd1 := sub_nonneg.mpr ht1
  have hd2 := sub_nonneg.mpr ht2
  have hd4 := sub_nonneg.mpr ht4
  have h1 := mul_nonneg (show 0 ≤ 1 / 2 - b1 - gamma by
    dsimp [gamma]; linarith [b1_lt_b2, b2_lt_b3]) hd1
  have h2 := mul_nonneg (show 0 ≤ 1 / 2 - b2 - gamma by
    dsimp [gamma]; linarith [b2_lt_b3]) hd2
  have h4 := mul_nonneg (show 0 ≤ 1 / 2 - b4 by linarith [b4_lt_half]) hd4
  have h5 := mul_nonneg (show 0 ≤ b5 - 1 / 2 - gamma by
    dsimp [gamma]; linarith [b5_add_b3_gt_one]) ht5
  have hMass := mul_le_mul_of_nonneg_left hSlack (le_of_lt gamma_pos)
  have hg := gamma_gt_fifteen_sixtyfourths
  have hG := G4_gt_negative_certificate
  dsimp [gamma] at h1 h2 h5 hMass hg
  nlinarith

theorem matching_contradiction (t1 t2 t3 t4 t5 Δ : ℝ)
    (ht1 : t1 ≤ 1 / 3) (ht2 : t2 ≤ 1 / 3)
    (ht3 : t3 ≤ 1 / 3) (ht4 : t4 ≤ 1 / 3) (ht5 : 0 ≤ t5)
    (hSlack : 1 / 24 ≤ (1 / 3 - t1) + (1 / 3 - t2) + (1 / 3 - t3) + t5)
    (hEq : Δ = 5 * alpha - 15 / 4 + (t1 + t2 + t3 + t4 + t5) / 2)
    (hLower : b1 * t1 + b2 * t2 + b3 * t3 + b4 * t4 + b5 * t5 ≤ Δ) : False := by
  have hGap := matching_gap t1 t2 t3 t4 t5 ht1 ht2 ht3 ht4 ht5 hSlack
  rw [← hEq] at hGap
  linarith [final_certificate_positive]

end
end Kusner5.MatchingArithmetic
