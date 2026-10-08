import Kusner5.QuartetPerimeter

-- Actual development013 panicked in SimprocEntry.try. Disable only this
-- optional simplifier automation; every resulting proof is kernel checked.
set_option simprocs false

/-!
Literal four-coordinate rectangle for two double balanced types. Its metric
is the full sum of four absolute coordinate differences, so each free scalar
contributes twice. The resulting perimeter is exactly eight times the sum
of the two effective halfwidths, including zero-length edges.
-/

namespace Kusner5.QuartetGeometry

open scoped BigOperators

noncomputable section

def pairedRectangle (A B : ℝ) : Fin 4 → Point 4 :=
  ![![A, -A, B, -B], ![-A, A, B, -B], ![-A, A, -B, B], ![A, -A, -B, B]]

private theorem four_distance_expanded (p q : Point 4) :
    l1dist p q = |p 0 - q 0| + |p 1 - q 1| + |p 2 - q 2| + |p 3 - q 3| := by
  simp only [l1dist, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change |p 0 - q 0| + (|p 1 - q 1| + (|p 2 - q 2| + |p 3 - q 3|)) =
    |p 0 - q 0| + |p 1 - q 1| + |p 2 - q 2| + |p 3 - q 3|
  ring

theorem pairedRectangle_budget (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (polygonFour (pairedRectangle A B)).budget = 8 * (A + B) := by
  have h2A : 0 ≤ 2 * A := mul_nonneg (by norm_num) hA
  have h2B : 0 ≤ 2 * B := mul_nonneg (by norm_num) hB
  have h0 : l1dist (pairedRectangle A B 0) (pairedRectangle A B 1) = 4 * A := by
    rw [four_distance_expanded]
    change |A - -A| + |-A - A| + |B - B| + |-B - -B| = 4 * A
    simp only [sub_self, abs_zero]
    rw [show A - -A = 2 * A by ring, show -A - A = -(2 * A) by ring,
      abs_neg, abs_of_nonneg h2A]
    ring
  have h1 : l1dist (pairedRectangle A B 1) (pairedRectangle A B 2) = 4 * B := by
    rw [four_distance_expanded]
    change |-A - -A| + |A - A| + |B - -B| + |-B - B| = 4 * B
    simp only [sub_self, abs_zero]
    rw [show B - -B = 2 * B by ring, show -B - B = -(2 * B) by ring,
      abs_neg, abs_of_nonneg h2B]
    ring
  have h2 : l1dist (pairedRectangle A B 2) (pairedRectangle A B 3) = 4 * A := by
    rw [four_distance_expanded]
    change |-A - A| + |A - -A| + |-B - -B| + |B - B| = 4 * A
    simp only [sub_self, abs_zero]
    rw [show -A - A = -(2 * A) by ring, show A - -A = 2 * A by ring,
      abs_neg, abs_of_nonneg h2A]
    ring
  have h3 : l1dist (pairedRectangle A B 3) (pairedRectangle A B 0) = 4 * B := by
    rw [four_distance_expanded]
    change |A - A| + |-A - -A| + |-B - B| + |B - -B| = 4 * B
    simp only [sub_self, abs_zero]
    rw [show -B - B = -(2 * B) by ring, show B - -B = 2 * B by ring,
      abs_neg, abs_of_nonneg h2B]
    ring
  rw [polygonFour_budget]
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change l1dist (pairedRectangle A B 0) (pairedRectangle A B 1) +
    (l1dist (pairedRectangle A B 1) (pairedRectangle A B 2) +
    (l1dist (pairedRectangle A B 2) (pairedRectangle A B 3) +
      l1dist (pairedRectangle A B 3) (pairedRectangle A B 0))) = 8 * (A + B)
  rw [h0, h1, h2, h3]
  ring

/-- Each literal saturated side is covered by its actual straight edge. -/
theorem pairedRectangle_covers (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (z : Point 4)
    (hp0 : z 0 + z 1 = 0) (hp1 : z 2 + z 3 = 0)
    (hzA : -A ≤ z 0 ∧ z 0 ≤ A) (hzB : -B ≤ z 2 ∧ z 2 ≤ B)
    (hface : |z 0| = A ∨ |z 2| = B) :
    (polygonFour (pairedRectangle A B)).Covers z := by
  rcases hface with hf | hf
  · have hcases : z 0 = A ∨ z 0 = -A := by
      by_cases hs : 0 ≤ z 0
      · exact Or.inl (by simpa only [abs_of_nonneg hs] using hf)
      · right
        rw [abs_of_nonpos (le_of_not_ge hs)] at hf
        linarith
    rcases hcases with hplus | hminus
    · obtain ⟨θ, hθ0, hθ1, hθ⟩ := scalar_between_interpolation
        (a := -B) (b := B) (z := z 2) (by
          rw [min_eq_left (by linarith : -B ≤ B), max_eq_right (by linarith : -B ≤ B)]
          exact hzB)
      have heq : linePoint (pairedRectangle A B 3) (pairedRectangle A B 0) θ = z := by
        funext k
        fin_cases k
        · change A + θ * (A - A) = z 0
          nlinarith
        · change -A + θ * (-A - -A) = z 1
          nlinarith
        · change -B + θ * (B - -B) = z 2
          exact hθ
        · change B + θ * (-B - B) = z 3
          nlinarith
      apply polygonFour_covers_edge (pairedRectangle A B) 3
      change (PhysicalPath.straight (pairedRectangle A B 3) (pairedRectangle A B 0)).Covers z
      have hc := PhysicalPath.straight_covers (pairedRectangle A B 3)
        (pairedRectangle A B 0) θ hθ0 hθ1
      simpa only [heq] using hc
    · obtain ⟨θ, hθ0, hθ1, hθ⟩ := scalar_between_interpolation
        (a := B) (b := -B) (z := z 2) (by
          rw [min_eq_right (by linarith : -B ≤ B), max_eq_left (by linarith : -B ≤ B)]
          exact hzB)
      have heq : linePoint (pairedRectangle A B 1) (pairedRectangle A B 2) θ = z := by
        funext k
        fin_cases k
        · change -A + θ * (-A - -A) = z 0
          nlinarith
        · change A + θ * (A - A) = z 1
          nlinarith
        · change B + θ * (-B - B) = z 2
          exact hθ
        · change -B + θ * (B - -B) = z 3
          nlinarith
      apply polygonFour_covers_edge (pairedRectangle A B) 1
      change (PhysicalPath.straight (pairedRectangle A B 1) (pairedRectangle A B 2)).Covers z
      have hc := PhysicalPath.straight_covers (pairedRectangle A B 1)
        (pairedRectangle A B 2) θ hθ0 hθ1
      simpa only [heq] using hc
  · have hcases : z 2 = B ∨ z 2 = -B := by
      by_cases hs : 0 ≤ z 2
      · exact Or.inl (by simpa only [abs_of_nonneg hs] using hf)
      · right
        rw [abs_of_nonpos (le_of_not_ge hs)] at hf
        linarith
    rcases hcases with hplus | hminus
    · obtain ⟨θ, hθ0, hθ1, hθ⟩ := scalar_between_interpolation
        (a := A) (b := -A) (z := z 0) (by
          rw [min_eq_right (by linarith : -A ≤ A), max_eq_left (by linarith : -A ≤ A)]
          exact hzA)
      have heq : linePoint (pairedRectangle A B 0) (pairedRectangle A B 1) θ = z := by
        funext k
        fin_cases k
        · change A + θ * (-A - A) = z 0
          exact hθ
        · change -A + θ * (A - -A) = z 1
          nlinarith
        · change B + θ * (B - B) = z 2
          nlinarith
        · change -B + θ * (-B - -B) = z 3
          nlinarith
      apply polygonFour_covers_edge (pairedRectangle A B) 0
      change (PhysicalPath.straight (pairedRectangle A B 0) (pairedRectangle A B 1)).Covers z
      have hc := PhysicalPath.straight_covers (pairedRectangle A B 0)
        (pairedRectangle A B 1) θ hθ0 hθ1
      simpa only [heq] using hc
    · obtain ⟨θ, hθ0, hθ1, hθ⟩ := scalar_between_interpolation
        (a := -A) (b := A) (z := z 0) (by
          rw [min_eq_left (by linarith : -A ≤ A), max_eq_right (by linarith : -A ≤ A)]
          exact hzA)
      have heq : linePoint (pairedRectangle A B 2) (pairedRectangle A B 3) θ = z := by
        funext k
        fin_cases k
        · change -A + θ * (A - -A) = z 0
          exact hθ
        · change A + θ * (-A - A) = z 1
          nlinarith
        · change -B + θ * (-B - -B) = z 2
          nlinarith
        · change B + θ * (B - B) = z 3
          nlinarith
      apply polygonFour_covers_edge (pairedRectangle A B) 2
      change (PhysicalPath.straight (pairedRectangle A B 2) (pairedRectangle A B 3)).Covers z
      have hc := PhysicalPath.straight_covers (pairedRectangle A B 2)
        (pairedRectangle A B 3) θ hθ0 hθ1
      simpa only [heq] using hc

end
end Kusner5.QuartetGeometry
