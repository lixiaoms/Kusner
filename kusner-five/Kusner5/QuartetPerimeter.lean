import Kusner5.QuartetProjection
import Mathlib.Data.Fin.VecNotation

-- Actual development009 panicked in SimprocEntry.try. Disable only this
-- optional simplifier automation; every resulting proof is kernel checked.
set_option simprocs false

/-!
Actual physical plane-section and rectangle tours. Budgets are computed using
the explicit sum-absolute-value metric on their literal coordinates.
-/

namespace Kusner5.QuartetGeometry

open scoped BigOperators

noncomputable section

def freeCoordinate (i : Fin 3) : Fin 3 := if i = 0 then 1 else 0

private theorem three_distance_expanded (p q : Point 3) :
    l1dist p q = |p 0 - q 0| + |p 1 - q 1| + |p 2 - q 2| := by
  norm_num [l1dist, Fin.sum_univ_succ]
  ring

/-- On a literal fixed-coordinate zero-sum edge the other two differences
are opposites. No affine-plane norm identification is assumed. -/
theorem zero_sum_fixed_edge_distance (p q : Point 3)
    (hp : (∑ k, p k) = 0) (hq : (∑ k, q k) = 0)
    (i : Fin 3) (hi : p i = q i) :
    l1dist p q = 2 * |p (freeCoordinate i) - q (freeCoordinate i)| := by
  have hp' : p 0 + p 1 + p 2 = 0 := by
    norm_num [Fin.sum_univ_succ] at hp
    linarith
  have hq' : q 0 + q 1 + q 2 = 0 := by
    norm_num [Fin.sum_univ_succ] at hq
    linarith
  rw [three_distance_expanded]
  fin_cases i
  · change p 0 = q 0 at hi
    change |p 0 - q 0| + |p 1 - q 1| + |p 2 - q 2| = 2 * |p 1 - q 1|
    have hd : p 2 - q 2 = -(p 1 - q 1) := by linarith
    rw [hi, sub_self, abs_zero, hd, abs_neg]
    ring
  · change p 1 = q 1 at hi
    change |p 0 - q 0| + |p 1 - q 1| + |p 2 - q 2| = 2 * |p 0 - q 0|
    have hd : p 2 - q 2 = -(p 0 - q 0) := by linarith
    rw [hi, sub_self, abs_zero, hd, abs_neg]
    ring
  · change p 2 = q 2 at hi
    change |p 0 - q 0| + |p 1 - q 1| + |p 2 - q 2| = 2 * |p 0 - q 0|
    have hd : p 1 - q 1 = -(p 0 - q 0) := by linarith
    rw [hi, sub_self, abs_zero, hd, abs_neg]
    ring

def planeHexagon (a b c : ℝ) : Fin 6 → Point 3 :=
  ![![a, c - a, -c], ![a, -b, b - a], ![b - c, -b, c],
    ![-a, a - c, c], ![-a, b, a - b], ![c - b, b, -c]]

theorem planeHexagon_zero_sum (a b c : ℝ) (i : Fin 6) :
    (∑ k, planeHexagon a b c i k) = 0 := by
  fin_cases i <;> norm_num [planeHexagon, Fin.sum_univ_succ] <;> ring

def planeHexagonEdgeBudget (a b c : ℝ) : Fin 6 → ℝ :=
  ![2 * (b + c - a), 2 * (a + c - b), 2 * (a + b - c),
    2 * (b + c - a), 2 * (a + c - b), 2 * (a + b - c)]

theorem planeHexagon_edge_distance (a b c : ℝ)
    (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) (i : Fin 6) :
    l1dist (planeHexagon a b c i) (planeHexagon a b c (nextSix i)) =
      planeHexagonEdgeBudget a b c i := by
  have hA : 0 ≤ b + c - a := by linarith
  have hB : 0 ≤ a + c - b := by linarith
  have hC : 0 ≤ a + b - c := by linarith
  fin_cases i
  · change l1dist (planeHexagon a b c 0) (planeHexagon a b c 1) = 2 * (b + c - a)
    rw [zero_sum_fixed_edge_distance _ _
      (planeHexagon_zero_sum a b c 0) (planeHexagon_zero_sum a b c 1) 0 rfl]
    change 2 * |(c - a) - -b| = 2 * (b + c - a)
    rw [show (c - a) - -b = b + c - a by ring, abs_of_nonneg hA]
  · change l1dist (planeHexagon a b c 1) (planeHexagon a b c 2) = 2 * (a + c - b)
    rw [zero_sum_fixed_edge_distance _ _
      (planeHexagon_zero_sum a b c 1) (planeHexagon_zero_sum a b c 2) 1 rfl]
    change 2 * |a - (b - c)| = 2 * (a + c - b)
    rw [show a - (b - c) = a + c - b by ring, abs_of_nonneg hB]
  · change l1dist (planeHexagon a b c 2) (planeHexagon a b c 3) = 2 * (a + b - c)
    rw [zero_sum_fixed_edge_distance _ _
      (planeHexagon_zero_sum a b c 2) (planeHexagon_zero_sum a b c 3) 2 rfl]
    change 2 * |(b - c) - -a| = 2 * (a + b - c)
    rw [show (b - c) - -a = a + b - c by ring, abs_of_nonneg hC]
  · change l1dist (planeHexagon a b c 3) (planeHexagon a b c 4) = 2 * (b + c - a)
    rw [zero_sum_fixed_edge_distance _ _
      (planeHexagon_zero_sum a b c 3) (planeHexagon_zero_sum a b c 4) 0 rfl]
    change 2 * |(a - c) - b| = 2 * (b + c - a)
    rw [show (a - c) - b = -(b + c - a) by ring, abs_neg, abs_of_nonneg hA]
  · change l1dist (planeHexagon a b c 4) (planeHexagon a b c 5) = 2 * (a + c - b)
    rw [zero_sum_fixed_edge_distance _ _
      (planeHexagon_zero_sum a b c 4) (planeHexagon_zero_sum a b c 5) 1 rfl]
    change 2 * |-a - (c - b)| = 2 * (a + c - b)
    rw [show -a - (c - b) = -(a + c - b) by ring, abs_neg, abs_of_nonneg hB]
  · change l1dist (planeHexagon a b c 5) (planeHexagon a b c 0) = 2 * (a + b - c)
    rw [zero_sum_fixed_edge_distance _ _
      (planeHexagon_zero_sum a b c 5) (planeHexagon_zero_sum a b c 0) 2 rfl]
    change 2 * |(c - b) - a| = 2 * (a + b - c)
    rw [show (c - b) - a = -(a + b - c) by ring, abs_neg, abs_of_nonneg hC]

/-- Zero-length faces are retained as zero-budget polygon edges. -/
theorem planeHexagon_budget (a b c : ℝ)
    (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    (polygonSix (planeHexagon a b c)).budget = 4 * (a + b + c) := by
  rw [polygonSix_budget]
  simp_rw [planeHexagon_edge_distance a b c ha hb hc]
  norm_num [planeHexagonEdgeBudget, Fin.sum_univ_succ]
  ring

/-- Every true saturated box face is covered by its actual straight edge
in the non-dominant plane section, including equality degeneracies. -/
theorem planeHexagon_covers (a b c : ℝ)
    (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b)
    (z : Point 3) (hz : (∑ k, z k) = 0)
    (hbox : InSymmetricBox ![a, b, c] z) (hface : TouchesBoxFace ![a, b, c] z) :
    (polygonSix (planeHexagon a b c)).Covers z := by
  have hsum : z 0 + z 1 + z 2 = 0 := by
    norm_num [Fin.sum_univ_succ] at hz
    linarith
  have hx : -a ≤ z 0 ∧ z 0 ≤ a := hbox 0
  have hy : -b ≤ z 1 ∧ z 1 ≤ b := hbox 1
  have hz2 : -c ≤ z 2 ∧ z 2 ≤ c := hbox 2
  obtain ⟨i, hi⟩ := hface
  fin_cases i
  · change |z 0| = a at hi
    by_cases hpos : 0 ≤ z 0
    · have hfix : z 0 = a := by simpa only [abs_of_nonneg hpos] using hi
      apply polygonSix_covers_edge _ 0
      apply zero_sum_three_edge_covers _ _ z
        (planeHexagon_zero_sum a b c 0) (planeHexagon_zero_sum a b c 1) hz
        0 1 (by decide) rfl
      · exact hfix
      · change min (c - a) (-b) ≤ z 1 ∧ z 1 ≤ max (c - a) (-b)
        have he : -b ≤ c - a := by linarith
        rw [min_eq_right he, max_eq_left he]
        constructor <;> linarith [hy.1, hz2.1]
    · have hfix : z 0 = -a := by
        rw [abs_of_nonpos (le_of_not_ge hpos)] at hi
        linarith
      apply polygonSix_covers_edge _ 3
      apply zero_sum_three_edge_covers _ _ z
        (planeHexagon_zero_sum a b c 3) (planeHexagon_zero_sum a b c 4) hz
        0 1 (by decide) rfl
      · exact hfix
      · change min (a - c) b ≤ z 1 ∧ z 1 ≤ max (a - c) b
        have he : a - c ≤ b := by linarith
        rw [min_eq_left he, max_eq_right he]
        constructor <;> linarith [hy.2, hz2.2]
  · change |z 1| = b at hi
    by_cases hpos : 0 ≤ z 1
    · have hfix : z 1 = b := by simpa only [abs_of_nonneg hpos] using hi
      apply polygonSix_covers_edge _ 4
      apply zero_sum_three_edge_covers _ _ z
        (planeHexagon_zero_sum a b c 4) (planeHexagon_zero_sum a b c 5) hz
        1 0 (by decide) rfl
      · exact hfix
      · change min (-a) (c - b) ≤ z 0 ∧ z 0 ≤ max (-a) (c - b)
        have he : -a ≤ c - b := by linarith
        rw [min_eq_left he, max_eq_right he]
        constructor <;> linarith [hx.1, hz2.1]
    · have hfix : z 1 = -b := by
        rw [abs_of_nonpos (le_of_not_ge hpos)] at hi
        linarith
      apply polygonSix_covers_edge _ 1
      apply zero_sum_three_edge_covers _ _ z
        (planeHexagon_zero_sum a b c 1) (planeHexagon_zero_sum a b c 2) hz
        1 0 (by decide) rfl
      · exact hfix
      · change min a (b - c) ≤ z 0 ∧ z 0 ≤ max a (b - c)
        have he : b - c ≤ a := by linarith
        rw [min_eq_right he, max_eq_left he]
        constructor <;> linarith [hx.2, hz2.2]
  · change |z 2| = c at hi
    by_cases hpos : 0 ≤ z 2
    · have hfix : z 2 = c := by simpa only [abs_of_nonneg hpos] using hi
      apply polygonSix_covers_edge _ 2
      apply zero_sum_three_edge_covers _ _ z
        (planeHexagon_zero_sum a b c 2) (planeHexagon_zero_sum a b c 3) hz
        2 0 (by decide) rfl
      · exact hfix
      · change min (b - c) (-a) ≤ z 0 ∧ z 0 ≤ max (b - c) (-a)
        have he : -a ≤ b - c := by linarith
        rw [min_eq_right he, max_eq_left he]
        constructor <;> linarith [hx.1, hy.1]
    · have hfix : z 2 = -c := by
        rw [abs_of_nonpos (le_of_not_ge hpos)] at hi
        linarith
      apply polygonSix_covers_edge _ 5
      apply zero_sum_three_edge_covers _ _ z
        (planeHexagon_zero_sum a b c 5) (planeHexagon_zero_sum a b c 0) hz
        2 0 (by decide) rfl
      · exact hfix
      · change min (c - b) a ≤ z 0 ∧ z 0 ≤ max (c - b) a
        have he : c - b ≤ a := by linarith
        rw [min_eq_left he, max_eq_right he]
        constructor <;> linarith [hx.2, hy.2]

def planeRectangle (b c : ℝ) : Fin 4 → Point 3 :=
  ![![b + c, -b, -c], ![c - b, b, -c],
    ![-b - c, b, c], ![b - c, -b, c]]

theorem planeRectangle_zero_sum (b c : ℝ) (i : Fin 4) :
    (∑ k, planeRectangle b c i k) = 0 := by
  fin_cases i <;> norm_num [planeRectangle, Fin.sum_univ_succ] <;> ring

theorem planeRectangle_budget (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (polygonFour (planeRectangle b c)).budget = 8 * (b + c) := by
  have h0 : l1dist (planeRectangle b c 0) (planeRectangle b c 1) = 4 * b := by
    rw [zero_sum_fixed_edge_distance _ _ (planeRectangle_zero_sum b c 0)
      (planeRectangle_zero_sum b c 1) 2 rfl]
    change 2 * |(b + c) - (c - b)| = 4 * b
    rw [show (b + c) - (c - b) = 2 * b by ring,
      abs_of_nonneg (mul_nonneg (by norm_num) hb)]
    ring
  have h1 : l1dist (planeRectangle b c 1) (planeRectangle b c 2) = 4 * c := by
    rw [zero_sum_fixed_edge_distance _ _ (planeRectangle_zero_sum b c 1)
      (planeRectangle_zero_sum b c 2) 1 rfl]
    change 2 * |(c - b) - (-b - c)| = 4 * c
    rw [show (c - b) - (-b - c) = 2 * c by ring,
      abs_of_nonneg (mul_nonneg (by norm_num) hc)]
    ring
  have h2 : l1dist (planeRectangle b c 2) (planeRectangle b c 3) = 4 * b := by
    rw [zero_sum_fixed_edge_distance _ _ (planeRectangle_zero_sum b c 2)
      (planeRectangle_zero_sum b c 3) 2 rfl]
    change 2 * |(-b - c) - (b - c)| = 4 * b
    rw [show (-b - c) - (b - c) = -(2 * b) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg (by norm_num) hb)]
    ring
  have h3 : l1dist (planeRectangle b c 3) (planeRectangle b c 0) = 4 * c := by
    rw [zero_sum_fixed_edge_distance _ _ (planeRectangle_zero_sum b c 3)
      (planeRectangle_zero_sum b c 0) 1 rfl]
    change 2 * |(b - c) - (b + c)| = 4 * c
    rw [show (b - c) - (b + c) = -(2 * c) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg (by norm_num) hc)]
    ring
  rw [polygonFour_budget]
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change l1dist (planeRectangle b c 0) (planeRectangle b c 1) +
    (l1dist (planeRectangle b c 1) (planeRectangle b c 2) +
      (l1dist (planeRectangle b c 2) (planeRectangle b c 3) +
        l1dist (planeRectangle b c 3) (planeRectangle b c 0))) = 8 * (b + c)
  rw [h0, h1, h2, h3]
  ring

/-- The largest coordinate may have no intersection with its original
saturated box face. The actual section then uses the four other faces. -/
theorem planeRectangle_covers (a b c : ℝ) (hdom : b + c < a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (z : Point 3) (hz : (∑ k, z k) = 0)
    (hbox : InSymmetricBox ![a, b, c] z) (hface : TouchesBoxFace ![a, b, c] z) :
    (polygonFour (planeRectangle b c)).Covers z := by
  have hsum : z 0 + z 1 + z 2 = 0 := by
    norm_num [Fin.sum_univ_succ] at hz
    linarith
  have hy : -b ≤ z 1 ∧ z 1 ≤ b := hbox 1
  have hz2 : -c ≤ z 2 ∧ z 2 ≤ c := hbox 2
  obtain ⟨i, hi⟩ := hface
  fin_cases i
  · change |z 0| = a at hi
    have habs : |z 0| ≤ b + c := by
      apply abs_le.mpr
      constructor <;> linarith [hy.1, hy.2, hz2.1, hz2.2]
    have ha : |z 0| = a := hi
    exact False.elim (by linarith)
  · change |z 1| = b at hi
    by_cases hpos : 0 ≤ z 1
    · have hfix : z 1 = b := by simpa only [abs_of_nonneg hpos] using hi
      apply polygonFour_covers_edge _ 1
      apply zero_sum_three_edge_covers _ _ z
        (planeRectangle_zero_sum b c 1) (planeRectangle_zero_sum b c 2) hz
        1 2 (by decide) rfl
      · exact hfix
      · change min (-c) c ≤ z 2 ∧ z 2 ≤ max (-c) c
        rw [min_eq_left (by linarith : -c ≤ c), max_eq_right (by linarith : -c ≤ c)]
        exact hz2
    · have hfix : z 1 = -b := by
        rw [abs_of_nonpos (le_of_not_ge hpos)] at hi
        linarith
      apply polygonFour_covers_edge _ 3
      apply zero_sum_three_edge_covers _ _ z
        (planeRectangle_zero_sum b c 3) (planeRectangle_zero_sum b c 0) hz
        1 2 (by decide) rfl
      · exact hfix
      · change min c (-c) ≤ z 2 ∧ z 2 ≤ max c (-c)
        rw [min_eq_right (by linarith : -c ≤ c), max_eq_left (by linarith : -c ≤ c)]
        exact hz2
  · change |z 2| = c at hi
    by_cases hpos : 0 ≤ z 2
    · have hfix : z 2 = c := by simpa only [abs_of_nonneg hpos] using hi
      apply polygonFour_covers_edge _ 2
      apply zero_sum_three_edge_covers _ _ z
        (planeRectangle_zero_sum b c 2) (planeRectangle_zero_sum b c 3) hz
        2 1 (by decide) rfl
      · exact hfix
      · change min b (-b) ≤ z 1 ∧ z 1 ≤ max b (-b)
        rw [min_eq_right (by linarith : -b ≤ b), max_eq_left (by linarith : -b ≤ b)]
        exact hy
    · have hfix : z 2 = -c := by
        rw [abs_of_nonpos (le_of_not_ge hpos)] at hi
        linarith
      apply polygonFour_covers_edge _ 0
      apply zero_sum_three_edge_covers _ _ z
        (planeRectangle_zero_sum b c 0) (planeRectangle_zero_sum b c 1) hz
        2 1 (by decide) rfl
      · exact hfix
      · change min (-b) b ≤ z 1 ∧ z 1 ≤ max (-b) b
        rw [min_eq_left (by linarith : -b ≤ b), max_eq_right (by linarith : -b ≤ b)]
        exact hy

namespace PhysicalPath

noncomputable def map {d e : ℕ} {a b : Point d} (path : PhysicalPath a b)
    (f : Point d → Point e)
    (hf : ∀ p q, l1dist (f p) (f q) ≤ l1dist p q) :
    PhysicalPath (f a) (f b) :=
  ⟨path.budget, path.nonneg, fun s => f (path.point s),
    congrArg f path.at_zero, congrArg f path.at_budget,
    fun s t hs hst ht => (hf _ _).trans (path.chord s t hs hst ht)⟩

@[simp] theorem map_budget {d e : ℕ} {a b : Point d} (path : PhysicalPath a b)
    (f : Point d → Point e) (hf : ∀ p q, l1dist (f p) (f q) ≤ l1dist p q) :
    (path.map f hf).budget = path.budget := rfl

theorem map_covers {d e : ℕ} {a b z : Point d} (path : PhysicalPath a b)
    (f : Point d → Point e) (hf : ∀ p q, l1dist (f p) (f q) ≤ l1dist p q)
    (hz : path.Covers z) : (path.map f hf).Covers (f z) := by
  obtain ⟨s, hs0, hsP, hsz⟩ := hz
  exact ⟨s, hs0, hsP, congrArg f hsz⟩

end PhysicalPath

def permutePoint {d : ℕ} (e : Equiv.Perm (Fin d)) (z : Point d) : Point d :=
  fun k => z (e k)

theorem permutePoint_distance {d : ℕ} (e : Equiv.Perm (Fin d)) (p q : Point d) :
    l1dist (permutePoint e p) (permutePoint e q) = l1dist p q :=
  sum_perm e (fun k => |p k - q k|)

@[simp] theorem permutePoint_symm_apply {d : ℕ} (e : Equiv.Perm (Fin d))
    (z : Point d) : permutePoint e.symm (permutePoint e z) = z := by
  funext k
  simp only [permutePoint, Equiv.apply_symm_apply]

/-- Exact finite physical perimeter theorem for every three-coordinate
zero-sum box, including unequal and dominant widths. -/
theorem exists_plane_box_tour (L : Point 3) (hL : ∀ i, 0 ≤ L i) :
    ∃ a : Point 3, ∃ path : PhysicalPath a a,
      path.budget ≤ 4 * (∑ i, L i) ∧
      ∀ z : Point 3, (∑ i, z i) = 0 → InSymmetricBox L z →
        TouchesBoxFace L z → path.Covers z := by
  classical
  by_cases h0 : L 0 ≤ L 1 + L 2
  · by_cases h1 : L 1 ≤ L 0 + L 2
    · by_cases h2 : L 2 ≤ L 0 + L 1
      · refine ⟨planeHexagon (L 0) (L 1) (L 2) 0,
          polygonSix (planeHexagon (L 0) (L 1) (L 2)), ?_, ?_⟩
        · rw [planeHexagon_budget _ _ _ h0 h1 h2]
          have hs : (∑ i, L i) = L 0 + L 1 + L 2 := by
            norm_num [Fin.sum_univ_succ]
            ring
          rw [hs]
        · intro z hz hb hf
          have he : (![L 0, L 1, L 2] : Point 3) = L := by
            funext i
            fin_cases i <;> rfl
          apply planeHexagon_covers _ _ _ h0 h1 h2 z hz
          · simpa only [he] using hb
          · simpa only [he] using hf
      · have hdom : L 0 + L 1 < L 2 := lt_of_not_ge h2
        let e : Equiv.Perm (Fin 3) := Equiv.swap 0 2
        let L' : Point 3 := permutePoint e L
        let path := polygonFour (planeRectangle (L' 1) (L' 2))
        let f := permutePoint e.symm
        have hf : ∀ p q, l1dist (f p) (f q) ≤ l1dist p q :=
          fun p q => (permutePoint_distance e.symm p q).le
        have hdom' : L' 1 + L' 2 < L' 0 := by
          change L 1 + L 0 < L 2
          linarith
        refine ⟨f (planeRectangle (L' 1) (L' 2) 0), path.map f hf, ?_, ?_⟩
        · rw [PhysicalPath.map_budget]
          change (polygonFour (planeRectangle (L' 1) (L' 2))).budget ≤ 4 * (∑ i, L i)
          rw [planeRectangle_budget (L' 1) (L' 2) (hL (e 1)) (hL (e 2))]
          have hs : (∑ i, L' i) = ∑ i, L i := sum_perm e L
          have hsum' : (∑ i, L' i) = L' 0 + L' 1 + L' 2 := by
            norm_num [Fin.sum_univ_succ]
            ring
          linarith
        · intro z hz hb hface
          have hsum : (∑ i, permutePoint e z i) = 0 := (sum_perm e z).trans hz
          have hb' : InSymmetricBox ![L' 0, L' 1, L' 2] (permutePoint e z) := by
            intro i
            fin_cases i <;> exact hb (e _)
          have hface' : TouchesBoxFace ![L' 0, L' 1, L' 2] (permutePoint e z) := by
            obtain ⟨i, hi⟩ := hface
            refine ⟨e.symm i, ?_⟩
            have hv : (![L' 0, L' 1, L' 2] : Point 3) = L' := by
              funext t
              fin_cases t <;> rfl
            rw [hv]
            change |z (e (e.symm i))| = L (e (e.symm i))
            simpa only [Equiv.apply_symm_apply] using hi
          have hc := planeRectangle_covers (L' 0) (L' 1) (L' 2) hdom'
            (hL (e 1)) (hL (e 2)) (permutePoint e z) hsum hb' hface'
          have hm := PhysicalPath.map_covers path f hf hc
          simpa only [f, permutePoint_symm_apply] using hm
    · have hdom : L 0 + L 2 < L 1 := lt_of_not_ge h1
      let e : Equiv.Perm (Fin 3) := Equiv.swap 0 1
      let L' : Point 3 := permutePoint e L
      let path := polygonFour (planeRectangle (L' 1) (L' 2))
      let f := permutePoint e.symm
      have hf : ∀ p q, l1dist (f p) (f q) ≤ l1dist p q :=
        fun p q => (permutePoint_distance e.symm p q).le
      have hdom' : L' 1 + L' 2 < L' 0 := by
        change L 0 + L 2 < L 1
        exact hdom
      refine ⟨f (planeRectangle (L' 1) (L' 2) 0), path.map f hf, ?_, ?_⟩
      · rw [PhysicalPath.map_budget]
        change (polygonFour (planeRectangle (L' 1) (L' 2))).budget ≤ 4 * (∑ i, L i)
        rw [planeRectangle_budget (L' 1) (L' 2) (hL (e 1)) (hL (e 2))]
        have hs : (∑ i, L' i) = ∑ i, L i := sum_perm e L
        have hsum' : (∑ i, L' i) = L' 0 + L' 1 + L' 2 := by
          norm_num [Fin.sum_univ_succ]
          ring
        linarith
      · intro z hz hb hface
        have hsum : (∑ i, permutePoint e z i) = 0 := (sum_perm e z).trans hz
        have hb' : InSymmetricBox ![L' 0, L' 1, L' 2] (permutePoint e z) := by
          intro i
          fin_cases i <;> exact hb (e _)
        have hface' : TouchesBoxFace ![L' 0, L' 1, L' 2] (permutePoint e z) := by
          obtain ⟨i, hi⟩ := hface
          refine ⟨e.symm i, ?_⟩
          have hv : (![L' 0, L' 1, L' 2] : Point 3) = L' := by
            funext t
            fin_cases t <;> rfl
          rw [hv]
          change |z (e (e.symm i))| = L (e (e.symm i))
          simpa only [Equiv.apply_symm_apply] using hi
        have hc := planeRectangle_covers (L' 0) (L' 1) (L' 2) hdom'
          (hL (e 1)) (hL (e 2)) (permutePoint e z) hsum hb' hface'
        have hm := PhysicalPath.map_covers path f hf hc
        simpa only [f, permutePoint_symm_apply] using hm
  · have hdom : L 1 + L 2 < L 0 := lt_of_not_ge h0
    refine ⟨planeRectangle (L 1) (L 2) 0, polygonFour (planeRectangle (L 1) (L 2)),
      ?_, ?_⟩
    · rw [planeRectangle_budget _ _ (hL 1) (hL 2)]
      have hs : (∑ i, L i) = L 0 + L 1 + L 2 := by
        norm_num [Fin.sum_univ_succ]
        ring
      linarith
    · intro z hz hb hface
      have he : (![L 0, L 1, L 2] : Point 3) = L := by
        funext i
        fin_cases i <;> rfl
      apply planeRectangle_covers (L 0) (L 1) (L 2) hdom (hL 1) (hL 2) z hz
      · simpa only [he] using hb
      · simpa only [he] using hface

end
end Kusner5.QuartetGeometry
