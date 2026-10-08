import Kusner5.Basic
import Kusner5.Orders

/-!
Actual coordinate extrema, medians and anchored range geometry for the original
sum-of-absolute-values metric. Ties and constant coordinates are retained.
-/

open scoped BigOperators

namespace Kusner5

noncomputable section

/-- Both endpoints are original labels, including when all values coincide. -/
structure CoordinateExtrema {n d : ℕ} (x : Fin n → Point d) (k : Fin d) where
  lo : Fin n
  hi : Fin n
  bound_all : ∀ i, x lo k ≤ x i k ∧ x i k ≤ x hi k

def CoordinateExtrema.range {n d : ℕ} {x : Fin n → Point d} {k : Fin d}
    (e : CoordinateExtrema x k) : ℝ := x e.hi k - x e.lo k

theorem exists_coordinateExtrema {n d : ℕ} [Nonempty (Fin n)]
    (x : Fin n → Point d) (k : Fin d) : Nonempty (CoordinateExtrema x k) := by
  classical
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n))
    (fun i => x i k) Finset.univ_nonempty
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun i => x i k) Finset.univ_nonempty
  exact ⟨⟨a, b, fun i => ⟨hmin i (Finset.mem_univ i),
    hmax i (Finset.mem_univ i)⟩⟩⟩

def coordinateExtrema {n d : ℕ} [Nonempty (Fin n)]
    (x : Fin n → Point d) (k : Fin d) : CoordinateExtrema x k :=
  Classical.choice (exists_coordinateExtrema x k)

theorem coordinate_abs_le_l1dist {d : ℕ} (a b : Point d) (k : Fin d) :
    |a k - b k| ≤ l1dist a b := by
  exact Finset.single_le_sum (fun j _ => abs_nonneg (a j - b j))
    (Finset.mem_univ k)

namespace CoordinateExtrema

variable {n d : ℕ} {x : Fin n → Point d} {k : Fin d}

theorem range_nonneg (e : CoordinateExtrema x k) : 0 ≤ e.range := by
  exact sub_nonneg.mpr (e.bound_all e.hi).1

theorem lo_ne_hi_of_wide (e : CoordinateExtrema x k) (hw : 1 / 2 < e.range) :
    e.lo ≠ e.hi := by
  intro h
  have hz : e.range = 0 := by simp [range, h]
  linarith

theorem range_le_one (e : CoordinateExtrema x k) (hEq : UnitEquilateral x) :
    e.range ≤ 1 := by
  by_cases hab : e.lo = e.hi
  · simp [range, hab]
  · have h := coordinate_abs_le_l1dist (x e.hi) (x e.lo) k
    rw [hEq e.hi e.lo (Ne.symm hab),
      abs_of_nonneg (sub_nonneg.mpr (e.bound_all e.hi).1)] at h
    exact h

end CoordinateExtrema

/-- The ordinary scalar clamp, with the actual two endpoints supplied. -/
def scalarClamp (lo hi t : ℝ) : ℝ := max lo (min hi t)

theorem scalarClamp_of_le_low {lo hi t : ℝ} (hlh : lo ≤ hi) (ht : t ≤ lo) :
    scalarClamp lo hi t = lo := by
  simp only [scalarClamp, min_eq_right (le_trans ht hlh), max_eq_left ht]

theorem scalarClamp_of_mem {lo hi t : ℝ} (htl : lo ≤ t) (hth : t ≤ hi) :
    scalarClamp lo hi t = t := by
  simp only [scalarClamp, min_eq_right hth, max_eq_right htl]

theorem scalarClamp_of_high_le {lo hi t : ℝ} (hlh : lo ≤ hi) (ht : hi ≤ t) :
    scalarClamp lo hi t = hi := by
  simp only [scalarClamp, min_eq_left ht, max_eq_right hlh]

theorem scalarClamp_bounds {lo hi : ℝ} (hlh : lo ≤ hi) (t : ℝ) :
    lo ≤ scalarClamp lo hi t ∧ scalarClamp lo hi t ≤ hi := by
  refine ⟨le_max_left _ _, max_le hlh (min_le_left _ _)⟩

theorem scalarClamp_monotone (lo hi : ℝ) : Monotone (scalarClamp lo hi) := by
  intro s t hst
  exact max_le_max_left lo (min_le_min_left hi hst)

/-- This is the actual median of three original scalar values. -/
def scalarMedian (a b c : ℝ) : ℝ := scalarClamp (min a b) (max a b) c

theorem scalarMedian_comm (a b c : ℝ) : scalarMedian a b c = scalarMedian b a c := by
  simp only [scalarMedian, min_comm, max_comm]

theorem scalarMedian_of_le {a b c : ℝ} (hab : a ≤ b) :
    scalarMedian a b c = scalarClamp a b c := by
  simp only [scalarMedian, min_eq_left hab, max_eq_right hab]

private theorem scalarMedian_geodesics_of_le {a b c : ℝ} (hab : a ≤ b) :
    |a - b| = |a - scalarMedian a b c| + |b - scalarMedian a b c| ∧
    |a - c| = |a - scalarMedian a b c| + |c - scalarMedian a b c| ∧
    |b - c| = |b - scalarMedian a b c| + |c - scalarMedian a b c| := by
  rcases le_total c a with hca | hac
  · have hcb : c ≤ b := le_trans hca hab
    have hm : scalarMedian a b c = a := by
      rw [scalarMedian_of_le hab, scalarClamp_of_le_low hab hca]
    refine ⟨?_, ?_, ?_⟩
    · simp only [hm, sub_self, abs_zero, zero_add, abs_sub_comm]
    · simp only [hm, sub_self, abs_zero, zero_add, abs_sub_comm]
    · rw [hm, abs_of_nonneg (sub_nonneg.mpr hcb),
        abs_of_nonneg (sub_nonneg.mpr hab), abs_of_nonpos (sub_nonpos.mpr hca)]
      ring
  · rcases le_total c b with hcb | hbc
    · have hm : scalarMedian a b c = c := by
        rw [scalarMedian_of_le hab, scalarClamp_of_mem hac hcb]
      refine ⟨?_, ?_, ?_⟩
      · rw [hm, abs_of_nonpos (sub_nonpos.mpr hab),
          abs_of_nonpos (sub_nonpos.mpr hac), abs_of_nonneg (sub_nonneg.mpr hcb)]
        ring
      · simp only [hm, sub_self, abs_zero, add_zero]
      · simp only [hm, sub_self, abs_zero, add_zero]
    · have hac' : a ≤ c := le_trans hab hbc
      have hm : scalarMedian a b c = b := by
        rw [scalarMedian_of_le hab, scalarClamp_of_high_le hab hbc]
      refine ⟨?_, ?_, ?_⟩
      · simp only [hm, sub_self, abs_zero, add_zero]
      · rw [hm, abs_of_nonpos (sub_nonpos.mpr hac'),
          abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonneg (sub_nonneg.mpr hbc)]
        ring
      · simp only [hm, sub_self, abs_zero, zero_add, abs_sub_comm]

theorem scalarMedian_geodesics (a b c : ℝ) :
    |a - b| = |a - scalarMedian a b c| + |b - scalarMedian a b c| ∧
    |a - c| = |a - scalarMedian a b c| + |c - scalarMedian a b c| ∧
    |b - c| = |b - scalarMedian a b c| + |c - scalarMedian a b c| := by
  rcases le_total a b with hab | hba
  · exact scalarMedian_geodesics_of_le hab
  · have h := scalarMedian_geodesics_of_le (c := c) hba
    rw [scalarMedian_comm a b c]
    refine ⟨?_, h.2.2, h.2.1⟩
    rw [abs_sub_comm a b, add_comm]
    exact h.1

def coordinatewiseMedian {d : ℕ} (a b c : Point d) : Point d :=
  fun k => scalarMedian (a k) (b k) (c k)

theorem coordinatewiseMedian_geodesics {d : ℕ} (a b c : Point d) :
    l1dist a b = l1dist a (coordinatewiseMedian a b c) +
      l1dist b (coordinatewiseMedian a b c) ∧
    l1dist a c = l1dist a (coordinatewiseMedian a b c) +
      l1dist c (coordinatewiseMedian a b c) ∧
    l1dist b c = l1dist b (coordinatewiseMedian a b c) +
      l1dist c (coordinatewiseMedian a b c) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    unfold l1dist
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
  · exact (scalarMedian_geodesics (a k) (b k) (c k)).1
  · exact (scalarMedian_geodesics (a k) (b k) (c k)).2.1
  · exact (scalarMedian_geodesics (a k) (b k) (c k)).2.2

theorem triple_median_half {d : ℕ} (a b c : Point d)
    (hab : l1dist a b = 1) (hac : l1dist a c = 1) (hbc : l1dist b c = 1) :
    l1dist a (coordinatewiseMedian a b c) = 1 / 2 ∧
    l1dist b (coordinatewiseMedian a b c) = 1 / 2 ∧
    l1dist c (coordinatewiseMedian a b c) = 1 / 2 := by
  have h := coordinatewiseMedian_geodesics a b c
  rw [hab, hac, hbc] at h
  exact ⟨by linarith [h.1, h.2.1, h.2.2],
    by linarith [h.1, h.2.1, h.2.2], by linarith [h.1, h.2.1, h.2.2]⟩

namespace CoordinateExtrema

variable {n d : ℕ} {x : Fin n → Point d} {k : Fin d}

theorem median_coordinate (e : CoordinateExtrema x k) (i : Fin n) :
    coordinatewiseMedian (x e.lo) (x e.hi) (x i) k = x i k := by
  change scalarMedian (x e.lo k) (x e.hi k) (x i k) = x i k
  rw [scalarMedian_of_le (e.bound_all e.hi).1]
  exact scalarClamp_of_mem (e.bound_all i).1 (e.bound_all i).2

theorem wide_inner_bounds (e : CoordinateExtrema x k) (hEq : UnitEquilateral x)
    (hw : 1 / 2 < e.range) (i : Fin n) (hia : i ≠ e.lo) (hib : i ≠ e.hi) :
    x e.hi k - 1 / 2 ≤ x i k ∧ x i k ≤ x e.lo k + 1 / 2 := by
  have hab := e.lo_ne_hi_of_wide hw
  have hh := triple_median_half (x e.lo) (x e.hi) (x i)
    (hEq e.lo e.hi hab) (hEq e.lo i (Ne.symm hia))
    (hEq e.hi i (Ne.symm hib))
  have hlow := coordinate_abs_le_l1dist (x e.lo)
    (coordinatewiseMedian (x e.lo) (x e.hi) (x i)) k
  have hhigh := coordinate_abs_le_l1dist (x e.hi)
    (coordinatewiseMedian (x e.lo) (x e.hi) (x i)) k
  rw [e.median_coordinate i, hh.1,
    abs_of_nonpos (sub_nonpos.mpr (e.bound_all i).1)] at hlow
  rw [e.median_coordinate i, hh.2.1,
    abs_of_nonneg (sub_nonneg.mpr (e.bound_all i).2)] at hhigh
  exact ⟨by linarith, by linarith⟩

theorem wide_lo_unique (e : CoordinateExtrema x k) (hEq : UnitEquilateral x)
    (hw : 1 / 2 < e.range) (i : Fin n) (hi : x i k = x e.lo k) : i = e.lo := by
  by_contra hia
  have hib : i ≠ e.hi := by
    intro h
    rw [h] at hi
    have hz : e.range = 0 := by simp [range, hi]
    linarith
  have hb := (e.wide_inner_bounds hEq hw i hia hib).1
  rw [hi] at hb
  dsimp [range] at hw
  linarith

theorem wide_hi_unique (e : CoordinateExtrema x k) (hEq : UnitEquilateral x)
    (hw : 1 / 2 < e.range) (i : Fin n) (hi : x i k = x e.hi k) : i = e.hi := by
  by_contra hib
  have hia : i ≠ e.lo := by
    intro h
    rw [h] at hi
    have hz : e.range = 0 := by simp [range, ← hi]
    linarith
  have hb := (e.wide_inner_bounds hEq hw i hia hib).2
  rw [hi] at hb
  dsimp [range] at hw
  linarith

end CoordinateExtrema

end

end Kusner5

namespace Kusner5

noncomputable section

namespace CoordinateExtrema

variable {n d : ℕ} {x : Fin n → Point d} {k : Fin d}

theorem wide_outer_gap_bounds (e : CoordinateExtrema x k) (hEq : UnitEquilateral x)
    (hw : 1 / 2 < e.range) (i : Fin n) (hia : i ≠ e.lo) (hib : i ≠ e.hi) :
    e.range - 1 / 2 ≤ x i k - x e.lo k ∧
    e.range - 1 / 2 ≤ x e.hi k - x i k := by
  have h := e.wide_inner_bounds hEq hw i hia hib
  dsimp [range]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem wide_inner_interval_width (e : CoordinateExtrema x k)
    (hEq : UnitEquilateral x) (hw : 1 / 2 < e.range)
    (i j : Fin n) (hia : i ≠ e.lo) (hib : i ≠ e.hi)
    (hja : j ≠ e.lo) (hjb : j ≠ e.hi) :
    x j k - x i k ≤ 1 - e.range := by
  have hi := e.wide_inner_bounds hEq hw i hia hib
  have hj := e.wide_inner_bounds hEq hw j hja hjb
  dsimp [range]
  linarith [hi.1, hj.2]

/-- A permutation is an order of the SAME original labels; ties are allowed. -/
def ofOrder {m d : ℕ} (x : Fin (m + 1) → Point d) (k : Fin d)
    (p : Equiv.Perm (Fin (m + 1)))
    (hp : Monotone (fun r => x (p r) k)) : CoordinateExtrema x k where
  lo := p 0
  hi := p (Fin.last m)
  bound_all := by
    intro i
    constructor
    · have h := hp (show (0 : Fin (m + 1)) ≤ p.symm i by
        change 0 ≤ (p.symm i).val
        omega)
      simpa using h
    · have h := hp (show p.symm i ≤ Fin.last m by
        change (p.symm i).val ≤ m
        have := (p.symm i).isLt
        omega)
      simpa using h

theorem ofOrder_range {m d : ℕ} (x : Fin (m + 1) → Point d) (k : Fin d)
    (p : Equiv.Perm (Fin (m + 1)))
    (hp : Monotone (fun r => x (p r) k)) :
    (ofOrder x k p hp).range = scalarRange (fun i => x i k) p := rfl

end CoordinateExtrema

theorem wide_ordered_outer_gaps {d : ℕ} (x : Fin 11 → Point d)
    (hEq : UnitEquilateral x) (k : Fin d) (p : Equiv.Perm (Fin 11))
    (hp : Monotone (fun r => x (p r) k))
    (hw : 1 / 2 < scalarRange (fun i => x i k) p) :
    scalarRange (fun i => x i k) p - 1 / 2 ≤ gap (fun i => x i k) p (0 : Fin 10) ∧
    scalarRange (fun i => x i k) p - 1 / 2 ≤ gap (fun i => x i k) p (9 : Fin 10) := by
  let e := CoordinateExtrema.ofOrder x k p hp
  have hew : 1 / 2 < e.range := hw
  have h1lo : p (1 : Fin 11) ≠ e.lo := by
    change p (1 : Fin 11) ≠ p 0
    intro h
    have := p.injective h
    norm_num at this
  have h1hi : p (1 : Fin 11) ≠ e.hi := by
    change p (1 : Fin 11) ≠ p 10
    intro h
    have := p.injective h
    norm_num at this
  have h9lo : p (9 : Fin 11) ≠ e.lo := by
    change p (9 : Fin 11) ≠ p 0
    intro h
    have := p.injective h
    norm_num at this
  have h9hi : p (9 : Fin 11) ≠ e.hi := by
    change p (9 : Fin 11) ≠ p 10
    intro h
    have := p.injective h
    norm_num at this
  have hlow := (e.wide_outer_gap_bounds hEq hew (p 1) h1lo h1hi).1
  have hhigh := (e.wide_outer_gap_bounds hEq hew (p 9) h9lo h9hi).2
  exact ⟨hlow, hhigh⟩

theorem outer_gap_range_inequality {d : ℕ} (x : Fin 11 → Point d)
    (hEq : UnitEquilateral x) (k : Fin d) (p : Equiv.Perm (Fin 11))
    (hp : Monotone (fun r => x (p r) k)) :
    scalarRange (fun i => x i k) p -
      (gap (fun i => x i k) p (0 : Fin 10) + gap (fun i => x i k) p (9 : Fin 10)) / 2
      ≤ 1 / 2 := by
  by_cases hw : 1 / 2 < scalarRange (fun i => x i k) p
  · have h := wide_ordered_outer_gaps x hEq k p hp hw
    linarith [h.1, h.2]
  · have hn := le_of_not_gt hw
    have h0 := gap_nonneg (fun i => x i k) p hp (0 : Fin 10)
    have h9 := gap_nonneg (fun i => x i k) p hp (9 : Fin 10)
    linarith

theorem actual_outer_gap_range_inequality {d : ℕ} (x : Fin 11 → Point d)
    (hEq : UnitEquilateral x) (k : Fin d) :
    scalarRange (fun i => x i k) (columnOrders x k) -
      (gap (fun i => x i k) (columnOrders x k) (0 : Fin 10) +
        gap (fun i => x i k) (columnOrders x k) (9 : Fin 10)) / 2 ≤ 1 / 2 :=
  outer_gap_range_inequality x hEq k (columnOrders x k) (columnOrders_monotone x k)

/-- The actual signed remainder after scalar clamping. -/
def scalarTail (lo hi t : ℝ) : ℝ := t - scalarClamp lo hi t

theorem scalarTail_expr {lo hi : ℝ} (hlh : lo ≤ hi) (t : ℝ) :
    scalarTail lo hi t = min (t - lo) 0 + max (t - hi) 0 := by
  by_cases htl : t ≤ lo
  · rw [scalarTail, scalarClamp_of_le_low hlh htl,
      min_eq_left (sub_nonpos.mpr htl),
      max_eq_right (sub_nonpos.mpr (le_trans htl hlh))]
    ring
  · have hlt : lo ≤ t := le_of_not_ge htl
    by_cases hht : hi ≤ t
    · rw [scalarTail, scalarClamp_of_high_le hlh hht,
        min_eq_right (sub_nonneg.mpr hlt), max_eq_left (sub_nonneg.mpr hht)]
      ring
    · have hth : t ≤ hi := le_of_not_ge hht
      rw [scalarTail, scalarClamp_of_mem hlt hth,
        min_eq_right (sub_nonneg.mpr hlt), max_eq_right (sub_nonpos.mpr hth)]
      ring

theorem scalarTail_monotone {lo hi : ℝ} (hlh : lo ≤ hi) :
    Monotone (scalarTail lo hi) := by
  intro s t hst
  rw [scalarTail_expr hlh s, scalarTail_expr hlh t]
  exact add_le_add (min_le_min_right 0 (sub_le_sub_right hst lo))
    (max_le_max_right 0 (sub_le_sub_right hst hi))

theorem scalarClamp_tail_distance_split {lo hi : ℝ} (hlh : lo ≤ hi) (s t : ℝ) :
    |s - t| = |scalarClamp lo hi s - scalarClamp lo hi t| +
      |scalarTail lo hi s - scalarTail lo hi t| := by
  rcases le_total s t with hst | hts
  · rw [abs_of_nonpos (sub_nonpos.mpr hst),
      abs_of_nonpos (sub_nonpos.mpr (scalarClamp_monotone lo hi hst)),
      abs_of_nonpos (sub_nonpos.mpr (scalarTail_monotone hlh hst))]
    dsimp [scalarTail]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr hts),
      abs_of_nonneg (sub_nonneg.mpr (scalarClamp_monotone lo hi hts)),
      abs_of_nonneg (sub_nonneg.mpr (scalarTail_monotone hlh hts))]
    dsimp [scalarTail]
    ring

theorem scalarTail_pos_clamp {lo hi t : ℝ} (hlh : lo ≤ hi)
    (ht : 0 < scalarTail lo hi t) : scalarClamp lo hi t = hi := by
  by_cases hht : hi ≤ t
  · exact scalarClamp_of_high_le hlh hht
  · have hth : t ≤ hi := le_of_not_ge hht
    have hc : t ≤ scalarClamp lo hi t := by
      rw [scalarClamp, min_eq_right hth]
      exact le_max_right _ _
    dsimp [scalarTail] at ht
    linarith

theorem scalarTail_neg_clamp {lo hi t : ℝ} (hlh : lo ≤ hi)
    (ht : scalarTail lo hi t < 0) : scalarClamp lo hi t = lo := by
  by_cases htl : t ≤ lo
  · exact scalarClamp_of_le_low hlh htl
  · have hlt : lo ≤ t := le_of_not_ge htl
    have hc : scalarClamp lo hi t ≤ t :=
      max_le hlt (min_le_right _ _)
    dsimp [scalarTail] at ht
    linarith

def SameSignedRay (a b : ℝ) : Prop := (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0)

theorem scalarClamp_eq_of_same_tail_ray {lo hi s t : ℝ} (hlh : lo ≤ hi)
    (h : SameSignedRay (scalarTail lo hi s) (scalarTail lo hi t)) :
    scalarClamp lo hi s = scalarClamp lo hi t := by
  rcases h with hpos | hneg
  · rw [scalarTail_pos_clamp hlh hpos.1, scalarTail_pos_clamp hlh hpos.2]
  · rw [scalarTail_neg_clamp hlh hneg.1, scalarTail_neg_clamp hlh hneg.2]

theorem scalarClamp_difference_le_width {lo hi : ℝ} (hlh : lo ≤ hi) (s t : ℝ) :
    |scalarClamp lo hi s - scalarClamp lo hi t| ≤ hi - lo := by
  have hs := scalarClamp_bounds hlh s
  have ht := scalarClamp_bounds hlh t
  exact abs_le.mpr ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩

def scalarOverlap (a b : ℝ) : ℝ := (|a| + |b| - |a - b|) / 2

theorem scalarOverlap_comm (a b : ℝ) : scalarOverlap a b = scalarOverlap b a := by
  simp only [scalarOverlap, abs_sub_comm, add_comm]

theorem scalarOverlap_nonneg (a b : ℝ) : 0 ≤ scalarOverlap a b := by
  have h : |a - b| ≤ |a| + |b| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le a 0 b
  dsimp [scalarOverlap]
  linarith

theorem scalarOverlap_eq_min_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    scalarOverlap a b = min a b := by
  rcases le_total a b with hab | hba
  · rw [scalarOverlap, abs_of_nonneg ha, abs_of_nonneg hb,
      abs_of_nonpos (sub_nonpos.mpr hab), min_eq_left hab]
    ring
  · rw [scalarOverlap, abs_of_nonneg ha, abs_of_nonneg hb,
      abs_of_nonneg (sub_nonneg.mpr hba), min_eq_right hba]
    ring

theorem scalarOverlap_eq_min_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    scalarOverlap a b = min (-a) (-b) := by
  rcases le_total a b with hab | hba
  · have hneg : -b ≤ -a := by linarith
    rw [scalarOverlap, abs_of_nonpos ha, abs_of_nonpos hb,
      abs_of_nonpos (sub_nonpos.mpr hab), min_eq_right hneg]
    ring
  · have hneg : -a ≤ -b := by linarith
    rw [scalarOverlap, abs_of_nonpos ha, abs_of_nonpos hb,
      abs_of_nonneg (sub_nonneg.mpr hba), min_eq_left hneg]
    ring

theorem scalarOverlap_eq_zero_of_opposite {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    scalarOverlap a b = 0 := by
  have hab : a - b ≤ 0 := by linarith
  rw [scalarOverlap, abs_of_nonpos ha, abs_of_nonneg hb, abs_of_nonpos hab]
  ring

def l1mass {I : Type*} [Fintype I] (x : I → ℝ) : ℝ := ∑ k, |x k|

def l1overlap {I : Type*} [Fintype I] (x y : I → ℝ) : ℝ :=
  ∑ k, scalarOverlap (x k) (y k)

theorem sum_distance_overlap_identity {I : Type*} [Fintype I] (x y : I → ℝ) :
    (∑ k, |x k - y k|) = l1mass x + l1mass y - 2 * l1overlap x y := by
  calc
    (∑ k, |x k - y k|) = ∑ k, (|x k| + |y k| - 2 * scalarOverlap (x k) (y k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [scalarOverlap]
      ring
    _ = _ := by
      simp only [l1mass, l1overlap, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.mul_sum]

theorem l1dist_overlap_identity {d : ℕ} (x y : Point d) :
    l1dist x y = l1mass x + l1mass y - 2 * l1overlap x y :=
  sum_distance_overlap_identity x y

def boxClamp {d : ℕ} (lo hi p : Point d) : Point d :=
  fun k => scalarClamp (lo k) (hi k) (p k)

def boxTail {d : ℕ} (lo hi p : Point d) : Point d :=
  fun k => scalarTail (lo k) (hi k) (p k)

theorem box_distance_split {d : ℕ} (lo hi p q : Point d) (hbox : ∀ k, lo k ≤ hi k) :
    l1dist p q = l1dist (boxClamp lo hi p) (boxClamp lo hi q) +
      l1dist (boxTail lo hi p) (boxTail lo hi q) := by
  unfold l1dist
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact scalarClamp_tail_distance_split (hbox k) (p k) (q k)

theorem box_tail_mass {d : ℕ} (lo hi p : Point d) :
    l1mass (boxTail lo hi p) = l1dist p (boxClamp lo hi p) := rfl

/-- Literal deletion of one physical scalar coordinate, not metric projection. -/
def erasedDistance {d : ℕ} (k : Fin d) (p q : Point d) : ℝ :=
  ∑ j ∈ Finset.univ.erase k, |p j - q j|

theorem erased_distance_nonneg {d : ℕ} (k : Fin d) (p q : Point d) :
    0 ≤ erasedDistance k p q := by
  exact Finset.sum_nonneg (fun j _ => abs_nonneg (p j - q j))

theorem erased_distance_comm {d : ℕ} (k : Fin d) (p q : Point d) :
    erasedDistance k p q = erasedDistance k q p := by
  simp only [erasedDistance, abs_sub_comm]

theorem erased_distance_triangle {d : ℕ} (k : Fin d) (p q r : Point d) :
    erasedDistance k p r ≤ erasedDistance k p q + erasedDistance k q r := by
  unfold erasedDistance
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun j _ => abs_sub_le (p j) (q j) (r j))

theorem erased_distance_add_coordinate {d : ℕ} (k : Fin d) (p q : Point d) :
    erasedDistance k p q + |p k - q k| = l1dist p q := by
  exact Finset.sum_erase_add _ _ (Finset.mem_univ k)

theorem erased_distance_reverse_triangle {d : ℕ} (k : Fin d) (a p q : Point d) :
    |erasedDistance k a p - erasedDistance k a q| ≤ erasedDistance k p q := by
  have h1 := erased_distance_triangle k a p q
  have h2 := erased_distance_triangle k a q p
  rw [erased_distance_comm k q p] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def anchorLow {d : ℕ} (a b : Point d) : Point d := fun k => min (a k) (b k)

def anchorHigh {d : ℕ} (a b : Point d) : Point d := fun k => max (a k) (b k)

def anchorClamp {d : ℕ} (a b p : Point d) : Point d := coordinatewiseMedian a b p

def anchorTail {d : ℕ} (a b p : Point d) : Point d :=
  boxTail (anchorLow a b) (anchorHigh a b) p

theorem anchor_distance_split {d : ℕ} (a b p q : Point d) :
    l1dist p q = l1dist (anchorClamp a b p) (anchorClamp a b q) +
      l1dist (anchorTail a b p) (anchorTail a b q) :=
  box_distance_split (anchorLow a b) (anchorHigh a b) p q
    (fun k => min_le_max)

theorem anchor_tail_mass {d : ℕ} (a b p : Point d) :
    l1mass (anchorTail a b p) = l1dist p (anchorClamp a b p) := rfl

theorem max_sub_min_eq_abs_difference (a b : ℝ) : max a b - min a b = |a - b| := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · rw [max_eq_left hba, min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]

namespace CoordinateExtrema

variable {n d : ℕ} {x : Fin n → Point d} {k : Fin d}

theorem erased_anchor_distance (e : CoordinateExtrema x k) (hEq : UnitEquilateral x)
    (hw : 1 / 2 < e.range) :
    erasedDistance k (x e.lo) (x e.hi) = 1 - e.range := by
  have h := erased_distance_add_coordinate k (x e.lo) (x e.hi)
  rw [hEq e.lo e.hi (e.lo_ne_hi_of_wide hw),
    abs_of_nonpos (sub_nonpos.mpr (e.bound_all e.hi).1)] at h
  dsimp [range]
  linarith

theorem anchor_tail_selected_zero (e : CoordinateExtrema x k) (i : Fin n) :
    anchorTail (x e.lo) (x e.hi) (x i) k = 0 := by
  change x i k - coordinatewiseMedian (x e.lo) (x e.hi) (x i) k = 0
  rw [e.median_coordinate i]
  ring

theorem anchor_tail_mass_half (e : CoordinateExtrema x k) (hEq : UnitEquilateral x)
    (hw : 1 / 2 < e.range) (i : Fin n) (hia : i ≠ e.lo) (hib : i ≠ e.hi) :
    l1mass (anchorTail (x e.lo) (x e.hi) (x i)) = 1 / 2 := by
  rw [anchor_tail_mass]
  exact (triple_median_half (x e.lo) (x e.hi) (x i)
    (hEq e.lo e.hi (e.lo_ne_hi_of_wide hw))
    (hEq e.lo i (Ne.symm hia)) (hEq e.hi i (Ne.symm hib))).2.2

theorem anchor_remaining_half (e : CoordinateExtrema x k) (hEq : UnitEquilateral x)
    (hw : 1 / 2 < e.range) (i : Fin n) (hia : i ≠ e.lo) (hib : i ≠ e.hi) :
    erasedDistance k (x e.lo) (anchorClamp (x e.lo) (x e.hi) (x i)) =
      1 / 2 - (x i k - x e.lo k) := by
  have hh := (triple_median_half (x e.lo) (x e.hi) (x i)
    (hEq e.lo e.hi (e.lo_ne_hi_of_wide hw))
    (hEq e.lo i (Ne.symm hia)) (hEq e.hi i (Ne.symm hib))).1
  have hc := e.median_coordinate i
  have h := erased_distance_add_coordinate k (x e.lo)
    (anchorClamp (x e.lo) (x e.hi) (x i))
  have h' : anchorClamp (x e.lo) (x e.hi) (x i) =
      coordinatewiseMedian (x e.lo) (x e.hi) (x i) := rfl
  rw [h'] at h ⊢
  rw [hc, hh, abs_of_nonpos (sub_nonpos.mpr (e.bound_all i).1)] at h
  linarith

/-- The deleted original scalar difference is controlled, rather than omitted. -/
theorem anchor_deleted_difference_le (e : CoordinateExtrema x k)
    (hEq : UnitEquilateral x) (hw : 1 / 2 < e.range)
    (i j : Fin n) (hia : i ≠ e.lo) (hib : i ≠ e.hi)
    (hja : j ≠ e.lo) (hjb : j ≠ e.hi) :
    |x i k - x j k| ≤ erasedDistance k
      (anchorClamp (x e.lo) (x e.hi) (x i))
      (anchorClamp (x e.lo) (x e.hi) (x j)) := by
  have h := erased_distance_reverse_triangle k (x e.lo)
    (anchorClamp (x e.lo) (x e.hi) (x i))
    (anchorClamp (x e.lo) (x e.hi) (x j))
  rw [e.anchor_remaining_half hEq hw i hia hib,
    e.anchor_remaining_half hEq hw j hja hjb] at h
  have hs : (1 / 2 - (x i k - x e.lo k)) -
      (1 / 2 - (x j k - x e.lo k)) = -(x i k - x j k) := by ring
  rw [hs, abs_neg] at h
  exact h

theorem anchor_tail_overlap_le (e : CoordinateExtrema x k)
    (hEq : UnitEquilateral x) (hw : 1 / 2 < e.range)
    (i j : Fin n) (hij : i ≠ j) (hia : i ≠ e.lo) (hib : i ≠ e.hi)
    (hja : j ≠ e.lo) (hjb : j ≠ e.hi) :
    l1overlap (anchorTail (x e.lo) (x e.hi) (x i))
      (anchorTail (x e.lo) (x e.hi) (x j)) ≤ erasedDistance k
      (anchorClamp (x e.lo) (x e.hi) (x i))
      (anchorClamp (x e.lo) (x e.hi) (x j)) := by
  have hsplit := anchor_distance_split (x e.lo) (x e.hi) (x i) (x j)
  rw [hEq i j hij] at hsplit
  have htail := l1dist_overlap_identity
    (anchorTail (x e.lo) (x e.hi) (x i))
    (anchorTail (x e.lo) (x e.hi) (x j))
  rw [e.anchor_tail_mass_half hEq hw i hia hib,
    e.anchor_tail_mass_half hEq hw j hja hjb] at htail
  have hc1 : anchorClamp (x e.lo) (x e.hi) (x i) k = x i k := e.median_coordinate i
  have hc2 : anchorClamp (x e.lo) (x e.hi) (x j) k = x j k := e.median_coordinate j
  have hclamp := erased_distance_add_coordinate k
    (anchorClamp (x e.lo) (x e.hi) (x i))
    (anchorClamp (x e.lo) (x e.hi) (x j))
  rw [hc1, hc2] at hclamp
  have hdeleted := e.anchor_deleted_difference_le hEq hw i j hia hib hja hjb
  linarith

end CoordinateExtrema

end

end Kusner5

namespace Kusner5

noncomputable section

/-- One of the two ACTUAL signed rays of a physical coordinate. -/
def rayMagnitude (a : ℝ) (positive : Bool) : ℝ :=
  if positive then max a 0 else max (-a) 0

theorem ray_dominance_overlap {a b : ℝ} (ha : a ≠ 0)
    (hb : rayMagnitude a (decide (0 < a)) ≤ rayMagnitude b (decide (0 < a))) :
    SameSignedRay a b ∧ scalarOverlap a b = |a| := by
  by_cases hap : 0 < a
  · have hmax : a ≤ max b 0 := by
      simpa [rayMagnitude, hap, max_eq_left hap.le] using hb
    have hbp : 0 < b := by
      by_contra hn
      have hbn : b ≤ 0 := le_of_not_gt hn
      rw [max_eq_right hbn] at hmax
      linarith
    have hab : a ≤ b := by rw [max_eq_left hbp.le] at hmax; exact hmax
    refine ⟨Or.inl ⟨hap, hbp⟩, ?_⟩
    rw [scalarOverlap_eq_min_nonneg hap.le hbp.le, min_eq_left hab, abs_of_pos hap]
  · have han : a < 0 := lt_of_le_of_ne (le_of_not_gt hap) ha
    have hmax : -a ≤ max (-b) 0 := by
      simpa [rayMagnitude, hap, max_eq_left (neg_nonneg.mpr han.le)] using hb
    have hbn : b < 0 := by
      by_contra hn
      have hbp : 0 ≤ b := le_of_not_gt hn
      rw [max_eq_right (neg_nonpos.mpr hbp)] at hmax
      linarith
    have hab : -a ≤ -b := by
      rw [max_eq_left (neg_nonneg.mpr hbn.le)] at hmax
      exact hmax
    refine ⟨Or.inr ⟨han, hbn⟩, ?_⟩
    rw [scalarOverlap_eq_min_nonpos han.le hbn.le, min_eq_left hab, abs_of_neg han]

theorem exists_maximum_ray_owners {U I : Type*} [Fintype U] [Nonempty U] [Fintype I]
    (w : U → I → ℝ) :
    ∃ owner : I × Bool → U, ∀ r j,
      rayMagnitude (w j r.1) r.2 ≤ rayMagnitude (w (owner r) r.1) r.2 := by
  classical
  have hex : ∀ r : I × Bool, ∃ h : U, ∀ j : U,
      rayMagnitude (w j r.1) r.2 ≤ rayMagnitude (w h r.1) r.2 := by
    intro r
    obtain ⟨h, hh, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset U)
      (fun j => rayMagnitude (w j r.1) r.2) Finset.univ_nonempty
    exact ⟨h, fun j => hmax j (Finset.mem_univ j)⟩
  choose owner howner using hex
  exact ⟨owner, howner⟩

/-- Distinct original owners are grouped before original pair bounds are summed.
The hypotheses here are the explicit tail/bridge facts derived below from the
original configuration; this lemma assumes no range cap or cardinality theorem. -/
theorem four_coordinate_owner_cap {U I : Type*} [Fintype U] [Nonempty U] [Fintype I]
    (hU : Fintype.card U = 9) (hI : Fintype.card I = 4)
    (w : U → I → ℝ) (ell : I → ℝ) (rho : ℝ)
    (hell : ∀ i, 0 ≤ ell i) (hrho : (∑ i, ell i) = rho)
    (hmass : ∀ j, l1mass (w j) = 1 / 2)
    (hpair : ∀ j h, j ≠ h → ∀ S : Finset I,
      (∀ i ∈ S, SameSignedRay (w j i) (w h i)) →
      l1overlap (w j) (w h) + (∑ i ∈ S, ell i) ≤ rho) :
    1 / 2 ≤ 3 * rho := by
  classical
  obtain ⟨owner, howner⟩ := exists_maximum_ray_owners w
  have hex : ∃ j : U, ∀ r : I × Bool, owner r ≠ j := by
    by_contra hn
    push_neg at hn
    have hsurj : Function.Surjective owner := hn
    have hc := Fintype.card_le_of_surjective owner hsurj
    simp only [Fintype.card_prod, Fintype.card_bool, hU, hI] at hc
    norm_num at hc
  obtain ⟨j, hj⟩ := hex
  let assigned : I → U := fun i => owner (i, decide (0 < w j i))
  let T : Finset I := Finset.univ.filter (fun i => w j i ≠ 0)
  let H : Finset U := T.image assigned
  have hdom : ∀ i ∈ T, SameSignedRay (w j i) (w (assigned i) i) ∧
      scalarOverlap (w j i) (w (assigned i) i) = |w j i| := by
    intro i hi
    exact ray_dominance_overlap (Finset.mem_filter.mp hi).2
      (howner (i, decide (0 < w j i)) j)
  have hcoverage : l1mass (w j) ≤ ∑ h ∈ H, l1overlap (w j) (w h) := by
    have hcoord : ∀ i : I, |w j i| ≤ ∑ h ∈ H, scalarOverlap (w j i) (w h i) := by
      intro i
      by_cases hz : w j i = 0
      · rw [hz, abs_zero]
        exact Finset.sum_nonneg (fun h _ => scalarOverlap_nonneg _ _)
      · have hi : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hz⟩
        have hh : assigned i ∈ H := Finset.mem_image.mpr ⟨i, hi, rfl⟩
        rw [← (hdom i hi).2]
        exact Finset.single_le_sum
          (f := fun h => scalarOverlap (w j i) (w h i))
          (fun h _ => scalarOverlap_nonneg _ _) hh
    calc
      l1mass (w j) ≤ ∑ i : I, ∑ h ∈ H, scalarOverlap (w j i) (w h i) :=
        Finset.sum_le_sum (fun i _ => hcoord i)
      _ = ∑ h ∈ H, l1overlap (w j) (w h) := by
        rw [Finset.sum_comm]
        rfl
  have hEach : ∀ h ∈ H,
      l1overlap (w j) (w h) + (∑ i ∈ T.filter (fun i => assigned i = h), ell i) ≤ rho := by
    intro h hh
    have hjh : j ≠ h := by
      obtain ⟨i, hi, hih⟩ := Finset.mem_image.mp hh
      have hne : assigned i ≠ j := hj (i, decide (0 < w j i))
      rw [hih] at hne
      exact Ne.symm hne
    apply hpair j h hjh
    intro i hi
    have hif := Finset.mem_filter.mp hi
    have hs := (hdom i hif.1).1
    simpa only [hif.2] using hs
  have hPartition :
      (∑ h ∈ H, ∑ i ∈ T.filter (fun i => assigned i = h), ell i) = ∑ i ∈ T, ell i := by
    calc
      _ = ∑ h ∈ H, ∑ i ∈ T, if assigned i = h then ell i else 0 := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [Finset.sum_filter]
      _ = ∑ i ∈ T, ∑ h ∈ H, if assigned i = h then ell i else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ i ∈ T, ell i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hh : assigned i ∈ H := Finset.mem_image.mpr ⟨i, hi, rfl⟩
        rw [Finset.sum_eq_single (assigned i)]
        · simp
        · intro h hh' hne
          exact if_neg (Ne.symm hne)
        · intro hnot
          exact False.elim (hnot hh)
  have hTotal := Finset.sum_le_sum (fun h hh => hEach h hh)
  have hTotal' : l1mass (w j) + (∑ i ∈ T, ell i) ≤ (H.card : ℝ) * rho := by
    have ht : (∑ h ∈ H, l1overlap (w j) (w h)) + (∑ i ∈ T, ell i) ≤
        (H.card : ℝ) * rho := by
      simpa only [Finset.sum_add_distrib, hPartition, Finset.sum_const, nsmul_eq_mul]
        using hTotal
    linarith
  rw [hmass j] at hTotal'
  have hHT : H.card ≤ T.card := Finset.card_image_le
  have hTI : T.card ≤ 4 := by
    calc
      T.card ≤ (Finset.univ : Finset I).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 4 := by simp only [Finset.card_univ, hI]
  have hrn : 0 ≤ rho := by
    rw [← hrho]
    exact Finset.sum_nonneg (fun i _ => hell i)
  by_cases hsmall : H.card ≤ 3
  · have hcast : (H.card : ℝ) ≤ 3 := by exact_mod_cast hsmall
    have hsn : 0 ≤ ∑ i ∈ T, ell i := Finset.sum_nonneg (fun i _ => hell i)
    have hmult := mul_le_mul_of_nonneg_right hcast hrn
    linarith
  · have hH : H.card = 4 := by omega
    have hT : T.card = (Finset.univ : Finset I).card := by
      simp only [Finset.card_univ, hI]
      omega
    have hTeq : T = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ T) (le_of_eq hT.symm)
    rw [hTeq, hrho, hH] at hTotal'
    norm_num at hTotal'
    linarith

theorem sum_over_finset {I : Type*} [DecidableEq I] (S : Finset I) (f : I → ℝ) :
    (∑ i : S, f i.val) = ∑ i ∈ S, f i := by
  classical
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    exact i.property
  · intro i hi j hj heq
    exact Subtype.ext heq
  · intro i hi
    exact ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  · intro i hi
    rfl

theorem sum_indicator_finset {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (f : I → ℝ) :
    (∑ i : I, if i ∈ S then f i else 0) = ∑ i ∈ S, f i := by
  classical
  calc
    _ = ∑ i ∈ S, if i ∈ S then f i else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i hi hnot
      simp only [hnot, if_false]
    _ = _ := by simp

def remainingCoordinates {d : ℕ} (k : Fin d) : Finset (Fin d) := Finset.univ.erase k

theorem remaining_coordinates_card (k : Fin 5) : (remainingCoordinates k).card = 4 := by
  simp [remainingCoordinates]

theorem restricted_sum_zero_coordinate {d : ℕ} (k : Fin d) (f : Fin d → ℝ)
    (hz : f k = 0) : (∑ i : remainingCoordinates k, f i.val) = ∑ i : Fin d, f i := by
  rw [sum_over_finset]
  have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ k)
  rw [hz, add_zero] at h
  exact h

namespace CoordinateExtrema

def innerLabels {n d : ℕ} {x : Fin n → Point d} {k : Fin d}
    (e : CoordinateExtrema x k) : Finset (Fin n) :=
  (Finset.univ.erase e.lo).erase e.hi

theorem mem_innerLabels {n d : ℕ} {x : Fin n → Point d} {k : Fin d}
    (e : CoordinateExtrema x k) (i : Fin n) :
    i ∈ e.innerLabels ↔ i ≠ e.lo ∧ i ≠ e.hi := by
  simp only [innerLabels, Finset.mem_erase, Finset.mem_univ, and_true]
  exact and_comm

theorem inner_labels_card {d : ℕ} {x : Fin 11 → Point d} {k : Fin d}
    (e : CoordinateExtrema x k) (hab : e.lo ≠ e.hi) : e.innerLabels.card = 9 := by
  have hb : e.hi ∈ (Finset.univ : Finset (Fin 11)).erase e.lo :=
    Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ e.hi⟩
  rw [innerLabels, Finset.card_erase_of_mem hb,
    Finset.card_erase_of_mem (Finset.mem_univ e.lo)]
  norm_num

/-- Only shared NONZERO signed tails remove bridge widths. No original pair
or deleted scalar contribution is discarded in this bound. -/
theorem anchor_tail_shared_width_bound {x : Configuration} {k : Coordinate}
    (e : CoordinateExtrema x k) (hEq : UnitEquilateral x) (hw : 1 / 2 < e.range)
    (i j : Label) (hij : i ≠ j) (hia : i ≠ e.lo) (hib : i ≠ e.hi)
    (hja : j ≠ e.lo) (hjb : j ≠ e.hi)
    (S : Finset (remainingCoordinates k))
    (hshared : ∀ c ∈ S,
      SameSignedRay (anchorTail (x e.lo) (x e.hi) (x i) c.val)
        (anchorTail (x e.lo) (x e.hi) (x j) c.val)) :
    l1overlap (anchorTail (x e.lo) (x e.hi) (x i))
      (anchorTail (x e.lo) (x e.hi) (x j)) +
      (∑ c ∈ S, |x e.lo c.val - x e.hi c.val|) ≤ 1 - e.range := by
  classical
  have hp : ∀ c : remainingCoordinates k,
      |anchorClamp (x e.lo) (x e.hi) (x i) c.val -
        anchorClamp (x e.lo) (x e.hi) (x j) c.val| +
        (if c ∈ S then |x e.lo c.val - x e.hi c.val| else 0) ≤
        |x e.lo c.val - x e.hi c.val| := by
    intro c
    by_cases hc : c ∈ S
    · have heq : anchorClamp (x e.lo) (x e.hi) (x i) c.val =
          anchorClamp (x e.lo) (x e.hi) (x j) c.val :=
        scalarClamp_eq_of_same_tail_ray min_le_max (hshared c hc)
      simp [heq, hc]
    · have h := scalarClamp_difference_le_width
        (lo := min (x e.lo c.val) (x e.hi c.val))
        (hi := max (x e.lo c.val) (x e.hi c.val)) min_le_max
        (x i c.val) (x j c.val)
      rw [max_sub_min_eq_abs_difference] at h
      show |anchorClamp (x e.lo) (x e.hi) (x i) c.val -
          anchorClamp (x e.lo) (x e.hi) (x j) c.val| +
        (if c ∈ S then |x e.lo c.val - x e.hi c.val| else 0) ≤
        |x e.lo c.val - x e.hi c.val|
      rw [if_neg hc, show anchorClamp (x e.lo) (x e.hi) (x i) c.val -
          anchorClamp (x e.lo) (x e.hi) (x j) c.val =
        scalarClamp (min (x e.lo c.val) (x e.hi c.val))
          (max (x e.lo c.val) (x e.hi c.val)) (x i c.val) -
        scalarClamp (min (x e.lo c.val) (x e.hi c.val))
          (max (x e.lo c.val) (x e.hi c.val)) (x j c.val) from rfl]
      linarith
  have hs : (∑ c : remainingCoordinates k,
      (|anchorClamp (x e.lo) (x e.hi) (x i) c.val -
        anchorClamp (x e.lo) (x e.hi) (x j) c.val| +
        (if c ∈ S then |x e.lo c.val - x e.hi c.val| else 0))) ≤
      ∑ c : remainingCoordinates k, |x e.lo c.val - x e.hi c.val| := by
    apply Finset.sum_le_sum
    intro c _
    exact hp c
  have hclamp : (∑ c : remainingCoordinates k,
      |anchorClamp (x e.lo) (x e.hi) (x i) c.val -
        anchorClamp (x e.lo) (x e.hi) (x j) c.val|) =
      erasedDistance k (anchorClamp (x e.lo) (x e.hi) (x i))
        (anchorClamp (x e.lo) (x e.hi) (x j)) :=
    sum_over_finset (remainingCoordinates k)
      (fun c => |anchorClamp (x e.lo) (x e.hi) (x i) c -
        anchorClamp (x e.lo) (x e.hi) (x j) c|)
  have hwidth : (∑ c : remainingCoordinates k, |x e.lo c.val - x e.hi c.val|) =
      1 - e.range := by
    rw [sum_over_finset (remainingCoordinates k)
      (fun c => |x e.lo c - x e.hi c|)]
    exact e.erased_anchor_distance hEq hw
  rw [Finset.sum_add_distrib, sum_indicator_finset, hclamp, hwidth] at hs
  have ho := e.anchor_tail_overlap_le hEq hw i j hij hia hib hja hjb
  linarith

end CoordinateExtrema

/-- Every actual coordinate range of ALL eleven original real unit-equilateral
labels is at most five sixths. The nine-label tail family and four remaining
physical coordinates below are derived from the original input. -/
theorem coordinate_range_le_five_sixths {x : Configuration} {k : Coordinate}
    (hEq : UnitEquilateral x) (e : CoordinateExtrema x k) : e.range ≤ 5 / 6 := by
  classical
  by_cases hw : 1 / 2 < e.range
  · let U := ↥e.innerLabels
    let I := ↥(remainingCoordinates k)
    have hU : Fintype.card U = 9 := by
      rw [Fintype.card_coe]
      exact e.inner_labels_card (e.lo_ne_hi_of_wide hw)
    have hI : Fintype.card I = 4 := by
      rw [Fintype.card_coe]
      exact remaining_coordinates_card k
    obtain ⟨u, hu⟩ : e.innerLabels.Nonempty := by
      have hpos : e.innerLabels.card = 9 :=
        e.inner_labels_card (e.lo_ne_hi_of_wide hw)
      have hpos2 : 0 < e.innerLabels.card := by rw [hpos]; norm_num
      exact Finset.card_pos.mp hpos2
    letI : Nonempty U := ⟨⟨u, hu⟩⟩
    let w : U → I → ℝ := fun j c => anchorTail (x e.lo) (x e.hi) (x j.val) c.val
    let ell : I → ℝ := fun c => |x e.lo c.val - x e.hi c.val|
    have hell : ∀ c, 0 ≤ ell c := fun c => abs_nonneg _
    have hrho : (∑ c, ell c) = 1 - e.range := by
      change (∑ c : remainingCoordinates k, |x e.lo c.val - x e.hi c.val|) = 1 - e.range
      rw [sum_over_finset (remainingCoordinates k)
        (fun c => |x e.lo c - x e.hi c|)]
      exact e.erased_anchor_distance hEq hw
    have hmass : ∀ j : U, l1mass (w j) = 1 / 2 := by
      intro j
      have hj := (e.mem_innerLabels j.val).mp j.property
      have hs := restricted_sum_zero_coordinate k
        (fun c => |anchorTail (x e.lo) (x e.hi) (x j.val) c|) (by
          rw [e.anchor_tail_selected_zero j.val, abs_zero])
      have hh := e.anchor_tail_mass_half hEq hw j.val hj.1 hj.2
      exact hs.trans hh
    have hpair : ∀ j h : U, j ≠ h → ∀ S : Finset I,
        (∀ c ∈ S, SameSignedRay (w j c) (w h c)) →
        l1overlap (w j) (w h) + (∑ c ∈ S, ell c) ≤ 1 - e.range := by
      intro j h hjh S hshared
      have hj := (e.mem_innerLabels j.val).mp j.property
      have hh := (e.mem_innerLabels h.val).mp h.property
      have hjh' : j.val ≠ h.val := fun hv => hjh (Subtype.ext hv)
      have ho : l1overlap (w j) (w h) =
          l1overlap (anchorTail (x e.lo) (x e.hi) (x j.val))
            (anchorTail (x e.lo) (x e.hi) (x h.val)) := by
        exact restricted_sum_zero_coordinate k
          (fun c => scalarOverlap (anchorTail (x e.lo) (x e.hi) (x j.val) c)
            (anchorTail (x e.lo) (x e.hi) (x h.val) c)) (by
              rw [e.anchor_tail_selected_zero j.val, e.anchor_tail_selected_zero h.val]
              norm_num [scalarOverlap])
      rw [ho]
      exact e.anchor_tail_shared_width_bound hEq hw j.val h.val hjh' hj.1 hj.2 hh.1 hh.2
        S hshared
    have hcap := four_coordinate_owner_cap hU hI w ell (1 - e.range) hell hrho hmass hpair
    linarith
  · have hn := le_of_not_gt hw
    linarith

theorem actual_coordinate_range_le_five_sixths (x : Configuration)
    (hEq : UnitEquilateral x) (k : Coordinate) :
    scalarRange (fun i => x i k) (columnOrders x k) ≤ 5 / 6 :=
  coordinate_range_le_five_sixths hEq
    (CoordinateExtrema.ofOrder x k (columnOrders x k) (columnOrders_monotone x k))

end

end Kusner5
