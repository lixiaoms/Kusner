import Kusner5.Orders
import Kusner5.QuartetBoundary
import Kusner5.RangeGeometry

/-!
An arbitrary quartet of the ORIGINAL eleven labels. The selected labels are
not contacts, and every quantity below is computed in the five original scalar
coordinates. Actual sorted orders retain ties and their zero gaps.

The final arbitrary-quartet lower bound is an outstanding obligation until its
full seven-outsider physical bridge and perimeter argument are implemented.
-/

open scoped BigOperators

namespace Kusner5

noncomputable section

def quartetColumn (x : Configuration) (q : Fin 4 → Label) (k : Coordinate) :
    Fin 4 → ℝ := fun i => x (q i) k

def quartetOrder (x : Configuration) (q : Fin 4 → Label) (k : Coordinate) :
    Equiv.Perm (Fin 4) := actualOrder (quartetColumn x q k)

def quartetGap (x : Configuration) (q : Fin 4 → Label) (k : Coordinate)
    (r : Fin 3) : ℝ := gap (quartetColumn x q k) (quartetOrder x q k) r

/-- Sum of genuine max-minus-min ranges of the selected original labels. -/
def quartetWidth (x : Configuration) (q : Fin 4 → Label) : ℝ :=
  ∑ k, scalarRange (quartetColumn x q k) (quartetOrder x q k)

def quartetSingletonAt (x : Configuration) (q : Fin 4 → Label)
    (i : Fin 4) (k : Coordinate) : ℝ :=
  (if quartetOrder x q k 0 = i then quartetGap x q k 0 else 0) +
    (if quartetOrder x q k 3 = i then quartetGap x q k 2 else 0)

def quartetSingletonWidth (x : Configuration) (q : Fin 4 → Label)
    (i : Fin 4) : ℝ := ∑ k, quartetSingletonAt x q i k

def tetrahedralSign (i : Fin 4) (t : Fin 3) : ℤ :=
  if i.val = 0 ∨ i.val = t.val + 1 then 1 else -1

def rankSign (r : Fin 4 → Fin 4) (i : Fin 4) : ℤ :=
  if (r i).val < 2 then -1 else 1

def rankPartition (r : Fin 4 → Fin 4) : Fin 3 :=
  if rankSign r 1 = rankSign r 0 then 0
  else if rankSign r 2 = rankSign r 0 then 1 else 2

def quartetPartition (x : Configuration) (q : Fin 4 → Label)
    (k : Coordinate) : Fin 3 := rankPartition (quartetOrder x q k).symm

def quartetBalancedWidth (x : Configuration) (q : Fin 4 → Label)
    (t : Fin 3) : ℝ :=
  ∑ k, if quartetPartition x q k = t then quartetGap x q k 1 else 0

def middlePairCoefficient (i j : Fin 4) (t : Fin 3) : ℝ :=
  if tetrahedralSign i t = tetrahedralSign j t then 0 else 1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem rank_tetrahedral_identity :
    ∀ r : Fin 4 → Fin 4, Function.Injective r → ∀ i,
      rankSign r i = rankSign r 0 * tetrahedralSign i (rankPartition r) := by
  decide

private theorem bottom_rank_cut : ∀ a b : Fin 4, a ≠ b →
    (if (a.val ≤ 0 ↔ b.val ≤ 0) then (0 : ℤ) else 1) =
      (if a = 0 then 1 else 0) + (if b = 0 then 1 else 0) := by decide

private theorem top_rank_cut : ∀ a b : Fin 4, a ≠ b →
    (if (a.val ≤ 2 ↔ b.val ≤ 2) then (0 : ℤ) else 1) =
      (if a = 3 then 1 else 0) + (if b = 3 then 1 else 0) := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem middle_rank_cut :
    ∀ r : Fin 4 → Fin 4, Function.Injective r → ∀ i j,
      (if ((r i).val ≤ 1 ↔ (r j).val ≤ 1) then (0 : ℤ) else 1) =
        (if tetrahedralSign i (rankPartition r) =
            tetrahedralSign j (rankPartition r) then 0 else 1) := by decide

private theorem bottom_cut_coefficient (p : Equiv.Perm (Fin 4))
    (i j : Fin 4) (hij : i ≠ j) :
    cutSep (prefixSet p (0 : Fin 3)) i j =
      (if p 0 = i then 1 else 0) + (if p 0 = j then 1 else 0) := by
  have hri : p 0 = i ↔ p.symm i = 0 := by
    constructor
    · intro h; rw [← h]; simp
    · intro h; simpa using (congrArg p h).symm
  have hrj : p 0 = j ↔ p.symm j = 0 := by
    constructor
    · intro h; rw [← h]; simp
    · intro h; simpa using (congrArg p h).symm
  have hne : p.symm i ≠ p.symm j := fun h => hij (p.symm.injective h)
  simp only [cutSep, mem_prefixSet, hri, hrj]
  exact_mod_cast bottom_rank_cut (p.symm i) (p.symm j) hne

private theorem top_cut_coefficient (p : Equiv.Perm (Fin 4))
    (i j : Fin 4) (hij : i ≠ j) :
    cutSep (prefixSet p (2 : Fin 3)) i j =
      (if p 3 = i then 1 else 0) + (if p 3 = j then 1 else 0) := by
  have hri : p 3 = i ↔ p.symm i = 3 := by
    constructor
    · intro h; rw [← h]; simp
    · intro h; simpa using (congrArg p h).symm
  have hrj : p 3 = j ↔ p.symm j = 3 := by
    constructor
    · intro h; rw [← h]; simp
    · intro h; simpa using (congrArg p h).symm
  have hne : p.symm i ≠ p.symm j := fun h => hij (p.symm.injective h)
  simp only [cutSep, mem_prefixSet, hri, hrj]
  exact_mod_cast top_rank_cut (p.symm i) (p.symm j) hne

private theorem middle_cut_coefficient (p : Equiv.Perm (Fin 4))
    (i j : Fin 4) :
    cutSep (prefixSet p (1 : Fin 3)) i j =
      middlePairCoefficient i j (rankPartition p.symm) := by
  simp only [cutSep, mem_prefixSet, middlePairCoefficient]
  exact_mod_cast middle_rank_cut p.symm p.symm.injective i j

theorem quartetGap_nonneg (x : Configuration) (q : Fin 4 → Label)
    (k : Coordinate) (r : Fin 3) : 0 ≤ quartetGap x q k r :=
  gap_nonneg _ _ (actualOrder_monotone _) _

theorem quartetSingletonWidth_nonneg (x : Configuration) (q : Fin 4 → Label)
    (i : Fin 4) : 0 ≤ quartetSingletonWidth x q i := by
  apply Finset.sum_nonneg
  intro k _
  unfold quartetSingletonAt
  split_ifs <;> nlinarith [quartetGap_nonneg x q k 0, quartetGap_nonneg x q k 2]

theorem quartetBalancedWidth_nonneg (x : Configuration) (q : Fin 4 → Label)
    (t : Fin 3) : 0 ≤ quartetBalancedWidth x q t := by
  apply Finset.sum_nonneg
  intro k _
  by_cases ht : quartetPartition x q k = t
  · simp only [if_pos ht]
    exact quartetGap_nonneg x q k 1
  · simp only [if_neg ht]
    exact le_rfl

private theorem quartet_scalar_pair (x : Configuration) (q : Fin 4 → Label)
    (k : Coordinate) (i j : Fin 4) (hij : i ≠ j) :
    |x (q i) k - x (q j) k| =
      quartetSingletonAt x q i k + quartetSingletonAt x q j k +
        quartetGap x q k 1 * middlePairCoefficient i j (quartetPartition x q k) := by
  have h := scalar_distance_eq_cuts (quartetColumn x q k) (quartetOrder x q k)
    (actualOrder_monotone _) i j
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero] at h
  have hb := bottom_cut_coefficient (quartetOrder x q k) i j hij
  have ht := top_cut_coefficient (quartetOrder x q k) i j hij
  have hm := middle_cut_coefficient (quartetOrder x q k) i j
  change quartetGap x q k 0 * cutSep (prefixSet (quartetOrder x q k) 0) i j +
    (quartetGap x q k 1 * cutSep (prefixSet (quartetOrder x q k) 1) i j +
      quartetGap x q k 2 * cutSep (prefixSet (quartetOrder x q k) 2) i j) = _ at h
  rw [hb, hm, ht] at h
  change _ = |x (q i) k - x (q j) k| at h
  unfold quartetSingletonAt quartetPartition
  rw [← h]
  split_ifs <;> ring

/-- Every selected pair is represented by the SAME actual outer and middle
gaps. This is a necessary identity, not a cut-cone converse. -/
theorem quartet_pair_ledger (x : Configuration) (q : Fin 4 → Label)
    (i j : Fin 4) (hij : i ≠ j) :
    l1dist (x (q i)) (x (q j)) =
      quartetSingletonWidth x q i + quartetSingletonWidth x q j +
        ∑ t, quartetBalancedWidth x q t * middlePairCoefficient i j t := by
  unfold l1dist
  simp_rw [quartet_scalar_pair x q _ i j hij]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  change (∑ k, quartetGap x q k 1 * middlePairCoefficient i j (quartetPartition x q k)) = _
  unfold quartetBalancedWidth
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp [ite_mul]

/-- The six original unit pairs force equal singleton and balanced totals. -/
theorem quartet_equal_cut_totals (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q) :
    (∀ i, quartetSingletonWidth x q i = quartetSingletonWidth x q 0) ∧
      (∀ t, quartetBalancedWidth x q t = 1 / 2 - quartetSingletonWidth x q 0) := by
  have hp (i j : Fin 4) (hij : i ≠ j) :=
    (quartet_pair_ledger x q i j hij).symm.trans
      (hx (q i) (q j) (fun h => hij (hq h)))
  have h01 := hp 0 1 (by decide)
  have h02 := hp 0 2 (by decide)
  have h03 := hp 0 3 (by decide)
  have h12 := hp 1 2 (by decide)
  have h13 := hp 1 3 (by decide)
  have h23 := hp 2 3 (by decide)
  norm_num [middlePairCoefficient, tetrahedralSign, Fin.sum_univ_succ] at h01 h02 h03 h12 h13 h23
  constructor
  · intro i
    fin_cases i
    · change quartetSingletonWidth x q 0 = quartetSingletonWidth x q 0
      rfl
    · change quartetSingletonWidth x q 1 = quartetSingletonWidth x q 0
      linarith
    · change quartetSingletonWidth x q 2 = quartetSingletonWidth x q 0
      linarith
    · change quartetSingletonWidth x q 3 = quartetSingletonWidth x q 0
      linarith
  · intro t
    fin_cases t
    · change quartetBalancedWidth x q 0 = 1 / 2 - quartetSingletonWidth x q 0
      linarith
    · change quartetBalancedWidth x q 1 = 1 / 2 - quartetSingletonWidth x q 0
      linarith
    · change quartetBalancedWidth x q 2 = 1 / 2 - quartetSingletonWidth x q 0
      linarith

theorem quartet_singleton_bounds (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q) :
    0 ≤ quartetSingletonWidth x q 0 ∧ quartetSingletonWidth x q 0 ≤ 1 / 2 := by
  refine ⟨quartetSingletonWidth_nonneg x q 0, ?_⟩
  have h := (quartet_equal_cut_totals x hx q hq).2 0
  linarith [quartetBalancedWidth_nonneg x q 0]

private theorem quartet_range_gap_identity (x : Configuration) (q : Fin 4 → Label)
    (k : Coordinate) :
    scalarRange (quartetColumn x q k) (quartetOrder x q k) =
      quartetGap x q k 0 + quartetGap x q k 1 + quartetGap x q k 2 := by
  change x (q (quartetOrder x q k 3)) k - x (q (quartetOrder x q k 0)) k =
    (x (q (quartetOrder x q k 1)) k - x (q (quartetOrder x q k 0)) k) +
      (x (q (quartetOrder x q k 2)) k - x (q (quartetOrder x q k 1)) k) +
      (x (q (quartetOrder x q k 3)) k - x (q (quartetOrder x q k 2)) k)
  ring

theorem quartet_width_cut_ledger (x : Configuration) (q : Fin 4 → Label) :
    quartetWidth x q = (∑ i, quartetSingletonWidth x q i) +
      ∑ t, quartetBalancedWidth x q t := by
  have hs : (∑ i, quartetSingletonWidth x q i) =
      ∑ k, ∑ i, quartetSingletonAt x q i k := by
    unfold quartetSingletonWidth
    exact Finset.sum_comm
  have hb : (∑ t, quartetBalancedWidth x q t) =
      ∑ k, ∑ t, if quartetPartition x q k = t then quartetGap x q k 1 else 0 := by
    unfold quartetBalancedWidth
    exact Finset.sum_comm
  rw [hs, hb]
  unfold quartetWidth
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [quartet_range_gap_identity]
  simp [quartetSingletonAt, Finset.sum_add_distrib]
  ring

/-- Width identity for ANY original quartet, including every scalar tie. -/
theorem quartet_width_identity (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q) :
    quartetWidth x q = 3 / 2 + quartetSingletonWidth x q 0 := by
  rw [quartet_width_cut_ledger]
  have h := quartet_equal_cut_totals x hx q hq
  simp_rw [h.1, h.2]
  simp
  ring

/-- Sorted endpoints really bound all four ACTUAL selected scalar values. -/
theorem quartet_endpoint_bounds (x : Configuration) (q : Fin 4 → Label)
    (k : Coordinate) (i : Fin 4) :
    x (q (quartetOrder x q k 0)) k ≤ x (q i) k ∧
      x (q i) k ≤ x (q (quartetOrder x q k 3)) k := by
  have hm := actualOrder_monotone (quartetColumn x q k)
  change Monotone (fun r : Fin 4 => x (q (quartetOrder x q k r)) k) at hm
  have hlo := hm (show (0 : Fin 4) ≤ (quartetOrder x q k).symm i by
    change 0 ≤ ((quartetOrder x q k).symm i).val; omega)
  have hhi := hm (show (quartetOrder x q k).symm i ≤ (3 : Fin 4) by
    change ((quartetOrder x q k).symm i).val ≤ 3
    have := ((quartetOrder x q k).symm i).isLt
    omega)
  simpa only [Equiv.apply_symm_apply] using And.intro hlo hhi

def quartetLower (x : Configuration) (q : Fin 4 → Label) : Point 5 :=
  fun k => x (q (quartetOrder x q k 1)) k

def quartetUpper (x : Configuration) (q : Fin 4 → Label) : Point 5 :=
  fun k => x (q (quartetOrder x q k 2)) k

def quartetMidpoint (x : Configuration) (q : Fin 4 → Label) : Point 5 :=
  fun k => (quartetLower x q k + quartetUpper x q k) / 2

def quartetHalfWidth (x : Configuration) (q : Fin 4 → Label) : Point 5 :=
  fun k => (quartetUpper x q k - quartetLower x q k) / 2

def quartetClamp (x : Configuration) (q : Fin 4 → Label) (j : Label) : Point 5 :=
  fun k => scalarClamp (quartetLower x q k) (quartetUpper x q k) (x j k) -
    quartetMidpoint x q k

def quartetTail (x : Configuration) (q : Fin 4 → Label) (j : Label) : Point 5 :=
  fun k => scalarTail (quartetLower x q k) (quartetUpper x q k) (x j k)

def quartetOwnerSign (x : Configuration) (q : Fin 4 → Label)
    (k : Coordinate) (i : Fin 4) : ℝ :=
  (rankSign (quartetOrder x q k).symm i : ℝ)

def quartetReflection (x : Configuration) (q : Fin 4 → Label)
    (k : Coordinate) : ℝ := quartetOwnerSign x q k 0

theorem quartetLower_le_upper (x : Configuration) (q : Fin 4 → Label)
    (k : Coordinate) : quartetLower x q k ≤ quartetUpper x q k :=
  actualOrder_monotone (quartetColumn x q k) (by decide : (1 : Fin 4) ≤ 2)

theorem quartetHalfWidth_nonneg (x : Configuration) (q : Fin 4 → Label)
    (k : Coordinate) : 0 ≤ quartetHalfWidth x q k :=
  div_nonneg (sub_nonneg.mpr (quartetLower_le_upper x q k)) (by norm_num)

theorem quartetHalfWidth_gap (x : Configuration) (q : Fin 4 → Label)
    (k : Coordinate) : quartetHalfWidth x q k = quartetGap x q k 1 / 2 := rfl

/-- Every label is clamped to the TRUE middle interval, retaining all tails. -/
theorem quartetClamp_bounds (x : Configuration) (q : Fin 4 → Label)
    (j : Label) (k : Coordinate) :
    -quartetHalfWidth x q k ≤ quartetClamp x q j k ∧
      quartetClamp x q j k ≤ quartetHalfWidth x q k := by
  have h := scalarClamp_bounds (quartetLower_le_upper x q k) (x j k)
  dsimp [quartetHalfWidth, quartetClamp, quartetMidpoint]
  constructor <;> linarith [h.1, h.2]

private theorem sorted_four_clamp (f : Fin 4 → ℝ) (p : Equiv.Perm (Fin 4))
    (hf : Monotone (fun r => f (p r))) (i : Fin 4) :
    scalarClamp (f (p 1)) (f (p 2)) (f i) - (f (p 1) + f (p 2)) / 2 =
      (rankSign p.symm i : ℝ) * ((f (p 2) - f (p 1)) / 2) := by
  have hmid : f (p 1) ≤ f (p 2) := hf (by decide : (1 : Fin 4) ≤ 2)
  have hlo : f (p 0) ≤ f (p 1) := hf (by decide : (0 : Fin 4) ≤ 1)
  have hhi : f (p 2) ≤ f (p 3) := hf (by decide : (2 : Fin 4) ≤ 3)
  generalize hr : p.symm i = r
  have hi : p r = i := by rw [← hr]; simp
  rw [← hi]
  fin_cases r <;> dsimp only at *
  · change scalarClamp (f (p 1)) (f (p 2)) (f (p 0)) - (f (p 1) + f (p 2)) / 2 =
      (rankSign p.symm (p 0) : ℝ) * ((f (p 2) - f (p 1)) / 2)
    rw [scalarClamp_of_le_low hmid hlo]
    norm_num [rankSign]
    ring
  · change scalarClamp (f (p 1)) (f (p 2)) (f (p 1)) - (f (p 1) + f (p 2)) / 2 =
      (rankSign p.symm (p 1) : ℝ) * ((f (p 2) - f (p 1)) / 2)
    rw [scalarClamp_of_mem le_rfl hmid]
    norm_num [rankSign]
    ring
  · change scalarClamp (f (p 1)) (f (p 2)) (f (p 2)) - (f (p 1) + f (p 2)) / 2 =
      (rankSign p.symm (p 2) : ℝ) * ((f (p 2) - f (p 1)) / 2)
    rw [scalarClamp_of_mem hmid le_rfl]
    norm_num [rankSign]
    ring
  · change scalarClamp (f (p 1)) (f (p 2)) (f (p 3)) - (f (p 1) + f (p 2)) / 2 =
      (rankSign p.symm (p 3) : ℝ) * ((f (p 2) - f (p 1)) / 2)
    rw [scalarClamp_of_high_le hmid hhi]
    norm_num [rankSign]
    ring

private theorem sorted_four_tail (f : Fin 4 → ℝ) (p : Equiv.Perm (Fin 4))
    (hf : Monotone (fun r => f (p r))) (i : Fin 4) :
    scalarTail (f (p 1)) (f (p 2)) (f i) =
      (if p 0 = i then -(f (p 1) - f (p 0)) else 0) +
        (if p 3 = i then f (p 3) - f (p 2) else 0) := by
  have hmid : f (p 1) ≤ f (p 2) := hf (by decide : (1 : Fin 4) ≤ 2)
  have hlo : f (p 0) ≤ f (p 1) := hf (by decide : (0 : Fin 4) ≤ 1)
  have hhi : f (p 2) ≤ f (p 3) := hf (by decide : (2 : Fin 4) ≤ 3)
  generalize hr : p.symm i = r
  have hi : p r = i := by rw [← hr]; simp
  rw [← hi]
  fin_cases r <;> dsimp only at *
  · change scalarTail (f (p 1)) (f (p 2)) (f (p 0)) =
      (if p 0 = p 0 then -(f (p 1) - f (p 0)) else 0) +
        (if p 3 = p 0 then f (p 3) - f (p 2) else 0)
    rw [scalarTail, scalarClamp_of_le_low hmid hlo]
    simp
  · change scalarTail (f (p 1)) (f (p 2)) (f (p 1)) =
      (if p 0 = p 1 then -(f (p 1) - f (p 0)) else 0) +
        (if p 3 = p 1 then f (p 3) - f (p 2) else 0)
    rw [scalarTail, scalarClamp_of_mem le_rfl hmid]
    simp
  · change scalarTail (f (p 1)) (f (p 2)) (f (p 2)) =
      (if p 0 = p 2 then -(f (p 1) - f (p 0)) else 0) +
        (if p 3 = p 2 then f (p 3) - f (p 2) else 0)
    rw [scalarTail, scalarClamp_of_mem hmid le_rfl]
    simp
  · change scalarTail (f (p 1)) (f (p 2)) (f (p 3)) =
      (if p 0 = p 3 then -(f (p 1) - f (p 0)) else 0) +
        (if p 3 = p 3 then f (p 3) - f (p 2) else 0)
    rw [scalarTail, scalarClamp_of_high_le hmid hhi]
    simp

theorem quartetClamp_selected (x : Configuration) (q : Fin 4 → Label)
    (i : Fin 4) (k : Coordinate) :
    quartetClamp x q (q i) k = quartetOwnerSign x q k i * quartetHalfWidth x q k :=
  sorted_four_clamp (quartetColumn x q k) (quartetOrder x q k)
    (actualOrder_monotone _) i

theorem quartetOwnerSign_tetrahedral (x : Configuration) (q : Fin 4 → Label)
    (k : Coordinate) (i : Fin 4) :
    quartetOwnerSign x q k i = quartetReflection x q k *
      (tetrahedralSign i (quartetPartition x q k) : ℝ) := by
  have h := rank_tetrahedral_identity (quartetOrder x q k).symm
    (quartetOrder x q k).symm.injective i
  change (rankSign (quartetOrder x q k).symm i : ℝ) =
    (rankSign (quartetOrder x q k).symm 0 : ℝ) *
      (tetrahedralSign i (rankPartition (quartetOrder x q k).symm) : ℝ)
  exact_mod_cast h

theorem quartetOwnerSign_abs (x : Configuration) (q : Fin 4 → Label)
    (k : Coordinate) (i : Fin 4) : |quartetOwnerSign x q k i| = 1 := by
  unfold quartetOwnerSign rankSign
  split_ifs <;> norm_num

theorem quartetTail_selected (x : Configuration) (q : Fin 4 → Label)
    (i : Fin 4) (k : Coordinate) :
    quartetTail x q (q i) k =
      (if quartetOrder x q k 0 = i then -quartetGap x q k 0 else 0) +
        (if quartetOrder x q k 3 = i then quartetGap x q k 2 else 0) :=
  sorted_four_tail (quartetColumn x q k) (quartetOrder x q k)
    (actualOrder_monotone _) i

theorem quartetTail_selected_abs (x : Configuration) (q : Fin 4 → Label)
    (i : Fin 4) (k : Coordinate) :
    |quartetTail x q (q i) k| = quartetSingletonAt x q i k := by
  rw [quartetTail_selected]
  unfold quartetSingletonAt
  by_cases hlo : quartetOrder x q k 0 = i
  · have hhi : ¬quartetOrder x q k 3 = i := by
      intro hh
      have he := (quartetOrder x q k).injective (hh.trans hlo.symm)
      norm_num at he
    simp [hlo, hhi, abs_of_nonneg (quartetGap_nonneg x q k 0)]
  · by_cases hhi : quartetOrder x q k 3 = i
    · simp [hlo, hhi, abs_of_nonneg (quartetGap_nonneg x q k 2)]
    · simp [hlo, hhi]

/-- The literal four owner tails, with their common original singleton mass. -/
theorem quartetTail_selected_mass (x : Configuration) (q : Fin 4 → Label)
    (i : Fin 4) : l1mass (quartetTail x q (q i)) = quartetSingletonWidth x q i := by
  simp only [l1mass, quartetTail_selected_abs, quartetSingletonWidth]

theorem quartetTail_owner_signed_disjoint (x : Configuration) (q : Fin 4 → Label)
    (i j : Fin 4) (hij : i ≠ j) (k : Coordinate) :
    quartetTail x q (q i) k * quartetTail x q (q j) k ≤ 0 := by
  rw [quartetTail_selected, quartetTail_selected]
  have hlo (hi : quartetOrder x q k 0 = i) (hj : quartetOrder x q k 0 = j) :
      False := hij (hi.symm.trans hj)
  have hhi (hi : quartetOrder x q k 3 = i) (hj : quartetOrder x q k 3 = j) :
      False := hij (hi.symm.trans hj)
  have hg0 := quartetGap_nonneg x q k 0
  have hg2 := quartetGap_nonneg x q k 2
  have hprod := mul_nonneg hg0 hg2
  split_ifs <;> simp_all <;> nlinarith

/-- EVERY original pair retains its full exact physical clamp/tail split. -/
theorem quartet_pair_split (x : Configuration) (q : Fin 4 → Label) (i j : Label) :
    l1dist (x i) (x j) = l1dist (quartetClamp x q i) (quartetClamp x q j) +
      l1dist (quartetTail x q i) (quartetTail x q j) := by
  unfold l1dist
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have h := scalarClamp_tail_distance_split (quartetLower_le_upper x q k) (x i k) (x j k)
  dsimp [quartetClamp, quartetTail]
  rw [show
    (scalarClamp (quartetLower x q k) (quartetUpper x q k) (x i k) - quartetMidpoint x q k) -
      (scalarClamp (quartetLower x q k) (quartetUpper x q k) (x j k) - quartetMidpoint x q k) =
    scalarClamp (quartetLower x q k) (quartetUpper x q k) (x i k) -
      scalarClamp (quartetLower x q k) (quartetUpper x q k) (x j k) by ring]
  exact h

theorem quartetTail_pos_face (x : Configuration) (q : Fin 4 → Label)
    (j : Label) (k : Coordinate) (h : 0 < quartetTail x q j k) :
    quartetClamp x q j k = quartetHalfWidth x q k := by
  have hc := scalarTail_pos_clamp (quartetLower_le_upper x q k) h
  dsimp [quartetClamp, quartetHalfWidth, quartetMidpoint]
  rw [hc]
  ring

theorem quartetTail_neg_face (x : Configuration) (q : Fin 4 → Label)
    (j : Label) (k : Coordinate) (h : quartetTail x q j k < 0) :
    quartetClamp x q j k = -quartetHalfWidth x q k := by
  have hc := scalarTail_neg_clamp (quartetLower_le_upper x q k) h
  dsimp [quartetClamp, quartetHalfWidth, quartetMidpoint]
  rw [hc]
  ring

end
end Kusner5
