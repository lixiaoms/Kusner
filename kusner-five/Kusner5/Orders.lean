import Kusner5.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Lean.Elab.Tactic.Omega

/-!
Actual scalar orders on the original labels. An order maps positions to labels;
its inverse is used by every prefix. Equal values are retained as distinct indexed
positions with zero consecutive gaps. No historical Kusner module is imported.
-/

open scoped BigOperators

namespace Kusner5

noncomputable section

def actualOrder {N : ℕ} (f : Fin N → ℝ) : Equiv.Perm (Fin N) := Tuple.sort f

theorem actualOrder_monotone {N : ℕ} (f : Fin N → ℝ) :
    Monotone (fun i => f (actualOrder f i)) := by
  intro i j hij
  exact Tuple.monotone_sort f hij

def cutSep {V : Type*} [DecidableEq V] (S : Finset V) (i j : V) : ℝ :=
  if (i ∈ S ↔ j ∈ S) then 0 else 1

@[simp] theorem cutSep_self {V : Type*} [DecidableEq V] (S : Finset V) (i : V) :
    cutSep S i i = 0 := by simp [cutSep]

theorem cutSep_symm {V : Type*} [DecidableEq V] (S : Finset V) (i j : V) :
    cutSep S i j = cutSep S j i := by simp only [cutSep, iff_comm]

def prefixSet {n : ℕ} (p : Equiv.Perm (Fin (n + 1))) (r : Fin n) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => (p.symm i).val ≤ r.val)

@[simp] theorem mem_prefixSet {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (r : Fin n) (i : Fin (n + 1)) :
    i ∈ prefixSet p r ↔ (p.symm i).val ≤ r.val := by simp [prefixSet]

def gap {n : ℕ} (f : Fin (n + 1) → ℝ)
    (p : Equiv.Perm (Fin (n + 1))) (r : Fin n) : ℝ :=
  f (p r.succ) - f (p r.castSucc)

def scalarRange {n : ℕ} (f : Fin (n + 1) → ℝ)
    (p : Equiv.Perm (Fin (n + 1))) : ℝ :=
  f (p (Fin.last n)) - f (p 0)

theorem gap_nonneg {n : ℕ} (f : Fin (n + 1) → ℝ)
    (p : Equiv.Perm (Fin (n + 1)))
    (hf : Monotone (fun i => f (p i))) (r : Fin n) : 0 ≤ gap f p r := by
  apply sub_nonneg.mpr
  apply hf
  change r.val ≤ r.val + 1
  omega

@[simp] theorem gap_constant {n : ℕ} (c : ℝ)
    (p : Equiv.Perm (Fin (n + 1))) (r : Fin n) :
    gap (fun _ => c) p r = 0 := by simp [gap]

@[simp] theorem scalarRange_constant {n : ℕ} (c : ℝ)
    (p : Equiv.Perm (Fin (n + 1))) :
    scalarRange (fun _ => c) p = 0 := by simp [scalarRange]

theorem gap_eq_zero_of_tie {n : ℕ} (f : Fin (n + 1) → ℝ)
    (p : Equiv.Perm (Fin (n + 1))) (r : Fin n)
    (htie : f (p r.succ) = f (p r.castSucc)) : gap f p r = 0 := by
  simp [gap, htie]

private def natCut (u v r : ℕ) : ℝ := if (u ≤ r ↔ v ≤ r) then 0 else 1

private theorem telescope (a : ℕ → ℝ) (m : ℕ) :
    (∑ r ∈ Finset.range m, (a (r + 1) - a r)) = a m - a 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

private theorem partial_telescope (a : ℕ → ℝ) (m t : ℕ) (ht : t ≤ m) :
    (∑ r ∈ Finset.range m, if r < t then a (r + 1) - a r else 0) =
      a t - a 0 := by
  induction m with
  | zero =>
    have : t = 0 := by omega
    subst t
    simp
  | succ m ih =>
    by_cases htm : t ≤ m
    · rw [Finset.sum_range_succ, ih htm]
      have hnot : ¬m < t := by omega
      simp [hnot]
    · have heq : t = m + 1 := by omega
      subst t
      rw [Finset.sum_range_succ]
      have hs : (∑ r ∈ Finset.range m,
          if r < m + 1 then a (r + 1) - a r else 0) = a m - a 0 := by
        calc
          _ = ∑ r ∈ Finset.range m, (a (r + 1) - a r) := by
            apply Finset.sum_congr rfl
            intro r hr
            have : r < m + 1 := by have := Finset.mem_range.mp hr; omega
            simp [this]
          _ = _ := telescope a m
      rw [hs]
      simp only [Nat.lt_add_one, le_refl, ite_true]
      ring

private theorem cut_sum_of_le (a : ℕ → ℝ) (m u v : ℕ)
    (hu : u ≤ m) (hv : v ≤ m) (huv : u ≤ v) :
    (∑ r ∈ Finset.range m, (a (r + 1) - a r) * natCut u v r) = a v - a u := by
  have he (r : ℕ) : (a (r + 1) - a r) * natCut u v r =
      (if r < v then a (r + 1) - a r else 0) -
        (if r < u then a (r + 1) - a r else 0) := by
    by_cases hur : u ≤ r <;> by_cases hvr : v ≤ r
    · have hru : ¬r < u := by omega
      have hrv : ¬r < v := by omega
      simp [natCut, hur, hvr, hru, hrv]
    · have hru : ¬r < u := by omega
      have hrv : r < v := by omega
      simp [natCut, hur, hvr, hru, hrv]
    · omega
    · have hru : r < u := by omega
      have hrv : r < v := by omega
      simp [natCut, hur, hvr, hru, hrv]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, partial_telescope a m v hv,
    partial_telescope a m u hu]
  ring

private theorem nat_scalar_distance (a : ℕ → ℝ) (ha : Monotone a)
    (m u v : ℕ) (hu : u ≤ m) (hv : v ≤ m) :
    (∑ r ∈ Finset.range m, (a (r + 1) - a r) * natCut u v r) = |a u - a v| := by
  rcases le_total u v with huv | hvu
  · rw [cut_sum_of_le a m u v hu hv huv, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (ha huv))]
  · have hs : ∀r, natCut u v r = natCut v u r := by
      intro r; simp only [natCut, iff_comm]
    simp_rw [hs]
    rw [cut_sum_of_le a m v u hv hu hvu, abs_of_nonneg (sub_nonneg.mpr (ha hvu))]

private def clipped {n : ℕ} (a : Fin (n + 1) → ℝ) (r : ℕ) : ℝ :=
  a ⟨min r n, by omega⟩

private theorem clipped_monotone {n : ℕ} (a : Fin (n + 1) → ℝ)
    (ha : Monotone a) : Monotone (clipped a) := by
  intro r s hrs
  apply ha
  change min r n ≤ min s n
  omega

private theorem clipped_eq {n : ℕ} (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    clipped a i.val = a i := by
  unfold clipped
  congr 1
  apply Fin.ext
  dsimp
  omega

theorem fin_sum_eq_range (m : ℕ) (f : ℕ → ℝ) :
    (∑ r : Fin m, f r.val) = ∑ r ∈ Finset.range m, f r := by
  apply Finset.sum_bij (fun r _ => r.val)
  · intro r hr; exact Finset.mem_range.mpr r.isLt
  · intro r hr s hs heq; exact Fin.ext heq
  · intro r hr; exact ⟨⟨r, Finset.mem_range.mp hr⟩, Finset.mem_univ _, rfl⟩
  · intro r hr; rfl

theorem scalar_distance_eq_cuts {n : ℕ} (f : Fin (n + 1) → ℝ)
    (p : Equiv.Perm (Fin (n + 1)))
    (hf : Monotone (fun i => f (p i))) (i j : Fin (n + 1)) :
    (∑ r : Fin n, gap f p r * cutSep (prefixSet p r) i j) = |f i - f j| := by
  have hg (r : Fin n) : gap f p r =
      clipped (fun i => f (p i)) (r.val + 1) -
        clipped (fun i => f (p i)) r.val := by
    change f (p r.succ) - f (p r.castSucc) =
      clipped (fun i => f (p i)) r.succ.val -
        clipped (fun i => f (p i)) r.castSucc.val
    rw [clipped_eq, clipped_eq]
  have hc (r : Fin n) : cutSep (prefixSet p r) i j =
      natCut (p.symm i).val (p.symm j).val r.val := by
    simp [cutSep, prefixSet, natCut]
  simp_rw [hg, hc]
  rw [fin_sum_eq_range n (fun r : ℕ =>
    (clipped (fun i => f (p i)) (r + 1) - clipped (fun i => f (p i)) r) *
      natCut (p.symm i).val (p.symm j).val r)]
  rw [nat_scalar_distance _ (clipped_monotone _ hf) n
    (p.symm i).val (p.symm j).val
    (by have := (p.symm i).isLt; omega) (by have := (p.symm j).isLt; omega)]
  rw [clipped_eq, clipped_eq]
  simp

theorem sum_gaps {n : ℕ} (f : Fin (n + 1) → ℝ)
    (p : Equiv.Perm (Fin (n + 1))) : (∑ r : Fin n, gap f p r) = scalarRange f p := by
  have hg (r : Fin n) : gap f p r =
      clipped (fun i => f (p i)) (r.val + 1) -
        clipped (fun i => f (p i)) r.val := by
    change f (p r.succ) - f (p r.castSucc) =
      clipped (fun i => f (p i)) r.succ.val -
        clipped (fun i => f (p i)) r.castSucc.val
    rw [clipped_eq, clipped_eq]
  simp_rw [hg]
  rw [fin_sum_eq_range n (fun r : ℕ =>
    clipped (fun i => f (p i)) (r + 1) - clipped (fun i => f (p i)) r), telescope]
  change clipped (fun i => f (p i)) (Fin.last n).val -
    clipped (fun i => f (p i)) (0 : Fin (n + 1)).val = _
  rw [clipped_eq, clipped_eq]
  rfl

theorem scalarRange_nonneg {n : ℕ} (f : Fin (n + 1) → ℝ)
    (p : Equiv.Perm (Fin (n + 1)))
    (hf : Monotone (fun i => f (p i))) : 0 ≤ scalarRange f p := by
  rw [←sum_gaps]
  exact Finset.sum_nonneg fun r _ => gap_nonneg f p hf r

def columnOrders {n d : ℕ} (x : Fin (n + 1) → Point d) :
    Fin d → Equiv.Perm (Fin (n + 1)) := fun k => actualOrder (fun i => x i k)

theorem columnOrders_monotone {n d : ℕ} (x : Fin (n + 1) → Point d) (k : Fin d) :
    Monotone (fun i => x (columnOrders x k i) k) := by
  exact actualOrder_monotone (fun i => x i k)

end
end Kusner5
