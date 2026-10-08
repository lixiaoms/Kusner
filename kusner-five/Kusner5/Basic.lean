import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ext
import Mathlib.Tactic.SimpRw
import Lean.Elab.Tactic.Omega

open scoped BigOperators

/-!
Original real Manhattan distance. The ordinary norm on a function type is
not used. Every label pair and physical coordinate is retained explicitly.
-/
namespace Kusner5

noncomputable section

abbrev Point (d : ℕ) := Fin d → ℝ
abbrev Label := Fin 11
abbrev Coordinate := Fin 5
abbrev Configuration := Label → Point 5

def l1dist {d : ℕ} (p q : Point d) : ℝ :=
  ∑ k, |p k - q k|

def Equilateral {n d : ℕ} (x : Fin n → Point d) (δ : ℝ) : Prop :=
  ∀ i j, i ≠ j → l1dist (x i) (x j) = δ

def UnitEquilateral {n d : ℕ} (x : Fin n → Point d) : Prop :=
  Equilateral x 1

def translated {d : ℕ} (o p : Point d) : Point d :=
  fun k => p k - o k

def scaled {d : ℕ} (r : ℝ) (p : Point d) : Point d :=
  fun k => r * p k

theorem l1dist_nonneg {d : ℕ} (p q : Point d) :
    0 ≤ l1dist p q := by
  exact Finset.sum_nonneg (fun k _ => abs_nonneg (p k - q k))

@[simp] theorem l1dist_self {d : ℕ} (p : Point d) :
    l1dist p p = 0 := by
  simp [l1dist]

theorem l1dist_comm {d : ℕ} (p q : Point d) :
    l1dist p q = l1dist q p := by
  unfold l1dist
  apply Finset.sum_congr rfl
  intro k _
  exact abs_sub_comm (p k) (q k)

theorem coordinate_distance_le {d : ℕ} (p q : Point d) (k : Fin d) :
    |p k - q k| ≤ l1dist p q := by
  exact Finset.single_le_sum (fun t _ => abs_nonneg (p t - q t))
    (Finset.mem_univ k)

theorem l1dist_translated {d : ℕ} (o p q : Point d) :
    l1dist (translated o p) (translated o q) = l1dist p q := by
  unfold l1dist translated
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  ring

theorem l1dist_scaled {d : ℕ} (r : ℝ) (p q : Point d) :
    l1dist (scaled r p) (scaled r q) = |r| * l1dist p q := by
  simp only [l1dist, scaled, ← mul_sub, abs_mul, Finset.mul_sum]

theorem l1dist_scaled_nonneg {d : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (p q : Point d) :
    l1dist (scaled r p) (scaled r q) = r * l1dist p q := by
  rw [l1dist_scaled, abs_of_nonneg hr]

theorem unitEquilateral_injective {n d : ℕ} {x : Fin n → Point d}
    (h : UnitEquilateral x) : Function.Injective x := by
  intro i j hij
  by_contra hne
  have hd := h i j hne
  have hzero : (0 : ℝ) = 1 := by
    simpa [hij, l1dist] using hd
  norm_num at hzero

theorem unitEquilateral_coordinate_bound {n d : ℕ}
    {x : Fin n → Point d} (h : UnitEquilateral x)
    {i j : Fin n} (hij : i ≠ j) (k : Fin d) :
    |x i k - x j k| ≤ 1 := by
  calc
    |x i k - x j k| ≤ l1dist (x i) (x j) :=
      coordinate_distance_le (x i) (x j) k
    _ = 1 := h i j hij

theorem normalize_equilateral {n d : ℕ} {x : Fin n → Point d}
    {δ : ℝ} (hδ : 0 < δ) (h : Equilateral x δ) :
    UnitEquilateral (fun i => scaled δ⁻¹ (x i)) := by
  intro i j hij
  rw [l1dist_scaled_nonneg (inv_nonneg.mpr hδ.le), h i j hij]
  exact inv_mul_cancel₀ (ne_of_gt hδ)

/-- Extract genuine members of a finite set without adding any geometric
hypothesis. Used both for original core labels and the final cardinality lift. -/
theorem exists_fin_injection_into_finset {α : Type*} [DecidableEq α]
    (s : Finset α) (m : ℕ) (hm : m ≤ s.card) :
    ∃ f : Fin m → α, Function.Injective f ∧ ∀ i, f i ∈ s := by
  classical
  have hc : Fintype.card ↥s = s.card := by simp
  refine ⟨fun i => ((Fintype.equivFin ↥s).symm
    ⟨i.val, by rw [hc]; exact lt_of_lt_of_le i.isLt hm⟩).val, ?_, ?_⟩
  · intro i i' h
    have hsub : (Fintype.equivFin ↥s).symm
        ⟨i.val, by rw [hc]; exact lt_of_lt_of_le i.isLt hm⟩ =
        (Fintype.equivFin ↥s).symm
        ⟨i'.val, by rw [hc]; exact lt_of_lt_of_le i'.isLt hm⟩ :=
      Subtype.ext h
    have hj := (Fintype.equivFin ↥s).symm.injective hsub
    injection hj with hval
    exact Fin.ext hval
  · intro i
    exact ((Fintype.equivFin ↥s).symm
      ⟨i.val, by rw [hc]; exact lt_of_lt_of_le i.isLt hm⟩).property

end
end Kusner5
