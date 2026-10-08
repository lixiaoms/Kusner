import Kusner5.Orders
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
Finite quadratic energy derived from the original absolute-value equations.
Every column acts on the SAME original labels. Sorting and cut completeness are
proved in Orders; zero/tied gaps require no strict-order premise.
-/

open scoped BigOperators

namespace Kusner5

noncomputable section

def cutIndicator {V : Type*} [DecidableEq V] (S : Finset V) (i : V) : ℝ :=
  if i ∈ S then 1 else 0

theorem cutSep_indicator {V : Type*} [DecidableEq V] (S : Finset V) (i j : V) :
    cutSep S i j = cutIndicator S i + cutIndicator S j -
      2 * cutIndicator S i * cutIndicator S j := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [cutSep, cutIndicator, hi, hj] <;> norm_num

theorem sum_indicator_mul {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (u : V → ℝ) :
    (∑ i, u i * cutIndicator S i) = ∑ i ∈ S, u i := by
  simp [cutIndicator, mul_ite]

theorem cut_quadratic_zero_sum {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (u : V → ℝ) (hu : (∑ i, u i) = 0) :
    (∑ i, ∑ j, u i * u j * cutSep S i j) = -2 * (∑ i ∈ S, u i) ^ 2 := by
  classical
  have key : ∀ i j : V, u i * u j * cutSep S i j =
      (u i * cutIndicator S i) * u j + u i * (u j * cutIndicator S j)
        - 2 * ((u i * cutIndicator S i) * (u j * cutIndicator S j)) := by
    intro i j
    rw [cutSep_indicator]
    ring
  have e1 : (∑ i, ∑ j, (u i * cutIndicator S i) * u j)
      = (∑ i, u i * cutIndicator S i) * (∑ j, u j) := by
    have h1 : ∀ i : V, (∑ j, (u i * cutIndicator S i) * u j)
        = (u i * cutIndicator S i) * (∑ j, u j) :=
      fun i => (Finset.mul_sum (s := (Finset.univ : Finset V)) (f := fun j => u j)
        (a := u i * cutIndicator S i)).symm
    simp only [h1]
    exact (Finset.sum_mul (s := (Finset.univ : Finset V)) (f := fun i => u i * cutIndicator S i)
      (a := (∑ j, u j))).symm
  have e2 : (∑ i, ∑ j, u i * (u j * cutIndicator S j))
      = (∑ i, u i) * (∑ j, u j * cutIndicator S j) := by
    have h2 : ∀ i : V, (∑ j, u i * (u j * cutIndicator S j))
        = u i * (∑ j, u j * cutIndicator S j) :=
      fun i => (Finset.mul_sum (s := (Finset.univ : Finset V)) (f := fun j => u j * cutIndicator S j)
        (a := u i)).symm
    simp only [h2]
    exact (Finset.sum_mul (s := (Finset.univ : Finset V)) (f := fun i => u i)
      (a := (∑ j, u j * cutIndicator S j))).symm
  have e3 : (∑ i, ∑ j, (u i * cutIndicator S i) * (u j * cutIndicator S j))
      = (∑ i, u i * cutIndicator S i) * (∑ j, u j * cutIndicator S j) := by
    have h3 : ∀ i : V, (∑ j, (u i * cutIndicator S i) * (u j * cutIndicator S j))
        = (u i * cutIndicator S i) * (∑ j, u j * cutIndicator S j) :=
      fun i => (Finset.mul_sum (s := (Finset.univ : Finset V)) (f := fun j => u j * cutIndicator S j)
        (a := u i * cutIndicator S i)).symm
    simp only [h3]
    exact (Finset.sum_mul (s := (Finset.univ : Finset V)) (f := fun i => u i * cutIndicator S i)
      (a := (∑ j, u j * cutIndicator S j))).symm
  have e4 : (∑ i, ∑ j, 2 * ((u i * cutIndicator S i) * (u j * cutIndicator S j)))
      = 2 * (∑ i, ∑ j, (u i * cutIndicator S i) * (u j * cutIndicator S j)) := by
    have h4 : ∀ i : V, (∑ j, 2 * ((u i * cutIndicator S i) * (u j * cutIndicator S j)))
        = 2 * (∑ j, (u i * cutIndicator S i) * (u j * cutIndicator S j)) :=
      fun i => (Finset.mul_sum (s := (Finset.univ : Finset V)) (f := fun j =>
        (u i * cutIndicator S i) * (u j * cutIndicator S j)) (a := 2)).symm
    simp only [h4]
    exact (Finset.mul_sum (s := (Finset.univ : Finset V)) (f := fun i =>
      (∑ j, (u i * cutIndicator S i) * (u j * cutIndicator S j))) (a := 2)).symm
  calc (∑ i, ∑ j, u i * u j * cutSep S i j)
      = ∑ i, ∑ j, ((u i * cutIndicator S i) * u j
          + u i * (u j * cutIndicator S j)
          - 2 * ((u i * cutIndicator S i) * (u j * cutIndicator S j))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [key]
    _ = (∑ i, ∑ j, (u i * cutIndicator S i) * u j)
          + (∑ i, ∑ j, u i * (u j * cutIndicator S j))
          - 2 * (∑ i, ∑ j, (u i * cutIndicator S i) * (u j * cutIndicator S j)) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        rw [e4]
    _ = (∑ i, u i * cutIndicator S i) * (∑ j, u j)
          + (∑ i, u i) * (∑ j, u j * cutIndicator S j)
          - 2 * ((∑ i, u i * cutIndicator S i) * (∑ j, u j * cutIndicator S j)) := by
        rw [e1, e2, e3]
    _ = -2 * (∑ i ∈ S, u i) ^ 2 := by
        rw [hu, sum_indicator_mul]
        ring

theorem sum_perm {N : ℕ} {A : Type*} [AddCommMonoid A]
    (p : Equiv.Perm (Fin N)) (f : Fin N → A) :
    (∑ i, f (p i)) = ∑ i, f i := by
  apply Finset.sum_bij (fun i _ => p i)
  · intro i hi; exact Finset.mem_univ _
  · intro i hi j hj hij; exact p.injective hij
  · intro j hj; exact ⟨p.symm j, Finset.mem_univ _, by simp⟩
  · intro i hi; rfl

def transport {N : ℕ} (p : Equiv.Perm (Fin N)) (v : Fin N → ℝ) : Fin N → ℝ :=
  fun i => v (p.symm i)

@[simp] theorem transport_at_order {N : ℕ} (p : Equiv.Perm (Fin N))
    (v : Fin N → ℝ) (i : Fin N) : transport p v (p i) = v i := by simp [transport]

theorem sum_transport {N : ℕ} (p : Equiv.Perm (Fin N)) (v : Fin N → ℝ) :
    (∑ i, transport p v i) = ∑ i, v i := sum_perm p.symm v

theorem sum_transport_sq {N : ℕ} (p : Equiv.Perm (Fin N)) (v : Fin N → ℝ) :
    (∑ i, (transport p v i) ^ 2) = ∑ i, (v i) ^ 2 := sum_perm p.symm (fun i => v i ^ 2)

def prefixMass {n : ℕ} (p : Equiv.Perm (Fin (n + 1))) (r : Fin n)
    (u : Fin (n + 1) → ℝ) : ℝ := ∑ i ∈ prefixSet p r, u i

theorem prefix_transport {n : ℕ} (p : Equiv.Perm (Fin (n + 1))) (r : Fin n)
    (v : Fin (n + 1) → ℝ) :
    prefixMass p r (transport p v) =
      ∑ i : Fin (n + 1), if i.val ≤ r.val then v i else 0 := by
  simpa [prefixMass, prefixSet, Finset.sum_filter, transport] using
    sum_perm p.symm (fun i => if i.val ≤ r.val then v i else 0)

theorem prefixSet_card {n : ℕ} (p : Equiv.Perm (Fin (n + 1))) (r : Fin n) :
    (prefixSet p r).card = r.val + 1 := by
  have h : (∑ i ∈ prefixSet p r, (1 : ℕ)) =
      ∑ s ∈ Finset.range (r.val + 1), (1 : ℕ) := by
    apply Finset.sum_bij (fun i _ => (p.symm i).val)
    · intro i hi
      apply Finset.mem_range.mpr
      have := (mem_prefixSet p r i).mp hi
      omega
    · intro i hi j hj hij
      apply p.symm.injective
      exact Fin.ext hij
    · intro s hs
      have hsr : s < r.val + 1 := Finset.mem_range.mp hs
      have hsn : s < n + 1 := by have := r.isLt; omega
      refine ⟨p ⟨s, hsn⟩, ?_, ?_⟩
      · apply (mem_prefixSet p r _).mpr
        simp only [Equiv.symm_apply_apply]
        change s ≤ r.val
        omega
      · simp
    · intro i hi
      rfl
  simpa using h

def scalarEnergy {n : ℕ} (f : Fin (n + 1) → ℝ)
    (p : Equiv.Perm (Fin (n + 1))) (u : Fin (n + 1) → ℝ) : ℝ :=
  ∑ r : Fin n, gap f p r * (prefixMass p r u) ^ 2

def prefixWeight {n : ℕ} (r : Fin n) : ℝ :=
  (r.val + 1 : ℝ) * (n - r.val : ℕ) / (n + 1 : ℝ)

def scalarTrace {n : ℕ} (f : Fin (n + 1) → ℝ)
    (p : Equiv.Perm (Fin (n + 1))) : ℝ :=
  ∑ r : Fin n, gap f p r * prefixWeight r

def columnEnergy {n d : ℕ} (x : Fin (n + 1) → Point d)
    (orders : Fin d → Equiv.Perm (Fin (n + 1))) (k : Fin d)
    (u : Fin (n + 1) → ℝ) : ℝ := scalarEnergy (fun i => x i k) (orders k) u

def columnTrace {n d : ℕ} (x : Fin (n + 1) → Point d)
    (orders : Fin d → Equiv.Perm (Fin (n + 1))) (k : Fin d) : ℝ :=
  scalarTrace (fun i => x i k) (orders k)

theorem scalarEnergy_nonneg {n : ℕ} (f : Fin (n + 1) → ℝ)
    (p : Equiv.Perm (Fin (n + 1)))
    (hf : Monotone (fun i => f (p i))) (u : Fin (n + 1) → ℝ) :
    0 ≤ scalarEnergy f p u :=
  Finset.sum_nonneg fun r _ => mul_nonneg (gap_nonneg f p hf r) (sq_nonneg _)

theorem prefixWeight_nonneg {n : ℕ} (r : Fin n) : 0 ≤ prefixWeight r := by
  unfold prefixWeight
  positivity

theorem scalarTrace_nonneg {n : ℕ} (f : Fin (n + 1) → ℝ)
    (p : Equiv.Perm (Fin (n + 1)))
    (hf : Monotone (fun i => f (p i))) : 0 ≤ scalarTrace f p :=
  Finset.sum_nonneg fun r _ => mul_nonneg (gap_nonneg f p hf r) (prefixWeight_nonneg r)

@[simp] theorem scalarEnergy_constant {n : ℕ} (c : ℝ)
    (p : Equiv.Perm (Fin (n + 1))) (u : Fin (n + 1) → ℝ) :
    scalarEnergy (fun _ => c) p u = 0 := by simp [scalarEnergy]

@[simp] theorem scalarTrace_constant {n : ℕ} (c : ℝ)
    (p : Equiv.Perm (Fin (n + 1))) : scalarTrace (fun _ => c) p = 0 := by
  simp [scalarTrace]

private theorem sum_swap_third {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
  calc
    _ = ∑ i, ∑ k, ∑ j, f i j k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem scalar_quadratic_eq_energy {n : ℕ} (f : Fin (n + 1) → ℝ)
    (p : Equiv.Perm (Fin (n + 1)))
    (hf : Monotone (fun i => f (p i))) (u : Fin (n + 1) → ℝ)
    (hu : (∑ i, u i) = 0) :
    (∑ i, ∑ j, u i * u j * |f i - f j|) = -2 * scalarEnergy f p u := by
  calc
    _ = ∑ i, ∑ j, u i * u j *
        ∑ r : Fin n, gap f p r * cutSep (prefixSet p r) i j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [scalar_distance_eq_cuts f p hf]
    _ = ∑ r : Fin n, gap f p r *
        (∑ i, ∑ j, u i * u j * cutSep (prefixSet p r) i j) := by
      simp_rw [Finset.mul_sum]
      rw [sum_swap_third]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = -2 * scalarEnergy f p u := by
      simp_rw [cut_quadratic_zero_sum _ u hu]
      unfold scalarEnergy prefixMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

theorem unit_equilateral_quadratic {N d : ℕ} (x : Fin N → Point d)
    (hx : UnitEquilateral x) (u : Fin N → ℝ) (hu : (∑ i, u i) = 0) :
    (∑ i, ∑ j, u i * u j * l1dist (x i) (x j)) = -(∑ i, u i ^ 2) := by
  have hpoint (i j : Fin N) : u i * u j * l1dist (x i) (x j) =
      u i * u j - (if i = j then u i ^ 2 else 0) := by
    by_cases hij : i = j
    · subst j
      simp [l1dist] <;> ring
    · rw [hx i j hij]
      simp [hij]
  simp_rw [hpoint]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hsq : (∑ i, ∑ j, u i * u j) = (∑ i, u i) * (∑ i, u i) := by
    have h1 : ∀ i : Fin N, (∑ j, u i * u j) = u i * (∑ j, u j) := by
      intro i
      rw [← Finset.mul_sum]
    simp only [h1, Finset.sum_mul]
  rw [hsq, hu]
  ring

theorem unit_equilateral_totalEnergy {n d : ℕ} (x : Fin (n + 1) → Point d)
    (hx : UnitEquilateral x)
    (orders : Fin d → Equiv.Perm (Fin (n + 1)))
    (horders : ∀ k, Monotone (fun i => x (orders k i) k))
    (u : Fin (n + 1) → ℝ) (hu : (∑ i, u i) = 0) :
    (∑ k, columnEnergy x orders k u) = (1 / 2 : ℝ) * ∑ i, u i ^ 2 := by
  have hq : (∑ i, ∑ j, u i * u j * l1dist (x i) (x j)) =
      -2 * ∑ k, columnEnergy x orders k u := by
    calc
      _ = ∑ k, ∑ i, ∑ j, u i * u j * |x i k - x j k| := by
        unfold l1dist
        simp_rw [Finset.mul_sum]
        exact sum_swap_third _
      _ = ∑ k, -2 * columnEnergy x orders k u := by
        apply Finset.sum_congr rfl
        intro k hk
        exact scalar_quadratic_eq_energy _ _ (horders k) u hu
      _ = _ := by rw [Finset.mul_sum]
  rw [unit_equilateral_quadratic x hx u hu] at hq
  linarith

theorem unit_equilateral_actual_totalEnergy {n d : ℕ} (x : Fin (n + 1) → Point d)
    (hx : UnitEquilateral x) (u : Fin (n + 1) → ℝ) (hu : (∑ i, u i) = 0) :
    (∑ k, columnEnergy x (columnOrders x) k u) =
      (1 / 2 : ℝ) * ∑ i, u i ^ 2 :=
  unit_equilateral_totalEnergy x hx _ (columnOrders_monotone x) u hu

theorem unit_equilateral_columnEnergy_le {n d : ℕ} (x : Fin (n + 1) → Point d)
    (hx : UnitEquilateral x)
    (orders : Fin d → Equiv.Perm (Fin (n + 1)))
    (horders : ∀ k, Monotone (fun i => x (orders k i) k))
    (u : Fin (n + 1) → ℝ) (hu : (∑ i, u i) = 0) (k : Fin d) :
    columnEnergy x orders k u ≤ (1 / 2 : ℝ) * ∑ i, u i ^ 2 := by
  rw [←unit_equilateral_totalEnergy x hx orders horders u hu]
  exact Finset.single_le_sum
    (f := fun l => columnEnergy x orders l u)
    (fun l _ => scalarEnergy_nonneg (fun i => x i l) (orders l) (horders l) u)
    (Finset.mem_univ k)

theorem sum_cutSep {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    (∑ i, ∑ j, cutSep S i j) =
      2 * (S.card : ℝ) * ((Fintype.card V : ℝ) - S.card) := by
  have hs : (∑ i, cutIndicator S i) = S.card := by simp [cutIndicator]
  simp_rw [cutSep_indicator]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ←Finset.mul_sum,
    ←Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs]
  ring

theorem scalar_pairSum_eq_trace {n : ℕ} (f : Fin (n + 1) → ℝ)
    (p : Equiv.Perm (Fin (n + 1)))
    (hf : Monotone (fun i => f (p i))) :
    (∑ i, ∑ j, |f i - f j|) = 2 * (n + 1 : ℝ) * scalarTrace f p := by
  calc
    _ = ∑ i, ∑ j, ∑ r : Fin n, gap f p r * cutSep (prefixSet p r) i j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact (scalar_distance_eq_cuts f p hf i j).symm
    _ = ∑ r : Fin n, gap f p r * (∑ i, ∑ j, cutSep (prefixSet p r) i j) := by
      rw [sum_swap_third]
      simp only [Finset.mul_sum]
    _ = ∑ r : Fin n, 2 * (n + 1 : ℝ) * (gap f p r * prefixWeight r) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [sum_cutSep, prefixSet_card]
      unfold prefixWeight
      have hrv : r.val ≤ n := by have := r.isLt; omega
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      rw [Nat.cast_sub hrv]
      simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
      field_simp [hn]
      <;> ring
    _ = _ := by unfold scalarTrace; rw [Finset.mul_sum]

theorem unit_equilateral_pairSum {n d : ℕ} (x : Fin (n + 1) → Point d)
    (hx : UnitEquilateral x) :
    (∑ i, ∑ j, l1dist (x i) (x j)) = (n + 1 : ℝ) * n := by
  have hpoint (i j : Fin (n + 1)) : l1dist (x i) (x j) =
      (1 : ℝ) - (if i = j then 1 else 0) := by
    by_cases hij : i = j
    · subst j; simp
    · simp [hx i j hij, hij]
  simp_rw [hpoint]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_fin, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem unit_equilateral_totalTrace {n d : ℕ} (x : Fin (n + 1) → Point d)
    (hx : UnitEquilateral x)
    (orders : Fin d → Equiv.Perm (Fin (n + 1)))
    (horders : ∀ k, Monotone (fun i => x (orders k i) k)) :
    (∑ k, columnTrace x orders k) = (n : ℝ) / 2 := by
  have ht : (∑ i, ∑ j, l1dist (x i) (x j)) =
      2 * (n + 1 : ℝ) * (∑ k, columnTrace x orders k) := by
    calc
      _ = ∑ k, ∑ i, ∑ j, |x i k - x j k| := by
        unfold l1dist
        exact sum_swap_third _
      _ = ∑ k, 2 * (n + 1 : ℝ) * columnTrace x orders k := by
        apply Finset.sum_congr rfl
        intro k hk
        exact scalar_pairSum_eq_trace _ _ (horders k)
      _ = _ := by rw [Finset.mul_sum]
  rw [unit_equilateral_pairSum x hx] at ht
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hc : 2 * (∑ k, columnTrace x orders k) = (n : ℝ) := by
    apply mul_left_cancel₀ hn
    nlinarith [ht]
  linarith

theorem unit_equilateral_actual_totalTrace {n d : ℕ} (x : Fin (n + 1) → Point d)
    (hx : UnitEquilateral x) :
    (∑ k, columnTrace x (columnOrders x) k) = (n : ℝ) / 2 :=
  unit_equilateral_totalTrace x hx _ (columnOrders_monotone x)

theorem unit_equilateral_five_totalTrace (x : Configuration) (hx : UnitEquilateral x) :
    (∑ k, columnTrace x (columnOrders x) k) = 5 := by
  have ht : (∑ k, columnTrace x (columnOrders x) k) = (10 : ℝ) / 2 :=
    unit_equilateral_actual_totalTrace x hx
  norm_num at ht
  exact ht

theorem scalarEnergy_transport_eq {n : ℕ} (f : Fin (n + 1) → ℝ)
    (p : Equiv.Perm (Fin (n + 1))) (v : Fin (n + 1) → ℝ) (h : Fin n → ℝ)
    (hprefix : ∀ r : Fin n,
      (∑ i : Fin (n + 1), if i.val ≤ r.val then v i else 0) = h r) :
    scalarEnergy f p (transport p v) = ∑ r : Fin n, gap f p r * (h r) ^ 2 := by
  unfold scalarEnergy
  simp_rw [prefix_transport, hprefix]

/-- Directed energy: row k's vector is transported through row k's actual order,
then evaluated on each OTHER actual original coordinate. -/
def crossEnergy {n d : ℕ} (x : Fin (n + 1) → Point d)
    (orders : Fin d → Equiv.Perm (Fin (n + 1))) (v : Fin (n + 1) → ℝ) : ℝ :=
  ∑ k, ∑ l ∈ Finset.univ.erase k, columnEnergy x orders l (transport (orders k) v)

theorem crossEnergy_nonneg {n d : ℕ} (x : Fin (n + 1) → Point d)
    (orders : Fin d → Equiv.Perm (Fin (n + 1)))
    (horders : ∀ k, Monotone (fun i => x (orders k i) k))
    (v : Fin (n + 1) → ℝ) : 0 ≤ crossEnergy x orders v := by
  unfold crossEnergy
  apply Finset.sum_nonneg
  intro k hk
  exact Finset.sum_nonneg fun l _ => scalarEnergy_nonneg _ _ (horders l) _

theorem crossEnergy_row {n d : ℕ} (x : Fin (n + 1) → Point d)
    (hx : UnitEquilateral x)
    (orders : Fin d → Equiv.Perm (Fin (n + 1)))
    (horders : ∀ k, Monotone (fun i => x (orders k i) k))
    (v : Fin (n + 1) → ℝ) (hv : (∑ i, v i) = 0) (k : Fin d) :
    (∑ l ∈ Finset.univ.erase k, columnEnergy x orders l (transport (orders k) v)) =
      (1 / 2 : ℝ) * (∑ i, v i ^ 2) -
        columnEnergy x orders k (transport (orders k) v) := by
  have hu : (∑ i, transport (orders k) v i) = 0 := by rw [sum_transport, hv]
  have hr := unit_equilateral_totalEnergy x hx orders horders (transport (orders k) v) hu
  rw [sum_transport_sq] at hr
  have hsplit : columnEnergy x orders k (transport (orders k) v) +
      (∑ l ∈ Finset.univ.erase k, columnEnergy x orders l (transport (orders k) v)) =
        ∑ l, columnEnergy x orders l (transport (orders k) v) := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin d))
      (fun l => columnEnergy x orders l (transport (orders k) v))
      (Finset.mem_univ k)
    linarith
  linarith

theorem crossEnergy_eq_deficit {n d : ℕ} (x : Fin (n + 1) → Point d)
    (hx : UnitEquilateral x)
    (orders : Fin d → Equiv.Perm (Fin (n + 1)))
    (horders : ∀ k, Monotone (fun i => x (orders k i) k))
    (v : Fin (n + 1) → ℝ) (hv : (∑ i, v i) = 0) :
    crossEnergy x orders v = (d : ℝ) * ((1 / 2 : ℝ) * (∑ i, v i ^ 2)) -
      ∑ k, columnEnergy x orders k (transport (orders k) v) := by
  unfold crossEnergy
  simp_rw [crossEnergy_row x hx orders horders v hv]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem crossEnergy_actual_eq_deficit {n d : ℕ} (x : Fin (n + 1) → Point d)
    (hx : UnitEquilateral x) (v : Fin (n + 1) → ℝ) (hv : (∑ i, v i) = 0) :
    crossEnergy x (columnOrders x) v =
      (d : ℝ) * ((1 / 2 : ℝ) * (∑ i, v i ^ 2)) -
        ∑ k, columnEnergy x (columnOrders x) k (transport (columnOrders x k) v) :=
  crossEnergy_eq_deficit x hx _ (columnOrders_monotone x) v hv

theorem prefixSet_first (p : Equiv.Perm (Fin 11)) :
    prefixSet p (0 : Fin 10) = {p 0} := by
  ext i
  simp only [mem_prefixSet, Fin.val_zero, Finset.mem_singleton]
  constructor
  · intro hi
    have hr : p.symm i = 0 := Fin.ext (by omega)
    simpa using congrArg p hr
  · intro hi
    subst i
    simp

theorem prefixSet_last (p : Equiv.Perm (Fin 11)) :
    prefixSet p (9 : Fin 10) = Finset.univ.erase (p (Fin.last 10)) := by
  ext i
  simp only [mem_prefixSet, Finset.mem_erase, Finset.mem_univ, and_true]
  have he : i = p (Fin.last 10) ↔ (p.symm i).val = 10 := by
    constructor
    · intro hi; subst i; simp
    · intro hr
      have hfin : p.symm i = Fin.last 10 := Fin.ext hr
      simpa using congrArg p hfin
  simp only [ne_eq, he]
  have := (p.symm i).isLt
  change (p.symm i).val ≤ 9 ↔ ¬(p.symm i).val = 10
  omega

theorem prefixMass_first (p : Equiv.Perm (Fin 11)) (u : Fin 11 → ℝ) :
    prefixMass p (0 : Fin 10) u = u (p 0) := by
  simp [prefixMass, prefixSet_first]

theorem prefixMass_last (p : Equiv.Perm (Fin 11)) (u : Fin 11 → ℝ)
    (hu : (∑ i, u i) = 0) :
    prefixMass p (9 : Fin 10) u = -u (p (Fin.last 10)) := by
  unfold prefixMass
  rw [prefixSet_last]
  have h : u (p (Fin.last 10)) +
      (∑ i ∈ Finset.univ.erase (p (Fin.last 10)), u i) = 0 := by
    rw [←Finset.sum_insert (by simp), Finset.insert_erase (Finset.mem_univ _), hu]
  linarith

theorem scalarEnergy_outer_lower (f : Fin 11 → ℝ) (p : Equiv.Perm (Fin 11))
    (hf : Monotone (fun i => f (p i))) (u : Fin 11 → ℝ)
    (hu : (∑ i, u i) = 0) (t : ℝ) (ht : 0 ≤ t)
    (hfirst : t ≤ gap f p (0 : Fin 10)) (hlast : t ≤ gap f p (9 : Fin 10)) :
    t * (u (p 0) ^ 2 + u (p (Fin.last 10)) ^ 2) ≤ scalarEnergy f p u := by
  have hpair : gap f p (0 : Fin 10) * (prefixMass p (0 : Fin 10) u) ^ 2 +
      gap f p (9 : Fin 10) * (prefixMass p (9 : Fin 10) u) ^ 2 ≤
        scalarEnergy f p u := by
    have hs : ({(0 : Fin 10), (9 : Fin 10)} : Finset (Fin 10)) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun r _ _ => mul_nonneg (gap_nonneg f p hf r) (sq_nonneg (prefixMass p r u)))
    simpa [scalarEnergy, Finset.sum_pair (by decide : (0 : Fin 10) ≠ 9)] using hsum
  rw [prefixMass_first, prefixMass_last p u hu, neg_sq] at hpair
  have ha := mul_le_mul_of_nonneg_right hfirst (sq_nonneg (u (p 0)))
  have hb := mul_le_mul_of_nonneg_right hlast (sq_nonneg (u (p (Fin.last 10))))
  nlinarith

end
end Kusner5
