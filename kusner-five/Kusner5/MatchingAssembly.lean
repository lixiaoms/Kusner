import Kusner5.ForestMatching
import Kusner5.Quartet

/-!
Original matching endpoints and the one selected original quartet. Coordinate
sorting permutes physical columns only; all point labels and pair equations
remain those of the same arbitrary real eleven-point input.
-/

namespace Kusner5.MatchingAssembly

open scoped BigOperators
open ForestMatching

noncomputable section

theorem sum_perm {V : Type*} [Fintype V] (p : Equiv.Perm V) (f : V → ℝ) :
    (∑ i, f (p i)) = ∑ i, f i := by
  classical
  apply Finset.sum_bij (fun i _ => p i)
  · intro i hi; exact Finset.mem_univ _
  · intro i hi j hj hij; exact p.injective hij
  · intro i hi; exact ⟨p.symm i, Finset.mem_univ _, by simp⟩
  · intro i hi; rfl

def sortedCoordinates (x : Configuration) : Equiv.Perm Coordinate :=
  actualOrder (fun k => -excess (actualExtrema x) k)

def sortedExcess (x : Configuration) (i : Coordinate) : ℝ :=
  excess (actualExtrema x) (sortedCoordinates x i)

theorem sortedExcess_antitone (x : Configuration) : Antitone (sortedExcess x) := by
  intro i j hij
  have h := actualOrder_monotone (fun k => -excess (actualExtrema x) k) hij
  change -sortedExcess x i ≤ -sortedExcess x j at h
  linarith

theorem sortedExcess_le_third (x : Configuration) (hx : UnitEquilateral x)
    (i : Coordinate) : sortedExcess x i ≤ 1 / 3 :=
  original_excess_le_third x hx (sortedCoordinates x i)

theorem sortedExcess_pos (x : Configuration)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (i : Coordinate) :
    0 < sortedExcess x i :=
  excess_pos (actualExtrema x) _ (hWide _)

def sortedEndpointLabel (x : Configuration) (p : Equiv.Perm Coordinate)
    (ib : Coordinate × Bool) : Label :=
  endpointLabel (actualExtrema x) (p ib.1, ib.2)

theorem sortedEndpointLabel_injective (x : Configuration)
    (p : Equiv.Perm Coordinate) (hWide : ∀ k, IsWide (actualExtrema x) k)
    (hMatching : IsMatching (actualExtrema x)) :
    Function.Injective (sortedEndpointLabel x p) := by
  intro a b hab
  have h := matching_endpointLabel_injective (actualExtrema x) hWide hMatching hab
  apply Prod.ext
  · exact p.injective (congrArg Prod.fst h)
  · have hSecond := congrArg (fun v : Coordinate × Bool => v.2) h
    exact hSecond

theorem sortedEndpointLabel_ne_other (x : Configuration)
    (p : Equiv.Perm Coordinate) (hWide : ∀ k, IsWide (actualExtrema x) k)
    (hMatching : IsMatching (actualExtrema x)) (u v : Coordinate) (b : Bool)
    (huv : u ≠ v) :
    sortedEndpointLabel x p (u, b) ≠ (actualExtrema x (p v)).lo ∧
      sortedEndpointLabel x p (u, b) ≠ (actualExtrema x (p v)).hi := by
  have hinj := sortedEndpointLabel_injective x p hWide hMatching
  constructor
  · intro h
    have heq : sortedEndpointLabel x p (u, b) =
        sortedEndpointLabel x p (v, false) := by
      simpa [sortedEndpointLabel, endpointLabel] using h
    exact huv (congrArg Prod.fst (hinj heq))
  · intro h
    have heq : sortedEndpointLabel x p (u, b) =
        sortedEndpointLabel x p (v, true) := by
      simpa [sortedEndpointLabel, endpointLabel] using h
    exact huv (congrArg Prod.fst (hinj heq))

/-- Core, both endpoints of the smallest edge, and one endpoint of the next
edge are all original labels. No radius or contact representation is used. -/
def matchingQuartet (x : Configuration) (p : Equiv.Perm Coordinate)
    (core : Label) : Fin 4 → Label :=
  ![core, sortedEndpointLabel x p (4, false),
    sortedEndpointLabel x p (4, true), sortedEndpointLabel x p (3, false)]

theorem matchingQuartet_injective (x : Configuration) (p : Equiv.Perm Coordinate)
    (hWide : ∀ k, IsWide (actualExtrema x) k)
    (hMatching : IsMatching (actualExtrema x))
    (core : Label) (hCore : IsCore (actualExtrema x) core) :
    Function.Injective (matchingQuartet x p core) := by
  have hinj := sortedEndpointLabel_injective x p hWide hMatching
  have h01 : core ≠ sortedEndpointLabel x p (4, false) := by
    simpa [sortedEndpointLabel, endpointLabel] using (hCore (p 4)).1
  have h02 : core ≠ sortedEndpointLabel x p (4, true) := by
    simpa [sortedEndpointLabel, endpointLabel] using (hCore (p 4)).2
  have h03 : core ≠ sortedEndpointLabel x p (3, false) := by
    simpa [sortedEndpointLabel, endpointLabel] using (hCore (p 3)).1
  have h12 : sortedEndpointLabel x p (4, false) ≠ sortedEndpointLabel x p (4, true) := by
    intro h; have heq := hinj h; norm_num at heq
  have h13 : sortedEndpointLabel x p (4, false) ≠ sortedEndpointLabel x p (3, false) := by
    intro h; have heq := congrArg Prod.fst (hinj h); norm_num at heq
  have h23 : sortedEndpointLabel x p (4, true) ≠ sortedEndpointLabel x p (3, false) := by
    intro h; have heq := congrArg Prod.fst (hinj h); norm_num at heq
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [matchingQuartet]

theorem matchingQuartet_inner_bounds (x : Configuration) (hx : UnitEquilateral x)
    (p : Equiv.Perm Coordinate) (hWide : ∀ k, IsWide (actualExtrema x) k)
    (hMatching : IsMatching (actualExtrema x))
    (core : Label) (hCore : IsCore (actualExtrema x) core)
    (k : Coordinate) (hk3 : k ≠ 3) (hk4 : k ≠ 4) (j : Fin 4) :
    x (actualExtrema x (p k)).hi (p k) - 1 / 2 ≤
        x (matchingQuartet x p core j) (p k) ∧
      x (matchingQuartet x p core j) (p k) ≤
        x (actualExtrema x (p k)).lo (p k) + 1 / 2 := by
  have hother4 (b : Bool) := sortedEndpointLabel_ne_other x p hWide hMatching 4 k b
    (Ne.symm hk4)
  have hother3 := sortedEndpointLabel_ne_other x p hWide hMatching 3 k false
    (Ne.symm hk3)
  fin_cases j
  · simpa [matchingQuartet] using
      (actualExtrema x (p k)).wide_inner_bounds hx (hWide _) core
        (hCore _).1 (hCore _).2
  · simpa [matchingQuartet] using
      (actualExtrema x (p k)).wide_inner_bounds hx (hWide _)
        (sortedEndpointLabel x p (4, false)) (hother4 false).1 (hother4 false).2
  · simpa [matchingQuartet] using
      (actualExtrema x (p k)).wide_inner_bounds hx (hWide _)
        (sortedEndpointLabel x p (4, true)) (hother4 true).1 (hother4 true).2
  · simpa [matchingQuartet] using
      (actualExtrema x (p k)).wide_inner_bounds hx (hWide _)
        (sortedEndpointLabel x p (3, false)) hother3.1 hother3.2

theorem matchingQuartet_inner_range_le (x : Configuration) (hx : UnitEquilateral x)
    (p : Equiv.Perm Coordinate) (hWide : ∀ k, IsWide (actualExtrema x) k)
    (hMatching : IsMatching (actualExtrema x))
    (core : Label) (hCore : IsCore (actualExtrema x) core)
    (k : Coordinate) (hk3 : k ≠ 3) (hk4 : k ≠ 4) :
    scalarRange (quartetColumn x (matchingQuartet x p core) (p k))
      (quartetOrder x (matchingQuartet x p core) (p k)) ≤
      1 - (actualExtrema x (p k)).range := by
  have h := subconfiguration_range_le_box x (matchingQuartet x p core) (p k)
    (quartetOrder x (matchingQuartet x p core) (p k))
    (x (actualExtrema x (p k)).hi (p k) - 1 / 2)
    (x (actualExtrema x (p k)).lo (p k) + 1 / 2)
    (matchingQuartet_inner_bounds x hx p hWide hMatching core hCore k hk3 hk4)
  change scalarRange (quartetColumn x (matchingQuartet x p core) (p k))
    (quartetOrder x (matchingQuartet x p core) (p k)) ≤ _ at h
  unfold CoordinateExtrema.range
  linarith

theorem matchingQuartet_fourth_range_le (x : Configuration) (hx : UnitEquilateral x)
    (p : Equiv.Perm Coordinate) (hWide : ∀ k, IsWide (actualExtrema x) k)
    (hMatching : IsMatching (actualExtrema x))
    (core : Label) (hCore : IsCore (actualExtrema x) core) :
    scalarRange (quartetColumn x (matchingQuartet x p core) (p 3))
      (quartetOrder x (matchingQuartet x p core) (p 3)) ≤ 1 / 2 := by
  have hother4 (b : Bool) := sortedEndpointLabel_ne_other x p hWide hMatching 4 3 b
    (by decide)
  have hbox (j : Fin 4) :
      x (actualExtrema x (p 3)).lo (p 3) ≤ x (matchingQuartet x p core j) (p 3) ∧
        x (matchingQuartet x p core j) (p 3) ≤
          x (actualExtrema x (p 3)).lo (p 3) + 1 / 2 := by
    refine ⟨(actualExtrema x (p 3)).bound_all _ |>.1, ?_⟩
    fin_cases j
    · simpa [matchingQuartet] using
        ((actualExtrema x (p 3)).wide_inner_bounds hx (hWide _) core
          (hCore _).1 (hCore _).2).2
    · simpa [matchingQuartet] using
        ((actualExtrema x (p 3)).wide_inner_bounds hx (hWide _)
          (sortedEndpointLabel x p (4, false)) (hother4 false).1 (hother4 false).2).2
    · simpa [matchingQuartet] using
        ((actualExtrema x (p 3)).wide_inner_bounds hx (hWide _)
          (sortedEndpointLabel x p (4, true)) (hother4 true).1 (hother4 true).2).2
    · change x (actualExtrema x (p 3)).lo (p 3) ≤
        x (actualExtrema x (p 3)).lo (p 3) + 1 / 2
      linarith
  have h := subconfiguration_range_le_box x (matchingQuartet x p core) (p 3)
    (quartetOrder x (matchingQuartet x p core) (p 3))
    (x (actualExtrema x (p 3)).lo (p 3))
    (x (actualExtrema x (p 3)).lo (p 3) + 1 / 2) hbox
  change scalarRange (quartetColumn x (matchingQuartet x p core) (p 3))
    (quartetOrder x (matchingQuartet x p core) (p 3)) ≤ _ at h
  linarith

theorem matchingQuartet_width_le (x : Configuration) (hx : UnitEquilateral x)
    (p : Equiv.Perm Coordinate) (hWide : ∀ k, IsWide (actualExtrema x) k)
    (hMatching : IsMatching (actualExtrema x))
    (core : Label) (hCore : IsCore (actualExtrema x) core) :
    quartetWidth x (matchingQuartet x p core) ≤
      (actualExtrema x (p 4)).range + 1 / 2 +
        (1 - (actualExtrema x (p 0)).range) +
        (1 - (actualExtrema x (p 1)).range) +
        (1 - (actualExtrema x (p 2)).range) := by
  have h0 := matchingQuartet_inner_range_le x hx p hWide hMatching core hCore 0
    (by decide) (by decide)
  have h1 := matchingQuartet_inner_range_le x hx p hWide hMatching core hCore 1
    (by decide) (by decide)
  have h2 := matchingQuartet_inner_range_le x hx p hWide hMatching core hCore 2
    (by decide) (by decide)
  have h3 := matchingQuartet_fourth_range_le x hx p hWide hMatching core hCore
  have h4 := subconfiguration_range_le_box x (matchingQuartet x p core) (p 4)
    (quartetOrder x (matchingQuartet x p core) (p 4))
    (x (actualExtrema x (p 4)).lo (p 4)) (x (actualExtrema x (p 4)).hi (p 4))
    (fun j => (actualExtrema x (p 4)).bound_all (matchingQuartet x p core j))
  change scalarRange (quartetColumn x (matchingQuartet x p core) (p 4))
      (quartetOrder x (matchingQuartet x p core) (p 4)) ≤
    (actualExtrema x (p 4)).range at h4
  unfold quartetWidth
  rw [← sum_perm p]
  norm_num [Fin.sum_univ_succ]
  linarith

/-- This bridge uses the selected ORIGINAL quartet's lower bound as its
intermediate input; the final composition must derive that bound itself. -/
theorem matching_original_slack (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k)
    (hMatching : IsMatching (actualExtrema x))
    (core : Label) (hCore : IsCore (actualExtrema x) core)
    (hQuartet : 37 / 24 ≤ quartetWidth x (matchingQuartet x (sortedCoordinates x) core)) :
    1 / 24 ≤ (1 / 3 - sortedExcess x 0) + (1 / 3 - sortedExcess x 1) +
      (1 / 3 - sortedExcess x 2) + sortedExcess x 4 := by
  have hWidth := matchingQuartet_width_le x hx (sortedCoordinates x) hWide hMatching
    core hCore
  simp only [sortedExcess, excess]
  linarith

def otherCoordinates : Coordinate → Fin 4 → Coordinate :=
  ![![1, 2, 3, 4], ![0, 2, 3, 4], ![0, 1, 3, 4],
    ![0, 1, 2, 4], ![0, 1, 2, 3]]

theorem otherCoordinates_ne (row : Coordinate) (i : Fin 4) :
    otherCoordinates row i ≠ row := by
  fin_cases row <;> fin_cases i <;> decide

theorem otherCoordinates_injective (row : Coordinate) :
    Function.Injective (otherCoordinates row) := by
  fin_cases row <;> decide

theorem otherCoordinates_monotone (row : Coordinate) :
    Monotone (otherCoordinates row) := by
  fin_cases row <;> decide

theorem otherCoordinates_covers :
    ∀ row k : Coordinate, k ≠ row → ∃ i : Fin 4, otherCoordinates row i = k := by
  decide

theorem sum_otherCoordinates (row : Coordinate) (f : Coordinate → ℝ) :
    (∑ i : Fin 4, f (otherCoordinates row i)) = ∑ k ∈ Finset.univ.erase row, f k := by
  classical
  apply Finset.sum_bij (fun i _ => otherCoordinates row i)
  · intro i hi
    exact Finset.mem_erase.mpr ⟨otherCoordinates_ne row i, Finset.mem_univ _⟩
  · intro i hi j hj hij; exact otherCoordinates_injective row hij
  · intro k hk
    obtain ⟨i, hi⟩ := otherCoordinates_covers row k (Finset.mem_erase.mp hk).1
    exact ⟨i, Finset.mem_univ _, hi⟩
  · intro i hi; rfl

theorem sum_erase_perm (p : Equiv.Perm Coordinate) (row : Coordinate)
    (f : Coordinate → ℝ) :
    (∑ k ∈ Finset.univ.erase row, f (p k)) =
      ∑ k ∈ Finset.univ.erase (p row), f k := by
  classical
  apply Finset.sum_bij (fun i _ => p i)
  · intro i hi
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    exact fun h => (Finset.mem_erase.mp hi).1 (p.injective h)
  · intro i hi j hj hij; exact p.injective hij
  · intro k hk
    refine ⟨p.symm k, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, by simp⟩
    intro h
    apply (Finset.mem_erase.mp hk).1
    calc
      k = p (p.symm k) := (p.apply_symm_apply k).symm
      _ = p row := congrArg p h
  · intro i hi; rfl

def pairedSlot : Fin 8 → Fin 4 × Bool :=
  ![(0, false), (0, true), (1, false), (1, true),
    (2, false), (2, true), (3, false), (3, true)]

theorem pairedSlot_injective : Function.Injective pairedSlot := by decide

def pairedOtherEndpoint (x : Configuration) (p : Equiv.Perm Coordinate)
    (row : Coordinate) (i : Fin 8) : Label :=
  sortedEndpointLabel x p (otherCoordinates row (pairedSlot i).1, (pairedSlot i).2)

def otherEndpointPositions (x : Configuration) (p : Equiv.Perm Coordinate)
    (row : Coordinate) (i : Fin 8) : Label :=
  (columnOrders x (p row)).symm (pairedOtherEndpoint x p row i)

theorem otherEndpointPositions_injective (x : Configuration)
    (p : Equiv.Perm Coordinate) (hWide : ∀ k, IsWide (actualExtrema x) k)
    (hMatching : IsMatching (actualExtrema x)) (row : Coordinate) :
    Function.Injective (otherEndpointPositions x p row) := by
  intro i j hij
  have hlabel := (columnOrders x (p row)).symm.injective hij
  have hp : (otherCoordinates row (pairedSlot i).1, (pairedSlot i).2) =
      (otherCoordinates row (pairedSlot j).1, (pairedSlot j).2) :=
    sortedEndpointLabel_injective x p hWide hMatching hlabel
  apply pairedSlot_injective
  apply Prod.ext
  · exact otherCoordinates_injective row (congrArg Prod.fst hp)
  · exact congrArg (fun v : Coordinate × Bool => v.2) hp

def rowVector (x : Configuration) (p : Equiv.Perm Coordinate)
    (row : Coordinate) : Label → ℝ :=
  transport (columnOrders x (p row)) Profiles.shiftedVector

def rowPairSquare (x : Configuration) (p : Equiv.Perm Coordinate)
    (row : Coordinate) (i : Fin 4) : ℝ :=
  rowVector x p row (actualExtrema x (p (otherCoordinates row i))).lo ^ 2 +
    rowVector x p row (actualExtrema x (p (otherCoordinates row i))).hi ^ 2

def rowCoefficient (x : Configuration) (row : Coordinate) : ℝ :=
  MatchingArithmetic.c1 * sortedExcess x (otherCoordinates row 0) +
    MatchingArithmetic.c2 * sortedExcess x (otherCoordinates row 1) +
    MatchingArithmetic.c3 * sortedExcess x (otherCoordinates row 2) +
    MatchingArithmetic.c4 * sortedExcess x (otherCoordinates row 3)

def rowCrossEnergy (x : Configuration) (row : Coordinate) : ℝ :=
  ∑ col ∈ Finset.univ.erase row,
    columnEnergy x (columnOrders x) col
      (transport (columnOrders x row) Profiles.shiftedVector)

theorem matching_row_position_lower (x : Configuration)
    (hWide : ∀ k, IsWide (actualExtrema x) k)
    (hMatching : IsMatching (actualExtrema x)) (row : Coordinate) :
    rowCoefficient x row ≤ ∑ i : Fin 4,
      sortedExcess x (otherCoordinates row i) *
        rowPairSquare x (sortedCoordinates x) row i := by
  let p := sortedCoordinates x
  let f := otherEndpointPositions x p row
  have hf : Function.Injective f := otherEndpointPositions_injective x p hWide hMatching row
  have hmono := otherCoordinates_monotone row
  have h01 := sortedExcess_antitone x (hmono (by decide : (0 : Fin 4) ≤ 1))
  have h12 := sortedExcess_antitone x (hmono (by decide : (1 : Fin 4) ≤ 2))
  have h23 := sortedExcess_antitone x (hmono (by decide : (2 : Fin 4) ≤ 3))
  have h3 := le_of_lt (sortedExcess_pos x hWide (otherCoordinates row 3))
  have hw := weighted_eight_positions f hf
    (sortedExcess x (otherCoordinates row 0)) (sortedExcess x (otherCoordinates row 1))
    (sortedExcess x (otherCoordinates row 2)) (sortedExcess x (otherCoordinates row 3))
    h01 h12 h23 h3
  have hcast (i : Fin 8) : squaredPosition (f i) =
      rowVector x p row (pairedOtherEndpoint x p row i) ^ 2 := by
    rw [← shiftedVector_sq_eq_position]
    rfl
  simp_rw [hcast] at hw
  simpa [rowCoefficient, rowPairSquare, pairedOtherEndpoint, pairedSlot,
    sortedEndpointLabel, endpointLabel, Fin.sum_univ_succ, p, add_assoc] using hw

/-- Each row is the actual original-label test vector, evaluated on the four
other physical coordinates. The two endpoints of every edge remain distinct. -/
theorem original_matching_row_lower (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k)
    (hMatching : IsMatching (actualExtrema x)) (row : Coordinate) :
    rowCoefficient x row ≤ rowCrossEnergy x (sortedCoordinates x row) := by
  let p := sortedCoordinates x
  have hu : (∑ i, rowVector x p row i) = 0 := by
    rw [rowVector, sum_transport, Profiles.sum_shiftedVector_zero]
  have hpoint (i : Fin 4) :
      sortedExcess x (otherCoordinates row i) * rowPairSquare x p row i ≤
        columnEnergy x (columnOrders x) (p (otherCoordinates row i)) (rowVector x p row) := by
    exact actual_wide_outer_energy_lower x hx (p (otherCoordinates row i)) (hWide _)
      (rowVector x p row) hu
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => hpoint i)
  rw [sum_otherCoordinates row
    (fun k => columnEnergy x (columnOrders x) (p k) (rowVector x p row)),
    sum_erase_perm p row
      (fun k => columnEnergy x (columnOrders x) k (rowVector x p row))] at hs
  exact le_trans (matching_row_position_lower x hWide hMatching row) hs

theorem sum_rowCoefficient (x : Configuration) :
    (∑ row, rowCoefficient x row) =
      MatchingArithmetic.b1 * sortedExcess x 0 + MatchingArithmetic.b2 * sortedExcess x 1 +
        MatchingArithmetic.b3 * sortedExcess x 2 + MatchingArithmetic.b4 * sortedExcess x 3 +
        MatchingArithmetic.b5 * sortedExcess x 4 := by
  norm_num [rowCoefficient, otherCoordinates, Fin.sum_univ_succ]
  dsimp [MatchingArithmetic.b1, MatchingArithmetic.b2, MatchingArithmetic.b3,
    MatchingArithmetic.b4, MatchingArithmetic.b5]
  ring

theorem original_five_matching_energy_lower (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k)
    (hMatching : IsMatching (actualExtrema x)) :
    MatchingArithmetic.b1 * sortedExcess x 0 + MatchingArithmetic.b2 * sortedExcess x 1 +
      MatchingArithmetic.b3 * sortedExcess x 2 + MatchingArithmetic.b4 * sortedExcess x 3 +
      MatchingArithmetic.b5 * sortedExcess x 4 ≤
        crossEnergy x (columnOrders x) Profiles.shiftedVector := by
  have hs := Finset.sum_le_sum (fun row (_ : row ∈ (Finset.univ : Finset Coordinate)) =>
    original_matching_row_lower x hx hWide hMatching row)
  rw [sum_rowCoefficient, sum_perm (sortedCoordinates x)] at hs
  exact hs

theorem totalWidth_sorted_excess (x : Configuration) :
    Profiles.totalWidth x = 5 / 2 + ∑ i, sortedExcess x i := by
  have hs : (∑ i, sortedExcess x i) = Profiles.totalWidth x - 5 / 2 := by
    unfold sortedExcess
    rw [sum_perm (sortedCoordinates x)]
    simp only [excess, actualExtrema_range, Finset.sum_sub_distrib]
    norm_num [Profiles.totalWidth]
  linarith

theorem original_five_matching_deficit (x : Configuration) (hx : UnitEquilateral x) :
    crossEnergy x (columnOrders x) Profiles.shiftedVector =
      5 * MatchingArithmetic.alpha - 15 / 4 + (∑ i, sortedExcess x i) / 2 := by
  rw [Profiles.shifted_crossEnergy x hx, totalWidth_sorted_excess]
  change 5 * MatchingArithmetic.alpha + (5 / 2 + ∑ i, sortedExcess x i) / 2 - 5 = _
  ring

/-- The final quartet input is explicitly an intermediate dependency. Main
must supply the full arbitrary-original-quartet theorem, never assume it. -/
theorem no_five_matching_of_quartet_bound (x : Configuration) (hx : UnitEquilateral x)
    (hWideCard : (wideCoordinates (actualExtrema x)).card = 5)
    (hNonisolated : (nonisolatedCoordinates (actualExtrema x)).card = 0)
    (hQuartet : ∀ q : Fin 4 → Label, Function.Injective q → 37 / 24 ≤ quartetWidth x q) :
    False := by
  have hWide := all_wide_of_card_five (actualExtrema x) hWideCard
  have hMatching := matching_of_no_nonisolated (actualExtrema x) hNonisolated
  obtain ⟨core, hCore⟩ := exists_core (actualExtrema x)
  have hq := matchingQuartet_injective x (sortedCoordinates x) hWide hMatching core hCore
  have hSlack := matching_original_slack x hx hWide hMatching core hCore
    (hQuartet _ hq)
  have hEq : crossEnergy x (columnOrders x) Profiles.shiftedVector =
      5 * MatchingArithmetic.alpha - 15 / 4 +
        (sortedExcess x 0 + sortedExcess x 1 + sortedExcess x 2 +
          sortedExcess x 3 + sortedExcess x 4) / 2 := by
    have h := original_five_matching_deficit x hx
    norm_num [Fin.sum_univ_succ] at h
    linarith
  exact MatchingArithmetic.matching_contradiction
    (sortedExcess x 0) (sortedExcess x 1) (sortedExcess x 2)
    (sortedExcess x 3) (sortedExcess x 4)
    (crossEnergy x (columnOrders x) Profiles.shiftedVector)
    (sortedExcess_le_third x hx 0) (sortedExcess_le_third x hx 1)
    (sortedExcess_le_third x hx 2) (sortedExcess_le_third x hx 3)
    (le_of_lt (sortedExcess_pos x hWide 4)) hSlack hEq
    (original_five_matching_energy_lower x hx hWide hMatching)

end
end Kusner5.MatchingAssembly
