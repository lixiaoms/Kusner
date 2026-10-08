import Kusner5.MatchingAssembly

/-!
The four-wide matching branch on the same original eleven labels. Six true
other-edge endpoints are used in a wide row, and all eight true wide-edge
endpoints in the remaining nonwide row. No endpoints of the nonwide column
are treated as a matching edge.
-/

namespace Kusner5.FourMatchingAssembly

open scoped BigOperators
open ForestMatching MatchingAssembly

noncomputable section

-- Avoid the observed simplifier-procedure panic; ordinary kernel proofs remain required.
set_option simprocs false

theorem sorted_last_nonwide (x : Configuration)
    (hCard : (wideCoordinates (actualExtrema x)).card = 4) :
    ¬IsWide (actualExtrema x) (sortedCoordinates x 4) := by
  classical
  intro h4
  have hAll : ∀ k, IsWide (actualExtrema x) k := by
    intro k
    let i := (sortedCoordinates x).symm k
    have hi : i ≤ (4 : Coordinate) := Fin.le_last _
    have ht := sortedExcess_antitone x hi
    have hp : 0 < sortedExcess x 4 := excess_pos (actualExtrema x) _ h4
    have hpi : 0 < sortedExcess x i := lt_of_lt_of_le hp ht
    have he : sortedCoordinates x i = k := by simp [i]
    unfold sortedExcess excess at hpi
    rw [he] at hpi
    exact (show (1 / 2 : ℝ) < (actualExtrema x k).range by linarith)
  have hEq : wideCoordinates (actualExtrema x) = Finset.univ := by
    ext k
    simp only [Finset.mem_univ, iff_true]
    exact (mem_wideCoordinates (actualExtrema x) k).mpr (hAll k)
  rw [hEq] at hCard
  norm_num at hCard

theorem sorted_first_four_wide (x : Configuration)
    (hCard : (wideCoordinates (actualExtrema x)).card = 4) (i : Fin 4) :
    IsWide (actualExtrema x) (sortedCoordinates x i.castSucc) := by
  classical
  have hCcard : ((wideCoordinates (actualExtrema x))ᶜ).card = 1 := by
    rw [Finset.card_compl, hCard]
    norm_num
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hCcard
  have hLast : sortedCoordinates x 4 ∈ (wideCoordinates (actualExtrema x))ᶜ := by
    apply Finset.mem_compl.mpr
    intro hm
    exact sorted_last_nonwide x hCard
      ((mem_wideCoordinates (actualExtrema x) _).mp hm)
  rw [hj, Finset.mem_singleton] at hLast
  have hC : (wideCoordinates (actualExtrema x))ᶜ = {sortedCoordinates x 4} := by
    simpa only [← hLast] using hj
  by_contra hn
  have hm : sortedCoordinates x i.castSucc ∈ (wideCoordinates (actualExtrema x))ᶜ := by
    apply Finset.mem_compl.mpr
    exact fun h => hn ((mem_wideCoordinates (actualExtrema x) _).mp h)
  rw [hC, Finset.mem_singleton] at hm
  have he := (sortedCoordinates x).injective hm
  have hv := congrArg Fin.val he
  have hi := i.isLt
  simp only [Fin.val_castSucc] at hv
  norm_num at hv
  omega

theorem sorted_first_four_positive (x : Configuration)
    (hCard : (wideCoordinates (actualExtrema x)).card = 4) (i : Fin 4) :
    0 < sortedExcess x i.castSucc :=
  excess_pos (actualExtrema x) _ (sorted_first_four_wide x hCard i)

theorem sorted_last_excess_nonpos (x : Configuration)
    (hCard : (wideCoordinates (actualExtrema x)).card = 4) : sortedExcess x 4 ≤ 0 := by
  have h := le_of_not_gt (sorted_last_nonwide x hCard)
  dsimp [sortedExcess, excess]
  linarith

def fourEndpointLabel (x : Configuration) (ib : Fin 4 × Bool) : Label :=
  endpointLabel (actualExtrema x) (sortedCoordinates x ib.1.castSucc, ib.2)

theorem fourEndpointLabel_injective (x : Configuration)
    (hCard : (wideCoordinates (actualExtrema x)).card = 4)
    (hMatching : IsMatching (actualExtrema x)) :
    Function.Injective (fourEndpointLabel x) := by
  intro a b hab
  rcases a with ⟨k, ka⟩
  rcases b with ⟨l, lb⟩
  have hkl : k = l := by
    by_contra hne
    have hPhysical : sortedCoordinates x k.castSucc ≠ sortedCoordinates x l.castSucc := by
      intro h
      have hv := congrArg Fin.val ((sortedCoordinates x).injective h)
      exact hne (Fin.ext hv)
    apply hMatching _ _ (sorted_first_four_wide x hCard k)
      (sorted_first_four_wide x hCard l) hPhysical
    exact ⟨fourEndpointLabel x (k, ka), endpointLabel_isEndpoint _ _,
      hab.symm ▸ endpointLabel_isEndpoint _ _⟩
  subst l
  cases ka <;> cases lb
  · rfl
  · simp [fourEndpointLabel, endpointLabel] at hab
    exact False.elim ((actualExtrema x _).lo_ne_hi_of_wide
      (sorted_first_four_wide x hCard k) hab)
  · simp [fourEndpointLabel, endpointLabel] at hab
    exact False.elim ((actualExtrema x _).lo_ne_hi_of_wide
      (sorted_first_four_wide x hCard k) hab.symm)
  · rfl

def otherWideCoordinates : Fin 4 → Fin 3 → Fin 4 :=
  ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

theorem otherWideCoordinates_injective (row : Fin 4) :
    Function.Injective (otherWideCoordinates row) := by
  fin_cases row <;> decide

theorem otherWideCoordinates_monotone (row : Fin 4) :
    Monotone (otherWideCoordinates row) := by
  fin_cases row <;> decide

theorem otherWideCoordinates_cast (row : Fin 4) (i : Fin 3) :
    (otherWideCoordinates row i).castSucc = otherCoordinates row.castSucc i.castSucc := by
  fin_cases row <;> fin_cases i <;> rfl

theorem otherCoordinates_last (row : Fin 4) : otherCoordinates row.castSucc 3 = 4 := by
  fin_cases row <;> rfl

def pairedSixSlot : Fin 6 → Fin 3 × Bool :=
  ![(0, false), (0, true), (1, false), (1, true), (2, false), (2, true)]

theorem pairedSixSlot_injective : Function.Injective pairedSixSlot := by decide

def sixOtherEndpoint (x : Configuration) (row : Fin 4) (i : Fin 6) : Label :=
  fourEndpointLabel x (otherWideCoordinates row (pairedSixSlot i).1, (pairedSixSlot i).2)

def sixOtherPositions (x : Configuration) (row : Fin 4) (i : Fin 6) : Label :=
  (columnOrders x (sortedCoordinates x row.castSucc)).symm (sixOtherEndpoint x row i)

theorem sixOtherPositions_injective (x : Configuration)
    (hCard : (wideCoordinates (actualExtrema x)).card = 4)
    (hMatching : IsMatching (actualExtrema x)) (row : Fin 4) :
    Function.Injective (sixOtherPositions x row) := by
  intro i j hij
  have hl := (columnOrders x (sortedCoordinates x row.castSucc)).symm.injective hij
  have hp := fourEndpointLabel_injective x hCard hMatching hl
  apply pairedSixSlot_injective
  apply Prod.ext
  · exact otherWideCoordinates_injective row (congrArg Prod.fst hp)
  · exact congrArg (fun v : Fin 4 × Bool => v.2) hp

def fourWidePairSquare (x : Configuration) (row : Coordinate) (i : Fin 4) : ℝ :=
  rowVector x (sortedCoordinates x) row
      (actualExtrema x (sortedCoordinates x i.castSucc)).lo ^ 2 +
    rowVector x (sortedCoordinates x) row
      (actualExtrema x (sortedCoordinates x i.castSucc)).hi ^ 2

def wideRowCoefficient (x : Configuration) (row : Fin 4) : ℝ :=
  MatchingArithmetic.c1 * sortedExcess x (otherWideCoordinates row 0).castSucc +
    MatchingArithmetic.c2 * sortedExcess x (otherWideCoordinates row 1).castSucc +
    MatchingArithmetic.c3 * sortedExcess x (otherWideCoordinates row 2).castSucc

theorem wide_row_position_lower (x : Configuration)
    (hCard : (wideCoordinates (actualExtrema x)).card = 4)
    (hMatching : IsMatching (actualExtrema x)) (row : Fin 4) :
    wideRowCoefficient x row ≤ ∑ i : Fin 3,
      sortedExcess x (otherWideCoordinates row i).castSucc *
        fourWidePairSquare x row.castSucc (otherWideCoordinates row i) := by
  let f := sixOtherPositions x row
  have hf : Function.Injective f := sixOtherPositions_injective x hCard hMatching row
  have hm := otherWideCoordinates_monotone row
  have h01 := sortedExcess_antitone x (show
      (otherWideCoordinates row 0).castSucc ≤ (otherWideCoordinates row 1).castSucc from
    hm (by decide : (0 : Fin 3) ≤ 1))
  have h12 := sortedExcess_antitone x (show
      (otherWideCoordinates row 1).castSucc ≤ (otherWideCoordinates row 2).castSucc from
    hm (by decide : (1 : Fin 3) ≤ 2))
  have hp := le_of_lt (sorted_first_four_positive x hCard (otherWideCoordinates row 2))
  have hw := weighted_six_positions f hf
    (sortedExcess x (otherWideCoordinates row 0).castSucc)
    (sortedExcess x (otherWideCoordinates row 1).castSucc)
    (sortedExcess x (otherWideCoordinates row 2).castSucc) h01 h12 hp
  have he (i : Fin 6) : squaredPosition (f i) =
      rowVector x (sortedCoordinates x) row.castSucc (sixOtherEndpoint x row i) ^ 2 := by
    rw [← shiftedVector_sq_eq_position]
    rfl
  simp_rw [he] at hw
  change wideRowCoefficient x row ≤
    sortedExcess x (otherWideCoordinates row 0).castSucc *
        fourWidePairSquare x row.castSucc (otherWideCoordinates row 0) +
      sortedExcess x (otherWideCoordinates row 1).castSucc *
        fourWidePairSquare x row.castSucc (otherWideCoordinates row 1) +
      sortedExcess x (otherWideCoordinates row 2).castSucc *
        fourWidePairSquare x row.castSucc (otherWideCoordinates row 2) at hw
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change wideRowCoefficient x row ≤
    sortedExcess x (otherWideCoordinates row 0).castSucc *
        fourWidePairSquare x row.castSucc (otherWideCoordinates row 0) +
      (sortedExcess x (otherWideCoordinates row 1).castSucc *
        fourWidePairSquare x row.castSucc (otherWideCoordinates row 1) +
       sortedExcess x (otherWideCoordinates row 2).castSucc *
        fourWidePairSquare x row.castSucc (otherWideCoordinates row 2))
  simpa only [add_assoc] using hw

theorem original_wide_row_lower (x : Configuration) (hx : UnitEquilateral x)
    (hCard : (wideCoordinates (actualExtrema x)).card = 4)
    (hMatching : IsMatching (actualExtrema x)) (row : Fin 4) :
    wideRowCoefficient x row ≤ rowCrossEnergy x (sortedCoordinates x row.castSucc) := by
  let p := sortedCoordinates x
  let u := rowVector x p row.castSucc
  have hu : (∑ i, u i) = 0 := by
    change (∑ i, transport (columnOrders x (p row.castSucc)) Profiles.shiftedVector i) = 0
    rw [sum_transport, Profiles.sum_shiftedVector_zero]
  have hPoint (i : Fin 3) :
      sortedExcess x (otherWideCoordinates row i).castSucc *
          fourWidePairSquare x row.castSucc (otherWideCoordinates row i) ≤
        columnEnergy x (columnOrders x) (p (otherWideCoordinates row i).castSucc) u :=
    actual_wide_outer_energy_lower x hx _
      (sorted_first_four_wide x hCard (otherWideCoordinates row i)) u hu
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hPoint i)
  have hn : 0 ≤ columnEnergy x (columnOrders x) (p 4) u :=
    scalarEnergy_nonneg _ _ (columnOrders_monotone x (p 4)) u
  have hCross : (∑ i : Fin 3,
      columnEnergy x (columnOrders x) (p (otherWideCoordinates row i).castSucc) u) ≤
      rowCrossEnergy x (p row.castSucc) := by
    change _ ≤ ∑ k ∈ Finset.univ.erase (p row.castSucc),
      columnEnergy x (columnOrders x) k u
    rw [← sum_erase_perm p row.castSucc, ← sum_otherCoordinates row.castSucc]
    simp_rw [otherWideCoordinates_cast]
    simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    change
      columnEnergy x (columnOrders x) (p (otherCoordinates row.castSucc 0)) u +
        (columnEnergy x (columnOrders x) (p (otherCoordinates row.castSucc 1)) u +
         columnEnergy x (columnOrders x) (p (otherCoordinates row.castSucc 2)) u) ≤
      columnEnergy x (columnOrders x) (p (otherCoordinates row.castSucc 0)) u +
        (columnEnergy x (columnOrders x) (p (otherCoordinates row.castSucc 1)) u +
         (columnEnergy x (columnOrders x) (p (otherCoordinates row.castSucc 2)) u +
          columnEnergy x (columnOrders x) (p (otherCoordinates row.castSucc 3)) u))
    rw [otherCoordinates_last]
    linarith
  exact le_trans (wide_row_position_lower x hCard hMatching row) (le_trans hs hCross)

def lastEndpointPositions (x : Configuration) (i : Fin 8) : Label :=
  (columnOrders x (sortedCoordinates x 4)).symm (fourEndpointLabel x (pairedSlot i))

theorem lastEndpointPositions_injective (x : Configuration)
    (hCard : (wideCoordinates (actualExtrema x)).card = 4)
    (hMatching : IsMatching (actualExtrema x)) :
    Function.Injective (lastEndpointPositions x) := by
  intro i j hij
  exact pairedSlot_injective (fourEndpointLabel_injective x hCard hMatching
    ((columnOrders x (sortedCoordinates x 4)).symm.injective hij))

def lastRowCoefficient (x : Configuration) : ℝ :=
  MatchingArithmetic.c1 * sortedExcess x 0 + MatchingArithmetic.c2 * sortedExcess x 1 +
    MatchingArithmetic.c3 * sortedExcess x 2 + MatchingArithmetic.c4 * sortedExcess x 3

theorem last_row_position_lower (x : Configuration)
    (hCard : (wideCoordinates (actualExtrema x)).card = 4)
    (hMatching : IsMatching (actualExtrema x)) :
    lastRowCoefficient x ≤ ∑ i : Fin 4,
      sortedExcess x i.castSucc * fourWidePairSquare x 4 i := by
  let f := lastEndpointPositions x
  have hw := weighted_eight_positions f (lastEndpointPositions_injective x hCard hMatching)
    (sortedExcess x 0) (sortedExcess x 1) (sortedExcess x 2) (sortedExcess x 3)
    (sortedExcess_antitone x (by decide : (0 : Coordinate) ≤ 1))
    (sortedExcess_antitone x (by decide : (1 : Coordinate) ≤ 2))
    (sortedExcess_antitone x (by decide : (2 : Coordinate) ≤ 3))
    (le_of_lt (sorted_first_four_positive x hCard 3))
  have he (i : Fin 8) : squaredPosition (f i) =
      rowVector x (sortedCoordinates x) 4 (fourEndpointLabel x (pairedSlot i)) ^ 2 := by
    rw [← shiftedVector_sq_eq_position]
    rfl
  simp_rw [he] at hw
  change lastRowCoefficient x ≤
    sortedExcess x 0 * fourWidePairSquare x 4 0 +
      sortedExcess x 1 * fourWidePairSquare x 4 1 +
      sortedExcess x 2 * fourWidePairSquare x 4 2 +
      sortedExcess x 3 * fourWidePairSquare x 4 3 at hw
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change lastRowCoefficient x ≤
    sortedExcess x 0 * fourWidePairSquare x 4 0 +
      (sortedExcess x 1 * fourWidePairSquare x 4 1 +
       (sortedExcess x 2 * fourWidePairSquare x 4 2 +
        sortedExcess x 3 * fourWidePairSquare x 4 3))
  simpa only [add_assoc] using hw

theorem original_last_row_lower (x : Configuration) (hx : UnitEquilateral x)
    (hCard : (wideCoordinates (actualExtrema x)).card = 4)
    (hMatching : IsMatching (actualExtrema x)) :
    lastRowCoefficient x ≤ rowCrossEnergy x (sortedCoordinates x 4) := by
  let p := sortedCoordinates x
  let u := rowVector x p 4
  have hu : (∑ i, u i) = 0 := by
    change (∑ i, transport (columnOrders x (p 4)) Profiles.shiftedVector i) = 0
    rw [sum_transport, Profiles.sum_shiftedVector_zero]
  have hPoint (i : Fin 4) : sortedExcess x i.castSucc * fourWidePairSquare x 4 i ≤
      columnEnergy x (columnOrders x) (p i.castSucc) u :=
    actual_wide_outer_energy_lower x hx _ (sorted_first_four_wide x hCard i) u hu
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => hPoint i)
  have he : (∑ i : Fin 4, columnEnergy x (columnOrders x) (p i.castSucc) u) =
      rowCrossEnergy x (p 4) := by
    change _ = ∑ k ∈ Finset.univ.erase (p 4), columnEnergy x (columnOrders x) k u
    rw [← sum_erase_perm p 4, ← sum_otherCoordinates 4]
    simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero] <;> rfl
  rw [he] at hs
  exact le_trans (last_row_position_lower x hCard hMatching) hs

def fourRowCoefficient (x : Configuration) : Coordinate → ℝ :=
  ![wideRowCoefficient x 0, wideRowCoefficient x 1, wideRowCoefficient x 2,
    wideRowCoefficient x 3, lastRowCoefficient x]

theorem sum_fourRowCoefficient (x : Configuration) :
    (∑ row, fourRowCoefficient x row) =
      MatchingArithmetic.b1 * sortedExcess x 0 + MatchingArithmetic.b2 * sortedExcess x 1 +
        MatchingArithmetic.b3 * sortedExcess x 2 + MatchingArithmetic.b4 * sortedExcess x 3 := by
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change
    (MatchingArithmetic.c1 * sortedExcess x 1 + MatchingArithmetic.c2 * sortedExcess x 2 +
      MatchingArithmetic.c3 * sortedExcess x 3) +
    ((MatchingArithmetic.c1 * sortedExcess x 0 + MatchingArithmetic.c2 * sortedExcess x 2 +
      MatchingArithmetic.c3 * sortedExcess x 3) +
    ((MatchingArithmetic.c1 * sortedExcess x 0 + MatchingArithmetic.c2 * sortedExcess x 1 +
      MatchingArithmetic.c3 * sortedExcess x 3) +
    ((MatchingArithmetic.c1 * sortedExcess x 0 + MatchingArithmetic.c2 * sortedExcess x 1 +
      MatchingArithmetic.c3 * sortedExcess x 2) +
     (MatchingArithmetic.c1 * sortedExcess x 0 + MatchingArithmetic.c2 * sortedExcess x 1 +
      MatchingArithmetic.c3 * sortedExcess x 2 + MatchingArithmetic.c4 * sortedExcess x 3)))) =
      MatchingArithmetic.b1 * sortedExcess x 0 + MatchingArithmetic.b2 * sortedExcess x 1 +
        MatchingArithmetic.b3 * sortedExcess x 2 + MatchingArithmetic.b4 * sortedExcess x 3
  dsimp [MatchingArithmetic.b1, MatchingArithmetic.b2, MatchingArithmetic.b3,
    MatchingArithmetic.b4]
  ring

theorem original_four_matching_energy_lower (x : Configuration) (hx : UnitEquilateral x)
    (hCard : (wideCoordinates (actualExtrema x)).card = 4)
    (hMatching : IsMatching (actualExtrema x)) :
    MatchingArithmetic.b1 * sortedExcess x 0 + MatchingArithmetic.b2 * sortedExcess x 1 +
      MatchingArithmetic.b3 * sortedExcess x 2 + MatchingArithmetic.b4 * sortedExcess x 3 ≤
        crossEnergy x (columnOrders x) Profiles.shiftedVector := by
  have hRow (row : Coordinate) :
      fourRowCoefficient x row ≤ rowCrossEnergy x (sortedCoordinates x row) := by
    fin_cases row
    · exact original_wide_row_lower x hx hCard hMatching 0
    · exact original_wide_row_lower x hx hCard hMatching 1
    · exact original_wide_row_lower x hx hCard hMatching 2
    · exact original_wide_row_lower x hx hCard hMatching 3
    · exact original_last_row_lower x hx hCard hMatching
  have hs := Finset.sum_le_sum (fun row (_ : row ∈ (Finset.univ : Finset Coordinate)) => hRow row)
  rw [sum_fourRowCoefficient, sum_perm (sortedCoordinates x)] at hs
  exact hs

theorem wideExcess_eq_first_four (x : Configuration)
    (hCard : (wideCoordinates (actualExtrema x)).card = 4) :
    Profiles.wideExcess x = sortedExcess x 0 + sortedExcess x 1 +
      sortedExcess x 2 + sortedExcess x 3 := by
  classical
  rw [← actual_wide_excess_eq]
  have he : (∑ k ∈ wideCoordinates (actualExtrema x), excess (actualExtrema x) k) =
      ∑ k, if IsWide (actualExtrema x) k then excess (actualExtrema x) k else 0 := by
    simp [wideCoordinates, Finset.sum_filter]
  rw [he, ← sum_perm (sortedCoordinates x)]
  have h0 := sorted_first_four_wide x hCard 0
  have h1 := sorted_first_four_wide x hCard 1
  have h2 := sorted_first_four_wide x hCard 2
  have h3 := sorted_first_four_wide x hCard 3
  have h4 := sorted_last_nonwide x hCard
  change IsWide (actualExtrema x) (sortedCoordinates x 0) at h0
  change IsWide (actualExtrema x) (sortedCoordinates x 1) at h1
  change IsWide (actualExtrema x) (sortedCoordinates x 2) at h2
  change IsWide (actualExtrema x) (sortedCoordinates x 3) at h3
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change
    (if IsWide (actualExtrema x) (sortedCoordinates x 0) then
      excess (actualExtrema x) (sortedCoordinates x 0) else 0) +
    ((if IsWide (actualExtrema x) (sortedCoordinates x 1) then
      excess (actualExtrema x) (sortedCoordinates x 1) else 0) +
    ((if IsWide (actualExtrema x) (sortedCoordinates x 2) then
      excess (actualExtrema x) (sortedCoordinates x 2) else 0) +
    ((if IsWide (actualExtrema x) (sortedCoordinates x 3) then
      excess (actualExtrema x) (sortedCoordinates x 3) else 0) +
     (if IsWide (actualExtrema x) (sortedCoordinates x 4) then
      excess (actualExtrema x) (sortedCoordinates x 4) else 0)))) =
      excess (actualExtrema x) (sortedCoordinates x 0) +
      excess (actualExtrema x) (sortedCoordinates x 1) +
      excess (actualExtrema x) (sortedCoordinates x 2) +
      excess (actualExtrema x) (sortedCoordinates x 3)
  rw [if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_neg h4]
  ring

theorem no_four_matching (x : Configuration) (hx : UnitEquilateral x)
    (hCard : (wideCoordinates (actualExtrema x)).card = 4)
    (hNonisolated : (nonisolatedCoordinates (actualExtrema x)).card = 0) : False := by
  have hMatching := matching_of_no_nonisolated (actualExtrema x) hNonisolated
  have hSupport : (endpointSupport (actualExtrema x)
      (wideCoordinates (actualExtrema x))).card ≤ 8 := by
    have h := endpointSupport_card_le_twice (actualExtrema x) (wideCoordinates (actualExtrema x))
    rw [hCard] at h
    norm_num at h
    exact h
  obtain ⟨q, hq, hCore⟩ := three_core_labels_of_support_le_eight (actualExtrema x) hSupport
  have hH := three_core_labels_force_excess_le_one x hx q hq hCore
  rw [wideExcess_eq_first_four x hCard] at hH
  have hEq := original_five_matching_deficit x hx
  have hLast := sorted_last_excess_nonpos x hCard
  have hUpper : crossEnergy x (columnOrders x) Profiles.shiftedVector ≤
      5 * MatchingArithmetic.alpha - 15 / 4 +
        (sortedExcess x 0 + sortedExcess x 1 + sortedExcess x 2 + sortedExcess x 3) / 2 := by
    simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hEq
    change crossEnergy x (columnOrders x) Profiles.shiftedVector =
      5 * MatchingArithmetic.alpha - 15 / 4 +
        (sortedExcess x 0 + (sortedExcess x 1 + (sortedExcess x 2 +
          (sortedExcess x 3 + sortedExcess x 4)))) / 2 at hEq
    linarith
  exact MatchingArithmetic.four_matching_contradiction
    (sortedExcess x 0) (sortedExcess x 1) (sortedExcess x 2) (sortedExcess x 3)
    (crossEnergy x (columnOrders x) Profiles.shiftedVector)
    (sortedExcess_le_third x hx 0) (sortedExcess_le_third x hx 1)
    (le_of_lt (sorted_first_four_positive x hCard 3)) hH
    (original_four_matching_energy_lower x hx hCard hMatching) hUpper

end
end Kusner5.FourMatchingAssembly
