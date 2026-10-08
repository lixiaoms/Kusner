import Kusner5.ForestMatching

/-!
Original-label exclusion of the two two-isolated wide-forest shapes.

Every theorem below takes only `UnitEquilateral x` (and the exhaustive count
case) at public scope. The shifted cross-energy identity, the shifted
shared-endpoint outer-cut bound, the physical range cap and the actual
isolated/nonisolated ledger are combined exactly as in the paper argument.
The three remaining forest shapes and the final matching are separate
obligations tracked in the review ledger.
-/

namespace Kusner5.ForestMatching

open scoped BigOperators
open Profiles MatchingArithmetic

noncomputable section

/-- Shifted-profile copy of `root_shared_endpoint_lower`: when a wide column
shares an endpoint with the wide row column, that endpoint's genuine outer cut
mass enters the directed energy with the shifted endpoint square `s1`. -/
theorem shifted_shared_endpoint_lower (x : Configuration) (hx : UnitEquilateral x)
    (row col : Coordinate) (hrow : IsWide (actualExtrema x) row)
    (hcol : IsWide (actualExtrema x) col)
    (hshare : ShareEndpoint (actualExtrema x) row col) :
    s1 * excess (actualExtrema x) col ≤
      columnEnergy x (columnOrders x) col
        (transport (columnOrders x row) shiftedVector) := by
  obtain ⟨i, hirow, hicol⟩ := hshare
  have hsq := shifted_actual_endpoint_sq x row i hirow
  have hlower := actual_wide_outer_energy_lower x hx col hcol
    (transport (columnOrders x row) shiftedVector)
    (by rw [sum_transport, sum_shiftedVector_zero])
  have ht := le_of_lt (excess_pos (actualExtrema x) col hcol)
  rcases hicol with hlo | hhi
  · rw [hlo] at hsq
    rw [hsq] at hlower
    have hother := mul_nonneg ht
      (sq_nonneg (transport (columnOrders x row) shiftedVector
        (actualExtrema x col).hi))
    nlinarith
  · rw [hhi] at hsq
    rw [hsq] at hlower
    have hother := mul_nonneg ht
      (sq_nonneg (transport (columnOrders x row) shiftedVector
        (actualExtrema x col).lo))
    nlinarith

/-- Shifted-profile copy of `original_root_nonisolated_lower`: one chosen
neighboring row per nonisolated column injects into the directed ledger, so
the total nonisolated excess is paid with the shifted endpoint square. -/
theorem original_shifted_nonisolated_lower (x : Configuration)
    (hx : UnitEquilateral x) :
    s1 * (∑ k ∈ nonisolatedCoordinates (actualExtrema x),
      excess (actualExtrema x) k) ≤
      crossEnergy x (columnOrders x) shiftedVector := by
  classical
  let N := nonisolatedCoordinates (actualExtrema x)
  let I := {k : Coordinate // k ∈ N}
  have hneighbors (k : I) :
      ∃ l ∈ N, l ≠ k.val ∧ ShareEndpoint (actualExtrema x) k.val l :=
    nonisolated_has_nonisolated_neighbor (actualExtrema x) k.val k.property
  choose neighbor hneighbor_mem hneighbor_ne hneighbor_share using hneighbors
  let pair : I → Coordinate × Coordinate := fun k => (neighbor k, k.val)
  have hpair : Function.Injective pair := by
    intro i j hij
    apply Subtype.ext
    exact congrArg Prod.snd hij
  have hterm (k : I) : s1 * excess (actualExtrema x) k.val ≤
      directedEnergy x shiftedVector (pair k) := by
    have hwidek := ((mem_nonisolatedCoordinates (actualExtrema x) k.val).mp
      k.property).1
    have hwider := ((mem_nonisolatedCoordinates (actualExtrema x) (neighbor k)).mp
      (hneighbor_mem k)).1
    have h := shifted_shared_endpoint_lower x hx (neighbor k) k.val hwider hwidek
      (shareEndpoint_symm (hneighbor_share k))
    simpa [directedEnergy, pair, Ne.symm (hneighbor_ne k)] using h
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset I)) => hterm k)
  have hsub := sum_comp_le_sum_of_injective pair hpair
    (directedEnergy x shiftedVector) (directedEnergy_nonneg x shiftedVector)
  rw [← Finset.mul_sum, sum_subtype_finset] at hsum
  rw [sum_directedEnergy] at hsub
  exact le_trans hsum hsub

/-- The actual wide excess splits into its nonisolated and isolated parts. -/
theorem wide_excess_split (x : Configuration) :
    Profiles.wideExcess x =
      (∑ k ∈ nonisolatedCoordinates (actualExtrema x),
        excess (actualExtrema x) k) +
        ∑ k ∈ isolatedCoordinates (actualExtrema x),
          excess (actualExtrema x) k := by
  rw [← actual_wide_excess_eq, wideCoordinates_partition,
    Finset.sum_union (isolated_nonisolated_disjoint (actualExtrema x))]
  ring

/-- Two isolated wide columns carry at most two thirds of excess. -/
theorem isolated_sum_le_of_card (x : Configuration) (hx : UnitEquilateral x)
    (hcard : (isolatedCoordinates (actualExtrema x)).card = 2) :
    (∑ k ∈ isolatedCoordinates (actualExtrema x),
      excess (actualExtrema x) k) ≤ 2 / 3 := by
  classical
  have hcap : ∀ k ∈ isolatedCoordinates (actualExtrema x),
      excess (actualExtrema x) k ≤ 1 / 3 :=
    fun k _ => original_excess_le_third x hx k
  calc (∑ k ∈ isolatedCoordinates (actualExtrema x),
        excess (actualExtrema x) k)
      ≤ ∑ _k ∈ isolatedCoordinates (actualExtrema x), (1 / 3 : ℝ) :=
        Finset.sum_le_sum (fun k hk => hcap k hk)
    _ = ((isolatedCoordinates (actualExtrema x)).card : ℝ) * (1 / 3) := by
        simp
    _ = 2 / 3 := by rw [hcard]; norm_num

/-- Case (four wide, two isolated, two nonisolated): the directed path bound
and the range cap contradict the exact shifted deficit. -/
theorem no_four_wide_two_isolated (x : Configuration) (hx : UnitEquilateral x)
    (hc4 : (wideCoordinates (actualExtrema x)).card = 4)
    (hi2 : (isolatedCoordinates (actualExtrema x)).card = 2)
    (hn2 : (nonisolatedCoordinates (actualExtrema x)).card = 2) : False := by
  classical
  have hΔ : crossEnergy x (columnOrders x) shiftedVector =
      5 * shiftedAlpha + totalWidth x / 2 - 5 := shifted_crossEnergy x hx
  have hUp : crossEnergy x (columnOrders x) shiftedVector <
      totalWidth x / 2 - 5 / 3 := by
    linarith [hΔ, shiftedAlpha_lt_two_thirds]
  have hN : s1 * (∑ k ∈ nonisolatedCoordinates (actualExtrema x),
      excess (actualExtrema x) k) ≤
      crossEnergy x (columnOrders x) shiftedVector :=
    original_shifted_nonisolated_lower x hx
  have hiso : (∑ k ∈ isolatedCoordinates (actualExtrema x),
      excess (actualExtrema x) k) ≤ 2 / 3 := isolated_sum_le_of_card x hx hi2
  have hsplit := wide_excess_split x
  have hbase : totalWidth x ≤ 5 / 2 + Profiles.wideExcess x :=
    totalWidth_le_base_add_wideExcess x
  have hge : totalWidth x - 19 / 6 ≤
      ∑ k ∈ nonisolatedCoordinates (actualExtrema x),
        excess (actualExtrema x) k := by
    have h1 : Profiles.wideExcess x ≤
        (∑ k ∈ nonisolatedCoordinates (actualExtrema x),
          excess (actualExtrema x) k) + 2 / 3 := by linarith
    linarith
  have hLow : (9 / 22) * (totalWidth x - 19 / 6) ≤
      crossEnergy x (columnOrders x) shiftedVector := by
    have hs1 : s1 = 9 / 22 := by norm_num [Profiles.s1]
    calc (9 / 22) * (totalWidth x - 19 / 6)
        ≤ (9 / 22) * (∑ k ∈ nonisolatedCoordinates (actualExtrema x),
          excess (actualExtrema x) k) :=
          mul_le_mul_of_nonneg_left hge (by norm_num)
      _ = s1 * (∑ k ∈ nonisolatedCoordinates (actualExtrema x),
          excess (actualExtrema x) k) := by rw [hs1]
      _ ≤ crossEnergy x (columnOrders x) shiftedVector := hN
  have hWcap : totalWidth x ≤ 23 / 6 := by
    classical
    have hcapall : ∀ k : Coordinate,
        scalarRange (fun i => x i k) (columnOrders x k) ≤ 5 / 6 :=
      fun k => actual_coordinate_range_le_five_sixths x hx k
    have hnonwide : ∀ k : Coordinate, k ∉ wideCoordinates (actualExtrema x) →
        scalarRange (fun i => x i k) (columnOrders x k) ≤ 1 / 2 := by
      intro k hk
      by_contra hgt
      push_neg at hgt
      have hgt' : IsWide (actualExtrema x) k := hgt
      exact hk ((mem_wideCoordinates (actualExtrema x) k).mpr hgt')
    have hwideSum : (∑ k ∈ wideCoordinates (actualExtrema x),
        scalarRange (fun i => x i k) (columnOrders x k)) ≤
        ((wideCoordinates (actualExtrema x)).card : ℝ) * (5 / 6 : ℝ) := by
      have h1 : (∑ k ∈ wideCoordinates (actualExtrema x),
          scalarRange (fun i => x i k) (columnOrders x k)) ≤
          ∑ _k ∈ wideCoordinates (actualExtrema x), (5 / 6 : ℝ) :=
        Finset.sum_le_sum (fun k _ => hcapall k)
      rwa [Finset.sum_const, nsmul_eq_mul] at h1
    have hnonSum : (∑ k ∈ (wideCoordinates (actualExtrema x))ᶜ,
        scalarRange (fun i => x i k) (columnOrders x k)) ≤
        (((wideCoordinates (actualExtrema x))ᶜ).card : ℝ) * (1 / 2 : ℝ) := by
      have h1 : (∑ k ∈ (wideCoordinates (actualExtrema x))ᶜ,
          scalarRange (fun i => x i k) (columnOrders x k)) ≤
          ∑ _k ∈ (wideCoordinates (actualExtrema x))ᶜ, (1 / 2 : ℝ) :=
        Finset.sum_le_sum (fun k hk => hnonwide k (Finset.mem_compl.mp hk))
      rwa [Finset.sum_const, nsmul_eq_mul] at h1
    have hc1 : (((wideCoordinates (actualExtrema x))ᶜ).card : ℝ) = 1 := by
      have hc1Nat : ((wideCoordinates (actualExtrema x))ᶜ).card = 1 := by
        rw [Finset.card_compl, hc4]
        norm_num
      exact_mod_cast hc1Nat
    have hsplitW : totalWidth x =
        (∑ k ∈ wideCoordinates (actualExtrema x),
          scalarRange (fun i => x i k) (columnOrders x k)) +
        ∑ k ∈ (wideCoordinates (actualExtrema x))ᶜ,
          scalarRange (fun i => x i k) (columnOrders x k) := by
      show (∑ k, scalarRange (fun i => x i k) (columnOrders x k)) = _
      rw [Finset.sum_add_sum_compl]
    calc
      totalWidth x = _ := hsplitW
      _ ≤ ((wideCoordinates (actualExtrema x)).card : ℝ) * (5 / 6 : ℝ) +
          (((wideCoordinates (actualExtrema x))ᶜ).card : ℝ) * (1 / 2 : ℝ) :=
        add_le_add hwideSum hnonSum
      _ = 23 / 6 := by rw [hc4, hc1]; norm_num
  exact four_wide_path_contradiction (totalWidth x)
    (crossEnergy x (columnOrders x) shiftedVector) hWcap hLow hUp

/-- Case (five wide, two isolated, three nonisolated): the core-width bound
`H ≤ 1` and the same directed bound contradict the exact shifted deficit. -/
theorem no_five_wide_two_isolated (x : Configuration) (hx : UnitEquilateral x)
    (hc5 : (wideCoordinates (actualExtrema x)).card = 5)
    (hi2 : (isolatedCoordinates (actualExtrema x)).card = 2)
    (hn3 : (nonisolatedCoordinates (actualExtrema x)).card = 3) : False := by
  classical
  have hsup := two_isolated_three_nonisolated_support_le_eight
    (actualExtrema x) hi2 hn3
  obtain ⟨q, hq, hcore⟩ := three_core_labels_of_support_le_eight
    (actualExtrema x) hsup
  have hH : Profiles.wideExcess x ≤ 1 :=
    three_core_labels_force_excess_le_one x hx q hq (fun i => hcore i)
  have hΔ : crossEnergy x (columnOrders x) shiftedVector =
      5 * shiftedAlpha + totalWidth x / 2 - 5 := shifted_crossEnergy x hx
  have hbase : totalWidth x ≤ 5 / 2 + Profiles.wideExcess x :=
    totalWidth_le_base_add_wideExcess x
  have hUp : crossEnergy x (columnOrders x) shiftedVector <
      Profiles.wideExcess x / 2 - 5 / 12 := by
    linarith [hΔ, hbase, shiftedAlpha_lt_two_thirds]
  have hN : s1 * (∑ k ∈ nonisolatedCoordinates (actualExtrema x),
      excess (actualExtrema x) k) ≤
      crossEnergy x (columnOrders x) shiftedVector :=
    original_shifted_nonisolated_lower x hx
  have hiso : (∑ k ∈ isolatedCoordinates (actualExtrema x),
      excess (actualExtrema x) k) ≤ 2 / 3 := isolated_sum_le_of_card x hx hi2
  have hsplit := wide_excess_split x
  have hge : Profiles.wideExcess x - 2 / 3 ≤
      ∑ k ∈ nonisolatedCoordinates (actualExtrema x),
        excess (actualExtrema x) k := by linarith
  have hLow : (9 / 22) * (Profiles.wideExcess x - 2 / 3) ≤
      crossEnergy x (columnOrders x) shiftedVector := by
    have hs1 : s1 = 9 / 22 := by norm_num [Profiles.s1]
    calc (9 / 22) * (Profiles.wideExcess x - 2 / 3)
        ≤ (9 / 22) * (∑ k ∈ nonisolatedCoordinates (actualExtrema x),
          excess (actualExtrema x) k) :=
          mul_le_mul_of_nonneg_left hge (by norm_num)
      _ = s1 * (∑ k ∈ nonisolatedCoordinates (actualExtrema x),
          excess (actualExtrema x) k) := by rw [hs1]
      _ ≤ crossEnergy x (columnOrders x) shiftedVector := hN
  exact five_wide_two_isolated_contradiction (Profiles.wideExcess x)
    (crossEnergy x (columnOrders x) shiftedVector) hH hLow hUp

end
end Kusner5.ForestMatching
