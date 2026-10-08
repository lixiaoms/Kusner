import Kusner5.Main

/-!
Independent type/trust inspection for the selected original theorem.
This file proves only direct type assignments to the completed public
declarations and prints their real transitive axiom dependencies.
It is not a replacement for any mathematical bridge or independent rebuild.
-/

open scoped BigOperators
set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs false

#print Kusner5.l1dist
#print Kusner5.Equilateral
#print Kusner5.UnitEquilateral
#print Kusner5.tenPoint
#print Kusner5.Point
#print Kusner5.Configuration
#print Kusner5.quartetWidth
#print Kusner5.crossEnergy
#print Kusner5.Profiles.wideExcess

namespace Kusner5.Audit
noncomputable section

example (x : Fin 11 → Fin 5 → ℝ)
    (h : ∀ i j : Fin 11, i ≠ j →
      (∑ k : Fin 5, |x i k - x j k|) = 1) : False :=
  Kusner5.no_eleven_unit x h

example (s : Finset (Fin 5 → ℝ)) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ p ∈ s, ∀ q ∈ s, p ≠ q →
      (∑ k : Fin 5, |p k - q k|) = δ) : s.card ≤ 10 :=
  Kusner5.finite_equilateral_card_le_ten s hδ h

example (S : Set (Fin 5 → ℝ)) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
      (∑ k : Fin 5, |p k - q k|) = δ) :
    ∃ hS : S.Finite, hS.toFinset.card ≤ 10 :=
  Kusner5.equilateral_set_finite_card_le_ten S hδ h

example : ∃ s : Finset (Fin 5 → ℝ), s.card = 10 ∧
    (∀ p ∈ s, ∀ q ∈ s, p ≠ q →
      (∑ k : Fin 5, |p k - q k|) = 1) :=
  Kusner5.exists_equilateral_ten

end
end Kusner5.Audit

#check @Kusner5.no_eleven_unit
#print axioms Kusner5.no_eleven_unit
#check @Kusner5.no_eleven_unit_explicit
#print axioms Kusner5.no_eleven_unit_explicit
#check @Kusner5.no_eleven_positive_distance
#print axioms Kusner5.no_eleven_positive_distance
#check @Kusner5.equilateral_array_card_le_ten
#print axioms Kusner5.equilateral_array_card_le_ten
#check @Kusner5.kusner_five_exact
#print axioms Kusner5.kusner_five_exact
#check @Kusner5.finite_equilateral_card_le_ten
#print axioms Kusner5.finite_equilateral_card_le_ten
#check @Kusner5.equilateral_set_finite_card_le_ten
#print axioms Kusner5.equilateral_set_finite_card_le_ten
#check @Kusner5.exists_equilateral_ten
#print axioms Kusner5.exists_equilateral_ten
#check @Kusner5.tenPoint_unit_equilateral
#print axioms Kusner5.tenPoint_unit_equilateral
#check @Kusner5.tenPoint_injective
#print axioms Kusner5.tenPoint_injective
#check @Kusner5.unit_equilateral_actual_totalEnergy
#print axioms Kusner5.unit_equilateral_actual_totalEnergy
#check @Kusner5.unit_equilateral_five_totalTrace
#print axioms Kusner5.unit_equilateral_five_totalTrace
#check @Kusner5.actual_coordinate_range_le_five_sixths
#print axioms Kusner5.actual_coordinate_range_le_five_sixths
#check @Kusner5.Profiles.at_least_four_wide
#print axioms Kusner5.Profiles.at_least_four_wide
#check @Kusner5.Profiles.shifted_crossEnergy
#print axioms Kusner5.Profiles.shifted_crossEnergy
#check @Kusner5.ForestMatching.original_at_least_two_isolated
#print axioms Kusner5.ForestMatching.original_at_least_two_isolated
#check @Kusner5.ForestMatching.original_exhaustive_counts
#print axioms Kusner5.ForestMatching.original_exhaustive_counts
#check @Kusner5.ForestMatching.no_four_wide_two_isolated
#print axioms Kusner5.ForestMatching.no_four_wide_two_isolated
#check @Kusner5.ForestMatching.no_five_wide_two_isolated
#print axioms Kusner5.ForestMatching.no_five_wide_two_isolated
#check @Kusner5.FourMatchingAssembly.no_four_matching
#print axioms Kusner5.FourMatchingAssembly.no_four_matching
#check @Kusner5.PathAssembly.no_five_wide_three_isolated
#print axioms Kusner5.PathAssembly.no_five_wide_three_isolated
#check @Kusner5.MatchingAssembly.original_five_matching_energy_lower
#print axioms Kusner5.MatchingAssembly.original_five_matching_energy_lower
#check @Kusner5.MatchingAssembly.matching_original_slack
#print axioms Kusner5.MatchingAssembly.matching_original_slack
#check @Kusner5.MatchingAssembly.no_five_matching_of_quartet_bound
#print axioms Kusner5.MatchingAssembly.no_five_matching_of_quartet_bound
#check @Kusner5.quartet_equal_cut_totals
#print axioms Kusner5.quartet_equal_cut_totals
#check @Kusner5.quartet_original_cooccurrence
#print axioms Kusner5.quartet_original_cooccurrence
#check @Kusner5.quartet_original_cross_equation
#print axioms Kusner5.quartet_original_cross_equation
#check @Kusner5.exists_original_quartet_projection
#print axioms Kusner5.exists_original_quartet_projection
#check @Kusner5.exists_original_quartet_face_projection
#print axioms Kusner5.exists_original_quartet_face_projection
#check @Kusner5.original_quartet_positive_slot_classification
#print axioms Kusner5.original_quartet_positive_slot_classification
#check @Kusner5.original_projected_seven_cycle_lower
#print axioms Kusner5.original_projected_seven_cycle_lower
#check @Kusner5.exists_original_113_section_tour
#print axioms Kusner5.exists_original_113_section_tour
#check @Kusner5.exists_original_122_section_tour
#print axioms Kusner5.exists_original_122_section_tour
#check @Kusner5.QuartetGeometry.seven_cycle_of_closed_path
#print axioms Kusner5.QuartetGeometry.seven_cycle_of_closed_path
#check @Kusner5.QuartetGeometry.exists_plane_box_tour
#print axioms Kusner5.QuartetGeometry.exists_plane_box_tour
#check @Kusner5.original_quartet_singleton_ge_one_twenty_fourth
#print axioms Kusner5.original_quartet_singleton_ge_one_twenty_fourth
#check @Kusner5.original_quartet_width_ge_thirty_seven_twenty_fourths
#print axioms Kusner5.original_quartet_width_ge_thirty_seven_twenty_fourths
#check @Kusner5.normalize_equilateral
#print axioms Kusner5.normalize_equilateral
#check @Kusner5.Profiles.root_crossEnergy
#print axioms Kusner5.Profiles.root_crossEnergy
#check @Kusner5.Profiles.modified_row_slack
#print axioms Kusner5.Profiles.modified_row_slack
#check @Kusner5.ForestMatching.original_root_nonisolated_lower
#print axioms Kusner5.ForestMatching.original_root_nonisolated_lower
#check @Kusner5.ForestMatching.original_isolated_mass_gt
#print axioms Kusner5.ForestMatching.original_isolated_mass_gt
#check @Kusner5.ForestMatching.three_core_labels_force_excess_le_one
#print axioms Kusner5.ForestMatching.three_core_labels_force_excess_le_one
#check @Kusner5.ForestMatching.actual_wide_excess_eq
#print axioms Kusner5.ForestMatching.actual_wide_excess_eq
#check @Kusner5.PathAssembly.exists_path_coordinates
#print axioms Kusner5.PathAssembly.exists_path_coordinates
#check @Kusner5.PathAssembly.exists_path_labels
#print axioms Kusner5.PathAssembly.exists_path_labels
#check @Kusner5.PathAssembly.original_path_small_lower
#print axioms Kusner5.PathAssembly.original_path_small_lower
#check @Kusner5.PathAssembly.original_path_large_lower
#print axioms Kusner5.PathAssembly.original_path_large_lower

