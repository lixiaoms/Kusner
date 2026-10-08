import Kusner5.Exclusions
import Kusner5.FourMatchingAssembly
import Kusner5.PathAssembly
import Kusner5.QuartetLowerBound
import Kusner5.Cardinality
import Kusner5.LowerWitness

/-!
Full five-dimensional assembly for the original sum-of-absolute-values
distance. Every branch is supplied by a proved original-equations bridge.
Positive-distance normalization, finite and infinite set cardinalities, and
the explicit ten-point witness are included in the public conclusion.
-/
namespace Kusner5

open scoped BigOperators

noncomputable section

/-- Eleven arbitrary original real points in five physical coordinates
cannot have unit Manhattan distance for every distinct pair. -/
theorem no_eleven_unit (x : Configuration) : ¬ UnitEquilateral x := by
  intro hx
  rcases ForestMatching.original_exhaustive_counts x hx with h42 | h44 | h52 | h53 | h55
  · exact ForestMatching.no_four_wide_two_isolated x hx h42.1 h42.2.1 h42.2.2
  · exact FourMatchingAssembly.no_four_matching x hx h44.1 h44.2.2
  · exact ForestMatching.no_five_wide_two_isolated x hx h52.1 h52.2.1 h52.2.2
  · exact PathAssembly.no_five_wide_three_isolated x hx h53.1 h53.2.1 h53.2.2
  · exact MatchingAssembly.no_five_matching_of_quartet_bound x hx h55.1 h55.2.2
      (fun q hq => original_quartet_width_ge_thirty_seven_twenty_fourths x hx q hq)

/-- Fully expanded original input: all distinct label pairs, including all
55 unordered pairs, and the literal five-coordinate real Manhattan sum. -/
theorem no_eleven_unit_explicit (x : Fin 11 → Fin 5 → ℝ) :
    ¬ (∀ i j : Fin 11, i ≠ j → (∑ k : Fin 5, |x i k - x j k|) = 1) :=
  no_eleven_unit x

theorem no_eleven_positive_distance (x : Configuration) {δ : ℝ} (hδ : 0 < δ) :
    ¬ Equilateral x δ := by
  intro hx
  exact no_eleven_unit (fun i => scaled δ⁻¹ (x i)) (normalize_equilateral hδ hx)

theorem finite_equilateral_card_le_ten (s : Finset (Point 5)) {δ : ℝ}
    (hδ : 0 < δ) (hEq : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → l1dist p q = δ) :
    s.card ≤ 10 :=
  CardinalityLifting.finite_equilateral_card_le_of_no_eleven no_eleven_unit s hδ hEq

/-- The bound holds for every set, without assuming finiteness. The proof
returns its finiteness together with the finite cardinal bound. -/
theorem equilateral_set_finite_card_le_ten (S : Set (Point 5)) {δ : ℝ}
    (hδ : 0 < δ) (hEq : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → l1dist p q = δ) :
    ∃ hS : S.Finite, hS.toFinset.card ≤ 10 :=
  CardinalityLifting.equilateral_set_finite_card_le_of_no_eleven no_eleven_unit S hδ hEq

theorem equilateral_array_card_le_ten {n : ℕ} (x : Fin n → Point 5) {δ : ℝ}
    (hδ : 0 < δ) (hEq : Equilateral x δ) : n ≤ 10 := by
  classical
  have hn := unitEquilateral_injective (normalize_equilateral hδ hEq)
  have hx : Function.Injective x := by
    intro i j hij
    exact hn (congrArg (scaled δ⁻¹) hij)
  let s := Finset.univ.image x
  have hs : s.card = n := by
    change (Finset.univ.image x).card = n
    rw [Finset.card_image_of_injective _ hx]
    simp only [Finset.card_univ, Fintype.card_fin]
  have hbound := finite_equilateral_card_le_ten s hδ (by
    intro p hp q hq hpq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    exact hEq i j (fun h => hpq (congrArg x h)))
  rw [hs] at hbound
  exact hbound

/-- The explicit witness is exactly the ten points ±e_k/2. -/
theorem exists_equilateral_ten :
    ∃ s : Finset (Point 5), s.card = 10 ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → l1dist p q = 1) := by
  classical
  let s := Finset.univ.image tenPoint
  refine ⟨s, ?_, ?_⟩
  · change (Finset.univ.image tenPoint).card = 10
    rw [Finset.card_image_of_injective _ tenPoint_injective]
    simp only [Finset.card_univ, Fintype.card_fin]
  · intro p hp q hq hpq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    exact tenPoint_unit_equilateral i j (fun h => hpq (congrArg tenPoint h))

/-- Exact maximum cardinality ten in the original real l1^5 metric: the
upper clause ranges over arbitrary sets and arbitrary positive distances,
and the lower clause supplies a ten-point unit-equilateral witness. -/
theorem kusner_five_exact :
    (∀ (S : Set (Point 5)) (δ : ℝ), 0 < δ →
      (∀ p ∈ S, ∀ q ∈ S, p ≠ q → l1dist p q = δ) →
        ∃ hS : S.Finite, hS.toFinset.card ≤ 10) ∧
    (∃ s : Finset (Point 5), s.card = 10 ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → l1dist p q = 1)) :=
  ⟨fun S _ hδ hEq => equilateral_set_finite_card_le_ten S hδ hEq,
    exists_equilateral_ten⟩

end
end Kusner5
