import Kusner5.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
Standard quantifier and scaling lifting. The explicit exclusion argument below
is an INTERMEDIATE input. Main must supply it from the fully proved original
geometry; this conditional module is not an upper-bound completion.
-/
namespace Kusner5.CardinalityLifting

noncomputable section

theorem finite_equilateral_card_le_of_no_eleven
    (hno : ∀ x : Configuration, ¬ UnitEquilateral x)
    (s : Finset (Point 5)) {δ : ℝ} (hδ : 0 < δ)
    (hEq : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → l1dist p q = δ) :
    s.card ≤ 10 := by
  classical
  by_contra hc
  have h11 : 11 ≤ s.card := by omega
  obtain ⟨f, hf, hmem⟩ := exists_fin_injection_into_finset s 11 h11
  have he : Equilateral f δ := by
    intro i j hij
    exact hEq (f i) (hmem i) (f j) (hmem j) (fun h => hij (hf h))
  exact hno (fun i => scaled δ⁻¹ (f i)) (normalize_equilateral hδ he)

theorem equilateral_set_finite_of_no_eleven
    (hno : ∀ x : Configuration, ¬ UnitEquilateral x)
    (S : Set (Point 5)) {δ : ℝ} (hδ : 0 < δ)
    (hEq : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → l1dist p q = δ) :
    S.Finite := by
  classical
  by_contra hinf
  have hs : S.Infinite := hinf
  obtain ⟨s, hsub, hcard⟩ := hs.exists_subset_card_eq 11
  have hbound := finite_equilateral_card_le_of_no_eleven hno s hδ
    (fun p hp q hq hne => hEq p (hsub hp) q (hsub hq) hne)
  omega

theorem equilateral_set_finite_card_le_of_no_eleven
    (hno : ∀ x : Configuration, ¬ UnitEquilateral x)
    (S : Set (Point 5)) {δ : ℝ} (hδ : 0 < δ)
    (hEq : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → l1dist p q = δ) :
    ∃ hS : S.Finite, hS.toFinset.card ≤ 10 := by
  classical
  let hS := equilateral_set_finite_of_no_eleven hno S hδ hEq
  refine ⟨hS, ?_⟩
  apply finite_equilateral_card_le_of_no_eleven hno hS.toFinset hδ
  intro p hp q hq hne
  exact hEq p (hS.mem_toFinset.mp hp) q (hS.mem_toFinset.mp hq) hne

end
end Kusner5.CardinalityLifting

