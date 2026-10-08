import Kusner5.Exclusions
import Kusner5.MatchingAssembly

-- Actual development009 panicked in SimprocEntry.try. Disable only this
-- optional simplifier automation; every resulting proof is kernel checked.
set_option simprocs false

/-!
Actual three-isolated/two-edge-path assembly. The shared path label is one
original label, with one combined weight. Every row is transported through
the actual order of its original physical coordinate.
-/

namespace Kusner5.PathAssembly

open scoped BigOperators
open ForestMatching Profiles MatchingArithmetic

noncomputable section

private theorem enumerate_finset {α : Type*} [DecidableEq α]
    (S : Finset α) (n : ℕ) (hc : S.card = n) :
    ∃ e : Fin n → α, Function.Injective e ∧ Finset.univ.image e = S := by
  classical
  obtain ⟨e, he, hm⟩ := exists_fin_injection_into_finset S n (by rw [hc])
  have hsub : Finset.univ.image e ⊆ S := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    exact hm i
  have hle : S.card ≤ (Finset.univ.image e).card := by
    rw [hc, Finset.card_image_of_injective _ he]
    simp only [Finset.card_univ, Fintype.card_fin, le_refl]
  exact ⟨e, he, Finset.eq_of_subset_of_card_le hsub hle⟩

structure PathCoordinates (x : Configuration) where
  order : Equiv.Perm Coordinate
  isolated : ∀ i : Fin 3, IsIsolated (actualExtrema x) (order ⟨i.val, by omega⟩)
  share : ShareEndpoint (actualExtrema x) (order 3) (order 4)

/-- The actual count case supplies a permutation of physical coordinates
with the isolated edges first and the two genuine neighboring edges last. -/
theorem exists_path_coordinates (x : Configuration)
    (hWide : (ForestMatching.wideCoordinates (actualExtrema x)).card = 5)
    (hIso : (isolatedCoordinates (actualExtrema x)).card = 3)
    (hNon : (nonisolatedCoordinates (actualExtrema x)).card = 2) :
    Nonempty (PathCoordinates x) := by
  classical
  let E := actualExtrema x
  let I := isolatedCoordinates E
  let N := nonisolatedCoordinates E
  obtain ⟨a, ha, himagea⟩ := enumerate_finset I 3 hIso
  obtain ⟨b, hb, himageb⟩ := enumerate_finset N 2 hNon
  have hma (i : Fin 3) : a i ∈ I := by
    rw [← himagea]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hmb (i : Fin 2) : b i ∈ N := by
    rw [← himageb]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hcross (i : Fin 3) (j : Fin 2) : a i ≠ b j := by
    intro heq
    have hn : a i ∈ N := by rw [heq]; exact hmb j
    exact Finset.disjoint_left.mp (isolated_nonisolated_disjoint E) (hma i) hn
  let f : Coordinate → Coordinate := ![a 0, a 1, a 2, b 0, b 1]
  have hna (i j : Fin 3) (hij : i ≠ j) : a i ≠ a j := fun h => hij (ha h)
  have hnb (i j : Fin 2) (hij : i ≠ j) : b i ≠ b j := fun h => hij (hb h)
  have hcross' (i : Fin 3) (j : Fin 2) : b j ≠ a i := Ne.symm (hcross i j)
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | (have h := ha hij
         have hv := congrArg (fun t : Fin 3 => t.val) h
         norm_num at hv)
      | (have h := hb hij
         have hv := congrArg (fun t : Fin 2 => t.val) h
         norm_num at hv)
      | exact False.elim (hcross _ _ hij)
      | exact False.elim (hcross' _ _ hij)
  have hsurj : Function.Surjective f := by
    intro k
    have hk : k ∈ ForestMatching.wideCoordinates E :=
      (mem_wideCoordinates E k).mpr (all_wide_of_card_five E hWide k)
    rw [wideCoordinates_partition] at hk
    rcases Finset.mem_union.mp hk with hk | hk
    · change k ∈ I at hk
      rw [← himagea] at hk
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hk
      fin_cases i <;> dsimp only at hi
      · exact ⟨0, hi⟩
      · exact ⟨1, hi⟩
      · exact ⟨2, hi⟩
    · change k ∈ N at hk
      rw [← himageb] at hk
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hk
      fin_cases i <;> dsimp only at hi
      · exact ⟨3, hi⟩
      · exact ⟨4, hi⟩
  let p : Equiv.Perm Coordinate := Equiv.ofBijective f ⟨hf, hsurj⟩
  have hshare : ShareEndpoint E (b 0) (b 1) := by
    obtain ⟨k, hk, hkne, hs⟩ := nonisolated_has_nonisolated_neighbor E (b 0) (hmb 0)
    change k ∈ N at hk
    rw [← himageb] at hk
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hk
    fin_cases i <;> dsimp only at hi
    · exact False.elim (hkne hi.symm)
    · change b 1 = k at hi
      rw [← hi] at hs
      exact hs
  refine ⟨⟨p, ?_, hshare⟩⟩
  intro i
  fin_cases i <;> dsimp only [p, Equiv.ofBijective, f] <;>
    exact (mem_isolatedCoordinates E _).mp (hma _)

def pathExcess (x : Configuration) (p : Equiv.Perm Coordinate) (i : Coordinate) : ℝ :=
  excess (actualExtrema x) (p i)

def isolatedExcess (x : Configuration) (p : Equiv.Perm Coordinate) : ℝ :=
  pathExcess x p 0 + pathExcess x p 1 + pathExcess x p 2

def sharedExcess (x : Configuration) (p : Equiv.Perm Coordinate) : ℝ :=
  pathExcess x p 3 + pathExcess x p 4

structure PathLabels (x : Configuration) (p : Equiv.Perm Coordinate) where
  labels : Fin 3 → Label
  injective : Function.Injective labels
  first : IsEndpoint (actualExtrema x) (p 3) (labels 0)
  middleFirst : IsEndpoint (actualExtrema x) (p 3) (labels 1)
  middleLast : IsEndpoint (actualExtrema x) (p 4) (labels 1)
  last : IsEndpoint (actualExtrema x) (p 4) (labels 2)
  pairFirst : ∀ g : Label → ℝ,
    g (actualExtrema x (p 3)).lo + g (actualExtrema x (p 3)).hi =
      g (labels 0) + g (labels 1)
  pairLast : ∀ g : Label → ℝ,
    g (actualExtrema x (p 4)).lo + g (actualExtrema x (p 4)).hi =
      g (labels 1) + g (labels 2)

/-- The two actual neighboring wide edges share exactly one endpoint.
Their three vertices remain distinct original labels. -/
theorem exists_path_labels (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (P : PathCoordinates x) :
    Nonempty (PathLabels x P.order) := by
  classical
  let p := P.order
  let E := actualExtrema x
  obtain ⟨B, hB3, hB4⟩ := P.share
  obtain ⟨s, hs⟩ : ∃ s : Bool, endpointLabel E (p 3, s) = B := by
    rcases hB3 with h | h
    · exact ⟨false, h.symm⟩
    · exact ⟨true, h.symm⟩
  obtain ⟨t, ht⟩ : ∃ t : Bool, endpointLabel E (p 4, t) = B := by
    rcases hB4 with h | h
    · exact ⟨false, h.symm⟩
    · exact ⟨true, h.symm⟩
  let A := endpointLabel E (p 3, !s)
  let C := endpointLabel E (p 4, !t)
  have hAB : A ≠ B := by
    have hne := (E (p 3)).lo_ne_hi_of_wide (hWide (p 3))
    cases s
    · change (E (p 3)).hi ≠ B
      change (E (p 3)).lo = B at hs
      intro h
      exact hne (hs.trans h.symm)
    · change (E (p 3)).lo ≠ B
      change (E (p 3)).hi = B at hs
      intro h
      exact hne (h.trans hs.symm)
  have hBC : B ≠ C := by
    have hne := (E (p 4)).lo_ne_hi_of_wide (hWide (p 4))
    cases t
    · change B ≠ (E (p 4)).hi
      change (E (p 4)).lo = B at ht
      intro h
      exact hne (ht.trans h)
    · change B ≠ (E (p 4)).lo
      change (E (p 4)).hi = B at ht
      intro h
      exact hne (h.symm.trans ht.symm)
  have hAC : A ≠ C := by
    intro h
    have hne : p 3 ≠ p 4 := fun heq => (by decide : (3 : Coordinate) ≠ 4) (p.injective heq)
    have hd := distinct_wide_endpoint_pairs hx E (p 3) (p 4) (hWide _) (hWide _) hne
    cases s <;> cases t <;> simp_all [A, C, endpointLabel]
  let q : Fin 3 → Label := ![A, B, C]
  have hq : Function.Injective q := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [q]
  refine ⟨⟨q, hq, endpointLabel_isEndpoint E (p 3, !s), hB3, hB4,
    endpointLabel_isEndpoint E (p 4, !t), ?_, ?_⟩⟩
  · intro g
    cases s
    · change g (E (p 3)).lo + g (E (p 3)).hi = g (E (p 3)).hi + g B
      change (E (p 3)).lo = B at hs
      rw [hs, add_comm]
    · change g (E (p 3)).lo + g (E (p 3)).hi = g (E (p 3)).lo + g B
      change (E (p 3)).hi = B at hs
      rw [hs]
  · intro g
    cases t
    · change g (E (p 4)).lo + g (E (p 4)).hi = g B + g (E (p 4)).hi
      change (E (p 4)).lo = B at ht
      rw [ht]
    · change g (E (p 4)).lo + g (E (p 4)).hi = g B + g (E (p 4)).lo
      change (E (p 4)).hi = B at ht
      rw [ht, add_comm]

theorem isolated_endpoint_ne (x : Configuration) (i k : Coordinate)
    (hi : IsIsolated (actualExtrema x) i) (hk : IsWide (actualExtrema x) k)
    (hik : i ≠ k) (a b : Label)
    (ha : IsEndpoint (actualExtrema x) i a) (hb : IsEndpoint (actualExtrema x) k b) :
    a ≠ b := by
  intro heq
  exact hi.2 ⟨k, hk, Ne.symm hik, a, ha, by simpa only [heq] using hb⟩

def isolatedEndpoint (x : Configuration) (p : Equiv.Perm Coordinate)
    (ib : Fin 3 × Bool) : Label :=
  endpointLabel (actualExtrema x) (p ⟨ib.1.val, by omega⟩, ib.2)

theorem isolatedEndpoint_injective (x : Configuration)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (P : PathCoordinates x) :
    Function.Injective (isolatedEndpoint x P.order) := by
  intro a b hab
  have hfst : a.1 = b.1 := by
    by_contra hn
    have hp : P.order ⟨a.1.val, by omega⟩ ≠ P.order ⟨b.1.val, by omega⟩ := by
      intro heq
      have hv := congrArg (fun k : Coordinate => k.val) (P.order.injective heq)
      exact hn (Fin.ext hv)
    exact isolated_endpoint_ne x _ _ (P.isolated a.1) (hWide _) hp _ _
      (endpointLabel_isEndpoint _ _) (endpointLabel_isEndpoint _ _) hab
  apply Prod.ext hfst
  have hne := (actualExtrema x (P.order ⟨a.1.val, by omega⟩)).lo_ne_hi_of_wide (hWide _)
  cases a with
  | mk ai ab =>
    cases b with
    | mk bi bb =>
      dsimp only at hfst
      subst bi
      cases ab <;> cases bb <;> simp_all [isolatedEndpoint, endpointLabel]

def tripleEndpointSlot : Fin 6 → Fin 3 × Bool :=
  ![(0, false), (0, true), (1, false), (1, true), (2, false), (2, true)]

theorem tripleEndpointSlot_injective : Function.Injective tripleEndpointSlot := by decide

def sixIsolatedLabels (x : Configuration) (p : Equiv.Perm Coordinate) : Fin 6 → Label :=
  fun i => isolatedEndpoint x p (tripleEndpointSlot i)

def forestLabels (x : Configuration) (p : Equiv.Perm Coordinate)
    (Q : PathLabels x p) : Fin 9 → Label :=
  ![sixIsolatedLabels x p 0, sixIsolatedLabels x p 1,
    sixIsolatedLabels x p 2, sixIsolatedLabels x p 3,
    sixIsolatedLabels x p 4, sixIsolatedLabels x p 5,
    Q.labels 0, Q.labels 1, Q.labels 2]

/-- Nine different original endpoint labels, including the shared vertex
exactly once. This is the injection used by every positional estimate. -/
theorem forestLabels_injective (x : Configuration)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (P : PathCoordinates x)
    (Q : PathLabels x P.order) : Function.Injective (forestLabels x P.order Q) := by
  have he : Function.Injective (sixIsolatedLabels x P.order) :=
    (isolatedEndpoint_injective x hWide P).comp tripleEndpointSlot_injective
  have hne (i j : Fin 6) (hij : i ≠ j) :
      sixIsolatedLabels x P.order i ≠ sixIsolatedLabels x P.order j := fun h => hij (he h)
  have hqp (i j : Fin 3) (hij : i ≠ j) : Q.labels i ≠ Q.labels j := fun h => hij (Q.injective h)
  have hout (i : Fin 6) (j : Fin 3) : sixIsolatedLabels x P.order i ≠ Q.labels j := by
    let u : Fin 3 := (tripleEndpointSlot i).1
    have hu := P.isolated u
    have hep : IsEndpoint (actualExtrema x) (P.order ⟨u.val, by omega⟩)
        (sixIsolatedLabels x P.order i) := endpointLabel_isEndpoint _ _
    have hn3 : P.order ⟨u.val, by omega⟩ ≠ P.order 3 := by
      intro h
      have hv := congrArg (fun k : Coordinate => k.val) (P.order.injective h)
      change u.val = 3 at hv
      have := u.isLt
      omega
    have hn4 : P.order ⟨u.val, by omega⟩ ≠ P.order 4 := by
      intro h
      have hv := congrArg (fun k : Coordinate => k.val) (P.order.injective h)
      change u.val = 4 at hv
      have := u.isLt
      omega
    fin_cases j <;> dsimp only
    · exact isolated_endpoint_ne x _ _ hu (hWide _) hn3 _ _ hep Q.first
    · exact isolated_endpoint_ne x _ _ hu (hWide _) hn3 _ _ hep Q.middleFirst
    · exact isolated_endpoint_ne x _ _ hu (hWide _) hn4 _ _ hep Q.last
  have hout' (i : Fin 6) (j : Fin 3) : Q.labels j ≠ sixIsolatedLabels x P.order i :=
    Ne.symm (hout i j)
  have hleft (i : Fin 9) (hi : i.val < 6) :
      forestLabels x P.order Q i = sixIsolatedLabels x P.order ⟨i.val, hi⟩ := by
    fin_cases i <;> first | rfl | norm_num at hi
  have hright (i : Fin 9) (hi : ¬i.val < 6) :
      forestLabels x P.order Q i = Q.labels ⟨i.val - 6, by omega⟩ := by
    fin_cases i <;> first | rfl | norm_num at hi
  intro i j hij
  apply Fin.ext
  by_cases hi : i.val < 6
  · by_cases hj : j.val < 6
    · rw [hleft i hi, hleft j hj] at hij
      exact congrArg (fun t : Fin 6 => t.val) (he hij)
    · rw [hleft i hi, hright j hj] at hij
      exact False.elim (hout ⟨i.val, hi⟩ ⟨j.val - 6, by omega⟩ hij)
  · by_cases hj : j.val < 6
    · rw [hright i hi, hleft j hj] at hij
      exact False.elim (hout' ⟨j.val, hj⟩ ⟨i.val - 6, by omega⟩ hij)
    · rw [hright i hi, hright j hj] at hij
      have hv := congrArg (fun t : Fin 3 => t.val) (Q.injective hij)
      change i.val - 6 = j.val - 6 at hv
      omega

def isolatedRowIndices : Fin 3 → Fin 7 → Fin 9 :=
  ![![2, 3, 4, 5, 6, 7, 8], ![0, 1, 4, 5, 6, 7, 8], ![0, 1, 2, 3, 6, 7, 8]]

def firstPathIndices : Fin 7 → Fin 9 := ![0, 1, 2, 3, 4, 5, 8]
def lastPathIndices : Fin 7 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6]

set_option maxRecDepth 20000 in
private theorem isolatedRowIndices_injective :
    ∀ i : Fin 3, Function.Injective (isolatedRowIndices i) := by decide

private theorem firstPathIndices_injective : Function.Injective firstPathIndices := by decide
private theorem lastPathIndices_injective : Function.Injective lastPathIndices := by decide

def isolatedRowWeights (x : Configuration) (p : Equiv.Perm Coordinate) : Fin 3 → Fin 7 → ℝ :=
  ![![pathExcess x p 1, pathExcess x p 1, pathExcess x p 2, pathExcess x p 2,
       pathExcess x p 3, sharedExcess x p, pathExcess x p 4],
    ![pathExcess x p 0, pathExcess x p 0, pathExcess x p 2, pathExcess x p 2,
       pathExcess x p 3, sharedExcess x p, pathExcess x p 4],
    ![pathExcess x p 0, pathExcess x p 0, pathExcess x p 1, pathExcess x p 1,
       pathExcess x p 3, sharedExcess x p, pathExcess x p 4]]

def firstPathWeights (x : Configuration) (p : Equiv.Perm Coordinate) : Fin 7 → ℝ :=
  ![pathExcess x p 0, pathExcess x p 0, pathExcess x p 1, pathExcess x p 1,
    pathExcess x p 2, pathExcess x p 2, pathExcess x p 4]

def lastPathWeights (x : Configuration) (p : Equiv.Perm Coordinate) : Fin 7 → ℝ :=
  ![pathExcess x p 0, pathExcess x p 0, pathExcess x p 1, pathExcess x p 1,
    pathExcess x p 2, pathExcess x p 2, pathExcess x p 3]

theorem sum_isolatedRowWeights (x : Configuration) (p : Equiv.Perm Coordinate) (i : Fin 3) :
    (∑ j, isolatedRowWeights x p i j) =
      2 * (isolatedExcess x p - pathExcess x p ⟨i.val, by omega⟩) +
        2 * sharedExcess x p := by
  fin_cases i
  · change (∑ j, isolatedRowWeights x p 0 j) =
      2 * (isolatedExcess x p - pathExcess x p 0) + 2 * sharedExcess x p
    simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    change pathExcess x p 1 + (pathExcess x p 1 + (pathExcess x p 2 +
      (pathExcess x p 2 + (pathExcess x p 3 + (sharedExcess x p + pathExcess x p 4))))) =
      2 * (isolatedExcess x p - pathExcess x p 0) + 2 * sharedExcess x p
    dsimp only [isolatedExcess, sharedExcess]
    ring
  · change (∑ j, isolatedRowWeights x p 1 j) =
      2 * (isolatedExcess x p - pathExcess x p 1) + 2 * sharedExcess x p
    simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    change pathExcess x p 0 + (pathExcess x p 0 + (pathExcess x p 2 +
      (pathExcess x p 2 + (pathExcess x p 3 + (sharedExcess x p + pathExcess x p 4))))) =
      2 * (isolatedExcess x p - pathExcess x p 1) + 2 * sharedExcess x p
    dsimp only [isolatedExcess, sharedExcess]
    ring
  · change (∑ j, isolatedRowWeights x p 2 j) =
      2 * (isolatedExcess x p - pathExcess x p 2) + 2 * sharedExcess x p
    simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    change pathExcess x p 0 + (pathExcess x p 0 + (pathExcess x p 1 +
      (pathExcess x p 1 + (pathExcess x p 3 + (sharedExcess x p + pathExcess x p 4))))) =
      2 * (isolatedExcess x p - pathExcess x p 2) + 2 * sharedExcess x p
    dsimp only [isolatedExcess, sharedExcess]
    ring

theorem sum_firstPathWeights (x : Configuration) (p : Equiv.Perm Coordinate) :
    (∑ j, firstPathWeights x p j) = 2 * isolatedExcess x p + pathExcess x p 4 := by
  norm_num [firstPathWeights, isolatedExcess, Fin.sum_univ_succ]
  ring

theorem sum_lastPathWeights (x : Configuration) (p : Equiv.Perm Coordinate) :
    (∑ j, lastPathWeights x p j) = 2 * isolatedExcess x p + pathExcess x p 3 := by
  norm_num [lastPathWeights, isolatedExcess, Fin.sum_univ_succ]
  ring

def outerFunctional (x : Configuration) (p : Equiv.Perm Coordinate)
    (row : Coordinate) (g : Label → ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.erase (p row),
    excess (actualExtrema x) k *
      (g (actualExtrema x k).lo + g (actualExtrema x k).hi)

theorem outerFunctional_coordinates (x : Configuration) (p : Equiv.Perm Coordinate)
    (row : Coordinate) (g : Label → ℝ) :
    outerFunctional x p row g =
      ∑ i : Fin 4, pathExcess x p (MatchingAssembly.otherCoordinates row i) *
        (g (actualExtrema x (p (MatchingAssembly.otherCoordinates row i))).lo +
          g (actualExtrema x (p (MatchingAssembly.otherCoordinates row i))).hi) := by
  unfold outerFunctional pathExcess
  rw [← MatchingAssembly.sum_erase_perm p row (fun k =>
    excess (actualExtrema x) k *
      (g (actualExtrema x k).lo + g (actualExtrema x k).hi)),
    ← MatchingAssembly.sum_otherCoordinates row (fun k =>
      excess (actualExtrema x) (p k) *
        (g (actualExtrema x (p k)).lo + g (actualExtrema x (p k)).hi))]

/-- One occurrence of the shared vertex has the combined weight a+c in
each isolated row; it is not split into two independently placed labels. -/
theorem isolated_outer_identity (x : Configuration) (p : Equiv.Perm Coordinate)
    (Q : PathLabels x p) (row : Fin 3) (g : Label → ℝ) :
    outerFunctional x p ⟨row.val, by omega⟩ g =
      ∑ j, isolatedRowWeights x p row j *
        g (forestLabels x p Q (isolatedRowIndices row j)) := by
  rw [outerFunctional_coordinates]
  fin_cases row
  · simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    change pathExcess x p 1 *
        (g (actualExtrema x (p 1)).lo + g (actualExtrema x (p 1)).hi) +
      (pathExcess x p 2 *
        (g (actualExtrema x (p 2)).lo + g (actualExtrema x (p 2)).hi) +
      (pathExcess x p 3 *
        (g (actualExtrema x (p 3)).lo + g (actualExtrema x (p 3)).hi) +
        pathExcess x p 4 *
          (g (actualExtrema x (p 4)).lo + g (actualExtrema x (p 4)).hi))) =
      pathExcess x p 1 * g (actualExtrema x (p 1)).lo +
      (pathExcess x p 1 * g (actualExtrema x (p 1)).hi +
      (pathExcess x p 2 * g (actualExtrema x (p 2)).lo +
      (pathExcess x p 2 * g (actualExtrema x (p 2)).hi +
      (pathExcess x p 3 * g (Q.labels 0) +
      (sharedExcess x p * g (Q.labels 1) + pathExcess x p 4 * g (Q.labels 2))))))
    rw [Q.pairFirst g, Q.pairLast g]
    dsimp only [sharedExcess]
    ring
  · simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    change pathExcess x p 0 *
        (g (actualExtrema x (p 0)).lo + g (actualExtrema x (p 0)).hi) +
      (pathExcess x p 2 *
        (g (actualExtrema x (p 2)).lo + g (actualExtrema x (p 2)).hi) +
      (pathExcess x p 3 *
        (g (actualExtrema x (p 3)).lo + g (actualExtrema x (p 3)).hi) +
        pathExcess x p 4 *
          (g (actualExtrema x (p 4)).lo + g (actualExtrema x (p 4)).hi))) =
      pathExcess x p 0 * g (actualExtrema x (p 0)).lo +
      (pathExcess x p 0 * g (actualExtrema x (p 0)).hi +
      (pathExcess x p 2 * g (actualExtrema x (p 2)).lo +
      (pathExcess x p 2 * g (actualExtrema x (p 2)).hi +
      (pathExcess x p 3 * g (Q.labels 0) +
      (sharedExcess x p * g (Q.labels 1) + pathExcess x p 4 * g (Q.labels 2))))))
    rw [Q.pairFirst g, Q.pairLast g]
    dsimp only [sharedExcess]
    ring
  · simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    change pathExcess x p 0 *
        (g (actualExtrema x (p 0)).lo + g (actualExtrema x (p 0)).hi) +
      (pathExcess x p 1 *
        (g (actualExtrema x (p 1)).lo + g (actualExtrema x (p 1)).hi) +
      (pathExcess x p 3 *
        (g (actualExtrema x (p 3)).lo + g (actualExtrema x (p 3)).hi) +
        pathExcess x p 4 *
          (g (actualExtrema x (p 4)).lo + g (actualExtrema x (p 4)).hi))) =
      pathExcess x p 0 * g (actualExtrema x (p 0)).lo +
      (pathExcess x p 0 * g (actualExtrema x (p 0)).hi +
      (pathExcess x p 1 * g (actualExtrema x (p 1)).lo +
      (pathExcess x p 1 * g (actualExtrema x (p 1)).hi +
      (pathExcess x p 3 * g (Q.labels 0) +
      (sharedExcess x p * g (Q.labels 1) + pathExcess x p 4 * g (Q.labels 2))))))
    rw [Q.pairFirst g, Q.pairLast g]
    dsimp only [sharedExcess]
    ring

theorem first_path_outer_identity (x : Configuration) (p : Equiv.Perm Coordinate)
    (Q : PathLabels x p) (g : Label → ℝ) :
    outerFunctional x p 3 g = pathExcess x p 4 * g (Q.labels 1) +
      ∑ j, firstPathWeights x p j * g (forestLabels x p Q (firstPathIndices j)) := by
  rw [outerFunctional_coordinates]
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change pathExcess x p 0 *
      (g (actualExtrema x (p 0)).lo + g (actualExtrema x (p 0)).hi) +
    (pathExcess x p 1 *
      (g (actualExtrema x (p 1)).lo + g (actualExtrema x (p 1)).hi) +
    (pathExcess x p 2 *
      (g (actualExtrema x (p 2)).lo + g (actualExtrema x (p 2)).hi) +
      pathExcess x p 4 *
        (g (actualExtrema x (p 4)).lo + g (actualExtrema x (p 4)).hi))) =
    pathExcess x p 4 * g (Q.labels 1) +
    (pathExcess x p 0 * g (actualExtrema x (p 0)).lo +
    (pathExcess x p 0 * g (actualExtrema x (p 0)).hi +
    (pathExcess x p 1 * g (actualExtrema x (p 1)).lo +
    (pathExcess x p 1 * g (actualExtrema x (p 1)).hi +
    (pathExcess x p 2 * g (actualExtrema x (p 2)).lo +
    (pathExcess x p 2 * g (actualExtrema x (p 2)).hi + pathExcess x p 4 * g (Q.labels 2)))))))
  rw [Q.pairLast g]
  ring

theorem last_path_outer_identity (x : Configuration) (p : Equiv.Perm Coordinate)
    (Q : PathLabels x p) (g : Label → ℝ) :
    outerFunctional x p 4 g = pathExcess x p 3 * g (Q.labels 1) +
      ∑ j, lastPathWeights x p j * g (forestLabels x p Q (lastPathIndices j)) := by
  rw [outerFunctional_coordinates]
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change pathExcess x p 0 *
      (g (actualExtrema x (p 0)).lo + g (actualExtrema x (p 0)).hi) +
    (pathExcess x p 1 *
      (g (actualExtrema x (p 1)).lo + g (actualExtrema x (p 1)).hi) +
    (pathExcess x p 2 *
      (g (actualExtrema x (p 2)).lo + g (actualExtrema x (p 2)).hi) +
      pathExcess x p 3 *
        (g (actualExtrema x (p 3)).lo + g (actualExtrema x (p 3)).hi))) =
    pathExcess x p 3 * g (Q.labels 1) +
    (pathExcess x p 0 * g (actualExtrema x (p 0)).lo +
    (pathExcess x p 0 * g (actualExtrema x (p 0)).hi +
    (pathExcess x p 1 * g (actualExtrema x (p 1)).lo +
    (pathExcess x p 1 * g (actualExtrema x (p 1)).hi +
    (pathExcess x p 2 * g (actualExtrema x (p 2)).lo +
    (pathExcess x p 2 * g (actualExtrema x (p 2)).hi + pathExcess x p 3 * g (Q.labels 0)))))))
  rw [Q.pairFirst g]
  ring

def pathRowVector (x : Configuration) (p : Equiv.Perm Coordinate)
    (row : Coordinate) : Label → ℝ :=
  transport (columnOrders x (p row)) shiftedVector

/-- Actual outer-cut energy is a lower bound within the original directed
row ledger. Its original-label vector has the proved zero sum. -/
theorem original_path_outer_lower (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (p : Equiv.Perm Coordinate)
    (row : Coordinate) :
    outerFunctional x p row (fun i => pathRowVector x p row i ^ 2) ≤
      MatchingAssembly.rowCrossEnergy x (p row) := by
  have hv : (∑ i, pathRowVector x p row i) = 0 := by
    rw [pathRowVector, sum_transport, sum_shiftedVector_zero]
  apply Finset.sum_le_sum
  intro col _
  exact actual_wide_outer_energy_lower x hx col (hWide col)
    (pathRowVector x p row) hv

def pathRowPositions (x : Configuration) (p : Equiv.Perm Coordinate)
    (Q : PathLabels x p) (row : Coordinate) (idx : Fin 7 → Fin 9) : Fin 7 → Label :=
  fun j => (columnOrders x (p row)).symm (forestLabels x p Q (idx j))

theorem pathRowPositions_injective (x : Configuration)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (P : PathCoordinates x)
    (Q : PathLabels x P.order) (row : Coordinate)
    (idx : Fin 7 → Fin 9) (hidx : Function.Injective idx) :
    Function.Injective (pathRowPositions x P.order Q row idx) :=
  (columnOrders x (P.order row)).symm.injective.comp
    ((forestLabels_injective x hWide P Q).comp hidx)

theorem pathRowPositions_square (x : Configuration) (p : Equiv.Perm Coordinate)
    (Q : PathLabels x p) (row : Coordinate) (idx : Fin 7 → Fin 9) (j : Fin 7) :
    squaredPosition (pathRowPositions x p Q row idx j) =
      pathRowVector x p row (forestLabels x p Q (idx j)) ^ 2 := by
  rw [← shiftedVector_sq_eq_position]
  rfl

theorem pathExcess_bounds (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (p : Equiv.Perm Coordinate)
    (i : Coordinate) : 0 ≤ pathExcess x p i ∧ pathExcess x p i ≤ 1 / 3 :=
  ⟨le_of_lt (excess_pos (actualExtrema x) _ (hWide _)), original_excess_le_third x hx _⟩

theorem isolated_weights_nonneg (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (p : Equiv.Perm Coordinate)
    (row : Fin 3) (j : Fin 7) : 0 ≤ isolatedRowWeights x p row j := by
  have h0 := (pathExcess_bounds x hx hWide p 0).1
  have h1 := (pathExcess_bounds x hx hWide p 1).1
  have h2 := (pathExcess_bounds x hx hWide p 2).1
  have h3 := (pathExcess_bounds x hx hWide p 3).1
  have h4 := (pathExcess_bounds x hx hWide p 4).1
  fin_cases row <;> fin_cases j <;> norm_num [isolatedRowWeights, sharedExcess] <;> linarith

theorem isolated_weights_cap_except_shared (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (p : Equiv.Perm Coordinate)
    (row : Fin 3) (j : Fin 7) (hj : j ≠ 5) : isolatedRowWeights x p row j ≤ 1 / 3 := by
  have h0 := (pathExcess_bounds x hx hWide p 0).2
  have h1 := (pathExcess_bounds x hx hWide p 1).2
  have h2 := (pathExcess_bounds x hx hWide p 2).2
  have h3 := (pathExcess_bounds x hx hWide p 3).2
  have h4 := (pathExcess_bounds x hx hWide p 4).2
  fin_cases row
  · fin_cases j
    · exact h1
    · exact h1
    · exact h2
    · exact h2
    · exact h3
    · exact False.elim (hj rfl)
    · exact h4
  · fin_cases j
    · exact h0
    · exact h0
    · exact h2
    · exact h2
    · exact h3
    · exact False.elim (hj rfl)
    · exact h4
  · fin_cases j
    · exact h0
    · exact h0
    · exact h1
    · exact h1
    · exact h3
    · exact False.elim (hj rfl)
    · exact h4

theorem isolated_weights_capped (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (p : Equiv.Perm Coordinate)
    (hS : sharedExcess x p ≤ 1 / 3) (row : Fin 3) (j : Fin 7) :
    0 ≤ isolatedRowWeights x p row j ∧ isolatedRowWeights x p row j ≤ 1 / 3 := by
  refine ⟨isolated_weights_nonneg x hx hWide p row j, ?_⟩
  by_cases hj : j = 5
  · subst j
    fin_cases row <;> change sharedExcess x p ≤ 1 / 3 <;> exact hS
  · exact isolated_weights_cap_except_shared x hx hWide p row j hj

theorem first_path_weights_capped (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (p : Equiv.Perm Coordinate) (j : Fin 7) :
    0 ≤ firstPathWeights x p j ∧ firstPathWeights x p j ≤ 1 / 3 := by
  fin_cases j <;> norm_num [firstPathWeights] <;> exact pathExcess_bounds x hx hWide p _

theorem last_path_weights_capped (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (p : Equiv.Perm Coordinate) (j : Fin 7) :
    0 ≤ lastPathWeights x p j ∧ lastPathWeights x p j ≤ 1 / 3 := by
  fin_cases j <;> norm_num [lastPathWeights] <;> exact pathExcess_bounds x hx hWide p _

theorem original_isolated_small_row_lower (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (P : PathCoordinates x)
    (Q : PathLabels x P.order) (hS : sharedExcess x P.order ≤ 1 / 3)
    (row : Fin 3) :
    s4 * (2 * (isolatedExcess x P.order - pathExcess x P.order ⟨row.val, by omega⟩) +
        2 * sharedExcess x P.order) - (3 * s4 - 2 * s5) / 3 ≤
      MatchingAssembly.rowCrossEnergy x (P.order ⟨row.val, by omega⟩) := by
  let p := P.order
  let idx := isolatedRowIndices row
  let w := isolatedRowWeights x p row
  have ht := seven_capped_threshold_s4
    (pathRowPositions x p Q ⟨row.val, by omega⟩ idx)
    (pathRowPositions_injective x hWide P Q _ idx (isolatedRowIndices_injective row))
    w (isolated_weights_capped x hx hWide p hS row)
  simp_rw [pathRowPositions_square] at ht
  rw [sum_isolatedRowWeights] at ht
  have ho := original_path_outer_lower x hx hWide p ⟨row.val, by omega⟩
  rw [isolated_outer_identity x p Q row] at ho
  exact ht.trans ho

theorem original_isolated_large_row_lower (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (P : PathCoordinates x)
    (Q : PathLabels x P.order) (hS : 1 / 3 ≤ sharedExcess x P.order)
    (row : Fin 3) :
    s4 * (2 * (isolatedExcess x P.order - pathExcess x P.order ⟨row.val, by omega⟩) +
        2 * sharedExcess x P.order) - sharedExcess x P.order * s4 -
          (2 / 3) * (s4 - s5) ≤
      MatchingAssembly.rowCrossEnergy x (P.order ⟨row.val, by omega⟩) := by
  let p := P.order
  let idx := isolatedRowIndices row
  let w := isolatedRowWeights x p row
  have hwS : w 5 ≤ sharedExcess x p := by
    fin_cases row <;> change sharedExcess x p ≤ sharedExcess x p <;> exact le_rfl
  have ht := seven_shared_threshold_s4
    (pathRowPositions x p Q ⟨row.val, by omega⟩ idx)
    (pathRowPositions_injective x hWide P Q _ idx (isolatedRowIndices_injective row))
    w 5 (sharedExcess x p) hS hwS
    (isolated_weights_nonneg x hx hWide p row)
    (isolated_weights_cap_except_shared x hx hWide p row)
  simp_rw [pathRowPositions_square] at ht
  rw [sum_isolatedRowWeights] at ht
  have ho := original_path_outer_lower x hx hWide p ⟨row.val, by omega⟩
  rw [isolated_outer_identity x p Q row] at ho
  exact ht.trans ho

theorem original_first_path_row_lower (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (P : PathCoordinates x)
    (Q : PathLabels x P.order) :
    pathExcess x P.order 4 * s1 +
      s3 * (2 * isolatedExcess x P.order + pathExcess x P.order 4) -
        (5 * s3 - 2 * s5 - 2 * s4) / 3 ≤
      MatchingAssembly.rowCrossEnergy x (P.order 3) := by
  let p := P.order
  have ht := seven_capped_threshold_s3
    (pathRowPositions x p Q 3 firstPathIndices)
    (pathRowPositions_injective x hWide P Q 3 firstPathIndices firstPathIndices_injective)
    (firstPathWeights x p) (first_path_weights_capped x hx hWide p)
  simp_rw [pathRowPositions_square] at ht
  rw [sum_firstPathWeights] at ht
  have ho := original_path_outer_lower x hx hWide p 3
  rw [first_path_outer_identity x p Q] at ho
  have hs : pathRowVector x p 3 (Q.labels 1) ^ 2 = s1 :=
    shifted_actual_endpoint_sq x (p 3) (Q.labels 1) Q.middleFirst
  rw [hs] at ho
  linarith

theorem original_last_path_row_lower (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (P : PathCoordinates x)
    (Q : PathLabels x P.order) :
    pathExcess x P.order 3 * s1 +
      s3 * (2 * isolatedExcess x P.order + pathExcess x P.order 3) -
        (5 * s3 - 2 * s5 - 2 * s4) / 3 ≤
      MatchingAssembly.rowCrossEnergy x (P.order 4) := by
  let p := P.order
  have ht := seven_capped_threshold_s3
    (pathRowPositions x p Q 4 lastPathIndices)
    (pathRowPositions_injective x hWide P Q 4 lastPathIndices lastPathIndices_injective)
    (lastPathWeights x p) (last_path_weights_capped x hx hWide p)
  simp_rw [pathRowPositions_square] at ht
  rw [sum_lastPathWeights] at ht
  have ho := original_path_outer_lower x hx hWide p 4
  rw [last_path_outer_identity x p Q] at ho
  have hs : pathRowVector x p 4 (Q.labels 1) ^ 2 = s1 :=
    shifted_actual_endpoint_sq x (p 4) (Q.labels 1) Q.middleLast
  rw [hs] at ho
  linarith

theorem sum_original_path_rows (x : Configuration) (p : Equiv.Perm Coordinate) :
    MatchingAssembly.rowCrossEnergy x (p 0) + MatchingAssembly.rowCrossEnergy x (p 1) +
      MatchingAssembly.rowCrossEnergy x (p 2) + MatchingAssembly.rowCrossEnergy x (p 3) +
      MatchingAssembly.rowCrossEnergy x (p 4) = crossEnergy x (columnOrders x) shiftedVector := by
  have h := Kusner5.sum_perm p (MatchingAssembly.rowCrossEnergy x)
  change (∑ i, MatchingAssembly.rowCrossEnergy x (p i)) =
    crossEnergy x (columnOrders x) shiftedVector at h
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero] at h
  change MatchingAssembly.rowCrossEnergy x (p 0) +
    (MatchingAssembly.rowCrossEnergy x (p 1) +
    (MatchingAssembly.rowCrossEnergy x (p 2) +
    (MatchingAssembly.rowCrossEnergy x (p 3) + MatchingAssembly.rowCrossEnergy x (p 4)))) =
      crossEnergy x (columnOrders x) shiftedVector at h
  linarith

theorem original_path_small_lower (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (P : PathCoordinates x)
    (Q : PathLabels x P.order) (hS : sharedExcess x P.order ≤ 1 / 3) :
    pathSmall (isolatedExcess x P.order) (sharedExcess x P.order) ≤
      crossEnergy x (columnOrders x) shiftedVector := by
  have h0 := original_isolated_small_row_lower x hx hWide P Q hS 0
  have h1 := original_isolated_small_row_lower x hx hWide P Q hS 1
  have h2 := original_isolated_small_row_lower x hx hWide P Q hS 2
  have h3 := original_first_path_row_lower x hx hWide P Q
  have h4 := original_last_path_row_lower x hx hWide P Q
  have hsum := sum_original_path_rows x P.order
  change s4 * (2 * (isolatedExcess x P.order - pathExcess x P.order 0) +
    2 * sharedExcess x P.order) - (3 * s4 - 2 * s5) / 3 ≤
      MatchingAssembly.rowCrossEnergy x (P.order 0) at h0
  change s4 * (2 * (isolatedExcess x P.order - pathExcess x P.order 1) +
    2 * sharedExcess x P.order) - (3 * s4 - 2 * s5) / 3 ≤
      MatchingAssembly.rowCrossEnergy x (P.order 1) at h1
  change s4 * (2 * (isolatedExcess x P.order - pathExcess x P.order 2) +
    2 * sharedExcess x P.order) - (3 * s4 - 2 * s5) / 3 ≤
      MatchingAssembly.rowCrossEnergy x (P.order 2) at h2
  dsimp only [pathSmall, isolatedExcess, sharedExcess] at *
  nlinarith

theorem original_path_large_lower (x : Configuration) (hx : UnitEquilateral x)
    (hWide : ∀ k, IsWide (actualExtrema x) k) (P : PathCoordinates x)
    (Q : PathLabels x P.order) (hS : 1 / 3 ≤ sharedExcess x P.order) :
    pathLarge (isolatedExcess x P.order) (sharedExcess x P.order) ≤
      crossEnergy x (columnOrders x) shiftedVector := by
  have h0 := original_isolated_large_row_lower x hx hWide P Q hS 0
  have h1 := original_isolated_large_row_lower x hx hWide P Q hS 1
  have h2 := original_isolated_large_row_lower x hx hWide P Q hS 2
  have h3 := original_first_path_row_lower x hx hWide P Q
  have h4 := original_last_path_row_lower x hx hWide P Q
  have hsum := sum_original_path_rows x P.order
  change s4 * (2 * (isolatedExcess x P.order - pathExcess x P.order 0) +
    2 * sharedExcess x P.order) - sharedExcess x P.order * s4 -
      (2 / 3) * (s4 - s5) ≤ MatchingAssembly.rowCrossEnergy x (P.order 0) at h0
  change s4 * (2 * (isolatedExcess x P.order - pathExcess x P.order 1) +
    2 * sharedExcess x P.order) - sharedExcess x P.order * s4 -
      (2 / 3) * (s4 - s5) ≤ MatchingAssembly.rowCrossEnergy x (P.order 1) at h1
  change s4 * (2 * (isolatedExcess x P.order - pathExcess x P.order 2) +
    2 * sharedExcess x P.order) - sharedExcess x P.order * s4 -
      (2 / 3) * (s4 - s5) ≤ MatchingAssembly.rowCrossEnergy x (P.order 2) at h2
  dsimp only [pathLarge, isolatedExcess, sharedExcess] at *
  nlinarith

theorem original_path_deficit (x : Configuration) (hx : UnitEquilateral x)
    (p : Equiv.Perm Coordinate) :
    crossEnergy x (columnOrders x) shiftedVector =
      5 * alpha - 15 / 4 + (isolatedExcess x p + sharedExcess x p) / 2 := by
  have hs : (∑ i, pathExcess x p i) = Profiles.totalWidth x - 5 / 2 := by
    unfold pathExcess
    rw [Kusner5.sum_perm p]
    simp only [excess, actualExtrema_range, Finset.sum_sub_distrib]
    norm_num [Profiles.totalWidth]
  have ht : (∑ i, pathExcess x p i) = isolatedExcess x p + sharedExcess x p := by
    simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    change pathExcess x p 0 + (pathExcess x p 1 +
      (pathExcess x p 2 + (pathExcess x p 3 + pathExcess x p 4))) =
        isolatedExcess x p + sharedExcess x p
    dsimp only [isolatedExcess, sharedExcess]
    ring
  have hwidth : Profiles.totalWidth x = 5 / 2 + isolatedExcess x p + sharedExcess x p := by
    linarith
  rw [shifted_crossEnergy x hx, hwidth]
  change 5 * alpha + (5 / 2 + isolatedExcess x p + sharedExcess x p) / 2 - 5 = _
  ring

/-- Original five-wide, three-isolated case exclusion. The row and scalar
arithmetic inputs above are all constructed from this same original x. -/
theorem no_five_wide_three_isolated (x : Configuration) (hx : UnitEquilateral x)
    (hWideCard : (ForestMatching.wideCoordinates (actualExtrema x)).card = 5)
    (hIsoCard : (isolatedCoordinates (actualExtrema x)).card = 3)
    (hNonCard : (nonisolatedCoordinates (actualExtrema x)).card = 2) : False := by
  have hWide := all_wide_of_card_five (actualExtrema x) hWideCard
  let P := Classical.choice (exists_path_coordinates x hWideCard hIsoCard hNonCard)
  let Q := Classical.choice (exists_path_labels x hx hWide P)
  have hU : isolatedExcess x P.order ≤ 1 := by
    have h0 := (pathExcess_bounds x hx hWide P.order 0).2
    have h1 := (pathExcess_bounds x hx hWide P.order 1).2
    have h2 := (pathExcess_bounds x hx hWide P.order 2).2
    dsimp only [isolatedExcess]
    linarith
  have hS0 : 0 ≤ sharedExcess x P.order := by
    exact add_nonneg (pathExcess_bounds x hx hWide P.order 3).1
      (pathExcess_bounds x hx hWide P.order 4).1
  have heq := original_path_deficit x hx P.order
  rcases le_total (sharedExcess x P.order) (1 / 3) with hs | hs
  · exact path_small_contradiction (isolatedExcess x P.order) (sharedExcess x P.order)
      (crossEnergy x (columnOrders x) shiftedVector) hU hS0 heq
      (original_path_small_lower x hx hWide P Q hs)
  · exact path_large_contradiction (isolatedExcess x P.order) (sharedExcess x P.order)
      (crossEnergy x (columnOrders x) shiftedVector) hU hs heq
      (original_path_large_lower x hx hWide P Q hs)

end
end Kusner5.PathAssembly
