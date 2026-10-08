import Kusner5.QuartetFaceProjection
import Kusner5.QuartetPerimeter
import Kusner5.QuartetDoublePerimeter

/-!
Actual coordinate enumeration and physical transport for the small-slot
quartet sections. Every embedding below inserts coordinates into their
original distinct physical positions and proves the explicit l1 sum identity.
-/

namespace Kusner5

open scoped BigOperators
open QuartetGeometry

noncomputable section

/-- Insert a finite vector into specified physical coordinates. -/
def physicalEmbedding {n d : ℕ} (e : Fin n → Fin d) (z : Point n) : Point d :=
  fun k => ∑ i, if e i = k then z i else 0

theorem physicalEmbedding_at {n d : ℕ} (e : Fin n → Fin d)
    (he : Function.Injective e) (z : Point n) (i : Fin n) :
    physicalEmbedding e z (e i) = z i := by
  classical
  unfold physicalEmbedding
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
  · intro j _ hji
    exact if_neg (fun h => hji (he h))
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ i))

theorem physicalEmbedding_outside {n d : ℕ} (e : Fin n → Fin d)
    (z : Point n) (k : Fin d) (hk : k ∉ Finset.univ.image e) :
    physicalEmbedding e z k = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (fun h => hk (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h⟩))

/-- Exact sum-abs isometry for a genuine injection of physical slots. -/
theorem physicalEmbedding_distance {n d : ℕ} (e : Fin n → Fin d)
    (he : Function.Injective e) (z w : Point n) :
    l1dist (physicalEmbedding e z) (physicalEmbedding e w) = l1dist z w := by
  classical
  have hsub :
      (∑ k ∈ Finset.univ.image e,
        |physicalEmbedding e z k - physicalEmbedding e w k|) =
      ∑ k, |physicalEmbedding e z k - physicalEmbedding e w k| := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hnot
    rw [physicalEmbedding_outside e z k hnot, physicalEmbedding_outside e w k hnot]
    simp only [sub_self, abs_zero]
  calc
    l1dist (physicalEmbedding e z) (physicalEmbedding e w) =
        ∑ k ∈ Finset.univ.image e,
          |physicalEmbedding e z k - physicalEmbedding e w k| := hsub.symm
    _ = ∑ i, |physicalEmbedding e z (e i) - physicalEmbedding e w (e i)| := by
      rw [Finset.sum_image]
      intro i _ j _ hij
      exact he hij
    _ = l1dist z w := by
      simp only [physicalEmbedding_at e he, l1dist]

theorem physicalEmbedding_of_supported {n d : ℕ} (e : Fin n → Fin d)
    (he : Function.Injective e) (z : Point d)
    (hsupport : ∀ k, k ∉ Finset.univ.image e → z k = 0) :
    physicalEmbedding e (fun i => z (e i)) = z := by
  classical
  funext k
  by_cases hk : k ∈ Finset.univ.image e
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    exact physicalEmbedding_at e he _ i
  · rw [physicalEmbedding_outside e _ k hk, hsupport k hk]

theorem exists_finset_enumeration {α : Type*} [DecidableEq α]
    (S : Finset α) (n : ℕ) (hcard : S.card = n) :
    ∃ e : Fin n → α, Function.Injective e ∧ Finset.univ.image e = S := by
  classical
  obtain ⟨e, he, hmem⟩ := exists_fin_injection_into_finset S n (by rw [hcard])
  have hsubset : Finset.univ.image e ⊆ S := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    exact hmem i
  have hle : S.card ≤ (Finset.univ.image e).card := by
    rw [hcard, Finset.card_image_of_injective _ he]
    simp only [Finset.card_univ, Fintype.card_fin, le_refl]
  exact ⟨e, he, Finset.eq_of_subset_of_card_le hsubset hle⟩

theorem sum_finset_enumeration {α : Type*} [DecidableEq α]
    {n : ℕ} (S : Finset α) (e : Fin n → α) (he : Function.Injective e)
    (himage : Finset.univ.image e = S) (f : α → ℝ) :
    (∑ i, f (e i)) = ∑ k ∈ S, f k := by
  classical
  rw [← himage, Finset.sum_image]
  intro i _ j _ hij
  exact he hij

def InQuartetSection (x : Configuration) (q : Fin 4 → Label) (z : Point 5) : Prop :=
  InSymmetricBox (quartetHalfWidth x q) z ∧
    ∀ t : Fin 3, (∑ k, if quartetPartition x q k = t then z k else 0) = 0

theorem quartet_section_zero_width (x : Configuration) (q : Fin 4 → Label)
    (z : Point 5) (hz : InQuartetSection x q z) (k : Coordinate)
    (hk : quartetHalfWidth x q k = 0) : z k = 0 := by
  have h := hz.1 k
  rw [hk] at h
  linarith [h.1, h.2]

theorem quartet_section_positive_slot_sum (x : Configuration)
    (q : Fin 4 → Label) (z : Point 5) (hz : InQuartetSection x q z) (t : Fin 3) :
    (∑ k ∈ positiveQuartetSlots x q t, z k) = 0 := by
  classical
  have heq : (∑ k ∈ positiveQuartetSlots x q t, z k) =
      ∑ k, if quartetPartition x q k = t then z k else 0 := by
    simp only [positiveQuartetSlots, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases ht : quartetPartition x q k = t
    · by_cases hp : 0 < quartetHalfWidth x q k
      · simp only [ht, hp, and_self, ite_true]
      · have hzero : quartetHalfWidth x q k = 0 :=
          le_antisymm (le_of_not_gt hp) (quartetHalfWidth_nonneg x q k)
        have hzk := quartet_section_zero_width x q z hz k hzero
        simp only [ht, hp, hzk, and_false, ite_false, ite_true]
    · simp only [ht, false_and, ite_false]
  exact heq.trans (hz.2 t)

/-- All auxiliary coordinates of a singleton type vanish. Zero-width
physical coordinates are dealt with by the box bound, without a tail claim. -/
theorem quartet_section_singleton_zero (x : Configuration) (q : Fin 4 → Label)
    (z : Point 5) (hz : InQuartetSection x q z) (t : Fin 3)
    (hcard : (positiveQuartetSlots x q t).card = 1)
    (k : Coordinate) (ht : quartetPartition x q k = t) : z k = 0 := by
  classical
  by_cases hp : 0 < quartetHalfWidth x q k
  · have hk : k ∈ positiveQuartetSlots x q t :=
      (mem_positiveQuartetSlots x q t k).mpr ⟨ht, hp⟩
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    have hka : k = a := by rw [ha] at hk; exact Finset.mem_singleton.mp hk
    have hs := quartet_section_positive_slot_sum x q z hz t
    rw [ha, Finset.sum_singleton] at hs
    simpa only [hka] using hs
  · have hzero : quartetHalfWidth x q k = 0 :=
      le_antisymm (le_of_not_gt hp) (quartetHalfWidth_nonneg x q k)
    exact quartet_section_zero_width x q z hz k hzero

theorem quartet_section_supported_one_type (x : Configuration)
    (q : Fin 4 → Label) (p : Equiv.Perm (Fin 3))
    (h0 : (positiveQuartetSlots x q (p 0)).card = 1)
    (h1 : (positiveQuartetSlots x q (p 1)).card = 1)
    (z : Point 5) (hz : InQuartetSection x q z) (k : Coordinate)
    (hnot : k ∉ positiveQuartetSlots x q (p 2)) : z k = 0 := by
  classical
  by_cases hp : 0 < quartetHalfWidth x q k
  · obtain ⟨i, hi⟩ := p.surjective (quartetPartition x q k)
    fin_cases i <;> dsimp only at hi
    · exact quartet_section_singleton_zero x q z hz (p 0) h0 k hi.symm
    · exact quartet_section_singleton_zero x q z hz (p 1) h1 k hi.symm
    · exact False.elim (hnot ((mem_positiveQuartetSlots x q _ k).mpr ⟨hi.symm, hp⟩))
  · have hzero : quartetHalfWidth x q k = 0 :=
      le_antisymm (le_of_not_gt hp) (quartetHalfWidth_nonneg x q k)
    exact quartet_section_zero_width x q z hz k hzero

theorem quartet_section_111_zero (x : Configuration) (q : Fin 4 → Label)
    (p : Equiv.Perm (Fin 3))
    (h0 : (positiveQuartetSlots x q (p 0)).card = 1)
    (h1 : (positiveQuartetSlots x q (p 1)).card = 1)
    (h2 : (positiveQuartetSlots x q (p 2)).card = 1)
    (z : Point 5) (hz : InQuartetSection x q z) : z = fun _ => 0 := by
  funext k
  obtain ⟨i, hi⟩ := p.surjective (quartetPartition x q k)
  fin_cases i <;> dsimp only at hi
  · exact quartet_section_singleton_zero x q z hz (p 0) h0 k hi.symm
  · exact quartet_section_singleton_zero x q z hz (p 1) h1 k hi.symm
  · exact quartet_section_singleton_zero x q z hz (p 2) h2 k hi.symm

/-- A genuine double/triple face belongs to the only nonsingleton type in
the 311 allocation. -/
theorem quartet_active_face_type_113 (x : Configuration) (q : Fin 4 → Label)
    (p : Equiv.Perm (Fin 3))
    (h0 : (positiveQuartetSlots x q (p 0)).card = 1)
    (h1 : (positiveQuartetSlots x q (p 1)).card = 1)
    (k : Coordinate)
    (hc : 2 ≤ (positiveQuartetSlots x q (quartetPartition x q k)).card) :
    quartetPartition x q k = p 2 := by
  obtain ⟨i, hi⟩ := p.surjective (quartetPartition x q k)
  fin_cases i <;> dsimp only at hi
  · rw [← hi] at hc
    change 2 ≤ (positiveQuartetSlots x q (p 0)).card at hc
    rw [h0] at hc
    omega
  · rw [← hi] at hc
    change 2 ≤ (positiveQuartetSlots x q (p 1)).card at hc
    rw [h1] at hc
    omega
  · exact hi.symm

/-- The original 311 physical section has an explicitly transported
closed tour. Its budget is derived from the actual three scalar widths. -/
theorem exists_original_113_section_tour (x : Configuration)
    (hx : UnitEquilateral x) (q : Fin 4 → Label) (hq : Function.Injective q)
    (p : Equiv.Perm (Fin 3))
    (h0 : (positiveQuartetSlots x q (p 0)).card = 1)
    (h1 : (positiveQuartetSlots x q (p 1)).card = 1)
    (h2 : (positiveQuartetSlots x q (p 2)).card = 3) :
    ∃ a : Point 5, ∃ path : PhysicalPath a a,
      path.budget ≤ 2 - 4 * quartetSingletonWidth x q 0 ∧
      ∀ z : Point 5, InQuartetSection x q z →
        (∃ k : Coordinate, 0 < quartetHalfWidth x q k ∧
          2 ≤ (positiveQuartetSlots x q (quartetPartition x q k)).card ∧
          |z k| = quartetHalfWidth x q k) → path.Covers z := by
  classical
  let S := positiveQuartetSlots x q (p 2)
  obtain ⟨e, he, himage⟩ := exists_finset_enumeration S 3 h2
  let L : Point 3 := fun i => quartetHalfWidth x q (e i)
  obtain ⟨a, path, hbudget, hcover⟩ :=
    exists_plane_box_tour L (fun i => quartetHalfWidth_nonneg x q (e i))
  let f := physicalEmbedding e
  have hf (u v : Point 3) : l1dist (f u) (f v) ≤ l1dist u v :=
    le_of_eq (physicalEmbedding_distance e he u v)
  refine ⟨f a, path.map f hf, ?_, ?_⟩
  · rw [PhysicalPath.map_budget]
    have hs : (∑ i, L i) = 1 / 4 - quartetSingletonWidth x q 0 / 2 := by
      rw [sum_finset_enumeration S e he himage (quartetHalfWidth x q),
        sum_positive_quartet_halfwidths]
      exact quartet_type_halfwidth_sum x hx q hq (p 2)
    rw [hs] at hbudget
    have hb := quartetSingletonWidth_nonneg x q 0
    linarith [path.nonneg]
  · intro z hz hface
    let u : Point 3 := fun i => z (e i)
    have hu : (∑ i, u i) = 0 := by
      rw [sum_finset_enumeration S e he himage z]
      exact quartet_section_positive_slot_sum x q z hz (p 2)
    have hub : InSymmetricBox L u := fun i => hz.1 (e i)
    obtain ⟨k, hkpos, hkcard, hkface⟩ := hface
    have hkt := quartet_active_face_type_113 x q p h0 h1 k hkcard
    have hk : k ∈ S := (mem_positiveQuartetSlots x q (p 2) k).mpr ⟨hkt, hkpos⟩
    rw [← himage] at hk
    obtain ⟨i, _, hei⟩ := Finset.mem_image.mp hk
    have huf : TouchesBoxFace L u := ⟨i, by simpa only [u, L, hei] using hkface⟩
    have hsupport (k : Coordinate) (hk : k ∉ Finset.univ.image e) : z k = 0 := by
      rw [himage] at hk
      exact quartet_section_supported_one_type x q p h0 h1 z hz k hk
    have heq : f u = z := physicalEmbedding_of_supported e he z hsupport
    rw [← heq]
    exact PhysicalPath.map_covers path f hf (hcover u hu hub huf)

/-- The 211 section is the literal double-coordinate line. Its parameter
diameter is at most one half, so three pair distances strictly above one
quarter are impossible. No boundary or zero-tail assertion is used here. -/
theorem not_three_original_112_section_points (x : Configuration)
    (hx : UnitEquilateral x) (q : Fin 4 → Label) (hq : Function.Injective q)
    (p : Equiv.Perm (Fin 3))
    (h0 : (positiveQuartetSlots x q (p 0)).card = 1)
    (h1 : (positiveQuartetSlots x q (p 1)).card = 1)
    (h2 : (positiveQuartetSlots x q (p 2)).card = 2)
    (z : Fin 3 → Point 5) (hz : ∀ i, InQuartetSection x q (z i))
    (hsep : ∀ i j, i ≠ j → 1 / 4 < l1dist (z i) (z j)) : False := by
  classical
  let S := positiveQuartetSlots x q (p 2)
  obtain ⟨e, he, himage⟩ := exists_finset_enumeration S 2 h2
  let A := min (quartetHalfWidth x q (e 0)) (quartetHalfWidth x q (e 1))
  let θ : Fin 3 → ℝ := fun i => 2 * z i (e 0)
  have hzsum (i : Fin 3) : z i (e 0) + z i (e 1) = 0 := by
    have hs : (∑ a : Fin 2, z i (e a)) = 0 := by
      rw [sum_finset_enumeration S e he himage (z i)]
      exact quartet_section_positive_slot_sum x q (z i) (hz i) (p 2)
    simpa [Fin.sum_univ_succ] using hs
  have hzembed (i : Fin 3) : physicalEmbedding e (fun a => z i (e a)) = z i := by
    apply physicalEmbedding_of_supported e he
    intro k hk
    rw [himage] at hk
    exact quartet_section_supported_one_type x q p h0 h1 (z i) (hz i) k hk
  have hdistance (i j : Fin 3) : l1dist (z i) (z j) = |θ i - θ j| := by
    rw [← hzembed i, ← hzembed j, physicalEmbedding_distance e he]
    have hsi := hzsum i
    have hsj := hzsum j
    have hd : z i (e 1) - z j (e 1) = -(z i (e 0) - z j (e 0)) := by linarith
    simp only [l1dist, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    change |z i (e 0) - z j (e 0)| + |z i (e 1) - z j (e 1)| = |θ i - θ j|
    rw [hd, abs_neg]
    change |z i (e 0) - z j (e 0)| + |z i (e 0) - z j (e 0)| =
      |2 * z i (e 0) - 2 * z j (e 0)|
    rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hθbounds (i : Fin 3) : -2 * A ≤ θ i ∧ θ i ≤ 2 * A := by
    have hb0 := (hz i).1 (e 0)
    have hb1 := (hz i).1 (e 1)
    have hs := hzsum i
    dsimp [θ, A]
    rcases le_total (quartetHalfWidth x q (e 0)) (quartetHalfWidth x q (e 1)) with h | h
    · rw [min_eq_left h]
      constructor <;> linarith [hb0.1, hb0.2]
    · rw [min_eq_right h]
      constructor <;> linarith [hb1.1, hb1.2]
  have hAspan : 4 * A ≤ 1 / 2 := by
    have hs : quartetHalfWidth x q (e 0) + quartetHalfWidth x q (e 1) =
        1 / 4 - quartetSingletonWidth x q 0 / 2 := by
      have hsum : (∑ a : Fin 2, quartetHalfWidth x q (e a)) =
          1 / 4 - quartetSingletonWidth x q 0 / 2 := by
        rw [sum_finset_enumeration S e he himage (quartetHalfWidth x q),
          sum_positive_quartet_halfwidths]
        exact quartet_type_halfwidth_sum x hx q hq (p 2)
      simpa [Fin.sum_univ_succ] using hsum
    have hA0 : A ≤ quartetHalfWidth x q (e 0) := min_le_left _ _
    have hA1 : A ≤ quartetHalfWidth x q (e 1) := min_le_right _ _
    linarith [quartetSingletonWidth_nonneg x q 0]
  let σ := actualOrder θ
  have hm : Monotone (fun i => θ (σ i)) := actualOrder_monotone θ
  have h01 : θ (σ 0) ≤ θ (σ 1) := hm (by decide : (0 : Fin 3) ≤ 1)
  have h12 : θ (σ 1) ≤ θ (σ 2) := hm (by decide : (1 : Fin 3) ≤ 2)
  have hsep01 := hsep (σ 0) (σ 1) (fun h => (by decide : (0 : Fin 3) ≠ 1) (σ.injective h))
  have hsep12 := hsep (σ 1) (σ 2) (fun h => (by decide : (1 : Fin 3) ≠ 2) (σ.injective h))
  rw [hdistance, abs_of_nonpos (sub_nonpos.mpr h01)] at hsep01
  rw [hdistance, abs_of_nonpos (sub_nonpos.mpr h12)] at hsep12
  have hlo := (hθbounds (σ 0)).1
  have hhi := (hθbounds (σ 2)).2
  linarith

private theorem paired_min_bounds {a b L M : ℝ} (hs : a + b = 0)
    (ha : -L ≤ a ∧ a ≤ L) (hb : -M ≤ b ∧ b ≤ M) :
    -min L M ≤ a ∧ a ≤ min L M := by
  rcases le_total L M with h | h
  · rw [min_eq_left h]
    exact ha
  · rw [min_eq_right h]
    constructor <;> linarith [hb.1, hb.2]

private theorem paired_face_min {a b L M : ℝ} (hs : a + b = 0)
    (ha : -L ≤ a ∧ a ≤ L) (hb : -M ≤ b ∧ b ≤ M)
    (hf : |a| = L ∨ |b| = M) : |a| = min L M := by
  have hab : b = -a := by linarith
  have habs : |b| = |a| := by rw [hab, abs_neg]
  have haL : |a| ≤ L := abs_le.mpr ha
  have haM : |a| ≤ M := by rw [← habs]; exact abs_le.mpr hb
  rcases hf with h | h
  · rw [← h, min_eq_left haM]
  · rw [habs] at h
    rw [← h, min_eq_right haL]

/-- The original 221 section is a literal paired rectangle in four distinct
physical coordinates. Its effective widths are minima of the two actual
widths in each balanced pair. -/
theorem exists_original_122_section_tour (x : Configuration)
    (hx : UnitEquilateral x) (q : Fin 4 → Label) (hq : Function.Injective q)
    (p : Equiv.Perm (Fin 3))
    (h0 : (positiveQuartetSlots x q (p 0)).card = 1)
    (h1 : (positiveQuartetSlots x q (p 1)).card = 2)
    (h2 : (positiveQuartetSlots x q (p 2)).card = 2) :
    ∃ a : Point 5, ∃ path : PhysicalPath a a,
      path.budget ≤ 2 - 4 * quartetSingletonWidth x q 0 ∧
      ∀ z : Point 5, InQuartetSection x q z →
        (∃ k : Coordinate, 0 < quartetHalfWidth x q k ∧
          2 ≤ (positiveQuartetSlots x q (quartetPartition x q k)).card ∧
          |z k| = quartetHalfWidth x q k) → path.Covers z := by
  classical
  let S1 := positiveQuartetSlots x q (p 1)
  let S2 := positiveQuartetSlots x q (p 2)
  obtain ⟨e1, he1, himage1⟩ := exists_finset_enumeration S1 2 h1
  obtain ⟨e2, he2, himage2⟩ := exists_finset_enumeration S2 2 h2
  have hmem1 (i : Fin 2) : e1 i ∈ S1 := by
    rw [← himage1]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hmem2 (i : Fin 2) : e2 i ∈ S2 := by
    rw [← himage2]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have htag1 (i : Fin 2) : quartetPartition x q (e1 i) = p 1 :=
    ((mem_positiveQuartetSlots x q (p 1) (e1 i)).mp (hmem1 i)).1
  have htag2 (i : Fin 2) : quartetPartition x q (e2 i) = p 2 :=
    ((mem_positiveQuartetSlots x q (p 2) (e2 i)).mp (hmem2 i)).1
  have hcross (i j : Fin 2) : e1 i ≠ e2 j := by
    intro heq
    have ht : p 1 = p 2 := (htag1 i).symm.trans ((congrArg (quartetPartition x q) heq).trans (htag2 j))
    exact (by decide : (1 : Fin 3) ≠ 2) (p.injective ht)
  let e : Fin 4 → Coordinate := ![e1 0, e1 1, e2 0, e2 1]
  have hne1 : e1 0 ≠ e1 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (he1 h)
  have hne2 : e2 0 ≠ e2 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (he2 h)
  have he : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [e, hcross]
  let A := min (quartetHalfWidth x q (e1 0)) (quartetHalfWidth x q (e1 1))
  let B := min (quartetHalfWidth x q (e2 0)) (quartetHalfWidth x q (e2 1))
  have hA : 0 ≤ A := le_min (quartetHalfWidth_nonneg x q _) (quartetHalfWidth_nonneg x q _)
  have hB : 0 ≤ B := le_min (quartetHalfWidth_nonneg x q _) (quartetHalfWidth_nonneg x q _)
  let path := polygonFour (pairedRectangle A B)
  let f := physicalEmbedding e
  have hf (u v : Point 4) : l1dist (f u) (f v) ≤ l1dist u v :=
    le_of_eq (physicalEmbedding_distance e he u v)
  refine ⟨f (pairedRectangle A B 0), path.map f hf, ?_, ?_⟩
  · rw [PhysicalPath.map_budget, pairedRectangle_budget A B hA hB]
    have hsum1 : quartetHalfWidth x q (e1 0) + quartetHalfWidth x q (e1 1) =
        1 / 4 - quartetSingletonWidth x q 0 / 2 := by
      have hs : (∑ i : Fin 2, quartetHalfWidth x q (e1 i)) =
          1 / 4 - quartetSingletonWidth x q 0 / 2 := by
        rw [sum_finset_enumeration S1 e1 he1 himage1 (quartetHalfWidth x q),
          sum_positive_quartet_halfwidths]
        exact quartet_type_halfwidth_sum x hx q hq (p 1)
      simpa [Fin.sum_univ_succ] using hs
    have hsum2 : quartetHalfWidth x q (e2 0) + quartetHalfWidth x q (e2 1) =
        1 / 4 - quartetSingletonWidth x q 0 / 2 := by
      have hs : (∑ i : Fin 2, quartetHalfWidth x q (e2 i)) =
          1 / 4 - quartetSingletonWidth x q 0 / 2 := by
        rw [sum_finset_enumeration S2 e2 he2 himage2 (quartetHalfWidth x q),
          sum_positive_quartet_halfwidths]
        exact quartet_type_halfwidth_sum x hx q hq (p 2)
      simpa [Fin.sum_univ_succ] using hs
    have hA0 : A ≤ quartetHalfWidth x q (e1 0) := min_le_left _ _
    have hA1 : A ≤ quartetHalfWidth x q (e1 1) := min_le_right _ _
    have hB0 : B ≤ quartetHalfWidth x q (e2 0) := min_le_left _ _
    have hB1 : B ≤ quartetHalfWidth x q (e2 1) := min_le_right _ _
    linarith
  · intro z hz hface
    let u : Point 4 := fun i => z (e i)
    have hs1 : z (e1 0) + z (e1 1) = 0 := by
      have hs : (∑ i : Fin 2, z (e1 i)) = 0 := by
        rw [sum_finset_enumeration S1 e1 he1 himage1 z]
        exact quartet_section_positive_slot_sum x q z hz (p 1)
      simpa [Fin.sum_univ_succ] using hs
    have hs2 : z (e2 0) + z (e2 1) = 0 := by
      have hs : (∑ i : Fin 2, z (e2 i)) = 0 := by
        rw [sum_finset_enumeration S2 e2 he2 himage2 z]
        exact quartet_section_positive_slot_sum x q z hz (p 2)
      simpa [Fin.sum_univ_succ] using hs
    have hu01 : u 0 + u 1 = 0 := hs1
    have hu23 : u 2 + u 3 = 0 := hs2
    have huA : -A ≤ u 0 ∧ u 0 ≤ A :=
      paired_min_bounds hs1 (hz.1 (e1 0)) (hz.1 (e1 1))
    have huB : -B ≤ u 2 ∧ u 2 ≤ B :=
      paired_min_bounds hs2 (hz.1 (e2 0)) (hz.1 (e2 1))
    obtain ⟨k, hkpos, hkcard, hkface⟩ := hface
    have huf : |u 0| = A ∨ |u 2| = B := by
      obtain ⟨i, hi⟩ := p.surjective (quartetPartition x q k)
      fin_cases i <;> dsimp only at hi
      · rw [← hi] at hkcard
        change 2 ≤ (positiveQuartetSlots x q (p 0)).card at hkcard
        rw [h0] at hkcard
        omega
      · left
        have hk : k ∈ S1 := (mem_positiveQuartetSlots x q (p 1) k).mpr ⟨hi.symm, hkpos⟩
        rw [← himage1] at hk
        obtain ⟨j, _, hej⟩ := Finset.mem_image.mp hk
        apply paired_face_min hs1 (hz.1 (e1 0)) (hz.1 (e1 1))
        fin_cases j <;> dsimp only at hej
        · change e1 0 = k at hej
          exact Or.inl (by rw [hej]; exact hkface)
        · change e1 1 = k at hej
          exact Or.inr (by rw [hej]; exact hkface)
      · right
        have hk : k ∈ S2 := (mem_positiveQuartetSlots x q (p 2) k).mpr ⟨hi.symm, hkpos⟩
        rw [← himage2] at hk
        obtain ⟨j, _, hej⟩ := Finset.mem_image.mp hk
        apply paired_face_min hs2 (hz.1 (e2 0)) (hz.1 (e2 1))
        fin_cases j <;> dsimp only at hej
        · change e2 0 = k at hej
          exact Or.inl (by rw [hej]; exact hkface)
        · change e2 1 = k at hej
          exact Or.inr (by rw [hej]; exact hkface)
    have hsupport (k : Coordinate) (hk : k ∉ Finset.univ.image e) : z k = 0 := by
      by_cases hp : 0 < quartetHalfWidth x q k
      · obtain ⟨i, hi⟩ := p.surjective (quartetPartition x q k)
        fin_cases i <;> dsimp only at hi
        · exact quartet_section_singleton_zero x q z hz (p 0) h0 k hi.symm
        · have hks : k ∈ S1 := (mem_positiveQuartetSlots x q (p 1) k).mpr ⟨hi.symm, hp⟩
          rw [← himage1] at hks
          obtain ⟨j, _, hej⟩ := Finset.mem_image.mp hks
          apply False.elim
          apply hk
          fin_cases j <;> dsimp only at hej
          · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hej⟩
          · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, hej⟩
        · have hks : k ∈ S2 := (mem_positiveQuartetSlots x q (p 2) k).mpr ⟨hi.symm, hp⟩
          rw [← himage2] at hks
          obtain ⟨j, _, hej⟩ := Finset.mem_image.mp hks
          apply False.elim
          apply hk
          fin_cases j <;> dsimp only at hej
          · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, hej⟩
          · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, hej⟩
      · have hzero : quartetHalfWidth x q k = 0 :=
          le_antisymm (le_of_not_gt hp) (quartetHalfWidth_nonneg x q k)
        exact quartet_section_zero_width x q z hz k hzero
    have heq : f u = z := physicalEmbedding_of_supported e he z hsupport
    rw [← heq]
    apply PhysicalPath.map_covers path f hf
    exact pairedRectangle_covers A B hA hB u hu01 hu23 huA huB huf

end
end Kusner5
