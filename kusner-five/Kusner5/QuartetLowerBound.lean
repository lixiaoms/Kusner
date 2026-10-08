import Kusner5.QuartetPhysicalSlots

/-!
The arbitrary ORIGINAL quartet lower bound. This file constructs the paid
seven-outside-point section, exhausts all positive physical slot allocations,
and compares the same ordered seven-point cycle with the literal section
perimeter. No matching, contact, general-position or auxiliary distance
preservation assumption is present in the public theorems.
-/

namespace Kusner5

open scoped BigOperators
open QuartetGeometry

noncomputable section

theorem original_quartet_singleton_ge_one_twenty_fourth
    (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q) :
    1 / 24 ≤ quartetSingletonWidth x q 0 := by
  classical
  by_contra hn
  have hb : quartetSingletonWidth x q 0 < 1 / 24 := lt_of_not_ge hn
  obtain ⟨r, hr, hout⟩ := exists_seven_original_outsiders q hq
  have hp (j : Fin 7) :
      ∃ z : Point 5, InQuartetSection x q z ∧
        l1dist z (quartetReflectedClamp x q (r j)) =
          agreementDisplacement (quartetAgreement x q (r j)) ∧
        ((∑ t : Fin 3, (positiveQuartetSlots x q t).card) = 5 →
          ∃ k : Coordinate, 0 < quartetHalfWidth x q k ∧
            2 ≤ (positiveQuartetSlots x q (quartetPartition x q k)).card ∧
            |z k| = quartetHalfWidth x q k) := by
    by_cases hfive : (∑ t : Fin 3, (positiveQuartetSlots x q t).card) = 5
    · obtain ⟨z, hbox, hsum, hpaid, hface⟩ :=
        exists_original_quartet_face_projection x hx q hq hb hfive (r j) (hout j)
      exact ⟨z, ⟨hbox, hsum⟩, hpaid, fun _ => hface⟩
    · obtain ⟨z, hbox, hsum, hpaid⟩ :=
        exists_original_quartet_projection x hx q hq (r j) (hout j)
      exact ⟨z, ⟨hbox, hsum⟩, hpaid, fun h => False.elim (hfive h)⟩
  choose z hz hpaid hface using hp
  have hsep (i j : Fin 7) (hij : i ≠ j) : 1 / 4 < l1dist (z i) (z j) := by
    have hl := quartet_projected_pair_separation x hx q hq (r i) (r j)
      (hout i) (hout j) (fun h => hij (hr h)) (z i) (z j)
      (le_of_eq (hpaid i)) (le_of_eq (hpaid j))
    linarith
  have hclose {a : Point 5} (path : PhysicalPath a a)
      (hbudget : path.budget ≤ 2 - 4 * quartetSingletonWidth x q 0)
      (hcover : ∀ j, path.Covers (z j)) : False := by
    obtain ⟨σ, hupper⟩ := seven_cycle_of_closed_path path z hcover
    have hlower := original_projected_seven_cycle_lower x hx q hq
      (fun j => r (σ j)) (hr.comp σ.injective) (fun j i => hout (σ j) i)
      (fun j => z (σ j)) (fun j => le_of_eq (hpaid (σ j)))
    linarith
  obtain ⟨p, hcases⟩ := original_quartet_positive_slot_classification x hx q hq hb
  rcases hcases with h111 | h112 | h113 | h122
  · have hz0 := quartet_section_111_zero x q p h111.1 h111.2.1 h111.2.2 (z 0) (hz 0)
    have hz1 := quartet_section_111_zero x q p h111.1 h111.2.1 h111.2.2 (z 1) (hz 1)
    have hs := hsep 0 1 (by decide)
    rw [hz0, hz1, l1dist_self] at hs
    linarith
  · let e : Fin 3 → Fin 7 := fun i => ⟨i.val, by omega⟩
    have he : Function.Injective e := by
      intro i j hij
      exact Fin.ext (congrArg (fun t : Fin 7 => t.val) hij)
    exact not_three_original_112_section_points x hx q hq p h112.1 h112.2.1 h112.2.2
      (fun i => z (e i)) (fun i => hz (e i))
      (fun i j hij => hsep (e i) (e j) (fun h => hij (he h)))
  · have hfive : (∑ t : Fin 3, (positiveQuartetSlots x q t).card) = 5 := by
      rw [← sum_perm p (fun t => (positiveQuartetSlots x q t).card)]
      norm_num [Fin.sum_univ_succ, h113.1, h113.2.1, h113.2.2]
    obtain ⟨a, path, hbudget, hcover⟩ :=
      exists_original_113_section_tour x hx q hq p h113.1 h113.2.1 h113.2.2
    exact hclose path hbudget (fun j => hcover (z j) (hz j) (hface j hfive))
  · have hfive : (∑ t : Fin 3, (positiveQuartetSlots x q t).card) = 5 := by
      rw [← sum_perm p (fun t => (positiveQuartetSlots x q t).card)]
      norm_num [Fin.sum_univ_succ, h122.1, h122.2.1, h122.2.2]
    obtain ⟨a, path, hbudget, hcover⟩ :=
      exists_original_122_section_tour x hx q hq p h122.1 h122.2.1 h122.2.2
    exact hclose path hbudget (fun j => hcover (z j) (hz j) (hface j hfive))

/-- Genuine max-minus-min width lower bound for every injection of four
labels from the same arbitrary original real l1 equilateral configuration. -/
theorem original_quartet_width_ge_thirty_seven_twenty_fourths
    (x : Configuration) (hx : UnitEquilateral x)
    (q : Fin 4 → Label) (hq : Function.Injective q) :
    37 / 24 ≤ quartetWidth x q := by
  rw [quartet_width_identity x hx q hq]
  linarith [original_quartet_singleton_ge_one_twenty_fourth x hx q hq]

end
end Kusner5
